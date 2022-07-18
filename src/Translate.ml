open InterpreterStatements
open Interpreter
module L = Logging
module T = Types
module A = LlbcAst
module M = Modules
module SA = SymbolicAst
module Micro = PureMicroPasses
open PureUtils
open TranslateCore

(** The local logger *)
let log = TranslateCore.log

type config = {
  eval_config : Contexts.partial_config;
  mp_config : Micro.config;
  use_state : bool;
      (** Controls whether we need to use a state to model the external world
          (I/O, for instance).
       *)
  split_files : bool;
      (** Controls whether we split the generated definitions between different
          files for the types, clauses and functions, or if we group them in
          one file.
       *)
  test_unit_functions : bool;
      (** If true, insert tests in the generated files to check that the
          unit functions normalize to `Success _`.
          
          For instance, in F* it generates code like this:
          ```
          let _ = assert_norm (FUNCTION () = Success ())
          ```
       *)
  extract_decreases_clauses : bool;
      (** If `true`, insert `decreases` clauses for all the recursive definitions.

          The body of such clauses must be defined by the user.
       *)
  extract_template_decreases_clauses : bool;
      (** In order to help the user, we can generate "template" decrease clauses
          (i.e., definitions with proper signatures but dummy bodies) in a
          dedicated file.
       *)
}

type symbolic_fun_translation = V.symbolic_value list * SA.expression
(** The result of running the symbolic interpreter on a function:
    - the list of symbolic values used for the input values
    - the generated symbolic AST
*)

(** Execute the symbolic interpreter on a function to generate a list of symbolic ASTs,
    for the forward function and the backward functions.
*)
let translate_function_to_symbolics (config : C.partial_config)
    (trans_ctx : trans_ctx) (fdef : A.fun_decl) :
    (symbolic_fun_translation * symbolic_fun_translation list) option =
  (* Debug *)
  log#ldebug
    (lazy
      ("translate_function_to_symbolics: "
      ^ Print.fun_name_to_string fdef.A.name));

  let { type_context; fun_context; global_context } = trans_ctx in
  let fun_context = {
    C.fun_decls = fun_context.fun_decls;
  } in

  match fdef.body with
  | None -> None
  | Some _ ->
      (* Evaluate *)
      let synthesize = true in
      let evaluate gid =
        let inputs, symb =
          evaluate_function_symbolic config synthesize
            type_context fun_context global_context
            fdef gid
        in
        (inputs, Option.get symb)
      in
      (* Execute the forward function *)
      let forward = evaluate None in
      (* Execute the backward functions *)
      let backwards =
        T.RegionGroupId.mapi
          (fun gid _ -> evaluate (Some gid))
          fdef.signature.regions_hierarchy
      in

      (* Return *)
      Some (forward, backwards)

(** Translate a function, by generating its forward and backward translations.

    [fun_sigs]: maps the forward/backward functions to their signatures. In case
    of backward functions, we also provide names for the outputs.
    TODO: maybe we should introduce a record for this.
*)
let translate_function_to_pure (config : C.partial_config)
    (mp_config : Micro.config) (trans_ctx : trans_ctx)
    (fun_sigs : SymbolicToPure.fun_sig_named_outputs RegularFunIdMap.t)
    (pure_type_decls : Pure.type_decl Pure.TypeDeclId.Map.t)
    (fdef : A.fun_decl)
    : pure_fun_translation =
  (* Debug *)
  log#ldebug
    (lazy
      ("translate_function_to_pure: " ^ Print.fun_name_to_string fdef.A.name));

  let { type_context; fun_context; global_context } = trans_ctx in
  let def_id = fdef.def_id in

  (* Compute the symbolic ASTs, if the function is transparent *)
  let symbolic_trans = translate_function_to_symbolics config trans_ctx fdef in
  let symbolic_forward, symbolic_backwards =
    match symbolic_trans with
    | None -> (None, None)
    | Some (fwd, backs) -> (Some fwd, Some backs)
  in

  (* Convert the symbolic ASTs to pure ASTs: *)

  (* Initialize the context *)
  let forward_sig = RegularFunIdMap.find (A.Regular def_id, None) fun_sigs in
  let sv_to_var = V.SymbolicValueId.Map.empty in
  let var_counter = Pure.VarId.generator_zero in
  let state_var, var_counter = Pure.VarId.fresh var_counter in
  let calls = V.FunCallId.Map.empty in
  let abstractions = V.AbstractionId.Map.empty in
  let type_context =
    {
      SymbolicToPure.types_infos = type_context.type_infos;
      llbc_type_decls = type_context.type_decls;
      type_decls = pure_type_decls;
    }
  in
  let fun_context =
    {
      SymbolicToPure.llbc_fun_decls = fun_context.fun_decls;
      fun_sigs;
      fun_infos = fun_context.fun_infos;
    }
  in
  let global_context = {
      SymbolicToPure.llbc_global_decls = global_context.global_decls
    }
  in
  let ctx =
    {
      SymbolicToPure.bid = None;
      (* Dummy for now *)
      sg = forward_sig.sg;
      (* Will need to be updated for the backward functions *)
      sv_to_var;
      var_counter;
      state_var;
      type_context;
      fun_context;
      global_context;
      fun_decl = fdef;
      forward_inputs = [];
      (* Empty for now *)
      backward_inputs = T.RegionGroupId.Map.empty;
      (* Empty for now *)
      backward_outputs = T.RegionGroupId.Map.empty;
      (* Empty for now *)
      calls;
      abstractions;
    }
  in

  (* We need to initialize the input/output variables *)
  let num_forward_inputs = List.length fdef.signature.inputs in
  let add_forward_inputs input_svs ctx =
    match fdef.body with
    | None -> ctx
    | Some body ->
        let forward_input_vars = LlbcAstUtils.fun_body_get_input_vars body in
        let forward_input_varnames =
          List.map (fun (v : A.var) -> v.name) forward_input_vars
        in
        let input_svs = List.combine forward_input_varnames input_svs in
        let ctx, forward_inputs =
          SymbolicToPure.fresh_named_vars_for_symbolic_values input_svs ctx
        in
        { ctx with forward_inputs }
  in

  (* The symbolic to pure config *)
  let sp_config =
    {
      SymbolicToPure.filter_useless_back_calls =
        mp_config.filter_useless_monadic_calls;
    }
  in

  (* Translate the forward function *)
  let pure_forward =
    match symbolic_forward with
    | None -> SymbolicToPure.translate_fun_decl sp_config ctx None
    | Some (fwd_svs, fwd_ast) ->
        SymbolicToPure.translate_fun_decl sp_config
          (add_forward_inputs fwd_svs ctx)
          (Some fwd_ast)
  in

  (* Translate the backward functions *)
  let translate_backward (rg : T.region_var_group) : Pure.fun_decl =
    (* For the backward inputs/outputs initialization: we use the fact that
     * there are no nested borrows for now, and so that the region groups
     * can't have parents *)
    assert (rg.parents = []);
    let back_id = rg.id in

    match symbolic_backwards with
    | None ->
        (* Initialize the context - note that the ret_ty is not really
         * useful as we don't translate a body *)
        let backward_sg =
          RegularFunIdMap.find (A.Regular def_id, Some back_id) fun_sigs
        in
        let ctx = { ctx with bid = Some back_id; sg = backward_sg.sg } in

        (* Translate *)
        SymbolicToPure.translate_fun_decl sp_config ctx None
    | Some symbolic_backwards ->
        let input_svs, symbolic =
          T.RegionGroupId.nth symbolic_backwards back_id
        in
        let ctx = add_forward_inputs input_svs ctx in
        (* TODO: the computation of the backward inputs is a bit awckward... *)
        let backward_sg =
          RegularFunIdMap.find (A.Regular def_id, Some back_id) fun_sigs
        in
        (* We need to ignore the forward inputs, and the state input (if there is) *)
        let fun_info =
          SymbolicToPure.get_fun_effect_info fun_context.fun_infos
            (A.Regular def_id) (Some back_id)
        in
        let _, backward_inputs =
          Collections.List.split_at backward_sg.sg.inputs
            (num_forward_inputs + if fun_info.input_state then 1 else 0)
        in
        (* As we forbid nested borrows, the additional inputs for the backward
         * functions come from the borrows in the return value of the rust function:
         * we thus use the name "ret" for those inputs *)
        let backward_inputs =
          List.map (fun ty -> (Some "ret", ty)) backward_inputs
        in
        let ctx, backward_inputs =
          SymbolicToPure.fresh_vars backward_inputs ctx
        in
        (* The outputs for the backward functions, however, come from borrows
         * present in the input values of the rust function: for those we reuse
         * the names of the  input values. *)
        let backward_outputs =
          List.combine backward_sg.output_names backward_sg.sg.doutputs
        in
        let ctx, backward_outputs =
          SymbolicToPure.fresh_vars backward_outputs ctx
        in
        let backward_inputs =
          T.RegionGroupId.Map.singleton back_id backward_inputs
        in
        let backward_outputs =
          T.RegionGroupId.Map.singleton back_id backward_outputs
        in

        (* Put everything in the context *)
        let ctx =
          {
            ctx with
            bid = Some back_id;
            sg = backward_sg.sg;
            backward_inputs;
            backward_outputs;
          }
        in

        (* Translate *)
        SymbolicToPure.translate_fun_decl sp_config ctx (Some symbolic)
  in
  let pure_backwards =
    List.map translate_backward fdef.signature.regions_hierarchy
  in

  (* Return *)
  (pure_forward, pure_backwards)

let translate_module_to_pure (config : C.partial_config)
    (mp_config : Micro.config) (use_state : bool) (m : M.llbc_module) :
    trans_ctx * Pure.type_decl list * (bool * pure_fun_translation) list =
  (* Debug *)
  log#ldebug (lazy "translate_module_to_pure");

  (* Compute the type and function contexts *)
  let type_context, fun_context, global_context = compute_type_fun_contexts m in
  let fun_infos = FA.analyze_module m fun_context.C.fun_decls use_state in
  let fun_context = {
    fun_decls = fun_context.fun_decls;
    fun_infos;
  } in
  let trans_ctx = { type_context; fun_context; global_context } in

  (* Translate all the type definitions *)
  let type_decls = SymbolicToPure.translate_type_decls m.types in

  (* Compute the type definition map *)
  let type_decls_map =
    Pure.TypeDeclId.Map.of_list
      (List.map (fun (def : Pure.type_decl) -> (def.def_id, def)) type_decls)
  in

  (* Translate all the function *signatures* *)
  let assumed_sigs =
    List.map
      (fun (id, sg, _, _) ->
        (A.Assumed id, List.map (fun _ -> None) (sg : A.fun_sig).inputs, sg))
      Assumed.assumed_infos
  in
  let local_sigs =
    List.map
      (fun (fdef : A.fun_decl) ->
        let input_names =
          match fdef.body with
          | None -> List.map (fun _ -> None) fdef.signature.inputs
          | Some body ->
              List.map
                (fun (v : A.var) -> v.name)
                (LlbcAstUtils.fun_body_get_input_vars body)
        in
        (A.Regular fdef.def_id, input_names, fdef.signature))
      m.functions
  in
  let sigs = List.append assumed_sigs local_sigs in
  let fun_sigs =
    SymbolicToPure.translate_fun_signatures fun_context.fun_infos
      type_context.type_infos sigs
  in

  (* Translate all the *transparent* functions *)
  let pure_translations =
    List.map
      (translate_function_to_pure config mp_config trans_ctx fun_sigs
         type_decls_map)
      m.functions
  in

  (* Apply the micro-passes *)
  let pure_translations =
    List.map
      (Micro.apply_passes_to_pure_fun_translation mp_config trans_ctx)
      pure_translations
  in

  (* Return *)
  (trans_ctx, type_decls, pure_translations)

type gen_ctx = {
  m : M.llbc_module;
  extract_ctx : PureToExtract.extraction_ctx;
  trans_types : Pure.type_decl Pure.TypeDeclId.Map.t;
  trans_funs : (bool * pure_fun_translation) A.FunDeclId.Map.t;
  functions_with_decreases_clause : A.FunDeclId.Set.t;
}
(** Extraction context *)

type gen_config = {
  mp_config : Micro.config;
  use_state : bool;
  extract_types : bool;
  extract_decreases_clauses : bool;
  extract_template_decreases_clauses : bool;
  extract_fun_decls : bool;
  extract_transparent : bool;
      (** If `true`, extract the transparent declarations, otherwise ignore. *)
  extract_opaque : bool;
      (** If `true`, extract the opaque declarations, otherwise ignore. *)
  extract_state_type : bool;
      (** If `true`, generate a definition/declaration for the state type *)
  interface : bool;
      (** `true` if we generate an interface file, `false` otherwise.
          For now, this only impacts whether we use `val` or `assume val` for the
          opaque definitions. In the future, we might want to extract all the
          declarations in an interface file, together with an implementation file
          if needed.
       *)
  test_unit_functions : bool;
}

(** Returns the pair: (has opaque type decls, has opaque fun decls) *)
let module_has_opaque_decls (ctx : gen_ctx) : bool * bool =
  let has_opaque_types =
    Pure.TypeDeclId.Map.exists
      (fun _ (d : Pure.type_decl) ->
        match d.kind with Opaque -> true | _ -> false)
      ctx.trans_types
  in
  let has_opaque_funs =
    A.FunDeclId.Map.exists
      (fun _ ((_, (t_fwd, _)) : bool * pure_fun_translation) ->
        Option.is_none t_fwd.body)
      ctx.trans_funs
  in
  (has_opaque_types, has_opaque_funs)

(** A generic utility to generate the extracted definitions: as we may want to
    split the definitions between different files (or not), we can control
    what is precisely extracted.
 *)
let extract_definitions (fmt : Format.formatter) (config : gen_config)
    (ctx : gen_ctx) : unit =
  (* Export the definition groups to the file, in the proper order *)
  let export_type (qualif : ExtractToFStar.type_decl_qualif)
      (id : Pure.TypeDeclId.id) : unit =
    (* Retrive the declaration *)
    let def = Pure.TypeDeclId.Map.find id ctx.trans_types in
    (* Update the qualifier, if the type is opaque *)
    let is_opaque, qualif =
      match def.kind with
      | Enum _ | Struct _ -> (false, qualif)
      | Opaque ->
          let qualif =
            if config.interface then ExtractToFStar.TypeVal
            else ExtractToFStar.AssumeType
          in
          (true, qualif)
    in
    (* Extract, if the config instructs to do so (depending on whether the type
     * is opaque or not) *)
    if
      (is_opaque && config.extract_opaque)
      || ((not is_opaque) && config.extract_transparent)
    then ExtractToFStar.extract_type_decl ctx.extract_ctx fmt qualif def
  in

  (* Utility to check a function has a decrease clause *)
  let has_decreases_clause (def : Pure.fun_decl) : bool =
    A.FunDeclId.Set.mem def.def_id ctx.functions_with_decreases_clause
  in

  (* In case of (non-mutually) recursive functions, we use a simple procedure to
   * check if the forward and backward functions are mutually recursive.
   *)
  let export_functions (is_rec : bool)
      (pure_ls : (bool * pure_fun_translation) list) : unit =
    (* Concatenate the function definitions, filtering the useless forward
     * functions. We also make pairs: (forward function, backward function)
     * (the forward function contains useful information that we want to keep) *)
    let fls =
      List.concat
        (List.map
           (fun (keep_fwd, (fwd, back_ls)) ->
             let back_ls = List.map (fun back -> (fwd, back)) back_ls in
             if keep_fwd then (fwd, fwd) :: back_ls else back_ls)
           pure_ls)
    in
    (* Extract the decrease clauses template bodies *)
    if config.extract_template_decreases_clauses then
      List.iter
        (fun (_, (fwd, _)) ->
          let has_decr_clause = has_decreases_clause fwd in
          if has_decr_clause then
            ExtractToFStar.extract_template_decreases_clause ctx.extract_ctx fmt
              fwd)
        pure_ls;
    (* Extract the function definitions *)
    (if config.extract_fun_decls then
     (* Check if the functions are mutually recursive - this really works
      * to check if the forward and backward translations of a single
      * recursive function are mutually recursive *)
     let is_mut_rec =
       if is_rec then
         if List.length pure_ls <= 1 then
           not (PureUtils.functions_not_mutually_recursive (List.map fst fls))
         else true
       else false
     in
     List.iteri
       (fun i (fwd_def, def) ->
         let is_opaque = Option.is_none fwd_def.Pure.body in
         let qualif =
           if is_opaque then
             if config.interface then ExtractToFStar.Val
             else ExtractToFStar.AssumeVal
           else if not is_rec then ExtractToFStar.Let
           else if is_mut_rec then
             if i = 0 then ExtractToFStar.LetRec else ExtractToFStar.And
           else ExtractToFStar.LetRec
         in
         let has_decr_clause =
           has_decreases_clause def && config.extract_decreases_clauses
         in
         (* Check if the definition needs to be filtered or not *)
         if
           ((not is_opaque) && config.extract_transparent)
           || (is_opaque && config.extract_opaque)
         then if def.is_global_body
          then ExtractToFStar.extract_global_decl ctx.extract_ctx fmt qualif def
          else ExtractToFStar.extract_fun_decl ctx.extract_ctx fmt qualif has_decr_clause def
        )
       fls);
    (* Insert unit tests if necessary *)
    if config.test_unit_functions then
      List.iter
        (fun (keep_fwd, (fwd, _)) ->
          if keep_fwd then
            ExtractToFStar.extract_unit_test_if_unit_fun ctx.extract_ctx fmt fwd)
        pure_ls
  in

  let export_state_type () : unit =
    let qualif =
      if config.interface then ExtractToFStar.TypeVal
      else ExtractToFStar.AssumeType
    in
    ExtractToFStar.extract_state_type fmt ctx.extract_ctx qualif
  in

  let export_decl (decl : M.declaration_group) : unit =
    match decl with
    | Type (NonRec id) ->
        if config.extract_types then export_type ExtractToFStar.Type id
    | Type (Rec ids) ->
        (* Rk.: we shouldn't have (mutually) recursive opaque types *)
        if config.extract_types then
          List.iteri
            (fun i id ->
              let qualif =
                if i = 0 then ExtractToFStar.Type else ExtractToFStar.And
              in
              export_type qualif id)
            ids
    | Fun (NonRec id) ->
        (* Lookup *)
        let pure_fun = A.FunDeclId.Map.find id ctx.trans_funs in
        (* Translate *)
        export_functions false [ pure_fun ]
    | Fun (Rec ids) ->
        (* General case of mutually recursive functions *)
        (* Lookup *)
        let pure_funs =
          List.map (fun id -> A.FunDeclId.Map.find id ctx.trans_funs) ids
        in
        (* Translate *)
        export_functions true pure_funs
  in

  (* If we need to export the state type: we try to export it after we defined
   * the type definitions, because if the user wants to define a model for the
   * type, he might want to reuse them in the state type.
   * More specifically: if we extract functions, we have no choice but to define
   * the state type before the functions, because they may reuse this state
   * type: in this case, we define/declare it at the very beginning. Otherwise,
   * we define/declare it at the very end.
   *)
  if config.extract_state_type && config.extract_fun_decls then
    export_state_type ();
  List.iter export_decl ctx.m.declarations;
  if config.extract_state_type && not config.extract_fun_decls then
    export_state_type ()

let extract_file (config : gen_config) (ctx : gen_ctx) (filename : string)
    (rust_module_name : string) (module_name : string) (custom_msg : string)
    (custom_imports : string list) (custom_includes : string list) : unit =
  (* Open the file and create the formatter *)
  let out = open_out filename in
  let fmt = Format.formatter_of_out_channel out in

  (* Print the headers.
   * Note that we don't use the OCaml formatter for purpose: we want to control
   * line insertion (we have to make sure that some instructions like `open MODULE`
   * are printed on one line!).
   * This is ok as long as we end up with a line break, so that the formatter's
   * internal count is consistent with the state of the file.
   *)
  (* Create the header *)
  Printf.fprintf out "(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)\n";
  Printf.fprintf out "(** [%s]%s *)\n" rust_module_name custom_msg;
  Printf.fprintf out "module %s\n" module_name;
  Printf.fprintf out "open Primitives\n";
  (* Add the custom imports *)
  List.iter (fun m -> Printf.fprintf out "open %s\n" m) custom_imports;
  (* Add the custom includes *)
  List.iter (fun m -> Printf.fprintf out "include %s\n" m) custom_includes;
  (* Z3 options - note that we use fuel 1 because it its useful for the decrease clauses *)
  Printf.fprintf out "\n#set-options \"--z3rlimit 50 --fuel 1 --ifuel 1\"\n";

  (* From now onwards, we use the formatter *)
  (* Set the margin *)
  Format.pp_set_margin fmt 80;

  (* Create a vertical box *)
  Format.pp_open_vbox fmt 0;

  (* Extract the definitions *)
  extract_definitions fmt config ctx;

  (* Close the box and end the formatting *)
  Format.pp_close_box fmt ();
  Format.pp_print_newline fmt ();

  (* Some logging *)
  log#linfo (lazy ("Generated: " ^ filename));

  (* Flush and close the file *)
  close_out out

(** Translate a module and write the synthesized code to an output file.
    TODO: rename to translate_crate
 *)
let translate_module (filename : string) (dest_dir : string) (config : config)
    (m : M.llbc_module) : unit =
  (* Translate the module to the pure AST *)
  let trans_ctx, trans_types, trans_funs =
    translate_module_to_pure config.eval_config config.mp_config
      config.use_state m
  in

  (* Initialize the extraction context - for now we extract only to F* *)
  let names_map =
    PureToExtract.initialize_names_map ExtractToFStar.fstar_names_map_init
  in
  let variant_concatenate_type_name = true in
  let fstar_fmt =
    ExtractToFStar.mk_formatter trans_ctx m.name variant_concatenate_type_name
  in
  let ctx =
    { PureToExtract.trans_ctx; names_map; fmt = fstar_fmt; indent_incr = 2 }
  in

  (* We need to compute which functions are recursive, in order to know
   * whether we should generate a decrease clause or not. *)
  let rec_functions =
    A.FunDeclId.Set.of_list
      (List.concat
         (List.map
            (fun decl -> match decl with M.Fun (Rec ids) -> ids | _ -> [])
            m.declarations))
  in

  (* Register unique names for all the top-level types and functions.
   * Note that the order in which we generate the names doesn't matter:
   * we just need to generate a mapping from identifier to name, and make
   * sure there are no name clashes. *)
  let ctx =
    List.fold_left
      (fun ctx def -> ExtractToFStar.extract_type_decl_register_names ctx def)
      ctx trans_types
  in

  let ctx =
    List.fold_left
      (fun ctx (keep_fwd, def) ->
        (* Note that we generate a decrease clause for all the recursive functions *)
        let gen_decr_clause =
          A.FunDeclId.Set.mem (fst def).Pure.def_id rec_functions
        in
        ExtractToFStar.extract_fun_decl_register_names ctx keep_fwd
          gen_decr_clause def)
      ctx trans_funs
  in

  (* Open the output file *)
  (* First compute the filename by replacing the extension and converting the
   * case (rust module names are snake case) *)
  let module_name, extract_filebasename =
    match Filename.chop_suffix_opt ~suffix:".llbc" filename with
    | None ->
        (* Note that we already checked the suffix upon opening the file *)
        failwith "Unreachable"
    | Some filename ->
        (* Retrieve the file basename *)
        let basename = Filename.basename filename in
        (* Convert the case *)
        let module_name = StringUtils.to_camel_case basename in
        (* Concatenate *)
        (module_name, Filename.concat dest_dir module_name)
  in

  (* Put the translated definitions in maps *)
  let trans_types =
    Pure.TypeDeclId.Map.of_list
      (List.map (fun (d : Pure.type_decl) -> (d.def_id, d)) trans_types)
  in
  let trans_funs =
    A.FunDeclId.Map.of_list
      (List.map
         (fun ((keep_fwd, (fd, bdl)) : bool * pure_fun_translation) ->
           (fd.def_id, (keep_fwd, (fd, bdl))))
         trans_funs)
  in

  (* Create the directory, if necessary *)
  if not (Sys.file_exists dest_dir) then (
    log#linfo (lazy ("Creating missing directory: " ^ dest_dir));
    (* Create a directory with *default* permissions *)
    Core_unix.mkdir_p dest_dir);

  (* Copy "Primitives.fst" - I couldn't find a "cp" function in the OCaml
   * libraries... *)
  let _ =
    let src = open_in "fstar/Primitives.fst" in
    let tgt_filename = Filename.concat dest_dir "Primitives.fst" in
    let tgt = open_out tgt_filename in
    try
      while true do
        (* We copy line by line *)
        let line = input_line src in
        Printf.fprintf tgt "%s\n" line
      done
    with End_of_file ->
      close_in src;
      close_out tgt;
      log#linfo (lazy ("Copied: " ^ tgt_filename))
  in

  (* Extract the file(s) *)
  let gen_ctx =
    {
      m;
      extract_ctx = ctx;
      trans_types;
      trans_funs;
      functions_with_decreases_clause = rec_functions;
    }
  in

  let use_state = config.use_state in

  (* Extract one or several files, depending on the configuration *)
  if config.split_files then (
    let base_gen_config =
      {
        mp_config = config.mp_config;
        use_state;
        extract_types = false;
        extract_decreases_clauses = config.extract_decreases_clauses;
        extract_template_decreases_clauses = false;
        extract_fun_decls = false;
        extract_transparent = true;
        extract_opaque = false;
        extract_state_type = false;
        interface = false;
        test_unit_functions = false;
      }
    in

    (* Check if there are opaque types and functions - in which case we need
     * to split *)
    let has_opaque_types, has_opaque_funs = module_has_opaque_decls gen_ctx in
    let has_opaque_types = has_opaque_types || use_state in

    (* Extract the types *)
    (* If there are opaque types, we extract in an interface *)
    let types_filename_ext = if has_opaque_types then ".fsti" else ".fst" in
    let types_filename = extract_filebasename ^ ".Types" ^ types_filename_ext in
    let types_module = module_name ^ ".Types" in
    let types_config =
      {
        base_gen_config with
        extract_types = true;
        extract_opaque = true;
        extract_state_type = use_state;
        interface = has_opaque_types;
      }
    in
    extract_file types_config gen_ctx types_filename m.M.name types_module
      ": type definitions" [] [];

    (* Extract the template clauses *)
    let needs_clauses_module =
      config.extract_decreases_clauses
      && not (A.FunDeclId.Set.is_empty rec_functions)
    in
    (if needs_clauses_module && config.extract_template_decreases_clauses then
     let clauses_filename = extract_filebasename ^ ".Clauses.Template.fst" in
     let clauses_module = module_name ^ ".Clauses.Template" in
     let clauses_config =
       { base_gen_config with extract_template_decreases_clauses = true }
     in
     extract_file clauses_config gen_ctx clauses_filename m.M.name
       clauses_module ": templates for the decreases clauses" [ types_module ]
       []);

    (* Extract the opaque functions, if needed *)
    let opaque_funs_module =
      if has_opaque_funs then (
        let opaque_filename = extract_filebasename ^ ".Opaque.fsti" in
        let opaque_module = module_name ^ ".Opaque" in
        let opaque_config =
          {
            base_gen_config with
            extract_fun_decls = true;
            extract_transparent = false;
            extract_opaque = true;
            interface = true;
          }
        in
        extract_file opaque_config gen_ctx opaque_filename m.M.name
          opaque_module ": opaque function definitions" [] [ types_module ];
        [ opaque_module ])
      else []
    in

    (* Extract the functions *)
    let fun_filename = extract_filebasename ^ ".Funs.fst" in
    let fun_module = module_name ^ ".Funs" in
    let fun_config =
      {
        base_gen_config with
        extract_fun_decls = true;
        test_unit_functions = config.test_unit_functions;
      }
    in
    let clauses_module =
      if needs_clauses_module then [ module_name ^ ".Clauses" ] else []
    in
    extract_file fun_config gen_ctx fun_filename m.M.name fun_module
      ": function definitions" []
      ([ types_module ] @ opaque_funs_module @ clauses_module))
  else
    let gen_config =
      {
        mp_config = config.mp_config;
        use_state;
        extract_types = true;
        extract_decreases_clauses = config.extract_decreases_clauses;
        extract_template_decreases_clauses =
          config.extract_template_decreases_clauses;
        extract_fun_decls = true;
        extract_transparent = true;
        extract_opaque = true;
        extract_state_type = use_state;
        interface = false;
        test_unit_functions = config.test_unit_functions;
      }
    in
    (* Add the extension for F* *)
    let extract_filename = extract_filebasename ^ ".fst" in
    extract_file gen_config gen_ctx extract_filename m.M.name module_name "" []
      []
