open InterpreterStatements
open Interpreter
module L = Logging
module T = Types
module A = LlbcAst
module SA = SymbolicAst
module Micro = PureMicroPasses
open PureUtils
open TranslateCore

(** The local logger *)
let log = TranslateCore.log

(** The result of running the symbolic interpreter on a function:
    - the list of symbolic values used for the input values
    - the generated symbolic AST
*)
type symbolic_fun_translation = V.symbolic_value list * SA.expression

(** Execute the symbolic interpreter on a function to generate a list of symbolic ASTs,
    for the forward function and the backward functions.
*)
let translate_function_to_symbolics (trans_ctx : trans_ctx) (fdef : A.fun_decl)
    : symbolic_fun_translation option =
  (* Debug *)
  log#ldebug
    (lazy
      ("translate_function_to_symbolics: "
      ^ Print.fun_name_to_string fdef.A.name));

  let { type_context; fun_context; global_context } = trans_ctx in
  let fun_context = { C.fun_decls = fun_context.fun_decls } in

  match fdef.body with
  | None -> None
  | Some _ ->
      (* Evaluate *)
      let synthesize = true in
      let inputs, symb =
        evaluate_function_symbolic synthesize type_context fun_context
          global_context fdef
      in
      Some (inputs, Option.get symb)

(** Translate a function, by generating its forward and backward translations.

    [fun_sigs]: maps the forward/backward functions to their signatures. In case
    of backward functions, we also provide names for the outputs.
    TODO: maybe we should introduce a record for this.
*)
let translate_function_to_pure (trans_ctx : trans_ctx)
    (fun_sigs : SymbolicToPure.fun_sig_named_outputs RegularFunIdNotLoopMap.t)
    (pure_type_decls : Pure.type_decl Pure.TypeDeclId.Map.t) (fdef : A.fun_decl)
    : pure_fun_translation_no_loops =
  (* Debug *)
  log#ldebug
    (lazy
      ("translate_function_to_pure: " ^ Print.fun_name_to_string fdef.A.name));

  let { type_context; fun_context; global_context } = trans_ctx in
  let def_id = fdef.def_id in

  (* Compute the symbolic ASTs, if the function is transparent *)
  let symbolic_trans = translate_function_to_symbolics trans_ctx fdef in

  (* Convert the symbolic ASTs to pure ASTs: *)

  (* Initialize the context *)
  let forward_sig =
    RegularFunIdNotLoopMap.find (A.Regular def_id, None) fun_sigs
  in
  let sv_to_var = V.SymbolicValueId.Map.empty in
  let var_counter = Pure.VarId.generator_zero in
  let state_var, var_counter = Pure.VarId.fresh var_counter in
  let back_state_var, var_counter = Pure.VarId.fresh var_counter in
  let fuel0, var_counter = Pure.VarId.fresh var_counter in
  let fuel, var_counter = Pure.VarId.fresh var_counter in
  let calls = V.FunCallId.Map.empty in
  let abstractions = V.AbstractionId.Map.empty in
  let recursive_type_decls =
    T.TypeDeclId.Set.of_list
      (List.filter_map
         (fun (tid, g) ->
           match g with Charon.GAst.NonRec _ -> None | Rec _ -> Some tid)
         (T.TypeDeclId.Map.bindings trans_ctx.type_context.type_decls_groups))
  in
  let type_context =
    {
      SymbolicToPure.type_infos = type_context.type_infos;
      llbc_type_decls = type_context.type_decls;
      type_decls = pure_type_decls;
      recursive_decls = recursive_type_decls;
    }
  in
  let fun_context =
    {
      SymbolicToPure.llbc_fun_decls = fun_context.fun_decls;
      fun_sigs;
      fun_infos = fun_context.fun_infos;
    }
  in
  let global_context =
    { SymbolicToPure.llbc_global_decls = global_context.global_decls }
  in

  (* Compute the set of loops, and find better ids for them (starting at 0).
     Note that we only need to explore the forward function: the backward
     functions should contain the same set of loops.
  *)
  let loop_ids_map =
    match symbolic_trans with
    | None -> V.LoopId.Map.empty
    | Some (_, ast) ->
        let m = ref V.LoopId.Map.empty in
        let _, fresh_loop_id = Pure.LoopId.fresh_stateful_generator () in

        let visitor =
          object
            inherit [_] SA.iter_expression as super

            method! visit_loop env loop =
              let _ =
                match V.LoopId.Map.find_opt loop.loop_id !m with
                | Some _ -> ()
                | None ->
                    m := V.LoopId.Map.add loop.loop_id (fresh_loop_id ()) !m
              in
              super#visit_loop env loop
          end
        in
        visitor#visit_expression () ast;
        !m
  in

  let ctx =
    {
      SymbolicToPure.bid = None;
      (* Dummy for now *)
      sg = forward_sig.sg;
      fwd_sg = forward_sig.sg;
      (* Will need to be updated for the backward functions *)
      sv_to_var;
      var_counter;
      state_var;
      back_state_var;
      fuel0;
      fuel;
      type_context;
      fun_context;
      global_context;
      fun_decl = fdef;
      forward_inputs = [];
      (* Empty for now *)
      backward_inputs = T.RegionGroupId.Map.empty;
      (* Empty for now *)
      backward_outputs = T.RegionGroupId.Map.empty;
      loop_backward_outputs = None;
      (* Empty for now *)
      calls;
      abstractions;
      loop_id = None;
      inside_loop = false;
      loop_ids_map;
      loops = Pure.LoopId.Map.empty;
    }
  in

  (* Add the forward inputs (the initialized input variables for the forward
     function)
  *)
  let ctx =
    match (fdef.body, symbolic_trans) with
    | None, None -> ctx
    | Some body, Some (input_svs, _) ->
        let forward_input_vars = LlbcAstUtils.fun_body_get_input_vars body in
        let forward_input_varnames =
          List.map (fun (v : A.var) -> v.name) forward_input_vars
        in
        let input_svs = List.combine forward_input_varnames input_svs in
        let ctx, forward_inputs =
          SymbolicToPure.fresh_named_vars_for_symbolic_values input_svs ctx
        in
        { ctx with forward_inputs }
    | _ -> raise (Failure "Unreachable")
  in

  (* Translate the forward function *)
  let pure_forward =
    match symbolic_trans with
    | None -> SymbolicToPure.translate_fun_decl ctx None
    | Some (_, ast) -> SymbolicToPure.translate_fun_decl ctx (Some ast)
  in

  (* Translate the backward functions *)
  let translate_backward (rg : T.region_var_group) : Pure.fun_decl =
    (* For the backward inputs/outputs initialization: we use the fact that
     * there are no nested borrows for now, and so that the region groups
     * can't have parents *)
    assert (rg.parents = []);
    let back_id = rg.id in

    match symbolic_trans with
    | None ->
        (* Initialize the context - note that the ret_ty is not really
         * useful as we don't translate a body *)
        let backward_sg =
          RegularFunIdNotLoopMap.find (A.Regular def_id, Some back_id) fun_sigs
        in
        let ctx = { ctx with bid = Some back_id; sg = backward_sg.sg } in

        (* Translate *)
        SymbolicToPure.translate_fun_decl ctx None
    | Some (_, symbolic) ->
        (* Finish initializing the context by adding the additional input
           variables required by the backward function.
        *)
        let backward_sg =
          RegularFunIdNotLoopMap.find (A.Regular def_id, Some back_id) fun_sigs
        in
        (* We need to ignore the forward inputs, and the state input (if there is) *)
        let backward_inputs =
          let sg = backward_sg.sg in
          (* We need to ignore the forward state and the backward state *)
          let num_forward_inputs =
            sg.info.num_fwd_inputs_with_fuel_with_state
          in
          let num_back_inputs = Option.get sg.info.num_back_inputs_no_state in
          Collections.List.subslice sg.inputs num_forward_inputs
            (num_forward_inputs + num_back_inputs)
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
         * the names of the input values. *)
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
        SymbolicToPure.translate_fun_decl ctx (Some symbolic)
  in
  let pure_backwards =
    List.map translate_backward fdef.signature.regions_hierarchy
  in

  (* Return *)
  (pure_forward, pure_backwards)

let translate_crate_to_pure (crate : A.crate) :
    trans_ctx * Pure.type_decl list * (bool * pure_fun_translation) list =
  (* Debug *)
  log#ldebug (lazy "translate_crate_to_pure");

  (* Compute the type and function contexts *)
  let type_context, fun_context, global_context =
    compute_type_fun_global_contexts crate
  in
  let fun_infos =
    FA.analyze_module crate fun_context.C.fun_decls
      global_context.C.global_decls !Config.use_state
  in
  let fun_context = { fun_decls = fun_context.fun_decls; fun_infos } in
  let trans_ctx = { type_context; fun_context; global_context } in

  (* Translate all the type definitions *)
  let type_decls = SymbolicToPure.translate_type_decls crate.types in

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
      crate.functions
  in
  let sigs = List.append assumed_sigs local_sigs in
  let fun_sigs =
    SymbolicToPure.translate_fun_signatures fun_context.fun_infos
      type_context.type_infos sigs
  in

  (* Translate all the *transparent* functions *)
  let pure_translations =
    List.map
      (translate_function_to_pure trans_ctx fun_sigs type_decls_map)
      crate.functions
  in

  (* Apply the micro-passes *)
  let pure_translations =
    Micro.apply_passes_to_pure_fun_translations trans_ctx pure_translations
  in

  (* Return *)
  (trans_ctx, type_decls, pure_translations)

(** Extraction context *)
type gen_ctx = {
  crate : A.crate;
  extract_ctx : ExtractBase.extraction_ctx;
  trans_types : Pure.type_decl Pure.TypeDeclId.Map.t;
  trans_funs : (bool * pure_fun_translation) A.FunDeclId.Map.t;
  functions_with_decreases_clause : PureUtils.FunLoopIdSet.t;
}

type gen_config = {
  extract_types : bool;
  extract_decreases_clauses : bool;
  extract_template_decreases_clauses : bool;
  extract_fun_decls : bool;
  extract_transparent : bool;
      (** If [true], extract the transparent declarations, otherwise ignore. *)
  extract_opaque : bool;
      (** If [true], extract the opaque declarations, otherwise ignore.

          For now, this controls only the opaque *functions*, not the opaque
          globals or types.
          TODO: update this. This is not trivial if we want to extract the opaque
          types in an opaque module, because some non-opaque types may refer
          to opaque types and vice-versa.
       *)
  extract_state_type : bool;
      (** If [true], generate a definition/declaration for the state type *)
  extract_globals : bool;
      (** If [true], generate a definition/declaration for top-level (global)
          declarations *)
  interface : bool;
      (** [true] if we generate an interface file, [false] otherwise.
          For now, this only impacts whether we use [val] or [assume val] for the
          opaque definitions. In the future, we might want to extract all the
          declarations in an interface file, together with an implementation file
          if needed.
       *)
  test_trans_unit_functions : bool;
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
      (fun _ ((_, ((t_fwd, _), _)) : bool * pure_fun_translation) ->
        Option.is_none t_fwd.body)
      ctx.trans_funs
  in
  (has_opaque_types, has_opaque_funs)

(** Export a type declaration.

    It may happen that we have to extract extra information/instructions.
    For instance, we might need to define some projector notations. This is
    why we have the two booleans [extract_decl] and [extract_extra_info].
    If [extract_decl] is [true], then we extract the type declaration. If
    [extract_extra_info] is [true], we extract this extra information (after
    the declaration, if both booleans are [true]).
 *)
let export_type (fmt : Format.formatter) (config : gen_config) (ctx : gen_ctx)
    (kind : ExtractBase.decl_kind) (id : Pure.TypeDeclId.id)
    (extract_decl : bool) (extract_extra_info : bool) : unit =
  (* Retrieve the declaration *)
  let def = Pure.TypeDeclId.Map.find id ctx.trans_types in
  (* Update the kind, if the type is opaque *)
  let is_opaque, kind =
    match def.kind with
    | Enum _ | Struct _ -> (false, kind)
    | Opaque ->
        let kind =
          if config.interface then ExtractBase.Declared else ExtractBase.Assumed
        in
        (true, kind)
  in
  (* Extract, if the config instructs to do so (depending on whether the type
   * is opaque or not) *)
  if
    (is_opaque && config.extract_opaque)
    || ((not is_opaque) && config.extract_transparent)
  then (
    if extract_decl then Extract.extract_type_decl ctx.extract_ctx fmt kind def;
    if extract_extra_info then
      Extract.extract_type_decl_extra_info ctx.extract_ctx fmt kind def)

(** Export a group of types.

    [is_rec]: [true] if the types are recursive. Necessarily [true] if there is
    > 1 type to extract.
 *)
let export_types_group (fmt : Format.formatter) (config : gen_config)
    (ctx : gen_ctx) (is_rec : bool) (ids : Pure.TypeDeclId.id list) : unit =
  let export_type = export_type fmt config ctx in
  let export_type_decl kind id = export_type kind id true false in
  let export_type_extra_info kind id = export_type kind id false true in

  (* Rem.: we shouldn't have (mutually) recursive opaque types *)
  let num_decls = List.length ids in
  let is_mut_rec = num_decls > 1 in
  let kind_from_index i =
    if not is_mut_rec then
      if is_rec then ExtractBase.SingleRec else ExtractBase.SingleNonRec
    else if i = 0 then ExtractBase.MutRecFirst
    else if i = num_decls - 1 then ExtractBase.MutRecLast
    else ExtractBase.MutRecInner
  in
  (* Extract the type declarations *)
  List.iteri
    (fun i id ->
      let kind = kind_from_index i in
      export_type_decl kind id)
    ids;
  (* Export the extra information (ex.: [Arguments] instructions in Coq) *)
  List.iteri
    (fun i id ->
      let kind = kind_from_index i in
      export_type_extra_info kind id)
    ids

(** Export a global declaration.

    TODO: check correct behaviour with opaque globals.
 *)
let export_global (fmt : Format.formatter) (config : gen_config) (ctx : gen_ctx)
    (id : A.GlobalDeclId.id) : unit =
  let global_decls = ctx.extract_ctx.trans_ctx.global_context.global_decls in
  let global = A.GlobalDeclId.Map.find id global_decls in
  let _, ((body, loop_fwds), body_backs) =
    A.FunDeclId.Map.find global.body_id ctx.trans_funs
  in
  assert (body_backs = []);
  assert (loop_fwds = []);

  let is_opaque = Option.is_none body.Pure.body in
  if
    config.extract_globals
    && (((not is_opaque) && config.extract_transparent)
       || (is_opaque && config.extract_opaque))
  then
    Extract.extract_global_decl ctx.extract_ctx fmt global body config.interface

(** Utility.

    Export a group of functions, used by {!export_functions_group}.

    We need this because for every function in Rust we may generate several functions
    in the translation (a forward function, several backward functions, loop
    functions, etc.). Those functions might call each other in different
    ways. In particular, they may be mutually recursive, in which case we might
    be able to group them into several groups of mutually recursive definitions,
    etc. For this reason, {!export_functions_group} computes the dependency
    graph of the functions as well as their strongly connected components, and
    gives each SCC at a time to {!export_functions_group_scc}.

    Rem.: this function only extracts the function *declarations*. It doesn't
    extract the decrease clauses, nor does it extract the unit tests.

    Rem.: this function doesn't check [config.extract_fun_decls]: it should have
    been checked by the caller.
 *)
let export_functions_group_scc (fmt : Format.formatter) (config : gen_config)
    (ctx : gen_ctx) (is_rec : bool) (decls : Pure.fun_decl list) : unit =
  (* Utility to check a function has a decrease clause *)
  let has_decreases_clause (def : Pure.fun_decl) : bool =
    PureUtils.FunLoopIdSet.mem (def.def_id, def.loop_id)
      ctx.functions_with_decreases_clause
  in

  (* Extract the function declarations *)
  (* Check if the functions are mutually recursive *)
  let is_mut_rec = List.length decls > 1 in
  assert ((not is_mut_rec) || is_rec);
  let decls_length = List.length decls in
  List.iteri
    (fun i def ->
      let is_opaque = Option.is_none def.Pure.body in
      let kind =
        if is_opaque then
          if config.interface then ExtractBase.Declared else ExtractBase.Assumed
        else if not is_rec then ExtractBase.SingleNonRec
        else if is_mut_rec then
          (* If the functions are mutually recursive, we need to distinguish:
           * - the first of the group
           * - the last of the group
           * - the inner functions
           *)
          if i = 0 then ExtractBase.MutRecFirst
          else if i = decls_length - 1 then ExtractBase.MutRecLast
          else ExtractBase.MutRecInner
        else ExtractBase.SingleRec
      in
      let has_decr_clause =
        has_decreases_clause def && config.extract_decreases_clauses
      in
      (* Check if the definition needs to be filtered or not *)
      if
        ((not is_opaque) && config.extract_transparent)
        || (is_opaque && config.extract_opaque)
      then Extract.extract_fun_decl ctx.extract_ctx fmt kind has_decr_clause def)
    decls

(** Export a group of function declarations.

    In case of (non-mutually) recursive functions, we use a simple procedure to
    check if the forward and backward functions are mutually recursive.
 *)
let export_functions_group (fmt : Format.formatter) (config : gen_config)
    (ctx : gen_ctx) (pure_ls : (bool * pure_fun_translation) list) : unit =
  (* Utility to check a function has a decrease clause *)
  let has_decreases_clause (def : Pure.fun_decl) : bool =
    PureUtils.FunLoopIdSet.mem (def.def_id, def.loop_id)
      ctx.functions_with_decreases_clause
  in

  (* Extract the decrease clauses template bodies *)
  if config.extract_template_decreases_clauses then
    List.iter
      (fun (_, ((fwd, loop_fwds), _)) ->
        (* We only generate decreases clauses for the forward functions, because
           the termination argument should only depend on the forward inputs.
           The backward functions thus use the same decreases clauses as the
           forward function.

           Rem.: we might filter backward functions in {!PureMicroPasses}, but
           we don't remove forward functions. Instead, we remember if we should
           filter those functions at extraction time with a boolean (see the
           type of the [pure_ls] input parameter).
        *)
        let extract_decrease decl =
          let has_decr_clause = has_decreases_clause decl in
          if has_decr_clause then
            match !Config.backend with
            | Lean ->
                Extract.extract_template_lean_termination_and_decreasing
                  ctx.extract_ctx fmt decl
            | FStar ->
                Extract.extract_template_fstar_decreases_clause ctx.extract_ctx
                  fmt decl
            | Coq ->
                raise (Failure "Coq doesn't have decreases/termination clauses")
        in
        extract_decrease fwd;
        List.iter extract_decrease loop_fwds)
      pure_ls;

  (* Concatenate the function definitions, filtering the useless forward
   * functions. *)
  let decls =
    List.concat
      (List.map
         (fun (keep_fwd, ((fwd, fwd_loops), (back_ls : fun_and_loops list))) ->
           let fwd = if keep_fwd then List.append fwd_loops [ fwd ] else [] in
           let back : Pure.fun_decl list =
             List.concat
               (List.map
                  (fun (back, loop_backs) -> List.append loop_backs [ back ])
                  back_ls)
           in
           List.append fwd back)
         pure_ls)
  in

  (* Extract the function definitions *)
  (if config.extract_fun_decls then
   (* Group the mutually recursive definitions *)
   let subgroups = ReorderDecls.group_reorder_fun_decls decls in

   (* Extract the subgroups *)
   let export_subgroup (is_rec : bool) (decls : Pure.fun_decl list) : unit =
     export_functions_group_scc fmt config ctx is_rec decls
   in
   List.iter (fun (is_rec, decls) -> export_subgroup is_rec decls) subgroups);

  (* Insert unit tests if necessary *)
  if config.test_trans_unit_functions then
    List.iter
      (fun (keep_fwd, ((fwd, _), _)) ->
        if keep_fwd then
          Extract.extract_unit_test_if_unit_fun ctx.extract_ctx fmt fwd)
      pure_ls

(** A generic utility to generate the extracted definitions: as we may want to
    split the definitions between different files (or not), we can control
    what is precisely extracted.
 *)
let extract_definitions (fmt : Format.formatter) (config : gen_config)
    (ctx : gen_ctx) : unit =
  (* Export the definition groups to the file, in the proper order.
     - [extract_decl]: extract the type declaration (if not filtered)
     - [extract_extra_info]: extra the extra type information (e.g.,
       the [Arguments] information in Coq).
  *)
  let export_functions_group = export_functions_group fmt config ctx in
  let export_global = export_global fmt config ctx in
  let export_types_group = export_types_group fmt config ctx in

  let export_state_type () : unit =
    let kind =
      if config.interface then ExtractBase.Declared else ExtractBase.Assumed
    in
    Extract.extract_state_type fmt ctx.extract_ctx kind
  in

  let export_decl_group (dg : A.declaration_group) : unit =
    match dg with
    | Type (NonRec id) ->
        if config.extract_types then export_types_group false [ id ]
    | Type (Rec ids) -> if config.extract_types then export_types_group true ids
    | Fun (NonRec id) ->
        (* Lookup *)
        let pure_fun = A.FunDeclId.Map.find id ctx.trans_funs in
        (* Translate *)
        export_functions_group [ pure_fun ]
    | Fun (Rec ids) ->
        (* General case of mutually recursive functions *)
        (* Lookup *)
        let pure_funs =
          List.map (fun id -> A.FunDeclId.Map.find id ctx.trans_funs) ids
        in
        (* Translate *)
        export_functions_group pure_funs
    | Global id -> export_global id
  in

  (* If we need to export the state type: we try to export it after we defined
   * the type definitions, because if the user wants to define a model for the
   * type, he might want to reuse those in the state type.
   * More specifically: if we extract functions in the same file as the type,
   * we have no choice but to define the state type before the functions,
   * because they may reuse this state type: in this case, we define/declare
   * it at the very beginning. Otherwise, we define/declare it at the very end.
   *)
  if config.extract_state_type && config.extract_fun_decls then
    export_state_type ();

  (* For Lean, we parameterize the entire development by a section variable
     called opaque_defs, of type OpaqueDefs. The code below emits the type
     definition for OpaqueDefs, which is a structure, in which each field is one
     of the functions marked as Opaque. We emit the `structure ...` bit here,
     then rely on `extract_fun_decl` to be aware of this, and skip the keyword
     (e.g. "axiom" or "val") so as to generate valid syntax for records. *)
  let wrap_in_sig =
    config.extract_opaque && config.extract_fun_decls && !Config.backend = Lean
  in
  if wrap_in_sig then (
    Format.pp_print_break fmt 0 0;
    Format.pp_open_vbox fmt ctx.extract_ctx.indent_incr;
    Format.pp_print_string fmt "structure OpaqueDefs where";
    Format.pp_print_break fmt 0 0);
  List.iter export_decl_group ctx.crate.declarations;

  if config.extract_state_type && not config.extract_fun_decls then
    export_state_type ();

  if wrap_in_sig then Format.pp_close_box fmt ()

let extract_file (config : gen_config) (ctx : gen_ctx) (filename : string)
    (rust_module_name : string) (module_name : string) (custom_msg : string)
    ?(custom_variables : string list = []) (custom_imports : string list)
    (custom_includes : string list) : unit =
  (* Open the file and create the formatter *)
  let out = open_out filename in
  let fmt = Format.formatter_of_out_channel out in

  (* Print the headers.
   * Note that we don't use the OCaml formatter for purpose: we want to control
   * line insertion (we have to make sure that some instructions like [open MODULE]
   * are printed on one line!).
   * This is ok as long as we end up with a line break, so that the formatter's
   * internal count is consistent with the state of the file.
   *)
  (* Create the header *)
  (match !Config.backend with
  | Lean ->
      Printf.fprintf out "-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS\n";
      Printf.fprintf out "-- [%s]%s\n" rust_module_name custom_msg
  | Coq | FStar ->
      Printf.fprintf out
        "(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)\n";
      Printf.fprintf out "(** [%s]%s *)\n" rust_module_name custom_msg);
  (match !Config.backend with
  | FStar ->
      Printf.fprintf out "module %s\n" module_name;
      Printf.fprintf out "open Primitives\n";
      (* Add the custom imports *)
      List.iter (fun m -> Printf.fprintf out "open %s\n" m) custom_imports;
      (* Add the custom includes *)
      List.iter (fun m -> Printf.fprintf out "include %s\n" m) custom_includes;
      (* Z3 options - note that we use fuel 1 because it its useful for the decrease clauses *)
      Printf.fprintf out "\n#set-options \"--z3rlimit 50 --fuel 1 --ifuel 1\"\n"
  | Coq ->
      Printf.fprintf out "Require Import Primitives.\n";
      Printf.fprintf out "Import Primitives.\n";
      Printf.fprintf out "Require Import Coq.ZArith.ZArith.\n";
      Printf.fprintf out "Local Open Scope Primitives_scope.\n";

      (* Add the custom imports *)
      List.iter
        (fun m -> Printf.fprintf out "Require Import %s.\n" m)
        custom_imports;
      (* Add the custom includes *)
      List.iter
        (fun m ->
          Printf.fprintf out "Require Export %s.\n" m;
          Printf.fprintf out "Import %s.\n" m)
        custom_includes;
      Printf.fprintf out "Module %s.\n" module_name
  | Lean ->
      Printf.fprintf out "import Base.Primitives\n";
      (* Add the custom imports *)
      List.iter (fun m -> Printf.fprintf out "import %s\n" m) custom_imports;
      (* Add the custom includes *)
      List.iter (fun m -> Printf.fprintf out "import %s\n" m) custom_includes;
      if custom_variables <> [] then (
        Printf.fprintf out "\n";
        List.iter (fun m -> Printf.fprintf out "%s\n" m) custom_variables));
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

  (* Close the module *)
  (match !Config.backend with
  | FStar | Lean -> ()
  | Coq -> Printf.fprintf out "End %s .\n" module_name);

  (* Some logging *)
  log#linfo (lazy ("Generated: " ^ filename));

  (* Flush and close the file *)
  close_out out

(** Translate a crate and write the synthesized code to an output file. *)
let translate_crate (filename : string) (dest_dir : string) (crate : A.crate) :
    unit =
  (* Translate the module to the pure AST *)
  let trans_ctx, trans_types, trans_funs = translate_crate_to_pure crate in

  (* Initialize the extraction context - for now we extract only to F*.
   * We initialize the names map by registering the keywords used in the
   * language, as well as some primitive names ("u32", etc.) *)
  let variant_concatenate_type_name = true in
  let mk_formatter_and_names_map = Extract.mk_formatter_and_names_map in
  let fmt, names_map =
    mk_formatter_and_names_map trans_ctx crate.name
      variant_concatenate_type_name
  in
  let ctx =
    {
      ExtractBase.trans_ctx;
      names_map;
      fmt;
      indent_incr = 2;
      use_opaque_pre = !Config.split_files;
    }
  in

  (* We need to compute which functions are recursive, in order to know
   * whether we should generate a decrease clause or not. *)
  let rec_functions =
    List.map
      (fun (_, ((fwd, loop_fwds), _)) ->
        let fwd =
          if fwd.Pure.signature.info.effect_info.is_rec then
            [ (fwd.def_id, None) ]
          else []
        in
        let loop_fwds =
          List.map
            (fun (def : Pure.fun_decl) -> [ (def.def_id, def.loop_id) ])
            loop_fwds
        in
        fwd :: loop_fwds)
      trans_funs
  in
  let rec_functions : PureUtils.fun_loop_id list =
    List.concat (List.concat rec_functions)
  in
  let rec_functions = PureUtils.FunLoopIdSet.of_list rec_functions in

  (* Register unique names for all the top-level types, globals and functions.
   * Note that the order in which we generate the names doesn't matter:
   * we just need to generate a mapping from identifier to name, and make
   * sure there are no name clashes. *)
  let ctx =
    List.fold_left
      (fun ctx def -> Extract.extract_type_decl_register_names ctx def)
      ctx trans_types
  in

  let ctx =
    List.fold_left
      (fun ctx (keep_fwd, defs) ->
        (* If requested by the user, register termination measures and decreases
           proofs for all the recursive functions *)
        let fwd_def = fst (fst defs) in
        let gen_decr_clause (def : Pure.fun_decl) =
          !Config.extract_decreases_clauses
          && PureUtils.FunLoopIdSet.mem
               (def.Pure.def_id, def.Pure.loop_id)
               rec_functions
        in
        (* Register the names, only if the function is not a global body -
         * those are handled later *)
        let is_global = fwd_def.Pure.is_global_decl_body in
        if is_global then ctx
        else
          Extract.extract_fun_decl_register_names ctx keep_fwd gen_decr_clause
            defs)
      ctx trans_funs
  in

  let ctx =
    List.fold_left Extract.extract_global_decl_register_names ctx crate.globals
  in

  (* Open the output file *)
  (* First compute the filename by replacing the extension and converting the
   * case (rust module names are snake case) *)
  let module_name, extract_filebasename =
    match Filename.chop_suffix_opt ~suffix:".llbc" filename with
    | None ->
        (* Note that we already checked the suffix upon opening the file *)
        raise (Failure "Unreachable")
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
           ((fst fd).def_id, (keep_fwd, (fd, bdl))))
         trans_funs)
  in

  let mkdir_if dest_dir =
    if not (Sys.file_exists dest_dir) then (
      log#linfo (lazy ("Creating missing directory: " ^ dest_dir));
      (* Create a directory with *default* permissions *)
      Core_unix.mkdir_p dest_dir)
  in

  (* Create the directory, if necessary *)
  mkdir_if dest_dir;

  let needs_clauses_module =
    !Config.extract_decreases_clauses
    && not (PureUtils.FunLoopIdSet.is_empty rec_functions)
  in

  (* Lean reflects the module hierarchy within the filesystem, so we need to
     create more directories *)
  if !Config.backend = Lean then (
    let ( ^^ ) = Filename.concat in
    mkdir_if (dest_dir ^^ "Base");
    if !Config.split_files then mkdir_if (dest_dir ^^ module_name);
    if needs_clauses_module then (
      assert !Config.split_files;
      mkdir_if (dest_dir ^^ module_name ^^ "Clauses")));

  (* Copy the "Primitives" file *)
  let _ =
    (* Retrieve the executable's directory *)
    let exe_dir = Filename.dirname Sys.argv.(0) in
    let primitives_src, primitives_destname =
      match !Config.backend with
      | Config.FStar -> ("/backends/fstar/Primitives.fst", "Primitives.fst")
      | Config.Coq -> ("/backends/coq/Primitives.v", "Primitives.v")
      | Config.Lean -> ("/backends/lean/Primitives.lean", "Base/Primitives.lean")
    in
    let src = open_in (exe_dir ^ primitives_src) in
    let tgt_filename = Filename.concat dest_dir primitives_destname in
    let tgt = open_out tgt_filename in
    (* Very annoying: I couldn't find a "cp" function in the OCaml libraries... *)
    try
      while true do
        (* We copy line by line *)
        let line = input_line src in
        Printf.fprintf tgt "%s\n" line
      done
    with End_of_file ->
      close_in src;
      close_out tgt;
      log#linfo (lazy ("Copied:    " ^ tgt_filename))
  in

  (* Extract the file(s) *)
  let gen_ctx =
    {
      crate;
      extract_ctx = ctx;
      trans_types;
      trans_funs;
      functions_with_decreases_clause = rec_functions;
    }
  in

  let module_delimiter =
    match !Config.backend with FStar -> "." | Coq -> "_" | Lean -> "."
  in
  let file_delimiter =
    if !Config.backend = Lean then "/" else module_delimiter
  in
  (* File extension for the "regular" modules *)
  let ext =
    match !Config.backend with FStar -> ".fst" | Coq -> ".v" | Lean -> ".lean"
  in
  (* File extension for the opaque module *)
  let opaque_ext =
    match !Config.backend with
    | FStar -> ".fsti"
    | Coq -> ".v"
    | Lean -> ".lean"
  in

  (* Extract one or several files, depending on the configuration *)
  (if !Config.split_files then (
   let base_gen_config =
     {
       extract_types = false;
       extract_decreases_clauses = !Config.extract_decreases_clauses;
       extract_template_decreases_clauses = false;
       extract_fun_decls = false;
       extract_transparent = true;
       extract_opaque = false;
       extract_state_type = false;
       extract_globals = false;
       interface = false;
       test_trans_unit_functions = false;
     }
   in

   (* Check if there are opaque types and functions - in which case we need
    * to split *)
   let has_opaque_types, has_opaque_funs = module_has_opaque_decls gen_ctx in
   let has_opaque_types = has_opaque_types || !Config.use_state in

   (* Extract the types *)
   (* If there are opaque types, we extract in an interface *)
   let types_filename_ext =
     match !Config.backend with
     | FStar -> if has_opaque_types then ".fsti" else ".fst"
     | Coq -> ".v"
     | Lean -> ".lean"
   in
   let types_filename =
     extract_filebasename ^ file_delimiter ^ "Types" ^ types_filename_ext
   in
   let types_module = module_name ^ module_delimiter ^ "Types" in
   let types_config =
     {
       base_gen_config with
       extract_types = true;
       extract_opaque = true;
       extract_state_type = !Config.use_state;
       interface = has_opaque_types;
     }
   in
   extract_file types_config gen_ctx types_filename crate.A.name types_module
     ": type definitions" [] [];

   (* Extract the template clauses *)
   (if needs_clauses_module && !Config.extract_template_decreases_clauses then
    let template_clauses_filename =
      extract_filebasename ^ file_delimiter ^ "Clauses" ^ file_delimiter
      ^ "Template" ^ ext
    in
    let template_clauses_module =
      module_name ^ module_delimiter ^ "Clauses" ^ module_delimiter ^ "Template"
    in
    let template_clauses_config =
      { base_gen_config with extract_template_decreases_clauses = true }
    in
    extract_file template_clauses_config gen_ctx template_clauses_filename
      crate.A.name template_clauses_module
      ": templates for the decreases clauses" [ types_module ] []);

   (* Extract the opaque functions, if needed *)
   let opaque_funs_module =
     if has_opaque_funs then (
       let opaque_filename =
         extract_filebasename ^ file_delimiter ^ "Opaque" ^ opaque_ext
       in
       let opaque_module = module_name ^ module_delimiter ^ "Opaque" in
       let opaque_config =
         {
           base_gen_config with
           extract_fun_decls = true;
           extract_transparent = false;
           extract_opaque = true;
           interface = true;
         }
       in
       let gen_ctx =
         {
           gen_ctx with
           extract_ctx = { gen_ctx.extract_ctx with use_opaque_pre = false };
         }
       in
       extract_file opaque_config gen_ctx opaque_filename crate.A.name
         opaque_module ": opaque function definitions" [] [ types_module ];
       [ opaque_module ])
     else []
   in

   (* Extract the functions *)
   let fun_filename = extract_filebasename ^ file_delimiter ^ "Funs" ^ ext in
   let fun_module = module_name ^ module_delimiter ^ "Funs" in
   let fun_config =
     {
       base_gen_config with
       extract_fun_decls = true;
       extract_globals = true;
       test_trans_unit_functions = !Config.test_trans_unit_functions;
     }
   in
   let clauses_module =
     if needs_clauses_module then
       let clauses_submodule =
         if !Config.backend = Lean then module_delimiter ^ "Clauses" else ""
       in
       [ module_name ^ clauses_submodule ^ module_delimiter ^ "Clauses" ]
     else []
   in
   let custom_variables =
     if has_opaque_funs then [ "section variable (opaque_defs: OpaqueDefs)" ]
     else []
   in
   extract_file fun_config gen_ctx fun_filename crate.A.name fun_module
     ": function definitions" [] ~custom_variables
     ([ types_module ] @ opaque_funs_module @ clauses_module))
  else
    let gen_config =
      {
        extract_types = true;
        extract_decreases_clauses = !Config.extract_decreases_clauses;
        extract_template_decreases_clauses =
          !Config.extract_template_decreases_clauses;
        extract_fun_decls = true;
        extract_transparent = true;
        extract_opaque = true;
        extract_state_type = !Config.use_state;
        extract_globals = true;
        interface = false;
        test_trans_unit_functions = !Config.test_trans_unit_functions;
      }
    in
    (* Add the extension for F* *)
    let extract_filename = extract_filebasename ^ ext in
    extract_file gen_config gen_ctx extract_filename crate.A.name module_name ""
      [] []);

  (* Generate the build file *)
  match !Config.backend with
  | Coq | FStar ->
      ()
      (* Nothing to do - TODO: we might want to generate the _CoqProject file for Coq.
         But then we can't modify it if we want to add more files for the proofs
         for instance. But we might want to put the proofs elsewhere anyway.
         Remark: there is the same problem for Lean actually.
      *)
  | Lean ->
      (*
       * Generate the library entry point, if the crate is split between
       * different files.
       *)
      if !Config.split_files then (
        let filename = Filename.concat dest_dir (module_name ^ ".lean") in
        let out = open_out filename in
        (* Write *)
        Printf.fprintf out "import %s.Funs\n" module_name;
        (* Flush and close the file, log *)
        close_out out;
        log#linfo (lazy ("Generated: " ^ filename)));

      (*
       * Generate the lakefile.lean file
       *)

      (* Open the file *)
      let filename = Filename.concat dest_dir "lakefile.lean" in
      let out = open_out filename in

      (* Generate the content *)
      Printf.fprintf out "import Lake\nopen Lake DSL\n\n";
      Printf.fprintf out "require mathlib from git\n";
      Printf.fprintf out
        "  \"https://github.com/leanprover-community/mathlib4.git\"\n\n";

      let package_name = StringUtils.to_snake_case module_name in
      Printf.fprintf out "package «%s» {}\n\n" package_name;

      Printf.fprintf out "lean_lib «Base» {}\n\n";

      Printf.fprintf out "@[default_target]\nlean_lib «%s» {}\n" module_name;

      (* No default target for now.
         Format would be:
         {[
           @[default_target]
           lean_exe «package_name» {
             root := `Main
           }
         ]}
      *)

      (* Flush and close the file *)
      close_out out;

      (* Logging *)
      log#linfo (lazy ("Generated: " ^ filename))
