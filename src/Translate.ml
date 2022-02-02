open InterpreterStatements
open Interpreter
module L = Logging
module T = Types
module A = CfimAst
module M = Modules
module SA = SymbolicAst
module Micro = PureMicroPasses
open PureUtils
open TranslateCore

(** The local logger *)
let log = TranslateCore.log

type symbolic_fun_translation = V.symbolic_value list * SA.expression
(** The result of running the symbolic interpreter on a function:
    - the list of symbolic values used for the input values
    - the generated symbolic AST
*)

(** Execute the symbolic interpreter on a function to generate a list of symbolic ASTs,
    for the forward function and the backward functions.
*)
let translate_function_to_symbolics (config : C.partial_config)
    (trans_ctx : trans_ctx) (fdef : A.fun_def) :
    symbolic_fun_translation * symbolic_fun_translation list =
  (* Debug *)
  log#ldebug
    (lazy
      ("translate_function_to_symbolics: " ^ Print.name_to_string fdef.A.name));

  let { type_context; fun_context } = trans_ctx in

  (* Evaluate *)
  let synthesize = true in
  let evaluate gid =
    let inputs, symb =
      evaluate_function_symbolic config synthesize type_context fun_context fdef
        gid
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
  (forward, backwards)

(** Translate a function, by generating its forward and backward translations.

    [fun_sigs]: maps the forward/backward functions to their signatures. In case
    of backward functions, we also provide names for the outputs.
    TODO: maybe we should introduce a record for this.
*)
let translate_function_to_pure (config : C.partial_config)
    (trans_ctx : trans_ctx)
    (fun_sigs : SymbolicToPure.fun_sig_named_outputs RegularFunIdMap.t)
    (fdef : A.fun_def) : pure_fun_translation =
  (* Debug *)
  log#ldebug
    (lazy ("translate_function_to_pure: " ^ Print.name_to_string fdef.A.name));

  let { type_context; fun_context } = trans_ctx in
  let def_id = fdef.def_id in

  (* Compute the symbolic ASTs *)
  let symbolic_forward, symbolic_backwards =
    translate_function_to_symbolics config trans_ctx fdef
  in

  (* Convert the symbolic ASTs to pure ASTs: *)

  (* Initialize the context *)
  let forward_sig = RegularFunIdMap.find (A.Local def_id, None) fun_sigs in
  let forward_ret_ty =
    match forward_sig.sg.outputs with
    | [ ty ] -> ty
    | _ -> failwith "Unreachable"
  in
  let sv_to_var = V.SymbolicValueId.Map.empty in
  let var_counter = Pure.VarId.generator_zero in
  let calls = V.FunCallId.Map.empty in
  let abstractions = V.AbstractionId.Map.empty in
  let type_context =
    {
      SymbolicToPure.types_infos = type_context.type_infos;
      cfim_type_defs = type_context.type_defs;
    }
  in
  let fun_context =
    { SymbolicToPure.cfim_fun_defs = fun_context.fun_defs; fun_sigs }
  in
  let ctx =
    {
      SymbolicToPure.bid = None;
      (* Dummy for now *)
      ret_ty = forward_ret_ty;
      (* Will need to be updated for the backward functions *)
      sv_to_var;
      var_counter;
      type_context;
      fun_context;
      fun_def = fdef;
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
  let forward_input_vars = CfimAstUtils.fun_def_get_input_vars fdef in
  let forward_input_varnames =
    List.map (fun (v : A.var) -> v.name) forward_input_vars
  in
  let num_forward_inputs = fdef.arg_count in
  let add_forward_inputs input_svs ctx =
    let input_svs = List.combine forward_input_varnames input_svs in
    let ctx, forward_inputs =
      SymbolicToPure.fresh_named_vars_for_symbolic_values input_svs ctx
    in
    { ctx with forward_inputs }
  in

  (* Translate the forward function *)
  let pure_forward =
    SymbolicToPure.translate_fun_def
      (add_forward_inputs (fst symbolic_forward) ctx)
      (snd symbolic_forward)
  in

  (* Translate the backward functions *)
  let translate_backward (rg : T.region_var_group) : Pure.fun_def =
    (* For the backward inputs/outputs initialization: we use the fact that
     * there are no nested borrows for now, and so that the region groups
     * can't have parents *)
    assert (rg.parents = []);
    let back_id = rg.id in
    let input_svs, symbolic = T.RegionGroupId.nth symbolic_backwards back_id in
    let ctx = add_forward_inputs input_svs ctx in
    (* TODO: the computation of the backward inputs is a bit awckward... *)
    let backward_sg =
      RegularFunIdMap.find (A.Local def_id, Some back_id) fun_sigs
    in
    let _, backward_inputs =
      Collections.List.split_at backward_sg.sg.inputs num_forward_inputs
    in
    (* As we forbid nested borrows, the additional inputs for the backward
     * functions come from the borrows in the return value of the rust function:
     * we thus use the name "ret" for those inputs *)
    let backward_inputs =
      List.map (fun ty -> (Some "ret", ty)) backward_inputs
    in
    let ctx, backward_inputs = SymbolicToPure.fresh_vars backward_inputs ctx in
    (* The outputs for the backward functions, however, come from borrows
     * present in the input values of the rust function: for those we reuse
     * the names of the  input values. *)
    let backward_outputs =
      List.combine backward_sg.output_names backward_sg.sg.outputs
    in
    let ctx, backward_outputs =
      SymbolicToPure.fresh_vars backward_outputs ctx
    in
    let backward_output_tys =
      List.map (fun (v : Pure.var) -> v.ty) backward_outputs
    in
    let backward_ret_ty = mk_tuple_ty backward_output_tys in
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
        ret_ty = backward_ret_ty;
        backward_inputs;
        backward_outputs;
      }
    in

    (* Translate *)
    SymbolicToPure.translate_fun_def ctx symbolic
  in
  let pure_backwards =
    List.map translate_backward fdef.signature.regions_hierarchy
  in

  (* Return *)
  (pure_forward, pure_backwards)

let translate_module_to_pure (config : C.partial_config) (m : M.cfim_module) :
    trans_ctx * Pure.type_def list * pure_fun_translation list =
  (* Debug *)
  log#ldebug (lazy "translate_module_to_pure");

  (* Compute the type and function contexts *)
  let type_context, fun_context = compute_type_fun_contexts m in
  let trans_ctx = { type_context; fun_context } in

  (* Translate all the type definitions *)
  let type_defs = SymbolicToPure.translate_type_defs m.types in

  (* Translate all the function *signatures* *)
  let assumed_sigs =
    List.map
      (fun (id, sg) ->
        (A.Assumed id, List.map (fun _ -> None) (sg : A.fun_sig).inputs, sg))
      Assumed.assumed_sigs
  in
  let local_sigs =
    List.map
      (fun (fdef : A.fun_def) ->
        ( A.Local fdef.def_id,
          List.map
            (fun (v : A.var) -> v.name)
            (CfimAstUtils.fun_def_get_input_vars fdef),
          fdef.signature ))
      m.functions
  in
  let sigs = List.append assumed_sigs local_sigs in
  let fun_sigs =
    SymbolicToPure.translate_fun_signatures type_context.type_infos sigs
  in

  (* Translate all the functions *)
  let pure_translations =
    List.map (translate_function_to_pure config trans_ctx fun_sigs) m.functions
  in

  (* Apply the micro-passes *)
  (* TODO: move the configuration *)
  let passes_config =
    {
      Micro.unfold_monadic_let_bindings = true;
      filter_unused_monadic_calls = true;
    }
  in
  let pure_translations =
    List.map
      (Micro.apply_passes_to_pure_fun_translation passes_config trans_ctx)
      pure_translations
  in

  (* Return *)
  (trans_ctx, type_defs, pure_translations)

(** Translate a module and write the synthesized code to an output file *)
let translate_module (filename : string) (config : C.partial_config)
    (m : M.cfim_module) : unit =
  (* Translate the module to the pure AST *)
  let trans_ctx, trans_types, trans_funs = translate_module_to_pure config m in

  (* Initialize the extraction context - for now we extract only to F* *)
  let names_map =
    PureToExtract.initialize_names_map ExtractToFStar.fstar_keywords
  in
  let variant_concatenate_type_name = true in
  let fstar_fmt =
    ExtractToFStar.mk_name_formatter trans_ctx variant_concatenate_type_name
  in
  let extract_ctx =
    { PureToExtract.trans_ctx; names_map; fmt = fstar_fmt; indent_incr = 2 }
  in

  (* Register unique names for all the top-level types and functions.
   * Note that the order in which we generate the names doesn't matter:
   * we just need to generate a mapping from identifier to name, and make
   * sure there are no name clashes. *)
  let extract_ctx =
    List.fold_left
      (fun extract_ctx def ->
        ExtractToFStar.extract_type_def_register_names extract_ctx def)
      extract_ctx trans_types
  in

  let extract_ctx =
    List.fold_left
      (fun extract_ctx def ->
        ExtractToFStar.extract_fun_def_register_names extract_ctx def)
      extract_ctx trans_funs
  in

  (* Open the output file *)
  (* First compute the filename by replacing the extension and converting the
   * case (rust module names are snake case) *)
  let module_name, extract_filename =
    match Filename.chop_suffix_opt ~suffix:".cfim" filename with
    | None ->
        (* Note that we already checked the suffix upon opening the file *)
        failwith "Unreachable"
    | Some filename ->
        (* Split between basename and dirname *)
        let dirname = Filename.dirname filename in
        let basename = Filename.basename filename in
        (* Convert the case *)
        let module_name = StringUtils.to_camel_case basename in
        (* We add the extension for F* *)
        (module_name, Filename.concat dirname (module_name ^ ".fst"))
  in
  let out = open_out extract_filename in
  let fmt = Format.formatter_of_out_channel out in

  (* Put the translated definitions in maps *)
  let trans_types =
    Pure.TypeDefId.Map.of_list
      (List.map (fun (d : Pure.type_def) -> (d.def_id, d)) trans_types)
  in
  let trans_funs =
    Pure.FunDefId.Map.of_list
      (List.map
         (fun ((fd, bdl) : pure_fun_translation) -> (fd.def_id, (fd, bdl)))
         trans_funs)
  in

  (* Set the margin *)
  Format.pp_set_margin fmt 80;

  (* Create a vertical box *)
  Format.pp_open_vbox fmt 0;

  (* Add the module name *)
  Format.pp_print_string fmt ("(** " ^ m.M.name ^ " *)");
  Format.pp_print_break fmt 0 0;
  Format.pp_print_string fmt ("module " ^ module_name);
  Format.pp_print_break fmt 0 0;
  Format.pp_print_string fmt "open FStar.Mul";
  Format.pp_print_break fmt 0 0;
  Format.pp_print_break fmt 0 0;
  Format.pp_print_string fmt "#set-options \"--z3rlimit 50 --fuel 0 --ifuel 1\"";
  Format.pp_print_break fmt 0 0;

  (* Export the definition groups to the file, in the proper order *)
  let export_type (qualif : ExtractToFStar.type_def_qualif)
      (id : Pure.TypeDefId.id) : unit =
    let def = Pure.TypeDefId.Map.find id trans_types in
    ExtractToFStar.extract_type_def extract_ctx fmt qualif def
  in
  let export_function (id : Pure.FunDefId.id) : unit =
    (* TODO *)
    (*    let pure_defs = Pure.FunDefId.Map.find id trans_funs in *)
    ()
  in
  let export_decl (decl : M.declaration_group) : unit =
    match decl with
    | Type (NonRec id) -> export_type ExtractToFStar.Type id
    | Type (Rec ids) ->
        List.iteri
          (fun i id ->
            let qualif =
              if i = 0 then ExtractToFStar.Type else ExtractToFStar.And
            in
            export_type qualif id)
          ids
    | Fun (NonRec id) -> export_function id
    | Fun (Rec ids) -> List.iter export_function ids
  in
  List.iter export_decl m.declarations;

  (* Close the box and end the formatting *)
  Format.pp_close_box fmt ();
  Format.pp_print_newline fmt ()
