open InterpreterStatements
open Interpreter
module L = Logging
module T = Types
module A = CfimAst
module M = Modules
module SA = SymbolicAst

(** The local logger *)
let log = L.translate_log

type pure_fun_translation = Pure.fun_def * Pure.fun_def list

(** Execute the symbolic interpreter on a function to generate a list of symbolic ASTs,
    for the forward function and the backward functions.
 *)
let translate_function_to_symbolics (config : C.partial_config)
    (type_context : C.type_context) (fun_context : C.fun_context)
    (fdef : A.fun_def) : SA.expression * SA.expression list =
  (* Debug *)
  log#ldebug
    (lazy
      ("translate_function_to_symbolics: " ^ Print.name_to_string fdef.A.name));

  (* Evaluate *)
  let synthesize = true in
  let evaluate =
    evaluate_function_symbolic config synthesize type_context fun_context fdef
  in
  (* Execute the forward function *)
  let forward = Option.get (evaluate None) in
  (* Execute the backward functions *)
  let backwards =
    T.RegionGroupId.mapi
      (fun gid _ -> Option.get (evaluate (Some gid)))
      fdef.signature.regions_hierarchy
  in

  (* Return *)
  (forward, backwards)

(** Translate a function, by generating its forward and backward translations. *)
let translate_function_to_pure (config : C.partial_config)
    (type_context : C.type_context) (fun_context : C.fun_context)
    (fun_sigs : Pure.fun_sig SymbolicToPure.RegularFunIdMap.t)
    (fdef : A.fun_def) : pure_fun_translation =
  (* Debug *)
  log#ldebug
    (lazy ("translate_function_to_pure: " ^ Print.name_to_string fdef.A.name));

  let def_id = fdef.def_id in

  (* Compute the symbolic ASTs *)
  let symbolic_forward, symbolic_backwards =
    translate_function_to_symbolics config type_context fun_context fdef
  in

  (* Convert the symbolic ASTs to pure ASTs: *)

  (* Initialize the context *)
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
      sv_to_var;
      var_counter;
      type_context;
      fun_context;
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

  (* We need to initialize the input/output variables. First, the inputs
   * for the forward function *)
  let module RegularFunIdMap = SymbolicToPure.RegularFunIdMap in
  let forward_sg = RegularFunIdMap.find (A.Local def_id, None) fun_sigs in
  let ctx, forward_inputs = SymbolicToPure.fresh_vars forward_sg.inputs ctx in

  let ctx = { ctx with forward_inputs } in

  (* Translate the forward function *)
  let pure_forward =
    SymbolicToPure.translate_fun_def fdef ctx symbolic_forward
  in

  (* Translate the backward functions *)
  let translate_backward (rg : T.region_var_group) : Pure.fun_def =
    (* For the backward inputs/outputs initialization: we use the fact that
     * there are no nested borrows for now, and so that the region groups
     * can't have parents *)
    assert (rg.parents = []);
    (* TODO: the computation of the backward inputs is a bit awckward... *)
    let back_id = rg.id in
    let backward_sg =
      RegularFunIdMap.find (A.Local def_id, Some back_id) fun_sigs
    in
    let _, backward_inputs =
      Collections.List.split_at backward_sg.inputs (List.length forward_inputs)
    in
    let ctx, backward_inputs = SymbolicToPure.fresh_vars backward_inputs ctx in
    let backward_outputs = backward_sg.outputs in
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
      { ctx with bid = Some back_id; backward_inputs; backward_outputs }
    in

    (* Translate *)
    let symbolic = T.RegionGroupId.nth symbolic_backwards back_id in
    SymbolicToPure.translate_fun_def fdef ctx symbolic
  in
  let pure_backwards =
    List.map translate_backward fdef.signature.regions_hierarchy
  in

  (* Return *)
  (pure_forward, pure_backwards)

let translate_module_to_pure (config : C.partial_config) (m : M.cfim_module) :
    Pure.type_def T.TypeDefId.Map.t * pure_fun_translation A.FunDefId.Map.t =
  (* Debug *)
  log#ldebug (lazy "translate_module_to_pure");

  (* Compute the type and function contexts *)
  let type_context, fun_context = compute_type_fun_contexts m in

  (* Translate all the type definitions *)
  let type_defs = SymbolicToPure.translate_type_defs m.types in

  (* Translate all the function *signatures* *)
  let assumed_sigs =
    List.map (fun (id, sg) -> (A.Assumed id, sg)) Assumed.assumed_sigs
  in
  let local_sigs =
    List.map
      (fun (fdef : A.fun_def) -> (A.Local fdef.def_id, fdef.signature))
      m.functions
  in
  let sigs = List.append assumed_sigs local_sigs in
  let fun_sigs =
    SymbolicToPure.translate_fun_signatures type_context.type_infos sigs
  in

  (* Translate all the functions *)
  let pure_translations =
    List.map
      (fun (fdef : A.fun_def) ->
        ( fdef.def_id,
          translate_function_to_pure config type_context fun_context fun_sigs
            fdef ))
      m.functions
  in

  (* Put the translated functions in a map *)
  let fun_defs =
    List.fold_left
      (fun m (def_id, trans) -> A.FunDefId.Map.add def_id trans m)
      A.FunDefId.Map.empty pure_translations
  in

  (* Return *)
  (type_defs, fun_defs)
