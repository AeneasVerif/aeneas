include Charon.Logging
open Collections

(** Below, we create loggers for various (sub-)modules, so that we can precisely
    toggle logging on/off, depending on which information we need *)

let loggers : L.logger StringMap.t ref = ref StringMap.empty

let create_logger name =
  let l = L.get_logger ("MainLogger." ^ name) in
  loggers := StringMap.add name l !loggers;
  l#set_level Info;
  l

let to_log_msg (f : string) (line : int) (msg : string) : string =
  let line = ", line " ^ string_of_int line in
  if msg = "" then f ^ line ^ "\n" else f ^ line ^ ":\n" ^ msg ^ "\n"

(** The main logger - this one is created in Charon *)
let () =
  loggers := StringMap.add "MainLogger" main_log !loggers;
  main_log#set_level Info

(** Logger for Errors *)
let errors_log = create_logger "Errors"

(** Logger for PrePasses *)
let pre_passes_log = create_logger "PrePasses"

(** Logger for RegionsHierarchy *)
let regions_hierarchy_log = create_logger "RegionsHierarchy"

(** Logger for TypesAnalysis *)
let types_analysis_log = create_logger "TypesAnalysis"

(** Logger for FunsAnalysis *)
let funs_analysis_log = create_logger "FunsAnalysis"

(** Logger for Translate *)
let translate_log = create_logger "Translate"

(** Logger for BorrowCheck *)
let borrow_check_log = create_logger "BorrowCheck"

(** Logger for Contexts *)
let contexts_log = create_logger "Contexts"

(** Logger for PureUtils *)
let pure_utils_log = create_logger "PureUtils"

(** Logger for PureTypeCheck *)
let pure_type_check_log = create_logger "PureTypeCheck"

(** Logger for SymbolicToPureTypes *)
let symbolic_to_pure_types_log = create_logger "SymbolicToPureTypes"

(** Logger for SymbolicToPureValues *)
let symbolic_to_pure_values_log = create_logger "SymbolicToPureValues"

(** Logger for SymbolicToPureAbs *)
let symbolic_to_pure_abs_log = create_logger "SymbolicToPureAbs"

(** Logger for SymbolicToPureExpressions *)
let symbolic_to_pure_expressions_log = create_logger "SymbolicToPureExpressions"

(** Logger for SymbolicToPure *)
let symbolic_to_pure_log = create_logger "SymbolicToPure"

(** Logger for PureMicroPasses *)
let pure_micro_passes_log = create_logger "PureMicroPasses"

(** Logger for PureMicroPasses.simplify_aggregates_unchanged_fields *)
let simplify_aggregates_unchanged_fields_log =
  create_logger "PureMicroPasses.simplify_aggregates_unchanged_fields"

(** Logger for ExtractBase *)
let extract_log = create_logger "Extract"

(** Logger for ExtractBuiltin *)
let builtin_log = create_logger "Builtin"

(** Logger for Interp *)
let interp_log = create_logger "Interp"

(** Logger for InterpMatchCtxs *)
let match_ctxs_log = create_logger "InterpMatchCtxs"

(** Logger for InterpReduceCollapse *)
let reduce_collapse_log = create_logger "InterpReduceCollapse"

(** Logger for InterpJoin *)
let join_log = create_logger "InterpJoin"

(** Logger for InterpLoopsFixedPoint *)
let loops_fixed_point_log = create_logger "InterpLoopsFixedPoint"

(** Logger for InterpLoops *)
let loops_log = create_logger "InterpLoops"

(** Logger for InterpStatements *)
let statements_log = create_logger "InterpStatements"

(** Logger for InterpExpressions *)
let expressions_log = create_logger "InterpExpressions"

(** Logger for InterpPaths *)
let paths_log = create_logger "InterpPaths"

(** Logger for InterpExpansion *)
let expansion_log = create_logger "InterpExpansion"

(** Logger for InterpProjectors *)
let projectors_log = create_logger "InterpProjectors"

(** Logger for InterpBorrows *)
let borrows_log = create_logger "InterpBorrows"

(** Logger for InterpAbs *)
let abs_log = create_logger "InterpAbs"

(** Logger for Invariants *)
let invariants_log = create_logger "Invariants"

(** Logger for SCC *)
let scc_log = create_logger "SCC"

(** Logger for pure/ReorderDecls *)
let reorder_decls_log = create_logger "ReorderDecls"
