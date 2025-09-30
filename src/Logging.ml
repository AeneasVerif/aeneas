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

let to_log_msg (f : string) (msg : string) : string =
  if msg = "" then f ^ "\n" else f ^ ":\n" ^ msg ^ "\n"

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

(** Logger for Interpreter *)
let interpreter_log = create_logger "Interpreter"

(** Logger for InterpreterLoopsMatchCtxs *)
let loops_match_ctxs_log = create_logger "Interpreter.LoopsMatchCtxs"

(** Logger for InterpreterLoopsJoinCtxs *)
let loops_join_ctxs_log = create_logger "Interpreter.LoopsJoinCtxs"

(** Logger for InterpreterLoopsFixedPoint *)
let loops_fixed_point_log = create_logger "Interpreter.LoopsFixedPoint"

(** Logger for InterpreterLoops *)
let loops_log = create_logger "Interpreter.Loops"

(** Logger for InterpreterStatements *)
let statements_log = create_logger "Interpreter.Statements"

(** Logger for InterpreterExpressions *)
let expressions_log = create_logger "Interpreter.Expressions"

(** Logger for InterpreterPaths *)
let paths_log = create_logger "Interpreter.Paths"

(** Logger for InterpreterExpansion *)
let expansion_log = create_logger "Interpreter.Expansion"

(** Logger for InterpreterProjectors *)
let projectors_log = create_logger "Interpreter.Projectors"

(** Logger for InterpreterBorrows *)
let borrows_log = create_logger "Interpreter.Borrows"

(** Logger for InterpreterAbs *)
let abs_log = create_logger "Interpreter.Abs"

(** Logger for Invariants *)
let invariants_log = create_logger "Interpreter.Invariants"

(** Logger for SCC *)
let scc_log = create_logger "Graph.SCC"

(** Logger for ReorderDecls *)
let reorder_decls_log = create_logger "Graph.ReorderDecls"
