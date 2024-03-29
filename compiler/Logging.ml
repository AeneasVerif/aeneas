include Charon.Logging

(** Below, we create subgloggers for various submodules, so that we can precisely
    toggle logging on/off, depending on which information we need *)

(** Logger for Errors *)
let errors_log = L.get_logger "MainLogger.Errors"

(** Logger for PrePasses *)
let pre_passes_log = L.get_logger "MainLogger.PrePasses"

(** Logger for RegionsHierarchy *)
let regions_hierarchy_log = L.get_logger "MainLogger.RegionsHierarchy"

(** Logger for Translate *)
let translate_log = L.get_logger "MainLogger.Translate"

(** Logger for Contexts *)
let contexts_log = L.get_logger "MainLogger.Contexts"

(** Logger for PureUtils *)
let pure_utils_log = L.get_logger "MainLogger.PureUtils"

(** Logger for SymbolicToPure *)
let symbolic_to_pure_log = L.get_logger "MainLogger.SymbolicToPure"

(** Logger for PureMicroPasses *)
let pure_micro_passes_log = L.get_logger "MainLogger.PureMicroPasses"

(** Logger for ExtractBase *)
let extract_log = L.get_logger "MainLogger.ExtractBase"

(** Logger for ExtractBuiltin *)
let builtin_log = L.get_logger "MainLogger.Builtin"

(** Logger for Interpreter *)
let interpreter_log = L.get_logger "MainLogger.Interpreter"

(** Logger for InterpreterLoopsMatchCtxs *)
let loops_match_ctxs_log = L.get_logger "MainLogger.Interpreter.LoopsMatchCtxs"

(** Logger for InterpreterLoopsJoinCtxs *)
let loops_join_ctxs_log = L.get_logger "MainLogger.Interpreter.LoopsJoinCtxs"

(** Logger for InterpreterLoopsFixedPoint *)
let loops_fixed_point_log = L.get_logger "MainLogger.Interpreter.FixedPoint"

(** Logger for InterpreterLoops *)
let loops_log = L.get_logger "MainLogger.Interpreter.Loops"

(** Logger for InterpreterStatements *)
let statements_log = L.get_logger "MainLogger.Interpreter.Statements"

(** Logger for InterpreterExpressions *)
let expressions_log = L.get_logger "MainLogger.Interpreter.Expressions"

(** Logger for InterpreterPaths *)
let paths_log = L.get_logger "MainLogger.Interpreter.Paths"

(** Logger for InterpreterExpansion *)
let expansion_log = L.get_logger "MainLogger.Interpreter.Expansion"

(** Logger for InterpreterProjectors *)
let projectors_log = L.get_logger "MainLogger.Interpreter.Projectors"

(** Logger for InterpreterBorrows *)
let borrows_log = L.get_logger "MainLogger.Interpreter.Borrows"

(** Logger for Invariants *)
let invariants_log = L.get_logger "MainLogger.Interpreter.Invariants"

(** Logger for AssociatedTypes *)
let associated_types_log = L.get_logger "MainLogger.AssociatedTypes"

(** Logger for SCC *)
let scc_log = L.get_logger "MainLogger.Graph.SCC"

(** Logger for ReorderDecls *)
let reorder_decls_log = L.get_logger "MainLogger.Graph.ReorderDecls"
