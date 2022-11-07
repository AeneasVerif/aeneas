include Charon.Logging

(** Below, we create subgloggers for various submodules, so that we can precisely
    toggle logging on/off, depending on which information we need *)

(** Logger for PrePasses *)
let pre_passes_log = L.get_logger "MainLogger.PrePasses"

(** Logger for Translate *)
let translate_log = L.get_logger "MainLogger.Translate"

(** Logger for PureUtils *)
let pure_utils_log = L.get_logger "MainLogger.PureUtils"

(** Logger for SymbolicToPure *)
let symbolic_to_pure_log = L.get_logger "MainLogger.SymbolicToPure"

(** Logger for PureMicroPasses *)
let pure_micro_passes_log = L.get_logger "MainLogger.PureMicroPasses"

(** Logger for PureToExtract *)
let pure_to_extract_log = L.get_logger "MainLogger.PureToExtract"

(** Logger for Interpreter *)
let interpreter_log = L.get_logger "MainLogger.Interpreter"

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
