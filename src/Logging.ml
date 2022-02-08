module H = Easy_logging.Handlers
module L = Easy_logging.Logging

let _ = L.make_logger "MainLogger" Debug [ Cli Debug ]

(** The main logger *)
let main_log = L.get_logger "MainLogger"

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

(** Logger for InterpreterBorrows *)
let borrows_log = L.get_logger "MainLogger.Interpreter.Borrows"

(** Logger for Invariants *)
let invariants_log = L.get_logger "MainLogger.Interpreter.Invariants"

(** Terminal colors - TODO: comes from easy_logging (did not manage to reuse the module directly) *)
type color =
  | Default
  | Black
  | Red
  | Green
  | Yellow
  | Blue
  | Magenta
  | Cyan
  | Gray
  | White
  | LRed
  | LGreen
  | LYellow
  | LBlue
  | LMagenta
  | LCyan
  | LGray

(** Terminal styles - TODO: comes from easy_logging (did not manage to reuse the module directly) *)
type format = Bold | Underline | Invert | Fg of color | Bg of color

(** TODO: comes from easy_logging (did not manage to reuse the module directly) *)
let to_fg_code c =
  match c with
  | Default -> 39
  | Black -> 30
  | Red -> 31
  | Green -> 32
  | Yellow -> 33
  | Blue -> 34
  | Magenta -> 35
  | Cyan -> 36
  | Gray -> 90
  | White -> 97
  | LRed -> 91
  | LGreen -> 92
  | LYellow -> 93
  | LBlue -> 94
  | LMagenta -> 95
  | LCyan -> 96
  | LGray -> 37

(** TODO: comes from easy_logging (did not manage to reuse the module directly) *)
let to_bg_code c =
  match c with
  | Default -> 49
  | Black -> 40
  | Red -> 41
  | Green -> 42
  | Yellow -> 43
  | Blue -> 44
  | Magenta -> 45
  | Cyan -> 46
  | Gray -> 100
  | White -> 107
  | LRed -> 101
  | LGreen -> 102
  | LYellow -> 103
  | LBlue -> 104
  | LMagenta -> 105
  | LCyan -> 106
  | LGray -> 47

(** TODO: comes from easy_logging (did not manage to reuse the module directly) *)
let style_to_codes s =
  match s with
  | Bold -> (1, 21)
  | Underline -> (4, 24)
  | Invert -> (7, 27)
  | Fg c -> (to_fg_code c, to_fg_code Default)
  | Bg c -> (to_bg_code c, to_bg_code Default)

(** TODO: comes from easy_logging (did not manage to reuse the module directly) *)
let level_to_color (lvl : L.level) =
  match lvl with
  | L.Flash -> LMagenta
  | Error -> LRed
  | Warning -> LYellow
  | Info -> LBlue
  | Trace -> Cyan
  | Debug -> Green
  | NoLevel -> Default

(** [format styles str] formats [str] to the given [styles] -
    TODO: comes from easy_logging (did not manage to reuse the module directl)
*)
let rec format styles str =
  match styles with
  | (_ as s) :: styles' ->
      let set, reset = style_to_codes s in
      Printf.sprintf "\027[%dm%s\027[%dm" set (format styles' str) reset
  | [] -> str

(** TODO: comes from easy_logging (did not manage to reuse the module directly) *)
let format_tags (tags : string list) =
  match tags with
  | [] -> ""
  | _ ->
      let elems_str = String.concat " | " tags in
      "[" ^ elems_str ^ "] "

(* Change the formatters *)
let main_logger_handler =
  (* TODO: comes from easy_logging *)
  let formatter (item : L.log_item) : string =
    let item_level_fmt =
      format [ Fg (level_to_color item.level) ] (L.show_level item.level)
    and item_msg_fmt =
      match item.level with
      | Flash -> format [ Fg Black; Bg LMagenta ] item.msg
      | _ -> item.msg
    in

    Format.pp_set_max_indent Format.str_formatter 200;
    Format.sprintf "@[[%-15s] %s%s@]" item_level_fmt (format_tags item.tags)
      item_msg_fmt
  in
  (* There should be exactly one handler *)
  let handlers = main_log#get_handlers in
  List.iter (fun h -> H.set_formatter h formatter) handlers;
  match handlers with [ handler ] -> handler | _ -> failwith "Unexpected"
