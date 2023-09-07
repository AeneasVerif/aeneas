(** This file declares external identifiers that we catch to map them to
    definitions coming from the standard libraries in our backends. *)

open Utils
open StringUtils
open Names

type simple_name = string list [@@deriving show, ord]

let name_to_simple_name (s : name) : simple_name =
  (* We simply ignore the disambiguators *)
  List.filter_map (function Ident id -> Some id | Disambiguator _ -> None) s

(** Small helper which cuts a string at the occurrences of "::" *)
let string_to_simple_name (s : string) : simple_name =
  (* No function to split by using string separator?? *)
  let name = String.split_on_char ':' s in
  List.filter (fun s -> s <> "") name

module SimpleNameOrd = struct
  type t = simple_name

  let compare = compare_simple_name
  let to_string = show_simple_name
  let pp_t = pp_simple_name
  let show_t = show_simple_name
end

module SimpleNameMap = Collections.MakeMap (SimpleNameOrd)

let assumed_globals : (string * string) list =
  [
    ("core::num::usize::MAX", "usize_max");
    ("core::num::u8::MAX", "u8_max");
    ("core::num::u16::MAX", "u16_max");
    ("core::num::u32::MAX", "u32_max");
    ("core::num::u64::MAX", "u64_max");
    ("core::num::u128::MAX", "u128_max");
    ("core::num::isize::MAX", "isize_max");
    ("core::num::i8::MAX", "i8_max");
    ("core::num::i16::MAX", "i16_max");
    ("core::num::i32::MAX", "i32_max");
    ("core::num::i64::MAX", "i64_max");
    ("core::num::i128::MAX", "i128_max");
  ]

let assumed_globals_map : string SimpleNameMap.t =
  SimpleNameMap.of_list
    (List.map (fun (x, y) -> (string_to_simple_name x, y)) assumed_globals)
