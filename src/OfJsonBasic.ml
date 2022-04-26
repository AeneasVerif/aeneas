(** This module defines various basic utilities for json deserialization.
   
 *)

open Yojson.Basic

type json = t

let ( let* ) o f = match o with Error e -> Error e | Ok x -> f x

let combine_error_msgs js msg res : ('a, string) result =
  match res with
  | Ok x -> Ok x
  | Error e -> Error ("[" ^ msg ^ "]" ^ " failed on: " ^ show js ^ "\n\n" ^ e)

let bool_of_json (js : json) : (bool, string) result =
  match js with
  | `Bool b -> Ok b
  | _ -> Error ("bool_of_json: not a bool: " ^ show js)

let int_of_json (js : json) : (int, string) result =
  match js with
  | `Int i -> Ok i
  | _ -> Error ("int_of_json: not an int: " ^ show js)

let char_of_json (js : json) : (char, string) result =
  match js with
  | `String c ->
      if String.length c = 1 then Ok c.[0]
      else Error ("char_of_json: stricly more than one character in: " ^ show js)
  | _ -> Error ("char_of_json: not a char: " ^ show js)

let rec of_json_list (a_of_json : json -> ('a, string) result) (jsl : json list)
    : ('a list, string) result =
  match jsl with
  | [] -> Ok []
  | x :: jsl' ->
      let* x = a_of_json x in
      let* jsl' = of_json_list a_of_json jsl' in
      Ok (x :: jsl')

let pair_of_json (a_of_json : json -> ('a, string) result)
    (b_of_json : json -> ('b, string) result) (js : json) :
    ('a * 'b, string) result =
  match js with
  | `List [ a; b ] ->
      let* a = a_of_json a in
      let* b = b_of_json b in
      Ok (a, b)
  | _ -> Error ("pair_of_json failed on: " ^ show js)

let list_of_json (a_of_json : json -> ('a, string) result) (js : json) :
    ('a list, string) result =
  combine_error_msgs js "list_of_json"
    (match js with
    | `List jsl -> of_json_list a_of_json jsl
    | _ -> Error ("not a list: " ^ show js))

let string_of_json (js : json) : (string, string) result =
  match js with
  | `String str -> Ok str
  | _ -> Error ("string_of_json: not a string: " ^ show js)

let option_of_json (a_of_json : json -> ('a, string) result) (js : json) :
    ('a option, string) result =
  combine_error_msgs js "option_of_json"
    (match js with
    | `Null -> Ok None
    | _ ->
        let* x = a_of_json js in
        Ok (Some x))

let string_option_of_json (js : json) : (string option, string) result =
  combine_error_msgs js "string_option_of_json"
    (option_of_json string_of_json js)
