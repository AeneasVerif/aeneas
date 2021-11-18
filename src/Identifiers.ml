exception IntegerOverflow of unit

(** Signature for a module describing an identifier.
    
    We often need identifiers (for definitions, variables, etc.) and in
    order to make sure we don't mix them, we use a generative functor
    (see [IdGen]).
*)
module type Id = sig
  type id

  type 'a vector

  val zero : id

  val incr : id -> id

  val to_string : id -> string

  val empty : 'a vector

  val id_of_json : Yojson.Basic.t -> (id, string) result

  val vector_of_json :
    (Yojson.Basic.t -> ('a, string) result) ->
    Yojson.Basic.t ->
    ('a vector, string) result

  (* TODO: remove *)
  (* module Map : Map.S with type key = id *)
end

(** Generative functor for identifiers.

    See [Id].
*)
module IdGen () : Id = struct
  (* TODO: use Int64.t *)
  type id = int

  type 'a vector = 'a list

  let zero = 0

  let incr x =
    (* Identifiers should never overflow (because max_int is a really big
     * value - but we really want to make sure we detect overflows if
     * they happen *)
    if x == max_int then raise (IntegerOverflow ()) else x + 1

  let to_string = string_of_int

  let empty = []

  let id_of_json js =
    match js with
    | `Int i -> Ok i
    | _ -> Error ("id_of_json: failed on " ^ Yojson.Basic.show js)

  let ( let* ) o f = match o with Error e -> Error e | Ok x -> f x

  (* TODO: this duplicates code from CfimToJson *)
  let rec of_json_list (a_of_json : Yojson.Basic.t -> ('a, string) result)
      (jsl : Yojson.Basic.t list) : ('a list, string) result =
    match jsl with
    | [] -> Ok []
    | x :: jsl' ->
        let* x = a_of_json x in
        let* jsl' = of_json_list a_of_json jsl' in
        Ok (x :: jsl')

  let vector_of_json a_of_json js =
    match js with
    | `List jsl -> (
        match of_json_list a_of_json jsl with
        | Error msg ->
            Error
              ("vector_of_json failed on: " ^ Yojson.Basic.show js ^ ":\n" ^ msg)
        | Ok x -> Ok x)
    | _ -> Error ("not a list: " ^ Yojson.Basic.show js)

  (* TODO: how to make this work? *)
  (* (module Ord : Map.OrderedType = struct
       type t = id

       let compare t1 t2 = t2 - t1
     end)

     module IdMap = Map.Make (Ord) *)

  (* module Map = Map.Make (struct
       type t = id

       let compare = Stdlib.compare
     end) *)

  (* let ord =
        (module struct
          type t = id

          let compare = Stdlib.compare
        end)

     module Map = Map.Make (ord) *)
end

type name = string list [@@deriving yojson]
(** A name such as: `std::collections::vector` (which would be represented as
    [["std"; "collections"; "vector"]]) *)
