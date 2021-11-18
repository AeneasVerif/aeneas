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

  val empty_vector : 'a vector

  module Set : Set.S with type elt = id

  val id_of_json : Yojson.Basic.t -> (id, string) result

  val vector_of_json :
    (Yojson.Basic.t -> ('a, string) result) ->
    Yojson.Basic.t ->
    ('a vector, string) result
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

  let empty_vector = []

  module Set = Set.Make (struct
    type t = id

    let compare = compare
  end)

  let id_of_json js =
    match js with
    | `Int i -> Ok i
    | _ -> Error ("id_of_json: failed on " ^ Yojson.Basic.show js)

  let vector_of_json a_of_json js =
    OfJsonBasic.combine_error_msgs js "vector_of_json"
      (OfJsonBasic.list_of_json a_of_json js)
end

type name = string list [@@deriving yojson]
(** A name such as: `std::collections::vector` (which would be represented as
    [["std"; "collections"; "vector"]]) *)
