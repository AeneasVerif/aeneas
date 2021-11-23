open Errors

(** Signature for a module describing an identifier.
    
    We often need identifiers (for definitions, variables, etc.) and in
    order to make sure we don't mix them, we use a generative functor
    (see [IdGen]).
*)
module type Id = sig
  type id

  type generator
  (** Id generator - simply a counter *)

  type 'a vector

  val zero : id

  val fresh : generator -> id * generator

  val to_string : id -> string

  val empty_vector : 'a vector

  val vector_to_list : 'a vector -> 'a list

  val vector_of_list : 'a list -> 'a vector

  val nth : 'a vector -> id -> 'a

  val nth_opt : 'a vector -> id -> 'a option

  val update_nth : 'a vector -> id -> 'a -> 'a vector

  val iter : ('a -> unit) -> 'a vector -> unit

  val map : ('a -> 'b) -> 'a vector -> 'b vector

  module Set : Set.S with type elt = id

  val set_to_string : Set.t -> string

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

  type generator = id

  type 'a vector = 'a list

  let zero = 0

  let incr x =
    (* Identifiers should never overflow (because max_int is a really big
     * value - but we really want to make sure we detect overflows if
     * they happen *)
    if x == max_int then raise (Errors.IntegerOverflow ()) else x + 1

  let fresh gen = (gen, incr gen)

  let to_string = string_of_int

  let empty_vector = []

  let vector_to_list v = v

  let vector_of_list v = v

  let nth v id = List.nth v id

  let nth_opt v id = List.nth_opt v id

  let rec update_nth vec id v =
    match (vec, id) with
    | [], _ -> failwith "Unreachable"
    | _ :: vec', 0 -> v :: vec'
    | x :: vec', _ -> x :: update_nth vec' (id - 1) v

  let iter = List.iter

  let map = List.map

  module Set = Set.Make (struct
    type t = id

    let compare = compare
  end)

  let set_to_string ids =
    let ids = Set.fold (fun id ids -> to_string id :: ids) ids [] in
    "{" ^ String.concat ", " (List.rev ids) ^ "}"

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
