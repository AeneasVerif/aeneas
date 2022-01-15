module C = Collections

(** Signature for a module describing an identifier.
    
    We often need identifiers (for definitions, variables, etc.) and in
    order to make sure we don't mix them, we use a generative functor
    (see [IdGen]).
*)
module type Id = sig
  type id

  type generator
  (** Id generator - simply a counter *)

  val zero : id

  val generator_zero : generator

  val fresh_stateful_generator : unit -> generator ref * (unit -> id)

  (* TODO: this should be stateful! - but we may want to be able to duplicate
     contexts...
     Maybe we could have a `fresh` and a `global_fresh`
     TODO: change the order of the returned types
  *)
  val fresh : generator -> id * generator

  val to_string : id -> string

  val pp_id : Format.formatter -> id -> unit

  val show_id : id -> string

  val id_of_json : Yojson.Basic.t -> (id, string) result

  val pp_generator : Format.formatter -> generator -> unit

  val show_generator : generator -> string

  val to_int : id -> int

  val of_int : int -> id

  val nth : 'a list -> id -> 'a

  val nth_opt : 'a list -> id -> 'a option

  val update_nth : 'a list -> id -> 'a -> 'a list
  (** Update the nth element of the list.

      Raises [Invalid_argument] if the identifier is out of range.
   *)

  val mapi : (id -> 'a -> 'b) -> 'a list -> 'b list

  val mapi_from1 : (id -> 'a -> 'b) -> 'a list -> 'b list
  (** Same as [mapi], but where the indices start with 1.
       
      TODO: generalize to `map_from_i`
   *)

  module Ord : C.OrderedType with type t = id

  module Set : C.Set with type elt = id

  module Map : C.Map with type key = id
end

(** Generative functor for identifiers.

    See [Id].
*)
module IdGen () : Id = struct
  (* TODO: use Z.t *)
  type id = int [@@deriving show]

  type generator = id [@@deriving show]

  let zero = 0

  let generator_zero = 0

  let incr x =
    (* Identifiers should never overflow (because max_int is a really big
     * value - but we really want to make sure we detect overflows if
     * they happen *)
    if x == max_int then raise (Errors.IntegerOverflow ()) else x + 1

  let fresh_stateful_generator () =
    let g = ref 0 in
    let fresh () =
      let id = !g in
      g := incr id;
      id
    in
    (g, fresh)

  let fresh gen = (gen, incr gen)

  let to_string = string_of_int

  let to_int x = x

  let of_int x = x

  let id_of_json js =
    (* TODO: check boundaries ? *)
    match js with
    | `Int i -> Ok i
    | _ -> Error ("id_of_json: failed on " ^ Yojson.Basic.show js)

  let nth v id = List.nth v id

  let nth_opt v id = List.nth_opt v id

  let rec update_nth vec id v =
    match (vec, id) with
    | [], _ -> raise (Invalid_argument "Out of range")
    | _ :: vec', 0 -> v :: vec'
    | x :: vec', _ -> x :: update_nth vec' (id - 1) v

  let mapi = List.mapi

  let mapi_from1 f ls =
    let rec aux i ls =
      match ls with [] -> [] | x :: ls' -> f i x :: aux (i + 1) ls'
    in
    aux 1 ls

  module Ord = struct
    type t = id

    let compare = compare

    let to_string = to_string

    let pp_t = pp_id

    let show_t = show_id
  end

  module Set = C.MakeSet (Ord)
  module Map = C.MakeMap (Ord)
end

type name = string list [@@deriving show]
(** A name such as: `std::collections::vector` (which would be represented as
    [["std"; "collections"; "vector"]]) *)
