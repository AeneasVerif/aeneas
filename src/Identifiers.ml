(** Signature for a module describing an identifier.
    
    We often need identifiers (for definitions, variables, etc.) and in
    order to make sure we don't mix them, we use a generative functor
    (see [IdGen]).
*)
module type Id = sig
  type id

  type generator
  (** Id generator - simply a counter *)

  type set_t

  val zero : id

  val generator_zero : generator

  (* TODO: this is stateful! - but we may want to be able to duplicate contexts... *)
  val fresh : generator -> id * generator
  (* TODO: change the order of the returned types *)

  val to_string : id -> string

  val pp_id : Format.formatter -> id -> unit

  val show_id : id -> string

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
  (** Same as [mapi], but where the indices start with 1 *)

  val pp_set_t : Format.formatter -> set_t -> unit

  val show_set_t : set_t -> string

  module Ord : Map.OrderedType with type t = id

  module Set : Set.S with type elt = id with type t = set_t

  val set_to_string : Set.t -> string

  module Map : Map.S with type key = id

  val id_of_json : Yojson.Basic.t -> (id, string) result
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

  let fresh gen = (gen, incr gen)

  let to_string = string_of_int

  let to_int x = x

  let of_int x = x

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
  end

  module Set = Set.Make (Ord)
  module Map = Map.Make (Ord)

  type set_t = Set.t

  let show_set_t s =
    let ids = Set.fold (fun id s -> to_string id :: s) s [] in
    let ids = List.rev ids in
    "{" ^ String.concat "," ids ^ "}"

  let pp_set_t fmt s = Format.pp_print_string fmt (show_set_t s)

  let set_to_string ids =
    let ids = Set.fold (fun id ids -> to_string id :: ids) ids [] in
    "{" ^ String.concat ", " (List.rev ids) ^ "}"

  let id_of_json js =
    (* TODO: check boundaries ? *)
    match js with
    | `Int i -> Ok i
    | _ -> Error ("id_of_json: failed on " ^ Yojson.Basic.show js)
end

type name = string list [@@deriving show]
(** A name such as: `std::collections::vector` (which would be represented as
    [["std"; "collections"; "vector"]]) *)
