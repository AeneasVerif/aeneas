module C = Collections

(** Signature for a module describing an identifier.
    
    We often need identifiers (for definitions, variables, etc.) and in
    order to make sure we don't mix them, we use a generative functor
    (see {!IdGen}).
*)
module type Id = sig
  type id

  (** Id generator - simply a counter *)
  type generator

  val zero : id
  val generator_zero : generator
  val generator_from_incr_id : id -> generator
  val fresh_stateful_generator : unit -> generator ref * (unit -> id)
  val mk_stateful_generator : generator -> generator ref * (unit -> id)
  val incr : id -> id

  (* TODO: this should be stateful! - but we may want to be able to duplicate
     contexts...
     Maybe we could have a [fresh] and a [global_fresh]
     TODO: change the order of the returned types
  *)
  val fresh : generator -> id * generator
  val to_string : id -> string
  val pp_id : Format.formatter -> id -> unit
  val show_id : id -> string
  val id_of_json : Yojson.Basic.t -> (id, string) result
  val compare_id : id -> id -> int
  val max : id -> id -> id
  val min : id -> id -> id
  val pp_generator : Format.formatter -> generator -> unit
  val show_generator : generator -> string
  val to_int : id -> int
  val of_int : int -> id
  val nth : 'a list -> id -> 'a
  (* TODO: change the signature (invert the index and the list *)

  val nth_opt : 'a list -> id -> 'a option

  (** Update the nth element of the list.

      Raises [Invalid_argument] if the identifier is out of range.
   *)
  val update_nth : 'a list -> id -> 'a -> 'a list

  val mapi : (id -> 'a -> 'b) -> 'a list -> 'b list

  (** Same as {!mapi}, but where the indices start with 1.
       
      TODO: generalize to [map_from_i]
   *)
  val mapi_from1 : (id -> 'a -> 'b) -> 'a list -> 'b list

  val iteri : (id -> 'a -> unit) -> 'a list -> unit

  module Ord : C.OrderedType with type t = id
  module Set : C.Set with type elt = id
  module Map : C.Map with type key = id
end

(** Generative functor for identifiers.

    See {!Id}.
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
    if x = max_int then raise (Errors.IntegerOverflow ()) else x + 1

  let generator_from_incr_id id = incr id

  let mk_stateful_generator g =
    let g = ref g in
    let fresh () =
      let id = !g in
      g := incr id;
      id
    in
    (g, fresh)

  let fresh_stateful_generator () = mk_stateful_generator 0
  let fresh gen = (gen, incr gen)
  let to_string = string_of_int
  let to_int x = x
  let of_int x = x

  let id_of_json js =
    (* TODO: check boundaries ? *)
    match js with
    | `Int i -> Ok i
    | _ -> Error ("id_of_json: failed on " ^ Yojson.Basic.show js)

  let compare_id = compare
  let max id0 id1 = if id0 > id1 then id0 else id1
  let min id0 id1 = if id0 < id1 then id0 else id1
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

  let iteri = List.iteri

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
