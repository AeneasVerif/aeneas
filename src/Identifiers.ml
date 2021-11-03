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
end

(** Generative functor for identifiers.

    See [Id].
*)
module IdGen () : Id = struct
  type id = int

  type 'a vector = 'a list (* TODO: use a map *)

  let zero = 0

  let incr x =
    (* Identifiers should never overflow (because max_int is a really big
     * value - but we really want to make sure we detect overflows if
     * they happen *)
    if x == max_int then raise (IntegerOverflow ()) else x + 1

  let to_string = string_of_int
end

type name = string list
(** A name such as: `std::collections::vector` *)
