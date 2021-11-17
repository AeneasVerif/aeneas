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

  val id_of_yojson : Yojson.Safe.t -> (id, string) Result.result

  val id_of_json : Yojson.Safe.t -> (id, string) Result.result

  val id_to_yojson : id -> Yojson.Safe.t

  val vector_of_yojson :
    (Yojson.Safe.t -> ('a, string) Result.result) ->
    Yojson.Safe.t ->
    ('a vector, string) Result.result

  val vector_of_json :
    (Yojson.Safe.t -> ('a, string) Result.result) ->
    Yojson.Safe.t ->
    ('a vector, string) Result.result

  val vector_to_yojson : ('a -> Yojson.Safe.t) -> 'a vector -> Yojson.Safe.t

  (* TODO: remove *)
  (* module Map : Map.S with type key = id *)
end

(** Generative functor for identifiers.

    See [Id].
*)
module IdGen () : Id = struct
  (* TODO: use Int64.t *)
  type id = int [@@deriving yojson]

  type 'a vector = 'a list [@@deriving yojson]

  let zero = 0

  let incr x =
    (* Identifiers should never overflow (because max_int is a really big
     * value - but we really want to make sure we detect overflows if
     * they happen *)
    if x == max_int then raise (IntegerOverflow ()) else x + 1

  let to_string = string_of_int

  let id_of_json = id_of_yojson

  let vector_of_json = vector_of_yojson

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
