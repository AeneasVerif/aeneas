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

module TypeVarId = IdGen ()

module TypeDefId = IdGen ()

module VariantId = IdGen ()

module FieldId = IdGen ()

module RegionVarId = IdGen ()

type type_var = {
  index : TypeVarId.id;  (** Unique index identifying the variable *)
  name : string;  (** Variable name *)
}

type region_var = {
  index : RegionVarId.id;  (** Unique index identifying the region *)
  name : string option;  (** Region name *)
}

(** A region.
    
    Regions are used in function signatures (in which case we use region variable
    ids) and in symbolic variables and projections (in which case we use region
    ids).
 *)
type 'rid region =
  | Static  (** Static region *)
  | Var of 'rid  (** Non-static region *)

(** The type of erased regions.
    
    We could use unit, but having a dedicated type makes things more explicit.
 *)
type erased_region = Erased

(* TODO *)
type rty = unit

type field = { name : string; ty : rty }

type variant = { name : string; fields : field FieldId.vector }

type type_def_kind =
  | Struct of field FieldId.vector
  | Enum of variant VariantId.vector

type type_def = {
  def_id : TypeDefId.id;
  name : name;
  region_params : region_var RegionVarId.vector;
  type_params : type_var TypeVarId.vector;
  kind : type_def_kind;
}

module Id0 = IdGen ()

module Id1 = IdGen ()

let x0 = Id0.zero

let x1 = Id0.incr x0

let () =
  let _ = print_endline "Hello, world!" in
  let _ = print_endline (Id0.to_string x1) in
  ()
