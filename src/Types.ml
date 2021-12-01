open Identifiers

module TypeVarId = IdGen ()

module TypeDefId = IdGen ()

module VariantId = IdGen ()

module FieldId = IdGen ()

module RegionVarId = IdGen ()

type ('id, 'name) indexed_var = {
  index : 'id;  (** Unique index identifying the variable *)
  name : 'name;  (** Variable name *)
}
[@@deriving show]

type type_var = (TypeVarId.id, string) indexed_var [@@deriving show]

type region_var = (RegionVarId.id, string option) indexed_var [@@deriving show]

(** A region.
    
    Regions are used in function signatures (in which case we use region variable
    ids) and in symbolic variables and projections (in which case we use region
    ids).
 *)
type 'rid region =
  | Static  (** Static region *)
  | Var of 'rid  (** Non-static region *)
[@@deriving show]

(** The type of erased regions.
    
    We could use unit, but having a dedicated type makes things more explicit.
 *)
type erased_region = Erased [@@deriving show]

type integer_type =
  | Isize
  | I8
  | I16
  | I32
  | I64
  | I128
  | Usize
  | U8
  | U16
  | U32
  | U64
  | U128
[@@deriving show]

type ref_kind = Mut | Shared [@@deriving show]

type assumed_ty = Box [@@deriving show]

type 'r ty =
  | Adt of TypeDefId.id * 'r list * 'r ty list
  | Tuple of 'r ty list
  | TypeVar of TypeVarId.id
  | Bool
  | Char
  | Never
  | Integer of integer_type
  | Str
  | Array of 'r ty (* TODO: there should be a constant with the array *)
  | Slice of 'r ty
  | Ref of 'r * 'r ty * ref_kind
  | Assumed of assumed_ty * 'r list * 'r ty list
[@@deriving show]
(* TODO: group Bool, Char, etc. in Constant *)

type rty = RegionVarId.id region ty [@@deriving show]
(** Type with *R*egions.

    Used in function signatures and type definitions.
 *)

type ety = erased_region ty [@@deriving show]
(** Type with *E*rased regions.
    
    Used in function bodies, "general" value types, etc.
 *)

type field = { field_name : string; field_ty : rty } [@@deriving show]

type variant = { variant_name : string; fields : field list } [@@deriving show]

type type_def_kind = Struct of field list | Enum of variant list
[@@deriving show]

type type_def = {
  def_id : TypeDefId.id;
  name : name;
  region_params : region_var list;
  type_params : type_var list;
  kind : type_def_kind;
}
[@@deriving show]
