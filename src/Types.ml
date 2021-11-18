open Identifiers

module TypeVarId = IdGen ()

module TypeDefId = IdGen ()

module VariantId = IdGen ()

module FieldId = IdGen ()

module RegionVarId = IdGen ()

type type_var = {
  tv_index : TypeVarId.id;  (** Unique index identifying the variable *)
  tv_name : string;  (** Variable name *)
}

type region_var = {
  rv_index : RegionVarId.id;  (** Unique index identifying the region *)
  rv_name : string option;  (** Region name *)
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

type ref_kind = Mut | Shared

type assumed_ty = Box

type 'r ty =
  | Adt of TypeDefId.id * 'r list * 'r ty list
  | TypeVar of TypeVarId.id
  | Bool
  | Char
  | Never
  | Integer of integer_type
  | Str
  | Array of 'r ty (* TODO: there should be a constant with the array *)
  | Slice of 'r ty
  | Ref of 'r * 'r ty * ref_kind
  | Tuple of 'r ty list
  | Assumed of assumed_ty * 'r list * 'r ty list

type rty = RegionVarId.id region ty
(** Type with *R*egions.

    Used in function signatures and type definitions.
 *)

type ety = erased_region ty
(** Type with *E*rased regions.
    
    Used in function bodies, "general" value types, etc.
 *)

type field = { field_name : string; field_ty : rty }

type variant = { variant_name : string; fields : field FieldId.vector }

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
