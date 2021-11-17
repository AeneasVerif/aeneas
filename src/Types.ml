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
[@@deriving yojson]

type region_var = {
  rv_index : RegionVarId.id;  (** Unique index identifying the region *)
  rv_name : string option;  (** Region name *)
}
[@@deriving yojson]

(** A region.
    
    Regions are used in function signatures (in which case we use region variable
    ids) and in symbolic variables and projections (in which case we use region
    ids).
 *)
type 'rid region =
  | Static  (** Static region *)
  | Var of 'rid  (** Non-static region *)
[@@deriving yojson]

(** The type of erased regions.
    
    We could use unit, but having a dedicated type makes things more explicit.
 *)
type erased_region = Erased [@@deriving yojson]

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
[@@deriving yojson]

type ref_kind = Mut | Shared [@@deriving yojson]

type assumed_ty = Box [@@deriving yojson]

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
[@@deriving yojson]

type rty = RegionVarId.id region ty [@@deriving yojson]
(** Type with *R*egions.

    Used in function signatures and type definitions.
 *)

type ety = erased_region ty [@@deriving yojson]
(** Type with *E*rased regions.
    
    Used in function bodies, "general" value types, etc.
 *)

type field = { name : string; ty : rty } [@@deriving yojson]

type variant = { name : string; fields : field FieldId.vector }
[@@deriving yojson]

type type_def_kind =
  | Struct of field FieldId.vector
  | Enum of variant VariantId.vector
[@@deriving yojson]

type type_def = {
  def_id : TypeDefId.id;
  name : name;
  region_params : region_var RegionVarId.vector;
  type_params : type_var TypeVarId.vector;
  kind : type_def_kind;
}
[@@deriving yojson]
