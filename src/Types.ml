open Identifiers

module TypeVarId = IdGen ()

module TypeDefId = IdGen ()

module VariantId = IdGen ()

module FieldId = IdGen ()

module RegionVarId = IdGen ()

type type_var = {
  index : TypeVarId.id;  (** Unique index identifying the variable *)
  name : string;  (** Variable name *)
}
[@@deriving of_yojson]

type region_var = {
  index : RegionVarId.id;  (** Unique index identifying the region *)
  name : string option;  (** Region name *)
}
[@@deriving of_yojson]

(** A region.
    
    Regions are used in function signatures (in which case we use region variable
    ids) and in symbolic variables and projections (in which case we use region
    ids).
 *)
type 'rid region =
  | Static  (** Static region *)
  | Var of 'rid  (** Non-static region *)
[@@deriving of_yojson]

(** The type of erased regions.
    
    We could use unit, but having a dedicated type makes things more explicit.
 *)
type erased_region = Erased [@@deriving of_yojson]

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
[@@deriving of_yojson]

type ref_kind = Mut | Shared [@@deriving of_yojson]

type assumed_ty = Box [@@deriving of_yojson]

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
  | Assumed of assumed_ty * 'r list * 'r ty
[@@deriving of_yojson]

type rty = RegionVarId.id region ty [@@deriving of_yojson]
(** Type with *R*egions.

    Used in function signatures and type definitions.
 *)

type ety = erased_region ty [@@deriving of_yojson]
(** Type with *E*rased regions.
    
    Used in function bodies, "general" value types, etc.
 *)

type field = { name : string; ty : rty } [@@deriving of_yojson]

type variant = { name : string; fields : field FieldId.vector }
[@@deriving of_yojson]

type type_def_kind =
  | Struct of field FieldId.vector
  | Enum of variant VariantId.vector
[@@deriving of_yojson]

type type_def = {
  def_id : TypeDefId.id;
  name : name;
  region_params : region_var RegionVarId.vector;
  type_params : type_var TypeVarId.vector;
  kind : type_def_kind;
}
[@@deriving of_yojson]
