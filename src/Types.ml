open Identifiers

module TypeVarId = IdGen ()

module TypeDefId = IdGen ()

module VariantId = IdGen ()

module FieldId = IdGen ()

module RegionVarId = IdGen ()

type type_var = {
  tv_index : TypeVarId.id;
      (** Unique index identifying the variable - TODO: may be redundant with
          using indexed vectors *)
  tv_name : string;  (** Variable name *)
}
[@@deriving show]

type region_var = {
  rv_index : RegionVarId.id;
      (** Unique index identifying the region - TODO: may be redundant *)
  rv_name : string option;  (** Region name *)
}
[@@deriving show]

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

(** Convert an [rty] to an [ety] by erasing the region variables
    
    TODO: this can be done through a substitution
*)
let rec erase_regions (ty : rty) : ety =
  match ty with
  | Adt (def_id, regions, tys) ->
      let regions = List.map (fun _ -> Erased) regions in
      let tys = List.map erase_regions tys in
      Adt (def_id, regions, tys)
  | Tuple tys -> Tuple (List.map erase_regions tys)
  | TypeVar vid -> TypeVar vid
  | Bool -> Bool
  | Char -> Char
  | Never -> Never
  | Integer int_ty -> Integer int_ty
  | Str -> Str
  | Array ty -> Array (erase_regions ty)
  | Slice ty -> Slice (erase_regions ty)
  | Ref (_, ty, ref_kind) -> Ref (Erased, erase_regions ty, ref_kind)
  | Assumed (aty, regions, tys) ->
      let regions = List.map (fun _ -> Erased) regions in
      let tys = List.map erase_regions tys in
      Assumed (aty, regions, tys)

(** Retrieve the list of fields for the given variant of a [type_def].

    Raises [Invalid_argument] if the arguments are incorrect.
 *)
let type_def_get_fields (def : type_def) (opt_variant_id : VariantId.id option)
    : field list =
  match (def.kind, opt_variant_id) with
  | Enum variants, Some variant_id -> (VariantId.nth variants variant_id).fields
  | Struct fields, None -> fields
  | _ ->
      raise
        (Invalid_argument
           "The variant id should be [Some] if and only if the definition is \
            an enumeration")

(** Return [true] if a [ty] is actually `unit` *)
let ty_is_unit (ty : 'r ty) : bool =
  match ty with Tuple tys -> List.length tys = 0 | _ -> false
