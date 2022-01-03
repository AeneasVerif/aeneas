open Identifiers

module TypeVarId = IdGen ()

module TypeDefId = IdGen ()

module VariantId = IdGen ()

module FieldId = IdGen ()

module RegionVarId = IdGen ()
(** Region variable ids. Used in function signatures. *)

module RegionId = IdGen ()
(** Region ids. Used for symbolic executions. *)

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

(** Type identifier for ADTs.

    ADTs are very general in our encoding: they account for "regular" ADTs,
    tuples and also assumed types.
*)
type type_id = AdtId of TypeDefId.id | Tuple | Assumed of assumed_ty
[@@deriving show]

(** Ancestor for iter visitor for [ty] *)
class ['self] iter_ty_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.iter

    method visit_'r : 'env -> 'r -> unit = fun _ _ -> ()

    method visit_id : 'env -> TypeVarId.id -> unit = fun _ _ -> ()

    method visit_type_id : 'env -> type_id -> unit = fun _ _ -> ()

    method visit_integer_type : 'env -> integer_type -> unit = fun _ _ -> ()

    method visit_ref_kind : 'env -> ref_kind -> unit = fun _ _ -> ()
  end

(** Ancestor for map visitor for [ty] *)
class ['self] map_ty_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.map

    method visit_'r : 'env -> 'r -> 'r = fun _ r -> r

    method visit_id : 'env -> TypeVarId.id -> TypeVarId.id = fun _ id -> id

    method visit_type_id : 'env -> type_id -> type_id = fun _ id -> id

    method visit_integer_type : 'env -> integer_type -> integer_type =
      fun _ ity -> ity

    method visit_ref_kind : 'env -> ref_kind -> ref_kind = fun _ rk -> rk
  end

type 'r ty =
  | Adt of type_id * 'r list * 'r ty list
      (** [Adt] encodes ADTs, tuples and assumed types *)
  | TypeVar of TypeVarId.id
  | Bool
  | Char
  | Never
  | Integer of integer_type
  | Str
  | Array of 'r ty (* TODO: there should be a constant with the array *)
  | Slice of 'r ty
  | Ref of 'r * 'r ty * ref_kind
[@@deriving
  show,
    visitors
      {
        name = "iter_ty";
        variety = "iter";
        ancestors = [ "iter_ty_base" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
        polymorphic = false;
      },
    visitors
      {
        name = "map_ty";
        variety = "map";
        ancestors = [ "map_ty_base" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
        polymorphic = false;
      }]
(* TODO: group Bool, Char, etc. in Constant *)

type sty = RegionVarId.id region ty [@@deriving show]
(** *S*ignature types.

    Used in function signatures and type definitions.
 *)

type rty = RegionId.id region ty [@@deriving show]
(** Type with *R*egions.

    Used during symbolic execution.
 *)

type ety = erased_region ty [@@deriving show]
(** Type with *E*rased regions.
    
    Used in function bodies, "general" value types, etc.
 *)

type field = { field_name : string; field_ty : sty } [@@deriving show]

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
