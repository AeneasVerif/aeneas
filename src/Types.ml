open Identifiers
open Names
open Meta
module TypeVarId = IdGen ()
module TypeDeclId = IdGen ()
module VariantId = IdGen ()
module FieldId = IdGen ()

(** Region variable ids. Used in function signatures. *)
module RegionVarId = IdGen ()

(** Region ids. Used for symbolic executions. *)
module RegionId = IdGen ()

module RegionGroupId = IdGen ()

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
[@@deriving show, ord]

(** The type of erased regions.
    
    We could use unit, but having a dedicated type makes things more explicit.
 *)
type erased_region = Erased [@@deriving show, ord]

(** A group of regions.

    Results from a lifetime analysis: we group the regions with the same
    lifetime together, and compute the hierarchy between the regions.
    This is necessary to introduce the proper abstraction with the
    proper constraints, when evaluating a function call in symbolic mode.
*)
type ('id, 'r) g_region_group = {
  id : 'id;
  regions : 'r list;
  parents : 'id list;
}
[@@deriving show]

type ('r, 'id) g_region_groups = ('r, 'id) g_region_group list [@@deriving show]

type region_var_group = (RegionGroupId.id, RegionVarId.id) g_region_group
[@@deriving show]

type region_var_groups = (RegionGroupId.id, RegionVarId.id) g_region_groups
[@@deriving show]

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
[@@deriving show, ord]

let all_signed_int_types = [ Isize; I8; I16; I32; I64; I128 ]
let all_unsigned_int_types = [ Usize; U8; U16; U32; U64; U128 ]
let all_int_types = List.append all_signed_int_types all_unsigned_int_types

type ref_kind = Mut | Shared [@@deriving show, ord]
type assumed_ty = Box | Vec | Option [@@deriving show, ord]

(** The variant id for [Option::None] *)
let option_none_id = VariantId.of_int 0

(** The variant id for [Option::Some] *)
let option_some_id = VariantId.of_int 1

(** Type identifier for ADTs.

    ADTs are very general in our encoding: they account for "regular" ADTs,
    tuples and also assumed types.
*)
type type_id = AdtId of TypeDeclId.id | Tuple | Assumed of assumed_ty
[@@deriving show, ord]

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
      (** {!Adt} encodes ADTs, tuples and assumed types *)
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
    ord,
    visitors
      {
        name = "iter_ty";
        variety = "iter";
        ancestors = [ "iter_ty_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
        polymorphic = false;
      },
    visitors
      {
        name = "map_ty";
        variety = "map";
        ancestors = [ "map_ty_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
        polymorphic = false;
      }]
(* TODO: group Bool, Char, etc. in Constant *)

(** Generic type with regions *)
type 'r gr_ty = 'r region ty [@@deriving show, ord]

(** *S*ignature types.

    Used in function signatures and type definitions.
 *)
type sty = RegionVarId.id gr_ty [@@deriving show, ord]

(** Type with *R*egions.

    Used to project borrows/loans inside of abstractions, during symbolic
    execution.
 *)
type rty = RegionId.id gr_ty [@@deriving show, ord]

(** Type with *E*rased regions.
    
    Used in function bodies, "regular" value types, etc.
 *)
type ety = erased_region ty [@@deriving show, ord]

type field = { meta : meta; field_name : string option; field_ty : sty }
[@@deriving show]

type variant = { meta : meta; variant_name : string; fields : field list }
[@@deriving show]

type type_decl_kind =
  | Struct of field list
  | Enum of variant list
  | Opaque
      (** An opaque type: either a local type marked as opaque, or an external type *)
[@@deriving show]

type type_decl = {
  def_id : TypeDeclId.id;
  meta : meta;
  name : type_name;
  region_params : region_var list;
  type_params : type_var list;
  kind : type_decl_kind;
  regions_hierarchy : region_var_groups;
      (** Stores the hierarchy between the regions (which regions have the
          same lifetime, which lifetime should end before which other lifetime,
          etc.) *)
}
[@@deriving show]
