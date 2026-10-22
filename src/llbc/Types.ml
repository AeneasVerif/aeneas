include Charon.Types

type integer_value = Charon.Values.integer_value [@@deriving show, ord]
type region_id_set = RegionId.Set.t [@@deriving show, eq, ord]

module RegionSet = Charon.TypesUtils.RegionSet

(** A set of regions.

    Contrary to {!region_id_set}, this set may contain the static region. We use
    it in particular for the regions owned by the region abstractions. *)
type region_set = RegionSet.t [@@deriving show, eq, ord]

(** Print a region (for debugging purposes) *)
let region_to_short_string (r : region) : string =
  match r with
  | RStatic -> "'static"
  | RVar (Free rid) -> RegionId.to_string rid
  | _ -> show_region r

(** Print a set of regions (for debugging purposes) *)
let region_set_to_string (rset : region_set) : string =
  "{ "
  ^ String.concat ", "
      (List.map region_to_short_string (RegionSet.elements rset))
  ^ " }"

(** A normalized projection type.

    A type where regions are either:
    - the free region of id 0 (the regions we want to keep during a projection)
    - erased (the regions we want to discard during a projection)

    Note that using this type (rather than, e.g., [ty]) only has an informative
    purpose. *)
type norm_proj_ty = ty [@@deriving show, eq, ord]

(** A group of regions, used to compute the hierarchy between the regions of a
    function signature. *)
type region_group = (region, RegionGroupId.id) g_region_group [@@deriving show]

type region_groups = region_group list [@@deriving show]
