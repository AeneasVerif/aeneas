include Charon.Types

type region_id_set = RegionId.Set.t [@@deriving show, ord]

(** A normalized projection type.

    A type where regions are either:
    - the free region of id 0 (the regions we want to keep during a projection)
    - erased (the regions we want to discard during a projection)

    Note that using this type (rather than, e.g., [ty]) only has an informative
    purpose. *)
type norm_proj_ty = ty [@@deriving show, ord]
