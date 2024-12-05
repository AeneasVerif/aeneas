include Charon.Types
module RegionId = FreeRegionId

type bound_region_id = BoundRegionId.id [@@deriving show, ord]
type region_id = RegionId.id [@@deriving show, ord]
type region_id_set = RegionId.Set.t [@@deriving show, ord]
