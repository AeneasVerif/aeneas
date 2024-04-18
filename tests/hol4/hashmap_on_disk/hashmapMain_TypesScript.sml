(** [hashmap_main]: type definitions *)
open primitivesLib divDefLib

val _ = new_theory "hashmapMain_Types"


Datatype:
  (** [hashmap_main::hashmap::List] *)
  hashmap_list_t = | HashmapListCons usize 't hashmap_list_t | HashmapListNil
End

Datatype:
  (** [hashmap_main::hashmap::HashMap] *)
  hashmap_hash_map_t =
  <|
    hashmap_hash_map_num_entries : usize;
    hashmap_hash_map_max_load_factor : (usize # usize);
    hashmap_hash_map_max_load : usize;
    hashmap_hash_map_slots : 't hashmap_list_t vec;
  |>
End

(** The state type used in the state-error monad *)
val _ = new_type ("state", 0)

val _ = export_theory ()
