(** Properties about the hashmap written on disk *)
module HashmapMain.Properties
open Primitives
open HashmapMain.Funs

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

/// Below, we focus on the functions to read from disk/write to disk to showcase
/// how such reasoning which mixes opaque functions together with a state-error
/// monad can be performed.

(*** Hypotheses *)

/// [state_v] gives us the hash map currently stored on disk
assume
val state_v : state -> hashmap_HashMap_t u64

/// [serialize] updates the hash map stored on disk
assume
val serialize_lem (hm : hashmap_HashMap_t u64) (st : state) : Lemma (
  match hashmap_utils_serialize hm st with
  | Fail _ -> True
  | Return (st', ()) -> state_v st' == hm)
  [SMTPat (hashmap_utils_serialize hm st)]

/// [deserialize] gives us the hash map stored on disk, without updating it
assume
val deserialize_lem (st : state) : Lemma (
  match hashmap_utils_deserialize st with
  | Fail _ -> True
  | Return (st', hm) -> hm == state_v st /\ st' == st)
  [SMTPat (hashmap_utils_deserialize st)]

(*** Lemmas *)

/// The obvious lemma about [insert_on_disk]: the updated hash map stored on disk
/// is exactly the hash map produced from inserting the binding ([key], [value])
/// in the hash map previously stored on disk.
val insert_on_disk_lem (key : usize) (value : u64) (st : state) : Lemma (
  match insert_on_disk key value st with
  | Fail _ -> True
  | Return (st', ()) ->
    let hm = state_v st in
    match hashmap_HashMap_insert u64 hm key value with
    | Fail _ -> False
    | Return hm' -> hm' == state_v st')

let insert_on_disk_lem key value st = ()
