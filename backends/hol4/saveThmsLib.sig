signature saveThmsLib =
sig
(* This library provides utilities to persistently store maps from terms to theorems.

   The issue is that theory files (i.e., Script.sml files) have no effects: it is
   not possible to update the content of a reference in a Script.sml file and see
   the effect of this change elsewhere. This is a problem because several tactics
   and utilities require to maintain data bases of theorems in which we perform
   lookups, and we generally add those theorems to the data bases right after we
   proved them.

   This file provides utilities to set up and maintain such a collection. An
   important point is that we need to be able to derive, from a theorem, a
   "term" that will be used as a key. We remember with a reference whether
   the map from "terms" to theorems has been initialized: if not, we initialize
   it before we perform any operation such as lookup or insert.
 *)

  include Abbrev

  (* Helper *)
  type thname = KernelSig.kernelname
  val lookup_thm : string -> thname * thm

  (* The user-provided functions *)
  type 'key key_fns = {
    compare : 'key * 'key -> order,
    (* Retrieve the key from the theorem and normalize it at the same time *)
    get_key_normalize_thm : thm -> ('key * thm)
  }

  (* The functions we return to the user to manipulate the map *)
  type 'key map_fns = {
    (* Persistently save a theorem *)
    save_thm : string -> unit,
    (* Persistently delete a theorem *)
    delete_thm : string -> unit,
    (* Temporarily save a theorem *)
    temp_save_thm : thm -> unit,
    (* Temporarily delete a theorem *)
    temp_delete_thm : thm -> unit,
    (* Get the key set *)
    get_keys : unit -> 'key Redblackset.set,
    (* Get the theorems map *)
    get_map : unit -> ('key, thm) Redblackmap.dict
  }

  (* Initialize a persistent map *)
  val create_map : 'key key_fns -> string -> 'key map_fns

end
