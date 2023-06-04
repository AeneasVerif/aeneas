structure saveThmsLib :> saveThmsLib =
struct

open HolKernel Abbrev

type thname = KernelSig.kernelname

(* The user-provided functions *)
type 'key key_fns = {
  compare : 'key * 'key -> order,
  get_key_from_thm : thm -> 'key
}

(* The functions we return to the user to manipulate the map *)
type 'key map_fns = {
  (* Persistently save a theorem *)
  save_thm : string -> unit,
  (* Temporarily save a theorem *)
  temp_save_thm : thm -> unit,
  (* Get the key set *)
  get_keys : unit -> 'key Redblackset.set,
  (* Get the theorems map *)
  get_map : unit -> ('key, thm) Redblackmap.dict
}

(* This function is adapted from ThmSetData.sml.

   It raises an exception if it can't find a theorem.
 *)
fun lookup_thm (s : string) : thname * thm =
  let
    val name =
     case String.fields (equal #".") s of
         [s0] => {Thy = current_theory(), Name = s}
       | [s1,s2] => {Thy = s1, Name = s2}
       | _ => raise mk_HOL_ERR "saveThmsLib" "lookup_thm" ("Malformed name: " ^ s)
    fun lookup_exn {Thy,Name} = DB.fetch Thy Name
  in
    (name, lookup_exn name)
  end

(* The state, a pair (set of keys, map from keys to theorems) *)
type 'key state = 'key Redblackset.set * ('key, thm) Redblackmap.dict

(* Initialize a persistent map *)
fun create_map (kf : 'key key_fns) (name : string) : 'key map_fns =
  let
     val { compare, get_key_from_thm } = kf
     
     (* Small helper *)
     fun add_to_state (th : thm) (s, m) =
       let
         val k = get_key_from_thm th
         val s = Redblackset.add (s, k)
         val m = Redblackmap.insert (m, k, th)
       in
         (s, m)
       end
  
     (* Persistently update the map given a delta  *)
     fun apply_delta (delta : ThmSetData.setdelta) st =
       case delta of
         ThmSetData.ADD (_, th) => add_to_state th st
       | ThmSetData.REMOVE _ =>
         raise mk_HOL_ERR "saveThmsLib" "create_map" ("Unexpected REMOVE")

     (* Initialize the dictionary *)
     val init_state = (Redblackset.empty compare, Redblackmap.mkDict compare)
     val {update_global_value, (* Local update *)
          record_delta, (* Global update *)
          get_deltas,
          get_global_value,
          DB = eval_ruleuction_map_by_theory,...} =
         ThmSetData.export_with_ancestry {
           settype = name,
           delta_ops = {apply_to_global = apply_delta,
                        uptodate_delta = K true,
                        thy_finaliser = NONE,
                        initial_value = init_state,
                        apply_delta = apply_delta}
         }

     (* Temporarily save a theorem: update the current session, but don't
        save the delta for the future sessions. *)
     fun temp_save_thm (th : thm) : unit =
       update_global_value (add_to_state th)

     (* Persistently save a theorem *)
     fun save_thm (s : string) : unit =
       let
         val th = lookup_thm s
       in
         (* Record delta saves a delta for the future sessions, but doesn't
            update the current sessions, which is why we also call [temp_save_thm] *)
           record_delta (ThmSetData.ADD th);
           temp_save_thm (snd th)
       end

     (* *)
     val get_keys = fst o get_global_value
     val get_map = snd o get_global_value
  in
    { save_thm = save_thm, temp_save_thm = temp_save_thm,
      get_keys = get_keys, get_map = get_map }
  end

end
