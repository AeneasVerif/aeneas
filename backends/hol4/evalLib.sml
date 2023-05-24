structure evalLib =
struct

open simpLib computeLib
open primitivesBaseTacLib

(* Lexicographic order over pairs  - TODO: this duplicates primitivesBaseTacLib *)
fun pair_compare (comp1 : 'a * 'a -> order) (comp2 : 'b * 'b -> order)
  ((p1, p2) : (('a * 'b) * ('a * 'b))) : order =
  let
    val (x1, y1) = p1;
    val (x2, y2) = p2;
  in
    case comp1 (x1, x2) of
      LESS => LESS
    | GREATER => GREATER
    | EQUAL => comp2 (y1, y2)
  end

(* A constant name (theory, constant name) - TODO: this duplicates primitivesBaseTacLib *)
type const_name = string * string
val const_name_compare = pair_compare String.compare String.compare
fun get_const_name (tm : term) : const_name =
  let
    val {Thy=thy, Name=name, Ty=_} = dest_thy_const tm
  in
    (thy, name)
  end

(* Create the persistent collection of rewrite theorems - TODO: more efficient
   collection than a list? *)
val (add_rewrite_thm, get_rewrite_thms) =
  let
    (* Small helper *)
    fun add_to_state (th : thm) s = th :: s

    (* Persistently update the maps given a delta  *)
    fun apply_delta (delta : ThmSetData.setdelta) st =
      case delta of
        ThmSetData.ADD (_, th) => add_to_state th st
      | ThmSetData.REMOVE _ =>
        raise mk_HOL_ERR "evalLib" "apply_delta" ("Unexpected REMOVE")

    (* Initialize the collection *)
    val init_state = []
    val {update_global_value, (* Local update *)
         record_delta, (* Global update *)
         get_global_value = get_rewrite_thms,
         ...} =
        ThmSetData.export_with_ancestry {
          settype = "evalLib_rewrite_theorems",
          delta_ops = {apply_to_global = apply_delta,
                       uptodate_delta = K true,
                       thy_finaliser = NONE,
                       initial_value = init_state,
                       apply_delta = apply_delta}
        }

    fun add_rewrite_thm (s : string) : unit =
      let
        val th = saveThmsLib.lookup_thm s
      in
        (* Record the delta - for persistence for the future sessions *)
        record_delta (ThmSetData.ADD th);
        (* Update the global value - for the current session: record_delta
           doesn't update the state of the current session *)
        update_global_value (add_to_state (snd th))
      end
  in
    (add_rewrite_thm, get_rewrite_thms)
  end

fun add_rewrite_thms (ls : string list) : unit =
  app add_rewrite_thm ls


(* Create the persistent collection of unfolding theorems, which is a pair:
   (set of constants, map from constant name to theorem)
 *)
type unfold_state = term Redblackset.set * (const_name, thm) Redblackmap.dict
fun get_custom_unfold_const (th : thm) : term = (fst o strip_comb o lhs o snd o strip_forall o concl) th

val (add_unfold_thm, get_unfold_thms_map) =
  let
    (* Small helper *)
    fun add_to_state (th : thm) (s, m) =
      let
        val k = get_custom_unfold_const th
        val name = get_const_name k
        val s = Redblackset.add (s, k)
        val m = Redblackmap.insert (m, name, th)
      in
        (s, m)
      end

    (* Persistently update the maps given a delta  *)
    fun apply_delta (delta : ThmSetData.setdelta) st =
      case delta of
        ThmSetData.ADD (_, th) => add_to_state th st
      | ThmSetData.REMOVE _ =>
        raise mk_HOL_ERR "evalLib" "apply_delta" ("Unexpected REMOVE")

    (* Initialize the collection *)
    val init_state = (Redblackset.empty compare, Redblackmap.mkDict const_name_compare)
    val {update_global_value, (* Local update *)
         record_delta, (* Global update *)
         get_global_value = get_unfold_thms_map,
         ...} =
        ThmSetData.export_with_ancestry {
          settype = "evalLib_unfold_theorems",
          delta_ops = {apply_to_global = apply_delta,
                       uptodate_delta = K true,
                       thy_finaliser = NONE,
                       initial_value = init_state,
                       apply_delta = apply_delta}
        }

    fun add_unfold_thm (s : string) : unit =
      let
        val th = saveThmsLib.lookup_thm s
      in
        (* Record the delta - for persistence for the future sessions *)
        record_delta (ThmSetData.ADD th);
        (* Update the global value - for the current session: record_delta
           doesn't update the state of the current session *)
        update_global_value (add_to_state (snd th))
      end
  in
    (add_unfold_thm, get_unfold_thms_map)
  end

fun add_unfold_thms (ls : string list) : unit =
  app add_unfold_thm ls

fun get_unfold_thms () : thm list =
  map snd (Redblackmap.listItems (snd (get_unfold_thms_map ())))

(* Apply a custom unfolding to the term, if possible.

   This conversion never fails nor raises exceptions.
 *)
fun apply_custom_unfold (tm : term) : thm =
  let
    (* Retrieve the custom unfoldings *)
    val custom_unfolds = snd (get_unfold_thms_map ())

    (* Remove all the matches to find the top-most scrutinee *)
    val scrut = strip_all_cases_get_scrutinee tm
    (* Find an unfolding to apply: we look at the application itself, then
       all its arguments, then unfold it.
       TODO: maybe do something more systematic, like CBV

       This function returns a theorem or raises an HOL_ERR
     *)
    fun find_unfolding (tm : term) : thm =
      (* Try to find an unfolding on the current term *)
      let
        (* Deconstruct the constant and attempt to lookup an unfolding
           theorem *)
        val c = (fst o strip_comb) tm
        val cname = get_const_name c
        val unfold_th = Redblackmap.find (custom_unfolds, cname)
          handle Redblackmap.NotFound => failwith "No theorem found"
        (* Instantiate the theorem *)
        val unfold_th = SPEC_ALL unfold_th
        val th_tm = (lhs o concl) unfold_th
        val (subst, inst) = match_term th_tm tm
        val unfold_th = INST subst (INST_TYPE inst unfold_th)
      in
        unfold_th
      end
      handle HOL_ERR _ =>
        (* Can't unfold the current term: decompose it and explore the subterms *)
        if is_comb tm then
          let
            val tm = strip_all_cases_get_scrutinee tm
            val (app, args) = strip_comb tm
            val tml = List.rev (app :: args)
          in
            find_unfolding_in_list tml
          end
        else failwith "Found no constant on which to apply an unfolding"
    and find_unfolding_in_list (ls : term list) : thm =
      case ls of
        [] => failwith "Found no constant on which to apply an unfolding"
      | tm :: tl =>
        (* Explore the argument, if it fails explore the application *)
          find_unfolding tm
          handle HOL_ERR _ => find_unfolding_in_list tl
    val unfold_th = find_unfolding scrut
  in
    (* Apply the theorem - for security, we apply it only once.
       TODO: we might want to be more precise and apply it exactly where
       we need to.
     *)
    PURE_ONCE_REWRITE_CONV [unfold_th] tm
  end
  handle HOL_ERR _ => REFL tm

fun eval_conv tm =
  let
    (* TODO: optimize: we recompute the list each time... *)
    val restr_tms = Redblackset.listItems (fst (get_unfold_thms_map ()))
    (* We do the following:
       - use the standard EVAL conv, but restrains it from unfolding terms for
         which we have custom unfolding theorems
       - apply custom unfoldings
       - simplify
     *)
    val standard_eval = RESTR_EVAL_CONV restr_tms
    val simp_no_fail_conv = (fn x => SIMP_CONV (srw_ss ()) (get_rewrite_thms ()) x handle UNCHANGED => REFL x)
    val one_step_conv = standard_eval THENC (apply_custom_unfold THENC simp_no_fail_conv)
    (* Wrap the conversion such that it fails if the term is unchanged *)
    fun one_step_changed_conv tm = (CHANGED_CONV one_step_conv) tm
  in
    (* Repeat *)
    REPEATC one_step_changed_conv tm
  end
  handle UNCHANGED => REFL tm

fun eval tm = (rhs o concl) (eval_conv tm)

end
