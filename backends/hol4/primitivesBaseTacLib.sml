(* Base tactics for the primitives library *)
structure primitivesBaseTacLib =
struct

open HolKernel boolLib bossLib intLib

val debug = ref false

fun print_dbg msg = if !debug then print msg else ()

(* Remark: below, we also have conversions *)
val gsym = GSYM

(* Ignore a theorem.

   To be used in conjunction with {!pop_assum} for instance.
 *)
fun ignore_tac (_ : thm) : tactic = ALL_TAC

(* REMARK: the last github version of HOL4 defines some functions which are
   absent from the last **release** version (which is older). We redefine some of
   them here for convenience.

   IMPORTANT: in practice, we use the last *release* version of HOL4 (i.e., not
   the last *development* version) to make sure that building the Nix flake
   succeeds (there *are* discrepancies of behavior).
 *)
val pop_last_assum = last_x_assum
val qexists = qexists_tac
(* END OF REMARK *)

val pop_ignore_tac = pop_assum ignore_tac

(* TODO: no exfalso tactic?? *)
val exfalso : tactic =
  SUBGOAL_THEN “F” (fn th => ASSUME_TAC th >> fs[])

val case_tac = CASE_TAC
val top_case_tac = BasicProvers.TOP_CASE_TAC
val try_tac = TRY
val first_tac = FIRST
val map_first_tac = MAP_FIRST
val fail_tac = FAIL_TAC
val map_every_tac = MAP_EVERY

(* TODO: rename assume to asm *)
fun qspec_assume x th = qspec_then x assume_tac th
fun qspecl_assume xl th = qspecl_then xl assume_tac th
fun first_qspec_assume x = first_assum (qspec_assume x)
fun first_qspecl_assume xl = first_assum (qspecl_assume xl)

val all_tac = all_tac
val pure_rewrite_tac = PURE_REWRITE_TAC
val pure_asm_rewrite_tac = PURE_ASM_REWRITE_TAC
val pure_once_rewrite_tac = PURE_ONCE_REWRITE_TAC

val pat_undisch_tac = Q.PAT_UNDISCH_TAC

val equiv_is_imp = prove (“∀x y. ((x ⇒ y) ∧ (y ⇒ x)) ⇒ (x ⇔ y)”, metis_tac [])
val equiv_tac = irule equiv_is_imp >> conj_tac

(* Rewrite the goal once, and on the left part of the goal seen as an application *)
fun pure_once_rewrite_left_tac ths =
  CONV_TAC (PATH_CONV "l" (PURE_ONCE_REWRITE_CONV ths))

(* Dependent rewrites *)
val dep_pure_once_rewrite_tac = dep_rewrite.DEP_PURE_ONCE_REWRITE_TAC
val dep_pure_rewrite_tac = dep_rewrite.DEP_PURE_REWRITE_TAC

(* Add a list of theorems in the assumptions *)
fun assume_tacl (thms : thm list) : tactic =
  let
    (* TODO: use MAP_EVERY *)
    fun t thms =
      case thms of
        [] => all_tac
      | thm :: thms => assume_tac thm >> t thms
  in
  t thms
  end

(* Given a theorem of the shape:
   {[
     A0, ..., An ⊢ B0 ==> ... ==> Bm ==> concl
   ]}

   Rewrite it so that it has the shape:
   {[
     ⊢ (A0 /\ ... /\ An /\ B0 /\ ... /\ Bm) ==> concl
   ]}
 *)
fun thm_to_conj_implies (thm : thm) : thm =
  let
    (* Discharge all the assumptions *)
    val thm = DISCH_ALL thm;
    (* Rewrite the implications as one conjunction *)
    val thm = PURE_REWRITE_RULE [GSYM satTheory.AND_IMP] thm;
  in thm end

(* Like THEN1 and >-, but doesn't fail if the first subgoal is not completely
   solved.

   TODO: how to get the notation right?
 *)
fun op partial_then1 (tac1: tactic) (tac2: tactic) : tactic = tac1 THEN_LT (NTH_GOAL tac2 1)

(* If the current goal is [asms ⊢ g], and given a lemma of the form
   [⊢ H ==> C], do the following:
   - introduce [asms ⊢ H] as a subgoal and apply the given tactic on it
   - also calls the theorem tactic with the theorem [asms ⊢ C]

   If the lemma is not an implication, we directly call the theorem tactic.
 *)
fun sg_premise_then (premise_tac: tactic) (then_tac: thm_tactic) (thm : thm)  : tactic =
  let
    val c = concl thm;
    (* First case: there is a premise to prove *)
    fun prove_premise_then (h : term) =
      partial_then1 (SUBGOAL_THEN h (fn h_thm => then_tac (MP thm h_thm))) premise_tac;
    (* Second case: no premise to prove *)
    val no_prove_premise_then = then_tac thm;
  in
    if is_imp c then prove_premise_then (fst (dest_imp c)) else no_prove_premise_then
  end

(* Add the first premise of the theorem as subgoal, and add the theorem without its
   first premise as an assumption.

   For instance, if we have the goal:
     asls
     ====
      c
   and the theorem: ⊢ H ==> G

   We generate:
   asls     asls
   ====     G
     H      ====
            C

*)
val sg_premise_tac = sg_premise_then all_tac assume_tac

(* Same as {!sg_premise_then} but fails if the premise_tac fails to prove the premise *)
fun prove_premise_then (premise_tac: tactic) (then_tac: thm_tactic) (thm : thm)  : tactic =
  sg_premise_then
    (premise_tac >> FAIL_TAC "prove_premise_then: could not prove premise")
    then_tac thm

(*
val thm = th
*)

(* Call a function on all the subterms of a term *)
fun dep_apply_in_subterms
  (f : string Redblackset.set -> term -> unit)
  (bound_vars : string Redblackset.set)
  (t : term) : unit =
  let
    val dep = dep_apply_in_subterms f;
    val _ = f bound_vars t;
  in
  case dest_term t of
    VAR (name, ty) => ()
  | CONST {Name=name, Thy=thy, Ty=ty} => ()
  | COMB (app, arg) =>
    let
      val _ = dep bound_vars app;
      val _ = dep bound_vars arg;
    in () end
  | LAMB (bvar, body) =>
    let
      val (varname, ty) = dest_var bvar;
      val bound_vars = Redblackset.add (bound_vars, varname);
      val _ = dep bound_vars body;
    in () end
  end

(* Return the set of free variables appearing in the residues of a term substitution *)
fun free_vars_in_subst_residue (s: (term, term) Term.subst) : string Redblackset.set =
  let
    val free_vars = free_varsl (map (fn {redex=_, residue=x} => x) s);
    val free_vars = map (fst o dest_var) free_vars;
    val free_vars = Redblackset.fromList String.compare free_vars;
  in free_vars end

(* Attempt to instantiate a rewrite theorem.

   Remark: this theorem should be of the form:
   H ⊢ x = y

   (without quantified variables).

   **REMARK**: the function raises a HOL_ERR exception if it fails.

   [forbid_vars]: forbid substituting with those vars (typically because
   we are maching in a subterm under lambdas, and some of those variables
   are bounds in the outer lambdas).
*)
fun inst_match_concl (forbid_vars : string Redblackset.set) (th : thm) (t : term) : thm =
  let
    (* Retrieve the lhs of the conclusion of the theorem *)
    val l = lhs (concl th);
    (* Match this lhs with the term *)
    val (var_s, ty_s) = match_term l t;
    (* Check that we are allowed to perform the substitution *)
    val free_vars = free_vars_in_subst_residue var_s;
    val _ = assert Redblackset.isEmpty (Redblackset.intersection (free_vars, forbid_vars));
  in
    (* Perform the substitution *)
    INST var_s (INST_TYPE ty_s th)
  end

(*
val forbid_vars = Redblackset.empty String.compare
val t = “u32_to_int (int_to_u32 x)”
val t = “u32_to_int (int_to_u32 3)”
val th = (UNDISCH_ALL o SPEC_ALL) int_to_u32_id
*)

(* Attempt to instantiate a theorem by matching its first premise.

   Note that we make the hypothesis tha all the free variables which need
   to be instantiated appear in the first premise, of course (the caller should
   enforce this).

   Remark: this theorem should be of the form:
   ⊢ H0 ==> ... ==> Hn ==> H

   (without quantified variables).

   **REMARK**: the function raises a HOL_ERR exception if it fails.

   [forbid_vars]: see [inst_match_concl]
*)
fun inst_match_first_premise
  (forbid_vars : string Redblackset.set) (th : thm) (t : term) : thm =
  let
    (* Retrieve the first premise *)
    val l = (fst o dest_imp o concl) th;
    (* Match this with the term *)
    val (var_s, ty_s) = match_term l t;
    (* Check that we are allowed to perform the substitution *)
    val free_vars = free_vars_in_subst_residue var_s;
    val _ = assert Redblackset.isEmpty (Redblackset.intersection (free_vars, forbid_vars));
  in
    (* Perform the substitution *)
    INST var_s (INST_TYPE ty_s th)
  end

(*
val forbid_vars = Redblackset.empty String.compare
val t = “u32_to_int z = u32_to_int i − 1”
val th = SPEC_ALL NUM_SUB_1_EQ
*)

(* Call a matching function on all the subterms in the provided list of term.
   This is a generic function.

   [try_match] should return a list of instantiated theorems, as well as terms which
   identify those theorem (the lhs of the equality, if this is a rewriting
   theorem for instance - we use this to check for collisions, and discard
   redundant instantiations).
   It takes as input the set of bound variables (it should not perform
   substitutions with variables belonging to this set).
 *)
fun inst_match_in_terms
  (try_match: string Redblackset.set -> term -> (term * thm) list)
  (tml : term list) : thm list =
  let
    (* We use a map when storing the theorems, to avoid storing the same theorem twice *)
    val inst_thms: (term, thm) Redblackmap.dict ref = ref (Redblackmap.mkDict Term.compare);
    fun try_instantiate bvars t =
      let
        val matched_thms = try_match bvars t;
        fun insert_th (inst_th_tm, inst_th) =
          inst_thms := Redblackmap.insert (!inst_thms, inst_th_tm, inst_th)
      in
        List.app insert_th matched_thms
      end
    (* Explore the term *)
    val _ = List.app (dep_apply_in_subterms try_instantiate (Redblackset.empty String.compare)) tml;
  in
    map snd (Redblackmap.listItems (!inst_thms))
  end

(* Given a net of rewriting theorems [ths] which have premises, return all the
   instantiations of those theorems which make its conclusion match subterms
   in the provided list of term.

   [keep]: if this function returns false on an instantiated theorem, ignore
   the theorem.

   The theorems in the Net should be of the shape:
   {[
     H0, ..., Hn ⊢ x = y
   ]}
   (no implications, no quantified variables)
   For the above theorem, the key term used in the net should be ‘x’.
 *)
fun inst_match_concl_in_terms (keep : thm -> bool) (ths : thm Net.net) (tml : term list) : thm list =
  let
    (* First, find potential matches in the net *)
    fun find_thms (t : term) : thm list = Net.match t ths
    (* Then, match more precisely for every theorem found *)
    fun try_match (bvars : string Redblackset.set) t th =
      let
        val _ = print_dbg ("inst_match_concl_in_terms:\n- thm: " ^ thm_to_string th ^
                           "\n- term: " ^ term_to_string t ^ "\n")
        val inst_th = inst_match_concl bvars th t
        val c = concl inst_th
        val _ = print_dbg ("inst_match_concl_in_terms: matched with success\n")
      in
        (* Check that we mustn't ignore the theorem *)
        if keep inst_th then
          let val _ = print_dbg "inst_match_concl_in_terms: keeping theorem\n\n" in
          (* There are several possibilities:
             - initially, we only kept the lhs of the conclusion (with premises)
               of the theorem
             - now, we keep the whole theorem
             The reason is that it happens that we can prove the premise of some
             instantiation but not on another instantiation, even though the
             conclusion is the same: in that case we want to keep both.
             For instance:
             
           *)
          (concl (DISCH_ALL inst_th), inst_th) end
        else
          let val _ = print_dbg ("inst_match_concl_in_terms: ignore theorem\n\n") in
          failwith "inst_match_concl_in_terms: ignore theorem" end
      end
    (* Compose *)
    fun try_match_on_thms bvars t =
      let
        val matched_thms = find_thms t
      in
        mapfilter (try_match bvars t) matched_thms
      end
    (* *)
    val thms = inst_match_in_terms try_match_on_thms tml
    (* Debug *)
    val _ =
      if !debug then
        let
          val thms_s = String.concatWith "\n" (map thm_to_string thms)
        in
          print ("inst_match_concl_in_terms: instantiated theorems:\n" ^ thms_s ^ "\n\n")
        end
      else ()
  in
    thms
  end

(*
val t = “!x. u32_to_int (int_to_u32 x) = u32_to_int (int_to_u32 y)”
val th = u32_to_int_int_to_u32
val th = (UNDISCH_ALL o SPEC_ALL) th
val ths = Net.insert ((lhs o concl) th, th) Net.empty
val keep = fn _ => true

val thms = inst_match_concl_in_terms keep ths [t]
*)


(* Given a net of theorems which have premises, return all the
   instantiations of those theorems which make their first premise match subterms
   in the provided list of term.

   The theorems in the Net should be of the shape:
   {[
     ⊢ H0 => ... => Hn => H
   ]}
   (no quantified variables)
   For the above theorem, the matching term used in the net should be ‘H0’.
 *)
fun inst_match_first_premise_in_terms
  (keep : thm -> bool) (ths : thm Net.net) (tml : term list) : thm list =
  let
    (* First, find potential matches in the net *)
    fun find_thms (t : term) : thm list = Net.match t ths
    (* Then, match more precisely for every theorem found *)
    fun try_match bvars t th =
      let
        val inst_th = inst_match_first_premise bvars th t;
      in
        if keep inst_th then  ((fst o dest_imp o concl) inst_th, inst_th)
        else failwith "inst_match_first_premise_in_terms: ignore theorem"
      end
    (* Compose *)
    fun try_match_on_thms bvars t =
      let
        val matched_thms = find_thms t
      in
        mapfilter (try_match bvars t) matched_thms
      end
  in
    inst_match_in_terms try_match_on_thms tml
  end

(*
val t = “n : int = m - 1 ==> T”
val th = prove (“x: int = y - 1 ==> x + 1 = y”, COOPER_TAC)
val th = SPEC_ALL th
val ths = Net.insert ((fst o dest_imp o concl) th, th) Net.empty
val keep = fn _ => true

val thms = inst_match_first_premise_in_terms keep ths [t]
*)


(* Attempt to apply dependent rewrites with a theorem by matching its
   conclusion with subterms in the given list of terms.

   Leaves the premises as subgoals if [prove_premise] doesn't prove them.

   The theorems in the Net should be of the shape:
   {[
     H0, ..., Hn ⊢ x = y
   ]}
   (no implications, no quantified variables)
   For the above theorem, the key term used in the net should be ‘x’.
 *)
fun apply_dep_rewrites_match_concl_with_terms_tac
  (prove_premise : tactic) (then_tac : thm_tactic)
  (ignore_tml : term list)
  (tml : term list) (ths : thm Net.net) : tactic =
  let
    val ignore = Redblackset.fromList Term.compare ignore_tml
    fun keep th = not (Redblackset.member (ignore, concl th))
    (* Discharge the assumptions so that the goal is one single term *)
    val thms = inst_match_concl_in_terms keep ths tml
    val thms = map thm_to_conj_implies thms
  in
    (* Try to prove each theorem, and insert the result in the subgoal *)
    map_every_tac (try_tac o sg_premise_then prove_premise then_tac) thms
  end

(* Attempt to apply dependent rewrites with theorems by matching their
   conclusion with subterms of the goal (including the assumptions).

   Leaves the premises as subgoals if [prove_premise] doesn't prove them.

   See [apply_dep_rewrites_match_concl_with_terms_tac] for the shape of
   the theorems used in the net.
 *)
fun apply_dep_rewrites_match_concl_with_all_tac
  (prove_premise : tactic) (then_tac : thm_tactic) (ths : thm Net.net) : tactic =
  fn (asms, g) =>
  apply_dep_rewrites_match_concl_with_terms_tac prove_premise then_tac
    asms (g :: asms) ths (asms, g)

(* Same as {!apply_dep_rewrites_match_concl_with_all_tac} but we only match the
   conclusion of the goal.
 *)
fun apply_dep_rewrites_match_concl_with_goal_tac
  (prove_premise : tactic) (then_tac : thm_tactic) (ths : thm Net.net) : tactic =
  fn (asms, g) =>
  apply_dep_rewrites_match_concl_with_terms_tac prove_premise then_tac asms [g] ths (asms, g)

(* A theorem might be of the shape: [H => A = B /\ C = D], in which
   case we can split it into:
   [H => A = B]
   [H => C = D]

   The theorem mustn't have assumptions.
 *)
fun split_rewrite_thm (th : thm) : thm list =
  let
    val _ = null (hyp th);
    val t = concl th;
    val (vars, t) = strip_forall t;
    val (impl, t) = strip_imp t;
    val tml = strip_conj t;
    fun mk_goal (t : term) = list_mk_forall (vars, (list_mk_imp (impl, t)))
    val prove_tac =
      rpt gen_tac >> rpt disch_tac >>
      qspecl_assume (map (fn a => ‘^a’) vars) th >>
      fs [];
    fun mk_th (t : term) = prove (mk_goal t, prove_tac);
    (* Change the shape of the theorem (one of the conjuncts may have
       universally quantified variables)
     *)
    fun transform_th (th : thm) : thm =
      (GEN_ALL o thm_to_conj_implies o SPEC_ALL o UNDISCH_ALL o SPEC_ALL) th
  in
    map (transform_th o mk_th) tml
  end

(* Create a net from a list of rewriting theorems, from which we will match
   the conclusion against various subterms. *)
fun net_of_rewrite_thms (thml : thm list) : thm Net.net =
  let
    fun insert_th (th, net) =
      let
        val th = (UNDISCH_ALL o SPEC_ALL) th
        val tm = (lhs o concl) th
      in
        Net.insert (tm, th) net
      end
  in
    foldl insert_th Net.empty thml
  end

(* A dependent rewrite tactic which introduces the premises in a new goal.

   We try to apply dependent rewrites to the whole goal, including its assumptions.

   TODO: this tactic sometimes introduces several times the same subgoal
   (because we split theorems...).
 *)
fun sg_dep_rewrite_all_tac (th : thm) =
  let
    (* Split the theorem *)
    val thml = split_rewrite_thm th
    val ths = net_of_rewrite_thms thml
  in
    apply_dep_rewrites_match_concl_with_all_tac all_tac assume_tac ths
  end

(* Same as {!sg_dep_rewrite_tac} but this time we apply rewrites only in the conclusion
   of the goal (not the assumptions).
 *)
fun sg_dep_rewrite_goal_tac (th : thm) =
  let
    (* Split the theorem *)
    val thml = split_rewrite_thm th
    val ths = net_of_rewrite_thms thml
  in
    apply_dep_rewrites_match_concl_with_goal_tac all_tac assume_tac ths
  end

(*
val (asms, g) = ([
  “u32_to_int z = u32_to_int i − u32_to_int (int_to_u32 1)”,
  “u32_to_int (int_to_u32 2) = 2”
], “T”)

apply_dep_rewrites_match_concl_tac
  (FULL_SIMP_TAC simpLib.empty_ss all_integer_bounds >> COOPER_TAC)
  (fn th => FULL_SIMP_TAC simpLib.empty_ss [th])
  int_to_u32_id
*)

(* Attempt to apply dependent rewrites with theorems by matching their
   first premise with subterms of the goal.

   Leaves the premises as subgoals if [prove_premise] doesn't prove them.
 *)
fun apply_dep_rewrites_match_first_premise_with_all_tac
  (keep : thm -> bool)
  (prove_premise : tactic) (then_tac : thm_tactic) (ths : thm Net.net) : tactic =
  fn (asms, g) =>
    let
      (* Discharge the assumptions so that the goal is one single term *)
      val thms = inst_match_first_premise_in_terms keep ths (g :: asms);
      val thms = map thm_to_conj_implies thms;
      fun apply_tac th =
        let
          val th = thm_to_conj_implies th;
        in
          sg_premise_then prove_premise then_tac th
        end;
    in
      (* Apply each theorem *)
      map_every_tac apply_tac thms (asms, g)
    end

val cooper_tac = COOPER_TAC

(* Filter the assumptions in the goal *)
fun filter_assums_tac (keep : term -> bool) : tactic =
  fn (asms, g) =>
  let
    val kept_asms = filter keep asms
    (* The validation function *)
    fun valid thms =
      case thms of
        [th] =>
        let
          (* Being a bit brutal - will optimize later *)
          val tac = ntac (length asms) strip_tac >>
            (* Small subtlety: we have to use the primitive irule here,
               because otherwise it won't work with goals of the shape
               “x <> y”, as those are actually of the shape: “x = y ==> F”:
               irule will attempt to match “F” with the goal, which will fail.
             *)
            prim_irule th >>
            (* Prove the assumptions of the theorem by using the assumptions
               in goal. TODO: simply use ‘simp []’? *)
            pure_asm_rewrite_tac [] >> SIMP_TAC bool_ss []
          val th = prove (list_mk_imp (asms, g), tac)
          val th = foldl (fn (_, th) => UNDISCH th) th asms
        in th end
      | _ => failwith "filter_assums: expected exactly one theorem"
  in
    ([(kept_asms, g)], valid)
  end
  
(* For debugging *)
val dest_assums_conjs_th = ref sumTheory.EXISTS_SUM
val dest_assums_conjs_goal = ref “T”

(* Destruct the conjunctions in the assumptions *)
val dest_assums_conjs_tac : tactic =
  fn (asms, g) =>
  let
    (* Destruct the conjunctions *)
    val dest_asms = flatten (map (rev o strip_conj) asms)
    (* The validation function *)
    fun valid thms =
      case thms of
        [th] =>
        let
          (* Save the theorem for debugging *)
          val _ = dest_assums_conjs_th := th
          (* Being a bit brutal - will optimize later *)
          val tac = ntac (length asms) strip_tac >>
            (* Small subtlety: we have to use the primitive irule here,
               because otherwise it won't work with goals of the shape
               “x <> y”, as those are actually of the shape: “x = y ==> F”:
               irule will attempt to match “F” with the goal, which will fail.
             *)
            prim_irule th >>
            (* Prove the assumptions of the theorem by using the assumptions
               in goal. TODO: simply use ‘simp []’? *)
            pure_asm_rewrite_tac [] >> SIMP_TAC bool_ss [] >> 
            (* We may need to finish the job with metis - TODO: there must be a better way *)
            metis_tac []
          (* Save the goal for debugging *)
          val ng = list_mk_imp (asms, g)
          val _ = dest_assums_conjs_goal := ng
          val th = prove (ng, tac)
          val th = foldl (fn (_, th) => UNDISCH th) th asms
        in th end
      | _ => failwith "dest_assums_conjs: expected exactly one theorem"
  in
    ([(dest_asms, g)], valid)
  end

(* Defining those here so that they are evaluated once and for all (parsing
   depends on the context) *)
val int_tac_pats = [
    “x: int = y”,
    “x: int <= y”,
    “x: int < y”,
    “x: int >= y”,
    “x: int > y”,
    “x: num = y”,
    “x: num <= y”,
    “x: num < y”,
    “x: num >= y”,
    “x: num > y”
]
val int_tac_ops = Redblackset.fromList Term.compare (map (fst o strip_comb) int_tac_pats)

(* We boost COOPER_TAC a bit *)
fun int_tac (asms, g) =
  let
    (* Following the bug we discovered in COOPER_TAC, we keep only the terms:
       - which are inequalities/equalities between terms of type “:int” or “:num”.
       - which are comparisons of terms of tyep “:int” or “:num”

       TODO: issue/PR for HOL4
     *)
    fun keep (x : term) : bool =
    let
      val x = if is_neg x then dest_neg x else x
    in
      case strip_comb x of
        (y, [_, _]) => Redblackset.member (int_tac_ops, y)
      | _ => false
    end
 in
   (dest_assums_conjs_tac >>
    filter_assums_tac keep >>
    first_tac [cooper_tac, exfalso >- cooper_tac]) (asms, g)
 end

(* Remark.: [strip_case] is too smart for what we want.
   For instance: (fst o strip_case) “if i = 0 then ... else ...”
   returns “i” while we want to get “i = 0”.

   Also, [dest_case] sometimes fails.

   Ex.:
   {[
     val t = “result_CASE (if T then Return 0 else Fail Failure) (λy. Return ()) Fail Diverge”
     dest_case t
   ]}
   TODO: file an issue

   We use a custom function [get_case_scrutinee] instead of [dest_case] for this reason.
 *)
fun get_case_scrutinee t =
  let
    val (_, tms) = strip_comb t
  in
    hd tms
  end

(* Repeatedly destruct cases and return the last scrutinee we get *)
fun strip_all_cases_get_scrutinee (t : term) : term =
  if TypeBase.is_case t
  then
    (strip_all_cases_get_scrutinee o get_case_scrutinee) t
  else t

(* Same as [strip_all_cases_get_scrutinee *but* if at some point we reach term
   of the shape:
   {[
     (λ(y,z). ...) x
   ]}
   then we return the ‘x’
 *)
fun strip_all_cases_get_scrutinee_or_curried (t : term) : term =
    let
      (* Check if we have a term of the shape “(λ(y,z). ...) x” *)
      val scrut =
        let
          val (app, x) = dest_comb t
          val (app, _) = dest_comb app
          val {Name=name, Thy=thy, Ty = _ } = dest_thy_const app
        in
          if thy = "pair" andalso name = "UNCURRY" then x else failwith "not a curried argument"
        end
        handle HOL_ERR _ =>
          if TypeBase.is_case t
          then
            (strip_all_cases_get_scrutinee_or_curried o get_case_scrutinee) t
          else t
    in scrut end

(*
TypeBase.dest_case “case ls of [] => T | _ => F”
TypeBase.strip_case “case ls of [] => T | _ => F”
TypeBase.strip_case “case (if b then [] else [0, 1]) of [] => T | _ => F”
TypeBase.strip_case “3”
TypeBase.dest_case “3”

strip_all_cases_get_scrutinee “case ls of [] => T | _ => F”
strip_all_cases_get_scrutinee “case (if b then [] else [0, 1]) of [] => T | _ => F”
strip_all_cases_get_scrutinee “3”
*)

(* Lexicographic order over pairs *)
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

(* A constant name (theory, constant name) *)
type const_name = string * string

val const_name_compare = pair_compare String.compare String.compare

(* Given a function call [f y0 ... yn] return the name of the function *)
fun get_fun_name_from_app (t : term) : const_name =
  let
    val f = (fst o strip_comb) t;
    val {Name=name, Thy=thy, Ty=_} = dest_thy_const f;
    val cn = (thy, name);
  in cn end

end
