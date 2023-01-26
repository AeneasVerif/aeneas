(* Base tactics for the primitives library *)
structure primitivesBaseTacLib =
struct

open HolKernel boolLib bossLib Parse
open boolTheory arithmeticTheory integerTheory intLib listTheory

(* Remark: below, we also have conversions *)
val gsym = GSYM

(* Ignore a theorem.

   To be used in conjunction with {!pop_assum} for instance.
 *)
fun ignore_tac (_ : thm) : tactic = ALL_TAC

val pop_ignore_tac = pop_assum ignore_tac

(* TODO: no exfalso tactic?? *)
val exfalso : tactic =
  SUBGOAL_THEN “F” (fn th => ASSUME_TAC th >> fs[])

val try_tac = TRY
val first_tac = FIRST
val map_first = MAP_FIRST
val fail_tac = FAIL_TAC

fun qspec_assume x th = qspec_then x assume_tac th
fun qspecl_assume xl th = qspecl_then xl assume_tac th
fun first_qspec_assume x = first_assum (qspec_assume x)
fun first_qspecl_assume xl = first_assum (qspecl_assume xl)

val all_tac = all_tac
val cooper_tac = COOPER_TAC
val pure_rewrite_tac = PURE_REWRITE_TAC
val pure_once_rewrite_tac = PURE_ONCE_REWRITE_TAC

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

   [try_match] should return an instantiated theorem, as well as a term which
   identifies this theorem (the lhs of the equality, if this is a rewriting
   theorem for instance - we use this to check for collisions, and discard
   redundant instantiations).
 *)
fun inst_match_in_terms
  (try_match: string Redblackset.set -> term -> term * thm)
  (tl : term list) : thm list =
  let
    (* We use a map when storing the theorems, to avoid storing the same theorem twice *)
    val inst_thms: (term, thm) Redblackmap.dict ref = ref (Redblackmap.mkDict Term.compare);
    fun try_instantiate bvars t =
      let
        val (inst_th_tm, inst_th) = try_match bvars t;
      in
        inst_thms := Redblackmap.insert (!inst_thms, inst_th_tm, inst_th)
      end
      handle HOL_ERR _ => ();
    (* Explore the term *)
    val _ = app (dep_apply_in_subterms try_instantiate (Redblackset.empty String.compare)) tl;
  in
    map snd (Redblackmap.listItems (!inst_thms))
  end

(* Given a rewriting theorem [th] which has premises, return all the
   instantiations of this theorem which make its conclusion match subterms
   in the provided list of term.

   [ignore]: if the conclusion of a theorem matches a term in this set, ignore it.
 *)
fun inst_match_concl_in_terms (ignore : term Redblackset.set) (th : thm) (tl : term list) : thm list =
  let
    val th = (UNDISCH_ALL o SPEC_ALL) th;
    fun try_match bvars t =
      let
        val inst_th = inst_match_concl bvars th t;
        val c = concl inst_th;
      in
        (* Check that we mustn't ignore the theorem *)
        if Redblackset.member (ignore, c) then failwith "inst_match_concl_in_terms: already in the assumptions"
        else (lhs (concl inst_th), inst_th)
      end;
  in
    inst_match_in_terms try_match tl
  end

(*
val t = “!x. u32_to_int (int_to_u32 x) = u32_to_int (int_to_u32 y)”
val th = int_to_u32_id

val thms = inst_match_concl_in_terms int_to_u32_id [t]
*)


(* Given a theorem [th] which has premises, return all the
   instantiations of this theorem which make its first premise match subterms
   in the provided list of term.
 *)
fun inst_match_first_premise_in_terms (th : thm) (tl : term list) : thm list =
  let
    val th = SPEC_ALL th;
    fun try_match bvars t =
      let
        val inst_th = inst_match_first_premise bvars th t;
      in
        ((fst o dest_imp o concl) inst_th, inst_th)
      end;
  in
    inst_match_in_terms try_match tl
  end

(*
val t = “x = y - 1 ==> T”
val th = SPEC_ALL NUM_SUB_1_EQ

val thms = inst_match_first_premise_in_terms th [t]
*)


(* Attempt to apply dependent rewrites with a theorem by matching its
   conclusion with subterms in the given list of terms.

   Leaves the premises as subgoals if [prove_premise] doesn't prove them.
 *)
fun apply_dep_rewrites_match_concl_with_terms_tac
  (prove_premise : tactic) (then_tac : thm_tactic) (tl : term list) (th : thm) : tactic =
  let
    val ignore = Redblackset.fromList Term.compare tl;
    (* Discharge the assumptions so that the goal is one single term *)
    val thms = inst_match_concl_in_terms ignore th tl;
    val thms = map thm_to_conj_implies thms;
  in
    (* Apply each theorem *)
    MAP_EVERY (sg_premise_then prove_premise then_tac) thms
  end

(* Attempt to apply dependent rewrites with a theorem by matching its
   conclusion with subterms of the goal (including the assumptions).

   Leaves the premises as subgoals if [prove_premise] doesn't prove them.
 *)
fun apply_dep_rewrites_match_concl_with_all_tac
  (prove_premise : tactic) (then_tac : thm_tactic) (th : thm) : tactic =
  fn (asms, g) => apply_dep_rewrites_match_concl_with_terms_tac prove_premise then_tac (g :: asms) th (asms, g)

(* Same as {!apply_dep_rewrites_match_concl_with_all_tac} but we only match the
   conclusion of the goal.
 *)
fun apply_dep_rewrites_match_concl_with_goal_tac
  (prove_premise : tactic) (then_tac : thm_tactic) (th : thm) : tactic =
  fn (asms, g) => apply_dep_rewrites_match_concl_with_terms_tac prove_premise then_tac [g] th (asms, g)

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
    val tl = strip_conj t;
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
    map (transform_th o mk_th) tl
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
  in
    MAP_EVERY (apply_dep_rewrites_match_concl_with_all_tac all_tac assume_tac) thml
  end

(* Same as {!sg_dep_rewrite_tac} but this time we apply rewrites only in the conclusion
   of the goal (not the assumptions).
 *)
fun sg_dep_rewrite_goal_tac (th : thm) =
  let
    (* Split the theorem *)
    val thml = split_rewrite_thm th
  in
    MAP_EVERY (apply_dep_rewrites_match_concl_with_goal_tac all_tac assume_tac) thml
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

(* Attempt to apply dependent rewrites with a theorem by matching its
   first premise with subterms of the goal.

   Leaves the premises as subgoals if [prove_premise] doesn't prove them.
 *)
fun apply_dep_rewrites_match_first_premise_tac
  (prove_premise : tactic) (then_tac : thm_tactic) (th : thm) : tactic =
  fn (asms, g) =>
    let
      (* Discharge the assumptions so that the goal is one single term *)
      val thms = inst_match_first_premise_in_terms th (g :: asms);
      val thms = map thm_to_conj_implies thms;
      fun apply_tac th =
        let
          val th = thm_to_conj_implies th;
        in
          sg_premise_then prove_premise then_tac th
        end;
    in
      (* Apply each theorem *)
      MAP_EVERY apply_tac thms (asms, g)
    end

end
