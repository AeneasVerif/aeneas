(* This file introduces a fixed-point operator to define potentially diverging
   functions so that the user doesn't have to prove termination at *definition time*
   but can prove it in an extrinsic manner.

   See divDefLib for a library which uses this fixed-point operator in an automated
   manner, and divDefExampleScript for hand-written and well commented examples of
   how to use it.
 *)

open primitivesArithTheory primitivesBaseTacLib primitivesTheory primitivesLib

val _ = new_theory "divDef"

(*======================
 * Fixed-point operator
 *======================*)

(* An auxiliary operator which uses some fuel *)
Definition fix_fuel_def:
  (fix_fuel (0 : num) (f : ('a -> 'b result) -> 'a -> 'b result) (x : 'a) : 'b result = Diverge) ∧
  (fix_fuel (SUC n) (f : ('a -> 'b result) -> 'a -> 'b result) (x : 'a) : 'b result = f (fix_fuel n f) x)
End

(* An auxiliary predicate *)
Definition fix_fuel_P_def:
  fix_fuel_P f x n = ~(is_diverge (fix_fuel n f x))
End

(* The fixed point operator *)
Definition fix_def:
  fix (f : ('a -> 'b result) -> 'a -> 'b result) (x : 'a) : 'b result =
    if (∃ n. fix_fuel_P f x n) then fix_fuel ($LEAST (fix_fuel_P f x)) f x else Diverge
End

(* An "executable" fixed point operator - useful for unit tests: we first test
   if ‘fix_fuel_P f x’ is true for a high quantity of fuel, otherwise we use
   ‘fix’ (which is not executable).

   We prove later that, under some constraints: ‘∀n. fix_nexec n f = fix f’
 *)
Definition fix_nexec_def:
  fix_nexec (n : num) (f : ('a -> 'b result) -> 'a -> 'b result) (x : 'a) : 'b result =
    if (fix_fuel_P f x n) then fix_fuel n f x else fix f x
End

(* We fix a quantity of fuel for ’fix_nexec *)
Definition fix_exec_def:
  fix_exec = fix_nexec 1000000
End

(* A validity condition.

   If a function body ‘f’ satisfies this condition, then we have the fixed point
   equation ‘fix f = f (fix f)’ (see [fix_fixed_eq]).
 *)
Definition is_valid_fp_body_def:
  (is_valid_fp_body (0 : num) (f : ('a -> 'a result) -> 'a -> 'a result) = F) ∧
  
  (is_valid_fp_body (SUC n) (f : ('a -> 'a result) -> 'a -> 'a result) =
    ∀x. (∀g h. f g x = f h x) ∨
         (∃ h y. is_valid_fp_body n h ∧
                  ∀g. f g x = do z <- g y; h g z od))
End

(*=====================================*
 * Lemmas about ‘fix_fuel’ and ‘fix’
 *=====================================*)
(* Auxiliary lemma.
   We generalize the goal of [fix_fuel_mono] in the case the fuel is non-empty
   (this allows us to unfold definitions like ‘fix_fuel’ once, and reveal
   a first intermediate function).

   Important: the structure of the proof is induction over ‘n’ then ‘N’.
 *)
Theorem fix_fuel_mono_aux:
  ∀n.
    ∀N M g f. is_valid_fp_body M f ⇒
      is_valid_fp_body N g ⇒
      ∀x. ~(is_diverge (g (fix_fuel n f) x)) ⇒
       ∀m. n ≤ m ⇒
         g (fix_fuel n f) x = g (fix_fuel m f) x
Proof
  Induct_on ‘n’ >>
  Induct_on ‘N’ >- fs [is_valid_fp_body_def]
  >-(  
    rw [] >>
    fs [is_valid_fp_body_def, is_diverge_def] >>
    first_x_assum (qspec_assume ‘x’) >>
    rw []
    >-((* Case 1: the continuation doesn't matter *) fs []) >>
    (* Case 2: the continuation *does* matter (i.e., there is a recursive call *)
    (* Instantiate the validity property with the different continuations *)
    first_assum (qspec_assume ‘fix_fuel n f’) >>
    first_assum (qspec_assume ‘fix_fuel n' f’) >>
    fs [] >>
    ntac 3 (pop_assum ignore_tac) >>
    fs [bind_def] >>
    fs [fix_fuel_def])
  >-(fs [is_valid_fp_body_def]) >>
  rw [] >>
  qpat_assum ‘is_valid_fp_body (SUC N) g’ mp_tac >>
  pure_rewrite_tac [is_valid_fp_body_def] >>
  fs [is_diverge_def] >>
  rw [] >>
  first_x_assum (qspec_assume ‘x’) >>
  rw []
  >-((* Case 1: the continuation doesn't matter *) fs []) >>
  (* Case 2: the continuation *does* matter (i.e., there is a recursive call *)
  (* Use the validity property with the different continuations *)
  fs [] >> pop_assum ignore_tac >>
  fs [bind_def, fix_fuel_def] >>
  Cases_on ‘m’ >- int_tac >>
  fs [fix_fuel_def] >>
  (* *)
  last_x_assum (qspecl_assume [‘M’, ‘M’, ‘f’, ‘f’]) >>
  gvs [] >>
  first_x_assum (qspec_assume ‘y’) >>
  Cases_on ‘f (fix_fuel n f) y’ >> fs [] >>
  first_x_assum (qspec_assume ‘n'’) >> gvs [] >> Cases_on ‘f (fix_fuel n' f) y’ >> fs [] >>
  (* *)  
  first_assum (qspecl_assume [‘M’, ‘h’, ‘f’]) >>
  gvs []
QED

(* ‘fix_fuel’ is monotonous over the fuel *)
Theorem fix_fuel_mono:
  ∀N f. is_valid_fp_body N f ⇒
    ∀n x. fix_fuel_P f x n ⇒
     ∀ m. n ≤ m ⇒
       fix_fuel n f x = fix_fuel m f x
Proof
  rw [] >>
  Cases_on ‘n’
  >-(fs [fix_fuel_P_def, is_diverge_def, fix_fuel_def]) >>
  fs [fix_fuel_P_def, fix_fuel_def] >> rw [] >>
  qspecl_assume [‘n'’, ‘N’, ‘N’, ‘f’, ‘f’] fix_fuel_mono_aux >>
  Cases_on ‘m’ >- fs [] >>
  gvs [fix_fuel_def]
QED

Theorem fix_fuel_mono_least:
  ∀N f. is_valid_fp_body N f ⇒
    ∀n x. fix_fuel_P f x n ⇒
      fix_fuel n f x = fix_fuel ($LEAST (fix_fuel_P f x)) f x
Proof
  rw [] >>
  pure_once_rewrite_tac [EQ_SYM_EQ] >>
  irule fix_fuel_mono >> fs [] >>
  (* Use the "fundamental" property about $LEAST *)
  qspec_assume ‘fix_fuel_P f x’ whileTheory.LEAST_EXISTS_IMP >>
  (* Prove the premise *)
  pop_assum sg_premise_tac >- metis_tac [] >> fs [] >>
  conj_tac
  >- (spose_not_then assume_tac >> fs [not_le_eq_gt]) >>
  metis_tac []
QED

Theorem fix_fuel_eq_fix:
  ∀N f. is_valid_fp_body N f ⇒
    ∀n x. fix_fuel_P f x n ⇒
      fix_fuel n f x = fix f x
Proof
  fs [fix_def] >>
  rw [] >>
  imp_res_tac fix_fuel_mono_least >>
  fs [fix_fuel_P_def, is_diverge_def] >>
  case_tac >> fs []
QED

Theorem fix_fuel_P_least:
  ∀f n x. fix_fuel n f x ≠ Diverge ⇒ fix_fuel_P f x ($LEAST (fix_fuel_P f x))
Proof
  rw [] >>
  qspec_assume ‘fix_fuel_P f x’ whileTheory.LEAST_EXISTS_IMP >>
  (* Prove the premise *)
  pop_assum sg_premise_tac
  >-(fs [fix_fuel_P_def, is_diverge_def] >> qexists ‘n’ >> fs [] >> case_tac >> fs []) >>
  rw []
QED

(* If ‘g (fix f) x’ doesn't diverge, we can write it in terms of ‘g (fix_fuel n f)’
   for some fuel ‘n’.

   This is an auxiliary lemma used to prove [fix_not_diverge_implies_fix_fuel]
 *)
Theorem fix_not_diverge_implies_fix_fuel_aux:
  ∀N M g f. is_valid_fp_body M f ⇒
    is_valid_fp_body N g ⇒
     ∀x. g (fix f) x ≠ Diverge ⇒
       ∃n. g (fix f) x = g (fix_fuel n f) x ∧
         ∀m. n ≤ m ⇒ g (fix_fuel m f) x = g (fix_fuel n f) x
Proof
  Induct_on ‘N’
  >-(fs [is_valid_fp_body_def]) >>
  rw [is_valid_fp_body_def] >>
  first_x_assum (qspec_assume ‘x’) >> rw []
  >-(first_assum (qspecl_assume [‘fix f’, ‘fix_fuel 0 f’]) >> fs []) >>
  (* Use the validity hypothesis *)
  fs [] >> pop_assum ignore_tac >>
  (* Use the induction hypothesis *)
  last_x_assum (qspecl_assume [‘M’, ‘h’, ‘f’]) >> gvs [] >>
  (* Case disjunction on ‘fix f ÿ’*)
  Cases_on ‘fix f y’ >> fs [bind_def] >~ [‘fix f y = Fail _’]
  >-(
    (* Fail case: easy, the call to ‘h’ is ignored *)
    fs [fix_def] >> pop_assum mp_tac >> rw [] >>
    qexists ‘$LEAST (fix_fuel_P f y)’ >>
    fs [] >>
    (* Use the monotonicity property for ‘f’ *)
    rw [] >>
    qspecl_assume [‘M’, ‘f’] fix_fuel_mono >> gvs [] >>
    first_x_assum (qspecl_assume [‘$LEAST (fix_fuel_P f y)’, ‘y’]) >> gvs [] >>
    fs [fix_fuel_P_def, is_diverge_def] >> gvs [] >>
    first_x_assum (qspecl_assume [‘m’]) >> gvs [] >>
    first_x_assum (fn th => assume_tac (GSYM th)) >> fs []
    ) >>
  (* Return case: we must take the maximum of the fuel for ‘f’ and ‘h’, and use
     the monotonicity property *)
  fs [fix_def] >> pop_assum mp_tac >> rw [] >>
  first_x_assum (qspec_assume ‘a’) >> gvs [] >>
  qexists ‘MAX ($LEAST (fix_fuel_P f y)) n'’ >> fs [] >>
  (* Use the monotonicity properties *)
  (* Instantiate the Monotonicity property for ‘f’ (the induction hypothesis gives
     the one for ‘h’) *)
  qspecl_assume [‘M’, ‘f’] fix_fuel_mono >> gvs [] >>
  first_x_assum (qspecl_assume [‘$LEAST (fix_fuel_P f y)’, ‘y’]) >> gvs [] >>
  fs [fix_fuel_P_def, is_diverge_def] >> gvs [] >>
  first_x_assum (qspecl_assume [‘MAX ($LEAST (fix_fuel_P f y)) n'’]) >> gvs [] >>
  first_x_assum (fn th => assume_tac (GSYM th)) >> fs [] >>
  (* Prove the monotonicity property for ‘do z <- fix f y; h (fix f) z’ *)
  rw [] >>
  (* First, one of the ‘fix_fuel ... f y’ doesn't use the proper fuel *)
  sg ‘fix_fuel ($LEAST (fix_fuel_P f y)) f y = Return a’
  >-(
    qspecl_assume [‘f’, ‘MAX ($LEAST (fix_fuel_P f y)) n'’, ‘y’] fix_fuel_P_least >>
    gvs [fix_fuel_P_def, is_diverge_def] >>
    Cases_on ‘fix_fuel ($LEAST (fix_fuel_P f y)) f y’ >> fs [] >>
    (* Use the monotonicity property - there are two goals here *)
    qspecl_assume [‘M’, ‘f’] fix_fuel_mono >> gvs [] >>
    first_x_assum (qspecl_assume [‘$LEAST (fix_fuel_P f y)’, ‘y’]) >> gvs [] >>
    fs [fix_fuel_P_def, is_diverge_def] >> gvs [] >>
    first_x_assum (qspecl_assume [‘MAX ($LEAST (fix_fuel_P f y)) n'’]) >> gvs []) >>
  (* Instantiate the monotonicity property for ‘f’ *)
  qspecl_assume [‘M’, ‘f’] fix_fuel_mono >> gvs [] >>
  first_x_assum (qspecl_assume [‘$LEAST (fix_fuel_P f y)’, ‘y’]) >> gvs [] >>
  gvs [fix_fuel_P_def, is_diverge_def] >> gvs [] >>
  first_x_assum (qspecl_assume [‘m’]) >> gvs [] >>
  first_x_assum (fn th => assume_tac (GSYM th)) >> fs []
QED

(* If ‘g (fix f) x’ doesn't diverge, we can write it in terms of ‘g (fix_fuel n f)’
   for some fuel ‘n’. *)
Theorem fix_not_diverge_implies_fix_fuel:
  ∀N f. is_valid_fp_body N f ⇒
     ∀x. f (fix f) x ≠ Diverge ⇒
       ∃n. f (fix f) x = f (fix_fuel n f) x
Proof
  metis_tac [fix_not_diverge_implies_fix_fuel_aux]
QED    

(* ‘fix’ satisfies the fixed point equation in case the evaluation diverges *)
Theorem fix_fixed_diverges:
  ∀N f. is_valid_fp_body N f ⇒ ∀x. ~(∃ n. fix_fuel_P f x n) ⇒ fix f x = f (fix f) x
Proof
  (* We do the proof by contraposition: if ‘f (fix f) x’ doesn't diverge, we
     can exhibit some fuel (lemma [fix_not_diverge_implies_fix_fuel]) *)
  rw [fix_def] >>
  imp_res_tac fix_not_diverge_implies_fix_fuel >>
  pop_assum (qspec_assume ‘x’) >>
  fs [fix_fuel_P_def, is_diverge_def] >>
  (* Case analysis: we have to prove that the ‘Return’ and ‘Fail’ cases lead
     to a contradiction *)
  Cases_on ‘f (fix f) x’ >> gvs [] >>
  first_x_assum (qspec_assume ‘SUC n’) >> fs [fix_fuel_def] >>
  pop_assum mp_tac >> case_tac >> fs []
QED

(* If ‘g (fix_fuel n f) x’ doesn't diverge, then it is equal to ‘g (fix f) x’ *)
Theorem fix_fuel_not_diverge_eq_fix_aux:
  ∀N M g f. is_valid_fp_body M f ⇒
    is_valid_fp_body N g ⇒
     ∀n x. g (fix_fuel n f) x ≠ Diverge ⇒
       g (fix f) x = g (fix_fuel n f) x
Proof
  Induct_on ‘N’
  >-(fs [is_valid_fp_body_def]) >>
  rw [is_valid_fp_body_def] >>
  first_x_assum (qspec_assume ‘x’) >> rw []
  >-(first_assum (qspecl_assume [‘fix f’, ‘fix_fuel 0 f’]) >> fs []) >>
  (* Use the validity hypothesis *)
  fs [] >> pop_assum ignore_tac >>
  (* For ‘fix f y = fix_fuel n f y’: use the monotonicity property *)
  sg ‘fix_fuel_P f y n’
  >-(Cases_on ‘fix_fuel n f y’ >> fs [fix_fuel_P_def, is_diverge_def, bind_def]) >>
  sg ‘fix f y = fix_fuel n f y’ >-(metis_tac [fix_fuel_eq_fix])>>
  (* Case disjunction on the call to ‘f’ *)
  Cases_on ‘fix_fuel n f y’ >> gvs [bind_def] >>
  (* We have to prove that: ‘h (fix f) a = h (fix_fuel n f) a’: use the induction hypothesis *)
  metis_tac []
QED

Theorem fix_fuel_not_diverge_eq_fix:
  ∀N f. is_valid_fp_body N f ⇒
     ∀n x. f (fix_fuel n f) x ≠ Diverge ⇒
       f (fix f) x = f (fix_fuel n f) x
Proof
  metis_tac [fix_fuel_not_diverge_eq_fix_aux]
QED

(* ‘fix’ satisfies the fixed point equation in case the evaluation terminates *)
Theorem fix_fixed_terminates:
  ∀N f. is_valid_fp_body N f ⇒ ∀x n. fix_fuel_P f x n ⇒ fix f x = f (fix f) x
Proof
  (* The proof simply uses the lemma [fix_fuel_not_diverge_eq_fix] *)
  rw [fix_fuel_P_def, is_diverge_def, fix_def] >> case_tac >> fs [] >>
  (* We can prove that ‘fix_fuel ($LEAST ...) f x ≠ Diverge’ *)
  qspecl_assume [‘f’, ‘n’, ‘x’] fix_fuel_P_least >>
  pop_assum sg_premise_tac >-(Cases_on ‘fix_fuel n f x’ >> fs []) >>
  fs [fix_fuel_P_def, is_diverge_def] >>
  (* *)
  Cases_on ‘($LEAST (fix_fuel_P f x))’ >> fs [fix_fuel_def] >>
  irule (GSYM fix_fuel_not_diverge_eq_fix) >>
  Cases_on ‘f (fix_fuel n'' f) x’ >> fs [] >> metis_tac []
QED

(* The final fixed point equation *)
Theorem fix_fixed_eq:
  ∀N f. is_valid_fp_body N f ⇒ ∀x. fix f x = f (fix f) x
Proof
  rw [] >>
  Cases_on ‘∃n. fix_fuel_P f x n’
  >- (irule fix_fixed_terminates >> metis_tac []) >>
  irule fix_fixed_diverges >>
  metis_tac []
QED

(*===============================
 * Lemmas about ‘fix_exec’
 *===============================*)

(* Prove that ‘fix_nexec’ is equivalent to ‘fix’ *)
Theorem fix_nexec_eq_fix:
  ∀ N f n. is_valid_fp_body N f ⇒ fix_nexec n f = fix f
Proof
  rw [] >>
  rpt (irule EQ_EXT >> gen_tac) >>
  fs [fix_nexec_def, fix_def] >>
  top_case_tac >>
  case_tac >> fs [] >>
  (* Use the properties of the least upper bound *)
  qspec_assume ‘fix_fuel_P f x’ whileTheory.LEAST_EXISTS_IMP >>
  pop_assum sg_premise_tac >- metis_tac [] >> fs [] >>
  (* Use the monotonicity property *)
  irule fix_fuel_mono_least >> metis_tac []
QED

(* Prove the fixed point property for ‘fix_exec’ *)
Theorem fix_exec_fixed_eq:
  ∀N f. is_valid_fp_body N f ⇒ ∀x. fix_exec f x = f (fix_exec f) x
Proof
  rw [fix_exec_def] >>
  imp_res_tac fix_nexec_eq_fix >> fs [] >>
  irule fix_fixed_eq >> fs [] >> metis_tac []
QED


(*===============================
 * Utilities for the automation
 *===============================*)

(* This theorem is important to shape the goal when proving that a body
   satifies the fixed point validity property.

   Important: this theorem (and its usafe) relies on the fact that errors are just
   transmitted to the caller (in particular, without modification).
 *)
Theorem case_result_switch_eq:
  (case (case x of Return y => f y | Fail e => Fail e | Diverge => Diverge) of
  | Return y => g y
  | Fail e => Fail e
  | Diverge => Diverge) =
  (case x of
   | Return y =>
     (case f y of
     | Return y => g y
     | Fail e => Fail e
     | Diverge => Diverge)
  | Fail e => Fail e
  | Diverge => Diverge)
Proof
  Cases_on ‘x’ >> fs []
QED

val _ = export_theory ()
