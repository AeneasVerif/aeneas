(* Prototype: divDefLib but with general combinators *)

open HolKernel boolLib bossLib Parse
open boolTheory arithmeticTheory integerTheory intLib listTheory stringTheory

open primitivesArithTheory primitivesBaseTacLib ilistTheory primitivesTheory
open primitivesLib

val _ = new_theory "divDefProto"

(*
 * Test with a general validity predicate.
 *
 * TODO: this works! Cleanup.
 *)
val fix_fuel_def = Define ‘
  (fix_fuel (0 : num) (f : ('a -> 'b result) -> 'a -> 'b result) (x : 'a) : 'b result = Diverge) ∧
  (fix_fuel (SUC n) (f : ('a -> 'b result) -> 'a -> 'b result) (x : 'a) : 'b result = f (fix_fuel n f) x)
’

val fix_fuel_P_def = Define ‘
  fix_fuel_P f x n = ~(is_diverge (fix_fuel n f x))
’

val fix_def = Define ‘
  fix (f : ('a -> 'b result) -> 'a -> 'b result) (x : 'a) : 'b result =
    if (∃ n. fix_fuel_P f x n) then fix_fuel ($LEAST (fix_fuel_P f x)) f x else Diverge
’

val is_valid_fp_body_def = Define ‘
  is_valid_fp_body (f : ('a -> 'b result) -> 'a -> 'b result) =
    ∀x. (∀g h. f g x = f h x) ∨ (∃ y. ∀g. f g x = g y)
’

Theorem fix_fuel_mono:
  ∀f. is_valid_fp_body f ⇒
    ∀n x. fix_fuel_P f x n ⇒
     ∀ m. n ≤ m ⇒
       fix_fuel n f x = fix_fuel m f x
Proof
  ntac 2 strip_tac >>
  Induct_on ‘n’ >> rpt strip_tac
  >- (fs [fix_fuel_P_def, is_diverge_def, fix_fuel_def]) >>
  Cases_on ‘m’ >- int_tac >> fs [] >>
    fs [is_valid_fp_body_def] >>
  fs [fix_fuel_P_def, is_diverge_def, fix_fuel_def] >>

  (* Use the validity property *)
  last_x_assum (qspec_assume ‘x’) >>
  (* This makes a case disjunction on the validity property *)
  rw []
  >-((* Case 1: the continuation doesn't matter *) fs []) >>
  (* Case 2: the continuation *does* matter (i.e., there is a recursive call *)
  (* Instantiate the validity property with the different continuations *)
  first_assum (qspec_assume ‘fix_fuel n f’) >>
  first_assum (qspec_assume ‘fix_fuel n' f’) >>
  last_assum (qspec_assume ‘y’) >>
  fs []
QED

(* TODO: remove? *)
Theorem fix_fuel_mono_least:
  ∀f. is_valid_fp_body f ⇒
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
  spose_not_then assume_tac >>
  fs [not_le_eq_gt]
QED

Theorem fix_fixed_diverges:
  ∀f. is_valid_fp_body f ⇒ ∀x. ~(∃ n. fix_fuel_P f x n) ⇒ fix f x = f (fix f) x
Proof
  rw [fix_def] >>
  (* Case disjunction on the validity hypothesis *)
  fs [is_valid_fp_body_def] >>
  last_x_assum (qspec_assume ‘x’) >>
  rw []
  >- (
    last_assum (qspec_assume ‘SUC n’) >>
    fs [fix_fuel_P_def, is_diverge_def, fix_fuel_def] >>
    first_assum (qspecl_assume [‘fix f’, ‘fix_fuel n f’]) >>
    Cases_on ‘f (fix_fuel n f) x’ >> fs []
  ) >>
  first_assum (qspec_assume ‘fix f’) >> fs [] >>
  fs [fix_def] >>
  (* Case disjunction on the ‘∃n. ...’ *)
  rw [] >>
  (* Use the hypothesis that there is no fuel s.t. ... *)
  last_assum (qspec_assume ‘SUC n’) >>
  fs [fix_fuel_P_def, is_diverge_def, fix_fuel_def] >>
  first_assum (qspec_assume ‘fix_fuel n f’) >>
  Cases_on ‘fix_fuel n f y’ >> fs []
QED

(* TODO: I think we can merge this with the theorem below *)
Theorem fix_fixed_termination_rec_case_aux:
  ∀x y n m.
  is_valid_fp_body f ⇒
  (∀g. f g x = g y) ⇒
  fix_fuel_P f x n ⇒
  fix_fuel_P f y m ⇒
  fix_fuel n f x = fix_fuel m f y
Proof
  rw [] >>
  Cases_on ‘n’ >- fs [fix_fuel_P_def, is_diverge_def, fix_fuel_def] >>
  pure_asm_rewrite_tac [fix_fuel_def] >>
  sg ‘fix_fuel_P f y n'’ >- rfs [fix_fuel_P_def, is_diverge_def, fix_fuel_def] >>
  imp_res_tac fix_fuel_mono_least >>
  fs []
QED

Theorem fix_fixed_termination_rec_case:
  ∀ x y n m.
  is_valid_fp_body f ⇒
  (∀g. f g x = g y) ⇒
  fix_fuel_P f x n ⇒
  fix_fuel_P f y m ⇒
  fix_fuel ($LEAST (fix_fuel_P f x)) f x =
  fix_fuel ($LEAST (fix_fuel_P f y)) f y
Proof
  rw [] >>
  imp_res_tac fix_fuel_mono_least >>
  irule fix_fixed_termination_rec_case_aux >>
  fs [] >>
  (* TODO: factorize *)
  qspec_assume ‘fix_fuel_P f x’ whileTheory.LEAST_EXISTS_IMP >>
  pop_assum sg_premise_tac >- metis_tac [] >>
  qspec_assume ‘fix_fuel_P f y’ whileTheory.LEAST_EXISTS_IMP >>
  pop_assum sg_premise_tac >- metis_tac [] >>
  rw []
QED

Theorem fix_fixed_terminates:
  ∀f. is_valid_fp_body f ⇒ ∀x n. fix_fuel_P f x n ⇒ fix f x = f (fix f) x
Proof
  rpt strip_tac >>
  (* Case disjunction on the validity hypothesis - we don't want to consume it *)
  last_assum mp_tac >>
  pure_rewrite_tac [is_valid_fp_body_def] >> rpt strip_tac >>
  pop_assum (qspec_assume ‘x’) >>
  rw []
  >-( (* No recursive call *)
    fs [fix_def] >> rw [] >> fs [] >>
    imp_res_tac fix_fuel_mono_least >>
    Cases_on ‘$LEAST (fix_fuel_P f x)’ >> fs [fix_fuel_P_def, is_diverge_def, fix_fuel_def]
  ) >>
  (* There exists a recursive call *)
  SUBGOAL_THEN “∃m. fix_fuel_P f y m” assume_tac >-(
    Cases_on ‘n’ >>
    fs [fix_fuel_P_def, is_diverge_def, fix_fuel_def] >>
    metis_tac []
  ) >>
  fs [fix_def] >> rw [] >> fs [] >>
  irule fix_fixed_termination_rec_case >>
  fs [] >>
  metis_tac []
QED

Theorem fix_fixed_eq:
  ∀f. is_valid_fp_body f ⇒ ∀x. fix f x = f (fix f) x
Proof
  rw [] >>
  Cases_on ‘∃n. fix_fuel_P f x n’
  >- (irule fix_fixed_terminates >> metis_tac []) >>
  irule fix_fixed_diverges >>
  fs []
QED  

(* Testing on an example *)
Datatype:
  list_t =
    ListCons 't list_t
  | ListNil
End

val nth_body_def = Define ‘
  nth_body (f : ('t list_t # u32) -> 't result) (x : ('t list_t # u32)) : 't result =
    let (ls, i) = x in
    case ls of
    | ListCons x tl =>
      if u32_to_int i = (0:int)
      then (Return x)
      else
        do
        i0 <- u32_sub i (int_to_u32 1);
        f (tl, i0)
        od
    | ListNil => Fail Failure
’

(* TODO: move *)
Theorem is_valid_suffice:
  ∃y. ∀g. g x = g y
Proof
  metis_tac []
QED

(* The general proof of is_valid_fp_body *)
Theorem nth_body_is_valid:
  is_valid_fp_body nth_body
Proof
  pure_rewrite_tac [is_valid_fp_body_def] >>
  gen_tac >>
  (* TODO: automate this *)
  Cases_on ‘x’ >> fs [] >>
  (* Expand *)
  fs [nth_body_def, bind_def] >>
  (* Explore all paths *)
  Cases_on ‘q’ >> fs [is_valid_suffice] >>
  Cases_on ‘u32_to_int r = 0’ >> fs [is_valid_suffice] >>
  Cases_on ‘u32_sub r (int_to_u32 1)’ >> fs [is_valid_suffice]
QED

val nth_raw_def = Define ‘
  nth (ls : 't list_t) (i : u32) = fix nth_body (ls, i)
’

Theorem nth_def:
  ∀ls i. nth (ls : 't list_t) (i : u32) : 't result =
    case ls of
    | ListCons x tl =>
      if u32_to_int i = (0:int)
      then (Return x)
      else
        do
        i0 <- u32_sub i (int_to_u32 1);
        nth tl i0
        od
    | ListNil => Fail Failure
Proof
  rpt strip_tac >>
  (* Expand the raw definition *)
  pure_rewrite_tac [nth_raw_def] >>
  (* Use the fixed-point equality *)
  sg ‘fix nth_body (ls,i) = nth_body (fix nth_body) (ls,i)’
  >- simp_tac bool_ss [HO_MATCH_MP fix_fixed_eq nth_body_is_valid] >>
  pure_asm_rewrite_tac [] >>
  (* Expand the body definition *)
  qspecl_assume [‘fix nth_body’, ‘(ls, i)’] nth_body_def >>
  pure_asm_rewrite_tac [LET_THM] >>
  simp_tac arith_ss []
QED

val _ = export_theory ()
