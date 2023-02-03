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
Theorem fix_fixed_termination_rec_case:
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
  irule fix_fixed_termination_rec_case >>
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

(************************** FAILED TESTS *)

(*
Datatype:
  fresult = FReturn 'b | FFail error | FRec 'a
End

(* TODO: monad converter from fresult to result + rewrite rules *)
val fres_to_res_def = Define ‘
  fres_to_res (f : 'a -> 'b result) (r : ('a, 'b) fresult) : 'b result =
    case r of
    | FReturn x => Return x
    | FFail e => Fail e
    | FRec y => f y
’

val fixa_fuel_def = Define ‘
  (fixa_fuel (0 : num) (f : 'a -> ('a, 'b) fresult) (x : 'a) : 'b result = Diverge) ∧
  (fixa_fuel (SUC n) (f : 'a -> ('a, 'b) fresult) (x : 'a) : 'b result =
    fres_to_res (fixa_fuel n f) (f x))
’

val fixa_fuel_P_def = Define ‘
  fixa_fuel_P f x n = ~(is_diverge (fixa_fuel n f x))
’

val fixa_def = Define ‘
  fixa (f : 'a -> ('a, 'b) fresult) (x : 'a) : 'b result =
    if (∃ n. fixa_fuel_P f x n) then fixa_fuel ($LEAST (fixa_fuel_P f x)) f x else Diverge
’

Theorem fixa_fuel_mono:
  ∀n m. n <= m ⇒ (∀f x. fixa_fuel_P f x n ⇒ fixa_fuel n f x = fixa_fuel m f x)
Proof
  Induct_on ‘n’ >> rpt strip_tac
  >- (fs [fixa_fuel_P_def, is_diverge_def, fixa_fuel_def, fres_to_res_def]) >>
  Cases_on ‘m’ >- int_tac >> fs [] >>
  last_x_assum imp_res_tac >>
  fs [fixa_fuel_P_def, is_diverge_def, fixa_fuel_def, fres_to_res_def] >>
  Cases_on ‘f x’ >> fs []
QED

(* TODO: remove ? *)
Theorem fixa_fuel_P_least:
  ∀f x n. fixa_fuel_P f x n ⇒ fixa_fuel_P f x ($LEAST (fixa_fuel_P f x))
Proof
  rw [] >>
  (* Use the "fundamental" property about $LEAST *)
  qspec_assume ‘fixa_fuel_P f x’ whileTheory.LEAST_EXISTS_IMP >>
  (* Prove the premise *)
  pop_assum sg_premise_tac >- metis_tac [] >>
  rw []
QED

Theorem fixa_fuel_mono_least:
  ∀n f x. fixa_fuel_P f x n ⇒ fixa_fuel n f x = fixa_fuel ($LEAST (fixa_fuel_P f x)) f x
Proof
  rw [] >>
  (* Use the "fundamental" property about $LEAST *)
  qspec_assume ‘fixa_fuel_P f x’ whileTheory.LEAST_EXISTS_IMP >>
  (* Prove the premise *)
  pop_assum sg_premise_tac >- metis_tac [] >>
  (* Prove that $LEAST ... ≤ n *)
  sg ‘n >= $LEAST (fixa_fuel_P f x)’ >-(
    spose_not_then assume_tac >>
    fs [not_ge_eq_lt]) >>
  pure_once_rewrite_tac [EQ_SYM_EQ] >>
  irule fixa_fuel_mono >>
  fs []
QED

Theorem fixa_fixed_eq:
  ∀f x. fixa f x = fres_to_res (fixa f) (f x)
Proof
  rw [fixa_def, fres_to_res_def]
  >- (
    (* Termination case *)
    imp_res_tac fixa_fuel_P_least >>
    Cases_on ‘$LEAST (fixa_fuel_P f x)’ >>
    fs [fixa_fuel_P_def, is_diverge_def, fixa_fuel_def, fres_to_res_def] >>
    Cases_on ‘f x’ >> fs [] >>
    rw [] >> fs [] >>
    irule fixa_fuel_mono_least >>
    fs [fixa_fuel_P_def, is_diverge_def, fixa_fuel_def]) >>
  (* Divergence case *)
  fs [fres_to_res_def] >>
  sg ‘∀n. ~(fixa_fuel_P f x (SUC n))’ >- fs [] >>
  Cases_on ‘f x’ >> fs [] >>
  fs [fixa_fuel_P_def, is_diverge_def, fixa_fuel_def, fres_to_res_def]  >>
  rw []
QED

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

Theorem fixa_fuel_eq_fix_fuel:
  ∀n (f : 'a -> ('a, 'b) fresult) (x : 'a).
    fixa_fuel n f x = fix_fuel n (\g y. fres_to_res g (f y)) x
Proof
  Induct_on ‘n’ >> rw [fixa_fuel_def, fix_fuel_def, fres_to_res_def]
QED

Theorem fixa_fuel_P_eq_fix_fuel_P:
  ∀(f : 'a -> ('a, 'b) fresult) (x : 'a).
    fixa_fuel_P f x = fix_fuel_P (\g y. fres_to_res g (f y)) x
Proof
  rw [] >> irule EQ_EXT >> rw [] >>
  qspecl_assume [‘x'’, ‘f’, ‘x’] fixa_fuel_eq_fix_fuel >>
  fs [fixa_fuel_P_def, fix_fuel_P_def]  
QED

Theorem fixa_fuel_eq_fix_fuel:
  ∀(f : 'a -> ('a, 'b) fresult) (x : 'a).
    fixa f x = fix (\g y. fres_to_res g (f y)) x
Proof
  rw [fixa_def, fix_def, fixa_fuel_P_eq_fix_fuel_P, fixa_fuel_eq_fix_fuel]
QED

(*
  The annoying thing is that to make this work, we need to rewrite the
  body by swapping matches, which is not easy to automate.
*)

(*
f x =
  case _ of
  | _ => Fail e
  | _ => Return x
  | _ => f y

f x (g : ('a, 'b) result => 'c)

f x (fres_to_res g) = f x g

*)

(*
val fix_fuel_def = Define ‘
  (fix_fuel (0 : num) (f : ('a -> 'b result) -> 'a -> 'b result) (x : 'a) : 'b result = Diverge) ∧
  (fix_fuel (SUC n) (f : ('a -> 'b result) -> 'a -> 'b result) (x : 'a) : 'b result = f (fix_fuel n f) x)
’

val fix_fuel_P_def = Define ‘
  fix_fuel_P f x n = ~(is_diverge (fix_fuel n f x))
’
*)


(*
val is_valid_FP_body_def = Define ‘
  is_valid_FP_body (f : (('a, 'b) fresult -> 'c) -> ('a, 'b) fresult -> 'c) =
    ∃ (fa: (('a, 'b) fresult -> ('a, 'b) fresult) -> ('a, 'b) fresult -> ('a, 'b) fresult).
      ∀ (g : ('a, 'b) fresult -> 'c) x.
        f g x = g (fa (\x. x) x)

val fix_fuel_def = Define ‘
  (fix_fuel (0 : num) (f : (('a, 'b) fresult -> 'b result) -> ('a, 'b) fresult -> 'b result) (x : ('a, 'b) fresult) : 'b result = Diverge) ∧
  (fix_fuel (SUC n) (f : (('a, 'b) fresult -> 'b result) -> ('a, 'b) fresult -> 'b result) (x : ('a, 'b) fresult) : 'b result = f (fix_fuel n f) x)
’

val fix_fuel_P_def = Define ‘
  fix_fuel_P f x n = ~(is_diverge (fix_fuel n f x))
’

val fix_def = Define ‘
  fix f x : 'b result =
    if (∃ n. fix_fuel_P f x n) then fix_fuel ($LEAST (fix_fuel_P f x)) f x else Diverge


Theorem fix_fuel_mono:
  ∀f. is_valid_FP_body f ⇒
  ∀n m. n <= m ⇒ (∀x. fix_fuel_P f x n ⇒ fix_fuel n f x = fix_fuel m f x)
Proof
  strip_tac >> strip_tac >>
  Induct_on ‘n’ >> rpt strip_tac
  >- (fs [fix_fuel_P_def, is_diverge_def, fix_fuel_def]) >>
  fs [fix_fuel_P_def, is_diverge_def, fix_fuel_def] >>
  Cases_on ‘m’ >- int_tac >>
  fs [fix_fuel_P_def, is_diverge_def, fix_fuel_def] >>
  fs [is_valid_FP_body] >>
  last_x_assum (qspec_assume ‘fix_fuel n f’) >>
  fs []
QED

’*)

(*
 * Test with a validity predicate which gives monotonicity.

   TODO: not enough to prove the fixed-point equation.
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

Theorem fix_eq:
  fix f = \x. if (∃ n. fix_fuel_P f x n) then fix_fuel ($LEAST (fix_fuel_P f x)) f x else Diverge
Proof
  irule EQ_EXT >> fs [fix_def]
QED

val is_valid_fp_body_def = Define ‘
  is_valid_fp_body (f : ('a -> 'b result) -> 'a -> 'b result) =
    ∀n m. n ≤ m ⇒ ∀x. fix_fuel_P f x n ⇒ fix_fuel n f x = fix_fuel m f x
’

Theorem fix_fuel_mono_least:
  ∀f. is_valid_fp_body f ⇒
    ∀n x. fix_fuel_P f x n ⇒ fix_fuel n f x = fix_fuel ($LEAST (fix_fuel_P f x)) f x
Proof
  rw [] >>
  (* Use the "fundamental" property about $LEAST *)
  qspec_assume ‘fix_fuel_P f x’ whileTheory.LEAST_EXISTS_IMP >>
  (* Prove the premise *)
  pop_assum sg_premise_tac >- metis_tac [] >> fs [] >>
  (* Prove that $LEAST ... ≤ n *)
  sg ‘n >= $LEAST (fix_fuel_P f x)’ >-(
    spose_not_then assume_tac >>
    fs [not_ge_eq_lt]) >>
  pure_once_rewrite_tac [EQ_SYM_EQ] >>
  (* Finish by using the monotonicity property *)
  fs [is_valid_fp_body_def]
QED


(* TODO: remove ? *)
Theorem fix_fuel_P_least:
  ∀f x n. fix_fuel_P f x n ⇒ fix_fuel_P f x ($LEAST (fix_fuel_P f x))
Proof
  rw [] >>
  (* Use the "fundamental" property about $LEAST *)
  qspec_assume ‘fix_fuel_P f x’ whileTheory.LEAST_EXISTS_IMP >>
  (* Prove the premise *)
  pop_assum sg_premise_tac >- metis_tac [] >>
  rw []
QED

(*Theorem test:
  fix_fuel_P f x (SUC n) ⇒
  (∀m. n ≤ m ⇒ f (fix_fuel n f) x = f (fix_fuel m f) x) ⇒
  f (fix_fuel n f) x = f (fix f) x
Proof
  rw [] >>
  spose_not_then assume_tac >>
  fs [fix_eq]
*)
Theorem fix_fixed_eq:
  ∀f. is_valid_fp_body f ⇒ ∀x. fix f x = f (fix f) x
Proof
  rw [fix_def] >> CASE_TAC >> fs []
  >- (
    (* Termination case *)
    sg ‘$LEAST (fix_fuel_P f x) <= n’ >- cheat >>
    imp_res_tac fix_fuel_P_least >>
    Cases_on ‘$LEAST (fix_fuel_P f x)’ >>
    fs [fix_fuel_P_def, is_diverge_def, fix_fuel_def] >>
    Cases_on ‘n’ >>
    fs [fix_fuel_P_def, is_diverge_def, fix_fuel_def] >>
    (* Use the validity assumption *)
    fs [is_valid_fp_body_def] >>
  
(*    last_x_assum imp_res_tac >> *)
    last_assum (qspecl_assume [‘SUC n'’, ‘SUC n''’]) >> fs [] >>
    pop_assum imp_res_tac >>
    pop_assum (qspec_assume ‘x’) >>
    pop_assum sg_premise_tac >- fs [fix_fuel_P_def, is_diverge_def, fix_fuel_def] >>
    
    fs [fix_fuel_def] >>

    
    fs [fix_fuel_P_def] >>
    rfs [fix_fuel_P_def, is_diverge_def, fix_fuel_def] >>
    
    fs [fix_eq] >>

    Cases_on ‘fix_fuel n' f x’ >> fs [] >>
    last_assum (qspecl_then [‘n'’, ‘’
    f (fix_fuel n' f) x >>

    Cases_on ‘f x’ >> fs [] >>
    rw [] >> fs [] >>
    irule fix_fuel_mono_least >>
    fs [fix_fuel_P_def, is_diverge_def, fix_fuel_def]) >>
  (* Divergence case *)
  fs [fres_to_res_def] >>
  sg ‘∀n. ~(fix_fuel_P f x (SUC n))’ >- fs [] >>
  Cases_on ‘f x’ >> fs [] >>
  fs [fix_fuel_P_def, is_diverge_def, fix_fuel_def]  >>
  rw []
QED


(* A slightly weaker and more precise validity criteria.

   We simply extracted the part of the inductive proof that we can't prove without
   knowing ‘f’.
 *)
val is_valid_fp_body_weak_def = Define ‘
   is_valid_fp_body_weak f =
   ∀n m x.
   ((∀x. fix_fuel_P f x n ⇒ fix_fuel n f x = fix_fuel m f x) ⇒
    n ≤ m ⇒
    fix_fuel_P f x (SUC n) ⇒
    fix_fuel (SUC n) f x = fix_fuel (SUC m) f x)
’

Theorem is_valid_fp_body_weak_imp_is_valid:
  ∀f. is_valid_fp_body_weak f ⇒ is_valid_fp_body f
Proof
  rpt strip_tac >> fs [is_valid_fp_body_def] >>
  Induct_on ‘n’ >- fs [fix_fuel_P_def, fix_fuel_def, is_diverge_def] >>
  Cases_on ‘m’ >> fs [] >>
  fs [is_valid_fp_body_weak_def]
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
    | ListNil => (Fail Failure)
’ 

(* The general proof of is_valid_fp_body. We isolate a more precise property below. *)
Theorem nth_body_is_valid:
  is_valid_fp_body nth_body
Proof
  pure_rewrite_tac [is_valid_fp_body_def] >>
  Induct_on ‘n’ >- fs [fix_fuel_P_def, fix_fuel_def, is_diverge_def] >>
  Cases_on ‘m’ >- fs [] >>
  rpt strip_tac >>
  (* TODO: here *)
  last_assum imp_res_tac >>
  (* TODO: here? *)
  fs [fix_fuel_def, nth_body_def, fix_fuel_P_def, is_diverge_def, bind_def] >>
  Cases_on ‘x’ >> fs [] >> (* TODO: automate this *)
  (* Explore all paths *)
  Cases_on ‘q’ >> fs [] >>
  Cases_on ‘u32_to_int r = 0’ >> fs [] >>
  Cases_on ‘u32_sub r (int_to_u32 1)’ >> fs []
QED


Theorem nth_body_is_valid_weak:
  is_valid_fp_body_weak nth_body
Proof
  pure_rewrite_tac [is_valid_fp_body_weak_def] >>
  rpt strip_tac >>
  (* TODO: automate this - we may need to destruct a variable number of times *)
  Cases_on ‘x’ >> fs [] >>
  (* Expand all *)
  fs [fix_fuel_def, nth_body_def, fix_fuel_P_def, is_diverge_def, bind_def] >>
  (* Explore all paths *)
  Cases_on ‘q’ >> fs [] >>
  Cases_on ‘u32_to_int r = 0’ >> fs [] >>
  Cases_on ‘u32_sub r (int_to_u32 1)’ >> fs []
QED

(*
 * Test with a more general validity predicate.
 *)
(* We need to control the way calls to the continuation are performed, so
   that we can inspect the inputs (otherwise we can't prove anything).
 *)
val is_valid_FP_body_def = Define ‘
  is_valid_FP_body (f : (('a, 'b) fresult -> 'c) -> 'a -> 'c) =
    ∃ (fa: (('a, 'b) fresult -> ('a, 'b) fresult) -> 'a -> ('a, 'b) fresult).
      ∀ (g : ('a, 'b) fresult -> 'c) x.
        f g x = g (fa (\x. x) x)
’


val fix_fuel_def = Define ‘
  (fix_fuel (0 : num) (f : (('a, 'b) fresult -> 'b result) -> 'a -> 'b result) (x : 'a) : 'b result = Diverge) ∧
  (fix_fuel (SUC n) (f : (('a, 'b) fresult -> 'b result) -> 'a -> 'b result) (x : 'a) : 'b result =
    f (fres_to_res (fix_fuel n f)) x)
’

val fix_fuel_P_def = Define ‘
  fix_fuel_P f x n = ~(is_diverge (fix_fuel n f x))
’

val fix_def = Define ‘
  fix f x : 'b result =
    if (∃ n. fix_fuel_P f x n) then fix_fuel ($LEAST (fix_fuel_P f x)) f x else Diverge
’

Theorem fix_fuel_mono:
  ∀f. is_valid_FP_body f ⇒
  ∀n m. n <= m ⇒ (∀x. fix_fuel_P f x n ⇒ fix_fuel n f x = fix_fuel m f x)
Proof
  strip_tac >> strip_tac >>
  Induct_on ‘n’ >> rpt strip_tac
  >- (fs [fix_fuel_P_def, is_diverge_def, fix_fuel_def]) >>
  fs [fix_fuel_P_def, is_diverge_def, fix_fuel_def, fres_to_res_def] >>
  Cases_on ‘m’ >- int_tac >>
  fs [fix_fuel_P_def, is_diverge_def, fix_fuel_def] >>
  fs [is_valid_FP_body_def, fres_to_res_def] >>
  CASE_TAC >>
  last_x_assum (qspec_assume ‘fres_to_res (fix_fuel n f)’) >>
  fs [fres_to_res_def]
QED

(* Tests *)



Datatype:
  list_t =
    ListCons 't list_t
  | ListNil
End

(*
val def_qt = ‘
  nth_mut_fwd (ls : 't list_t) (i : u32) : 't result =
  case ls of
  | ListCons x tl =>
    if u32_to_int i = (0:int)
    then Return x
    else
      do
      i0 <- u32_sub i (int_to_u32 1);
      nth_mut_fwd tl i0
      od
  | ListNil =>
    Fail Failure
’
*)

val nth_body_def = Define ‘
  nth_body (f : ('t list_t # u32, 't) fresult -> 'c) (ls : 't list_t, i : u32) : 'c =
    case ls of
    | ListCons x tl =>
      if u32_to_int i = (0:int)
      then f (FReturn x)
      else
        do
        i0 <- u32_sub i (int_to_u32 1);
        f (FRec (tl, i0))
        od
    | ListNil => f (FFail Failure)
’

Theorem nth_body_is_valid_FP_body:
  is_valid_FP_body nth_body
Proof
  fs [is_valid_FP_body_def] >>
  exists_tac “nth_body” >>
QED

“nth_body”

(* TODO: abbreviation for ‘(\g y. fres_to_res g (f y))’ *)
Theorem fix_fixed_eq:
  ∀f x. fix (\g y. fres_to_res g (f y)) x =
     (f x)
    fres_to_res (\g y. fres_to_res g (f y))



(*
TODO: can't prove that

Theorem fix_fuel_mono:
  ∀n m. n <= m ⇒ (∀f x. fix_fuel_P f x n ⇒ fix_fuel n f x = fix_fuel m f x)
Proof
  Induct_on ‘n’ >> rpt strip_tac
  >- (fs [fix_fuel_P_def, is_diverge_def, fix_fuel_def]) >>
  fs [fix_fuel_P_def, is_diverge_def, fix_fuel_def] >>
  Cases_on ‘m’ >- int_tac >>
  fs [fix_fuel_P_def, is_diverge_def, fix_fuel_def] >>

  sg ‘fix_fuel n f = fix_fuel n' f’ >>

  last_x_assum imp_res_tac >>
  pop_assum (qspecl_assume [‘x’, ‘f’]) >>

Theorem fix_def_eq:
  ∀f x. fix f x = f (fix f) x
Proof
  
*)
*)


val _ = export_theory ()
