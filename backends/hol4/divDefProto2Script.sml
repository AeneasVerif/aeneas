(* Prototype: divDefLib but with general combinators *)

open HolKernel boolLib bossLib Parse
open boolTheory arithmeticTheory integerTheory intLib listTheory stringTheory

open primitivesArithTheory primitivesBaseTacLib ilistTheory primitivesTheory
open primitivesLib

val _ = new_theory "divDefProto2"


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
  (is_valid_fp_body (0 : num) (f : ('a -> 'a result) -> 'a -> 'a result) = F) ∧
  
  (is_valid_fp_body (SUC n) (f : ('a -> 'a result) -> 'a -> 'a result) =
    ∀x. (∀g h. f g x = f h x) ∨
         (∃ h y. is_valid_fp_body n h ∧
                  ∀g. f g x = do z <- g y; h g z od))
’

(* Auxiliary lemma.
   We generalize the goal of fix_fuel_mono in the case the fuel is non-empty
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

(* TODO: remove? *)
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

(* If ‘g (fix f) x’ doesn't diverge, we can exhibit some fuel *)
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

(* If ‘g (fix f) x’ doesn't diverge, we can exhibit some fuel *)
Theorem fix_not_diverge_implies_fix_fuel:
  ∀N f. is_valid_fp_body N f ⇒
     ∀x. f (fix f) x ≠ Diverge ⇒
       ∃n. f (fix f) x = f (fix_fuel n f) x
Proof
  metis_tac [fix_not_diverge_implies_fix_fuel_aux]
QED    

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

Theorem fix_fixed_eq:
  ∀N f. is_valid_fp_body N f ⇒ ∀x. fix f x = f (fix f) x
Proof
  rw [] >>
  Cases_on ‘∃n. fix_fuel_P f x n’
  >- (irule fix_fixed_terminates >> metis_tac []) >>
  irule fix_fixed_diverges >>
  metis_tac []
QED  

(*
 * Attempt to make the lemmas work with more general types
 * (we want ‘: 'a -> 'b result’, not ‘:'a -> 'a result’).
 *)
val simp_types_def = Define ‘
  simp_types (f : 'a -> 'b result) : ('a + 'b) -> ('a + 'b) result =
    \x. case x of
    | INL x =>
      (case f x of
       | Fail e => Fail e
       | Diverge => Diverge
       | Return y =>
         Return (INR y))
    | INR _ => Fail Failure
’

(* Testing on an example *)
Datatype:
  list_t =
    ListCons 't list_t
  | ListNil
End

(* We use this version of the body to prove that the body is valid *)
val nth_body_def = Define ‘
  nth_body (f : (('t list_t # u32) + 't) -> (('t list_t # u32) + 't) result)
    (x : (('t list_t # u32) + 't)) :
    (('t list_t # u32) + 't) result =
    case x of
    | INL x => (
      let (ls, i) = x in
      case ls of
      | ListCons x tl =>
        if u32_to_int i = (0:int)
        then Return (INR x)
        else
          do
          i0 <- u32_sub i (int_to_u32 1);
          r <- f (INL (tl, i0));
          case r of
          | INL _ => Fail Failure
          | INR i1 => Return (INR i1)
          od
      | ListNil => Fail Failure)
    | INR _ => Fail Failure
’

(* TODO: move *)
Theorem is_valid_suffice:
  ∃y. ∀g. g x = g y
Proof
  metis_tac []
QED

(* We first prove the theorem with ‘SUC (SUC n)’ where ‘n’ is a variable
   to prevent this quantity from being rewritten to 2 *)
Theorem nth_body_is_valid_aux:
  is_valid_fp_body (SUC (SUC n)) nth_body
Proof
  pure_once_rewrite_tac [is_valid_fp_body_def] >>
  gen_tac >>
  (* TODO: automate this *)
  Cases_on ‘x’ >> fs [] >>
  (* Expand *)
  fs [nth_body_def, bind_def] >>
  (* Explore all paths *)
  Cases_on ‘x'’ >> fs [] >>
  Cases_on ‘q’ >> fs [] >>
  Cases_on ‘u32_to_int r = 0’ >> fs [] >>
  Cases_on ‘u32_sub r (int_to_u32 1)’ >> fs [] >>
  disj2_tac >>
  (* This is hard *)
  qexists ‘\g x. case x of | INL _ => Fail Failure | INR i1 => Return (INR i1)’ >>
  qexists ‘INL (l, a)’ >>
  conj_tac
  >-(
    (* Prove that the body of h is valid *)
    pure_once_rewrite_tac [is_valid_fp_body_def] >>
    (* *)
    fs []) >>
  gen_tac >>
  (* Explore all paths *)
  Cases_on ‘g (INL (l,a))’ >> fs [] >>
  Cases_on ‘a'’ >> fs []
QED

Theorem nth_body_is_valid:
  is_valid_fp_body (SUC (SUC 0)) nth_body
Proof
  irule nth_body_is_valid_aux
QED

val nth_raw_def = Define ‘
  nth (ls : 't list_t) (i : u32) =
    case fix nth_body (INL (ls, i)) of
    | Fail e => Fail e
    | Diverge => Diverge
    | Return r =>
      case r of
      | INL _ => Fail Failure
      | INR x => Return x
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
  sg ‘fix nth_body (INL (ls,i)) = nth_body (fix nth_body) (INL (ls,i))’
  >- (simp_tac bool_ss [HO_MATCH_MP fix_fixed_eq nth_body_is_valid]) >>
  pop_assum (fn th => pure_asm_rewrite_tac [th]) >>
  (* Expand the body definition *)
  qspecl_assume [‘fix nth_body’, ‘(INL (ls, i))’] nth_body_def >>
  pop_assum (fn th => pure_rewrite_tac [th, LET_THM]) >>
  (* Explore all the paths - maybe we can be smarter, but this is fast and really easy *)
  fs [bind_def] >>
  Cases_on ‘ls’ >> fs [] >>
  Cases_on ‘u32_to_int i = 0’ >> fs [] >>
  Cases_on ‘u32_sub i (int_to_u32 1)’ >> fs [] >>
  Cases_on ‘fix nth_body (INL (l,a))’ >> fs [] >>
  Cases_on ‘a'’ >> fs []
QED

val _ = export_theory ()
