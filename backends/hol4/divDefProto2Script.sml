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
  (fix_fuel (0 : num) (f : ('a -> 'a result) -> 'a -> 'a result) (x : 'a) : 'a result = Diverge) ∧
  (fix_fuel (SUC n) (f : ('a -> 'a result) -> 'a -> 'a result) (x : 'a) : 'a result = f (fix_fuel n f) x)
’

val fix_fuel_P_def = Define ‘
  fix_fuel_P f x n = ~(is_diverge (fix_fuel n f x))
’

val fix_def = Define ‘
  fix (f : ('a -> 'a result) -> 'a -> 'a result) (x : 'a) : 'a result =
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

(*
Type ft = ``: 'a -> ('a result + (num # num # 'a))``

val fix_fuel_def = Define ‘
  (fix_fuel (0 : num) (fs : ('a ft) list)
            (i : num) (x : 'a) : 'a result = Diverge) ∧
  
  (fix_fuel (SUC n) fs i x =
    case EL i fs x of
    | INL r => r
    | INR (j, k, y) =>
      case fix_fuel n fs j y of
      | Fail e => Fail e
      | Diverge => Diverge
      | Return z =>
        fix_fuel n fs k z)
’

val fix_fuel_P_def = Define ‘
  fix_fuel_P fs i x n = ~(is_diverge (fix_fuel n fs i x))
’

val fix_def = Define ‘
  fix (fs : ('a ft) list) (i : num) (x : 'a) : 'a result =
    if (∃ n. fix_fuel_P fs i x n)
    then fix_fuel ($LEAST (fix_fuel_P fs i x)) fs i x
    else Diverge
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

  (*(* Use the validity property *)
  last_assum (qspec_assume ‘x’) >> (* TODO: consume? *) *)

  (*pop_assum ignore_tac >> (* TODO: not sure *) *)
  Induct_on ‘N’ >- fs [eval_ftree_def] >>
  rw [] >>
  rw [eval_ftree_def] >>
  Cases_on ‘h x’ >> fs [] >>
  Cases_on ‘y’ >> fs [] >>
  Cases_on ‘y'’ >> fs [] >>
  
  last_assum (qspec_assume ‘q’) >>
  Cases_on ‘fix_fuel n f q’ >> fs [] >>
  
  Cases_on ‘N’ >> fs [eval_ftree_def] >>
  
  Cases_on ‘y’ >> fs [] >>
  Cases_on ‘y'’ >> fs [] >>
  rw [] >>
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



Type ft = ``: ('a -> 'a result) -> 'a -> ('a result + (num # 'a))``

val fix_fuel_def = Define ‘
  (fix_fuel (0 : num) (fs : ('a ft) list) (g : 'a -> 'a result)
            (i : num) (x : 'a) : 'a result = Diverge) ∧
  
  (fix_fuel (SUC n) fs g i x =
    case EL i fs g x of
    | INL r => r
    | INR (j, y) =>
      case g y of
      | Fail e => Fail e
      | Diverge => Diverge
      | Return z => fix_fuel n fs g j z)
’

val fix_fuel_def = Define ‘
  (fix_fuel (0 : num) (fs : ('a ft) list) g (i : num) (x : 'a) : 'a result = Diverge) ∧
  
  (fix_fuel (SUC n) fs g i x =
    case EL i fs x of
    | INL r => r
    | INR (j, y) =>
      case g y of
      | Fail e => Fail e
      | Diverge => Diverge
      | Return z => fix_fuel n fs g j z)
’

val fix_fuel_def = Define ‘
  (fix_fuel (0 : num) (f : ('a -> 'a result) -> 'a -> 'a result) (x : 'a) : 'a result = Diverge) ∧
  (fix_fuel (SUC n) (f : ('a -> 'a result) -> 'a -> 'a result) (x : 'a) : 'a result = f (fix_fuel n f) x)
’

val fix_fuel_P_def = Define ‘
  fix_fuel_P f x n = ~(is_diverge (fix_fuel n f x))
’

val fix_def = Define ‘
  fix (f : ('a -> 'a result) -> 'a -> 'a result) (x : 'a) : 'a result =
    if (∃ n. fix_fuel_P f x n) then fix_fuel ($LEAST (fix_fuel_P f x)) f x else Diverge
’

(*Datatype:
  ftree = Rec (('a -> ('a result + ('a # num))) # ftree list) | NRec ('a -> 'a result)
End

Type frtree = ``: ('b -> ('b result + ('a # num))) list``
Type ftree = “: ('a, 'b) frtree # ('b result + ('a # num))”
*)

val eval_ftree_def = Define ‘
  (eval_ftree 0 (g : 'a -> 'a result)
    (fs : ('a -> ('a result + ('a # num))) list) x = Diverge) ∧

  (eval_ftree (SUC n) g fs x =
    case x of
    | INL r => r
    | INR (y, i) =>
      case g y of
      | Fail e => Fail e
      | Diverge => Diverge
      | Return z =>
        let f = EL i fs in
        eval_ftree n g fs (f z))
’

Theorem fix_fuel_mono:
  ∀N fs i.
  let f = (\g x. eval_ftree N g fs (INR (x, i))) in
  ∀n x. fix_fuel_P f x n ⇒
  ∀ m. n ≤ m ⇒ fix_fuel n f x = fix_fuel m f x
Proof
  Induct_on ‘N’
  >-(
    fs [eval_ftree_def] >>

  ntac 2 strip_tac >>
  Induct_on ‘n’ >> rpt strip_tac
  >- (fs [fix_fuel_P_def, is_diverge_def, fix_fuel_def]) >>
  Cases_on ‘m’ >- int_tac >> fs [] >>
  fs [is_valid_fp_body_def] >>
  fs [fix_fuel_P_def, is_diverge_def, fix_fuel_def] >>


val is_valid_fp_body_def = Define ‘
  is_valid_fp_body (f : ('a -> 'b result) -> 'a -> 'b result) =
    (∃N ft. ∀x g. f g x = eval_ftree N g ft (x, i))
’

val eval_ftree_def = Define ‘
  (eval_ftree 0 (g : 'a -> 'b result)
    (fs : ('b -> ('b result + ('a # num))) list, x : 'b result + ('a # num)) = Diverge) ∧
  
  (eval_ftree (SUC n) g (fs, x) =
    case x of
    | INL r => r
    | INR (y, i) =>
      case g y of
      | Fail e => Fail e
      | Diverge => Diverge
      | Return z =>
        let f = EL i fs in
        eval_ftree n g (fs, f z))
’

val is_valid_fp_body_def = Define ‘
  is_valid_fp_body (f : ('a -> 'b result) -> 'a -> 'b result) =
    (∃N ft h. ∀x g. f g x = eval_ftree N g (ft, h x))
’

Theorem fix_fuel_mono:
  let f = (\x. eval_ftree N g (ft, h x)) in
  ∀n x. fix_fuel_P f x n ⇒
   ∀ m. n ≤ m ⇒ fix_fuel n f x = fix_fuel m f x
Proof


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

  (*(* Use the validity property *)
  last_assum (qspec_assume ‘x’) >> (* TODO: consume? *) *)

  (*pop_assum ignore_tac >> (* TODO: not sure *) *)
  Induct_on ‘N’ >- fs [eval_ftree_def] >>
  rw [] >>
  rw [eval_ftree_def] >>
  Cases_on ‘h x’ >> fs [] >>
  Cases_on ‘y’ >> fs [] >>
  Cases_on ‘y'’ >> fs [] >>
  
  last_assum (qspec_assume ‘q’) >>
  Cases_on ‘fix_fuel n f q’ >> fs [] >>
  
  Cases_on ‘N’ >> fs [eval_ftree_def] >>
  
  Cases_on ‘y’ >> fs [] >>
  Cases_on ‘y'’ >> fs [] >>
  rw [] >>
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


val length_ftree = “
(
  [
    (\n. INL (return (1 + n)))
  ],
  (case ls of
   | ListCons x tl =>
     INR (tl, 0)
   | ListNil => INL (return 0))
) : ('a list_t, int) ftree
”

val eval_length_ftree = mk_icomb (“eval_ftree 1 g”, length_ftree)

Theorem length_body_eq:
  eval_ftree (SUC (SUC 0)) g
  (
    [
      (\n. INL (Return (1 + n)))
    ],
    (case ls of
     | ListCons x tl =>
       INR (tl, 0)
     | ListNil => INL (Return 0))
  ) =
  case ls of
  | ListCons x tl =>
    do
      n <- g tl;
      Return (1 + n)
    od
  | ListNil => Return 0
Proof
  fs [eval_ftree_def, bind_def] >>
  Cases_on ‘ls’ >> fs []
QED

val eval_ftree_def = Define ‘
  eval_ftree 0 (fs : ('a, 'b) ftree) (g : 'a -> 'b result) (x : 'b result + ('a # num)) = Diverge ∧
  
  eval_ftree (SUC n) fs g x =
    case x of
    | INL r => r
    | INR (y, i) =>
      case g y of
      | Fail e => Fail e
      | Diverge => Diverge
      | Return z =>
        let f = EL i fs in
        eval_ftree n fs g (f z)
’

val length_body_funs_def = Define 

“
[
  (\ls. case ls of
   | ListCons x tl =>
     INR (tl, 1)
   | ListNil => INL (return 0)),
  (\n. INL (return (1 + n)))
]
”



“:('a, 'b) FT”

Define 

val nth_body = Define ‘
  

’

“INL”
“INR”

“
  Rec (
    case ls of
    | ListCons x tl =>
      do
        INR (tl, 0)
      od
    | ListNil => INL (return 0),
    [NRec (\n. return (1 + n))])
”

“
  case ls of
  | ListCons x tl =>
    if u32_to_int i = (0:int)
    then (Return x)
    else
      do
      i0 <- u32_sub i (int_to_u32 1);
      y <- nth tl i0;
      return y
      od
  | ListNil => Fail Failure
”


“:'a + 'b”
“:'a # 'b”

(*** Encoding of a function *)
Datatype:
  ('a, 'b) test = Return ('a -> 'b)
End

val tyax =
      new_type_definition ("three",
        Q.prove(`?p. (\(x,y). ~(x /\ y)) p`, cheat))

val three_bij = define_new_type_bijections
                      {name="three_tybij", ABS="abs3", REP="rep3", tyax=tyax}
type_of “rep3”
type_of “abs3”

m “”

                Q.EXISTS_TAC `(F,F)` THEN GEN_BETA_TAC THEN REWRITE_TAC []));

“Return (\x. x)”

Datatype:
  ftree = Rec ('a -> ('a result + ('a # ftree))) | NRec ('a -> 'a result)
End

Datatype:
  'a ftree = Rec ('a -> ('a result + ('a # ftree))) | NRec ('a -> 'a result)
End

Datatype:
  ftree = Rec ('a -> ('a result + ('a # ftree))) | NRec ('a -> 'a result)
End

Datatype:
  result = Return 'a | Fail error | Diverge
End

Type M = ``: 'a result``


val fix_def = Define ‘
  fix (f : ('a -> 'b result) -> 'a -> 'b result) (x : 'a) : 'b result =
    if (∃ n. fix_fuel_P f x n) then fix_fuel ($LEAST (fix_fuel_P f x)) f x else Diverge
’

val _ = export_theory ()
