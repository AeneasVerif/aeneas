
(* TODO: Cleanup imports and scopes *)
Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Local Open Scope Primitives_scope.
Require Export Hashmap_Types.
Import Hashmap_Types.
Require Export Hashmap_Funs.
Import Hashmap_Funs.
Require Import Lia.
Require Import Coq.Unicode.Utf8.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Bool.Bool.
Require Import String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Unicode.Utf8.
Require Import ltac2_string_ident.

Module Primitives_Ext.

(*  +------------------------------+
    | Generic, intuitive utilities |
    +------------------------------+
*)

Lemma neg_impl {A B: Prop} : (A -> B) -> ~B -> ~A.
intuition. Qed.

Lemma neg_equiv {A B: Prop} : A <-> B -> ~A <-> ~B.
apply not_iff_compat. Qed.

Lemma orb_dis {A B: bool} : (A || B) = false <-> A = false /\ B = false.
destruct A, B ; intuition. Qed.

Lemma Ztrans_le_lt a b c : a < b -> b <= c -> a <= c.
intuition. Qed.

Lemma Zsucc_le_mono n m : n <= m -> n <= Z.succ m.
intuition. Qed.

Lemma Zpred_le_mono n m : n <= m -> Z.pred n <= m.
intuition. Qed.

Lemma Zle_antisym {n m} : (n <= m) <-> (m >= n).
intuition. Qed.

Lemma repeat_zero {T} {x: T} : repeat x 0 = [].
intuition. Qed.

Lemma cons_app_sing {T} {x: T} {t: list T} : x :: t = [x] ++ t.
intuition. Qed.

(*  +-------------------+
    | Monadic utilities |
    +-------------------+
*)

Definition res_of_opt {T} (o: option T) : result T :=
    match o with
    | Some n => Return n
    | None   => Fail_ Failure
    end.

Definition res_fmap {A B} (x: result A) (f: A -> B) : result B :=
    x' <- x; Return (f x').

Lemma res_bind_id {T} {x: result T} : (v <- x; Return v) = x.
Proof.
now destruct x ; simpl.
Qed.

(* Useful to simplify trivial bindings without mentioning f *)
Lemma res_bind_value {A B} {f: A -> result B} (x: A) :
    (v <- Return x ; f v) = f x.
Proof.
trivial.
Qed.

(*  +------------------+
    | Vector utilities |
    +------------------+
*)

(* Uses proof irrelevance so vector underlying lists can be equated *)
Lemma vec_list_inj {T} {a b: vec T} : (vec_to_list a = vec_to_list b) -> (a = b).
Proof.
destruct a, b.
apply ProofIrrelevanceTheory.subset_eq_compat.
Qed.

(* May be more clear as a lambda-term as it's a definition *)
Definition bounded_vec_push_back {T} (v: vec T) (x: T) (b: vec_length v < usize_max) : vec T.
Proof.
exists (x :: vec_to_list v).
simpl (List.length (x :: vec_to_list v)).
rewrite Nat2Z.inj_succ.
now apply (Zlt_le_succ _ _ b).
Defined.

(*
Lemma vec_push_success {T} (v: vec T) (x: T) (b: vec_length v < usize_max) :
  vec_push_back T v x = Return (bounded_vec_push_back v x b).
Proof.
remember (vec_push_back T v x) as W.
destruct W.
- f_equal
1: { unfold vec_push_back in HeqW. unfold bounded_vec_push_back. simpl. now exists v0. }

(* Contradiction from vec_push_back impl *)
exfalso.
unfold vec_push_back, vec_bind in Heqw.
set (l := vec_to_list v ++ x :: nil) in Heqw.
simpl in Heqw.
assert (Z.of_nat (length l) <= scalar_max Usize).
change l with (vec_to_list v ++ x :: nil).
rewrite app_length.
simpl.
rewrite Nat.add_1_r.
rewrite Nat2Z.inj_succ.
unfold vec_length in b.
now apply (Zlt_le_succ _ _ b).

remember (Sumbool.sumbool_of_bool (scalar_le_max Usize (Z.of_nat (length l)))) as s in Heqw.
destruct s.
- inversion Heqw.
- clear Heqs Heqw.
  apply (proj1 orb_dis) in e0.
  destruct e0.
  rewrite (proj2 (Z.leb_le _ _) H) in H1.
  inversion H1.
Qed.

Definition bounded_vec_push_back {T} (v: vec T) (x: T) (b: vec_length v < usize_max) : vec T :=
  exist _ (vec_to_list v :: x) ().
*)

(*  +----------------------+
    | Arithmetic utilities |
    +----------------------+
*)

Definition scalar_ty_of {ty} (n: scalar ty) := ty.

(* Comparisons *)

(* Not sure if it works well, but we want to e.g. simpl constants *)
#[export]
Hint Unfold usize_to_nat : core.

(* Uses proof irrelevance so scalars with the same number can be equated *)
Lemma scalar_Z_inj {ty} {n m: scalar ty} : (to_Z n = to_Z m) -> (n = m).
Proof.
destruct m, n.
apply ProofIrrelevanceTheory.subset_eq_compat.
Qed.

(* Usize lemmas can be generalized for positive scalars *)
Lemma usize_nat_inj {n m: usize} : (usize_to_nat n = usize_to_nat m) <-> (n = m).
Proof.
split ; intro H.
- unfold usize_to_nat in H.
  apply Z2Nat.inj in H.
  + apply scalar_Z_inj, H.
  + apply (proj2_sig n).
  + apply (proj2_sig m).
- now f_equal.
Qed.

(* It's a simple implication in "scalar_in_bounds_valid" *)
Lemma scalar_in_bounds_valid2 (ty: scalar_ty) (x: Z) :
  scalar_in_bounds ty x = true <-> scalar_min ty <= x <= scalar_max ty.
Proof.
split. now apply scalar_in_bounds_valid.
intro H.
unfold scalar_in_bounds, scalar_ge_min, scalar_le_max.
lia.
Qed.

(* This direct way of filling scalar may allow (relatively) simpler proofs *)
Definition mk_bounded_scalar ty (n: Z) (Hmin: scalar_min ty <= n) (Hmax: n <= scalar_max ty) : scalar ty :=
    exist _ n (conj Hmin Hmax).

Lemma mk_bounded_scalar_success ty (n: Z) (Hmin: scalar_min ty <= n) (Hmax: n <= scalar_max ty) :
    mk_scalar ty n = Return (mk_bounded_scalar ty n Hmin Hmax).
Proof.
unfold mk_scalar.
(* set (H := proj2 (scalar_in_bounds_valid2 ty n) (conj Hmin Hmax)).
   Ideally, want "now rewrite H" *)
remember (Sumbool.sumbool_of_bool (scalar_in_bounds ty n)) as b.
destruct b.
- now apply f_equal, scalar_Z_inj.
- exfalso.
  clear Heqb.
  rewrite (proj2 (scalar_in_bounds_valid2 ty n) (conj Hmin Hmax)) in e.
  inversion e.
Qed.

Definition bounded_scalar_succ {ty} (n: scalar ty) (p: to_Z n < scalar_max ty) : scalar ty :=
    let z := (to_Z n) in
    let p0 := Zsucc_le_mono (scalar_min ty) z (proj1 (proj2_sig n)) in
    let p1 := Zlt_le_succ z (scalar_max ty) p in
    mk_bounded_scalar _ (Z.succ z) p0 p1.

Lemma sc_succ_above_min {ty} (n: scalar ty) b : to_Z (bounded_scalar_succ n b) > scalar_min ty.
Proof.
assert (H := proj2_sig n).
simpl in *.
unfold to_Z.
lia.
Qed.

(* Should be generalized for any scalar *)
Lemma sc_succ_pred_eq (n: usize) {b} :
  usize_sub (bounded_scalar_succ n b) (1%usize) = Return n.
Proof.
unfold usize_sub, scalar_sub.
cut (to_Z (bounded_scalar_succ n b) - to_Z 1 %usize = to_Z n).
- intro H. rewrite H.
  assert (p := proj2_sig n).
  rewrite (mk_bounded_scalar_success Usize (to_Z n) (proj1 p) (proj2 p)).
  now apply f_equal, scalar_Z_inj.
- apply Z.pred_succ.
Qed.

Lemma mk_scalar_success (ty: scalar_ty) {n: Z} : (scalar_min ty <= n) -> (n <= scalar_max ty) -> ∃x, mk_scalar ty n = Return x.
Proof.
intros Hmin Hmax.
exists (mk_bounded_scalar ty n Hmin Hmax).
apply mk_bounded_scalar_success.
Qed.

Lemma usize_peano_ind (P: usize -> Prop) :
  P (0%usize) ->
  (∀n, ∀b: to_Z n < usize_max, P n -> P (bounded_scalar_succ n b)) ->
  ∀n, P n.
Proof.
intros base rec n.
destruct n.

(* We should exploit Peano induction on either Z with constraints or positives with upper bound *)
(* Here, we destruct the Z number of do the induction on natural numbers *)
destruct x.
3: { exfalso. simpl in *. lia. }
- set (x := exist (λ x0 : Z, scalar_min Usize <= x0 <= scalar_max Usize) 0 a).
  set (y := 0%usize).
  assert (H : x = y) by now apply usize_nat_inj.
  now apply (eq_ind y P base x).
- (* nat_ind: P P0 (f:∀n.Pn->PSn) -> ∀n.Pn *)
  admit.
Admitted.

(* Not trivial to generalize due to eq_refl in %usize. The zero and successor case are done to ease recursion *)
Lemma usize_nat_zero {n: usize} : (usize_to_nat n = 0%nat) <-> (n = 0 %usize).
Proof.
split ; intro H.
- now apply usize_nat_inj, H.
- now rewrite H.
Qed.

Lemma usize_nat_succ {n: usize} {m: nat} : (usize_to_nat n = S m) -> (∃i, usize_sub n 1 %usize = Return i).
Proof.
destruct n. intro I.
destruct x.
1: { inversion I. }
2: { inversion I. }

set (z := Z.pos p).
assert (Hmin: 0 <= z - 1) by lia.
assert (Hmax: z - 1 <= scalar_max Usize) by lia.

apply (mk_scalar_success Usize Hmin Hmax).
Qed.

Lemma usize_to_nonzero {n: usize} : n <> 0%usize <-> ∃m, usize_to_nat n = S m.
Proof.
split.
- intros H.
  assert (H':= neg_impl (proj1 usize_nat_inj) H).
  unfold usize_to_nat at 2 in H'. simpl in H'.
  exists (Nat.pred (usize_to_nat n)).
  destruct (usize_to_nat n).
  + contradiction.
  + now rewrite Nat.pred_succ.
- intros p H.
  destruct p.
  apply (f_equal usize_to_nat) in H.
  rewrite H0 in H.
  inversion H.
Qed.

(* There are may similar lemmas to be defined *)
Lemma scalar_eqb_eq {ty} {n m: scalar ty} :
    (n s= m) = true <-> n = m.
Proof.
unfold scalar_eqb.
split ; intro.
- now apply scalar_Z_inj, Z.eqb_eq.
- now apply Z.eqb_eq, f_equal.
Qed.

Lemma scalar_eqb_ne {ty} {n m: scalar ty} :
(n s= m) = false <-> n <> m.
Proof.
rewrite <-(not_true_iff_false (n s= m)).
apply (neg_equiv scalar_eqb_eq).
Qed.

(*  +--------------------------+
    | Reasoning on Z and lists |
    +--------------------------+
*)

(* This is the currently fostered approach : it reduces the number of needed lemmas and allows to easily leverage lia.
*)

Lemma S_scalar_bounds {ty} (n: scalar ty) :
  scalar_min ty <= to_Z n <= scalar_max ty.
Proof.
Admitted.

Lemma S_scalar_Z_inj {ty} (n m: scalar ty) :
  to_Z n = to_Z m -> n = m.
Proof.
Admitted.

Lemma S_eqb_Z {ty} (n m: scalar ty) :
  (n s= m) = (to_Z n =? to_Z m).
Proof.
trivial.
Qed.

Lemma S_mk_bounded ty (x: Z) :
  scalar_min ty <= x <= scalar_max ty ->
  ∃n, mk_scalar ty x = Return n
   /\ to_Z n = x.
Proof.
Admitted.

Lemma S_add_bounded {ty} (n m: scalar ty) :
  scalar_min ty <= (to_Z n) + (to_Z m) <= scalar_max ty ->
  ∃x, scalar_add n m = Return x
   /\ to_Z x = (to_Z n) + (to_Z m).
Proof.
Admitted.

Lemma S_sub_bounded {ty} (n m: scalar ty) :
  scalar_min ty <= (to_Z n) - (to_Z m) <= scalar_max ty ->
  ∃x, scalar_sub n m = Return x
   /\ to_Z x = (to_Z n) - (to_Z m).
Proof.
Admitted.

Lemma S_mul_bounded {ty} (n m: scalar ty) :
  scalar_min ty <= (to_Z n) * (to_Z m) <= scalar_max ty ->
  ∃x, scalar_mul n m = Return x
   /\ to_Z x = (to_Z n) * (to_Z m).
Proof.
Admitted.

Lemma S_div_bounded {ty} (n m: scalar ty) :
  to_Z m <> 0 ->
  scalar_min ty <= (to_Z n) / (to_Z m) <= scalar_max ty ->
  ∃x, scalar_div n m = Return x
   /\ to_Z x = (to_Z n) / (to_Z m).
Proof.
Admitted.

Lemma V_push_back_bounded {T} (v: vec T) (x: T) :
  vec_length v < usize_max ->
  ∃w, vec_push_back T v x = Return w
   /\ vec_to_list w = (vec_to_list v) ++ [x].
Proof.
Admitted.

Lemma usize_nat_to_Z (n: usize) : Z.of_nat (usize_to_nat n) = to_Z n.
Proof.
unfold usize_to_nat.
apply Z2Nat.id.
apply (S_scalar_bounds n).
Qed.

(*  +---------+
    | Tactics |
    +---------+
*)

Ltac push_scalar_bounds_tac a :=
  let Ha := fresh "Ha" in
  assert (Ha := S_scalar_bounds a);
  simpl in Ha.

(* fffffffffffff *)
Ltac VEC v x :=
  let wVal := constr:(vec_push_back _ v x) in

  assert (b: vec_length v < usize_max);
  match goal with [ |- vec_length v < usize_max ] =>
    push_scalar_bounds_tac v;
    simpl; try lia
  | _ =>
    
  let h := fresh "H" in
  let w := string_to_ident wStr in
  destruct (V_push_back_bounded v x b) as (w, h)
  clear b;

  let hr := fresh "Hr" in
  let hw := string_to_ident ("H" ++ wStr)%string in
  destruct h as (hr, hw);

  rewrite hr;
  clear hr;
  try rewrite res_bind_value;
  try rewrite res_bind_id

(* A first tactic which tries to abstract over the "S_sub_bounded" lemma. It :
 - Adds the boundary prerequisites as additional goals.
 - Tries to resolve them automatically with "lia", some "simpl" applications and the boundaries of a & b.
 - Rewrites the main goal with "S_sub_bounded" existential variable.
 - "clear" some hypothesis and try monadic simplifications.
 *)
Ltac rewrite_scalar_sub_tac a b xStr :=
  (* Getting the scalar type *)
  let T := constr:(scalar_ty_of a) in
  let xVal := constr:((to_Z a) - (to_Z b)) in

  (* Proving or supposing the lower bound *)
  let B12 := fresh "B1" in
  assert (B1: scalar_min T <= xVal);
  match goal with [ |- scalar_min T <= xVal ] =>
    push_scalar_bounds_tac a;
    push_scalar_bounds_tac b;
    simpl; try lia
  | [ |- _ ] =>

  (* Same for the upper bound
     TODO: Factorize with the part above,
     They are separated only because "lia" gives no partial progress on the proof.
  *)
  let B2 := fresh "B2" in
  assert (B2: xVal <= scalar_max T);
  match goal with [ |- xVal <= scalar_max T ] =>
    push_scalar_bounds_tac a;
    push_scalar_bounds_tac b;
    simpl; try lia
  | [ |- _ ] =>

  (* Apply the theorem about subtraction *)
  let H := fresh "H" in
  let x := string_to_ident xStr in
  destruct (S_sub_bounded a b (conj B1 B2)) as (x, H);

  (* Remove previous bounds *)
  clear B1 B2;

  (* Obtain the properties about the result *)
  let Hr := fresh "Hr" in
  let Hx := string_to_ident ("H" ++ xStr)%string in
  destruct H as (Hr, Hx);

  (* Refine the goal to then rewrite the expression.
     TODO: Match T to do only one try.
  *)
  rewrite Hr;
  clear Hr;

  (* Apply simplifications on the result monad *)
  try rewrite res_bind_value;
  try rewrite res_bind_id

  end end.

Tactic Notation "rewrite_scalar_sub" constr(a) constr(b) :=
  rewrite_scalar_sub_tac a b "x"%string.

Tactic Notation "rewrite_scalar_sub" constr(a) constr(b) "as" constr(x) :=
  rewrite_scalar_sub_tac a b x.

(* Other tactics, mainly implemented with copypaste *)

(* scalar_add *)
Ltac rewrite_scalar_add_tac a b xStr :=
  let T := constr:(scalar_ty_of a) in
  let xVal := constr:((to_Z a) + (to_Z b)) in

  let B1 := fresh "B1" in
  assert (B1: scalar_min T <= xVal);
  match goal with [ |- scalar_min T <= xVal ] =>
    push_scalar_bounds_tac a;
    push_scalar_bounds_tac b;
    simpl; try lia
  | [ |- _ ] =>

  let B2 := fresh "B2" in
  assert (B2: xVal <= scalar_max T);
  match goal with [ |- xVal <= scalar_max T ] =>
    push_scalar_bounds_tac a;
    push_scalar_bounds_tac b;
    simpl; try lia
  | [ |- _ ] =>

  let H := fresh "H" in
  let x := string_to_ident xStr in
  destruct (S_add_bounded a b (conj B1 B2)) as (x, H);
  clear B1 B2;

  let Hr := fresh "Hr" in
  let Hx := string_to_ident ("H" ++ xStr)%string in
  destruct H as (Hr, Hx);

  rewrite Hr;
  clear Hr;
  try rewrite res_bind_value;
  try rewrite res_bind_id
  end end.

Tactic Notation "rewrite_scalar_add" constr(a) constr(b) :=
  rewrite_scalar_add_tac a b "x"%string.

Tactic Notation "rewrite_scalar_add" constr(a) constr(b) "as" constr(x) :=
  rewrite_scalar_add_tac a b x.

(* scalar_mul *)
Ltac rewrite_scalar_mul_tac a b xStr :=
  let T := constr:(scalar_ty_of a) in
  let xVal := constr:((to_Z a) * (to_Z b)) in

  let B1 := fresh "B1" in
  assert (B1: scalar_min T <= xVal);
  match goal with [ |- scalar_min T <= xVal ] =>
    push_scalar_bounds_tac a;
    push_scalar_bounds_tac b;
    simpl; try lia
  | [ |- _ ] =>

  let B2 := fresh "B2" in
  assert (B2: xVal <= scalar_max T);
  match goal with [ |- xVal <= scalar_max T ] =>
    push_scalar_bounds_tac a;
    push_scalar_bounds_tac b;
    simpl; try lia
  | [ |- _ ] =>

  let H := fresh "H" in
  let x := string_to_ident xStr in
  destruct (S_mul_bounded a b (conj B1 B2)) as (x, H);
  clear B1 B2;

  let Hr := fresh "Hr" in
  let Hx := string_to_ident ("H" ++ xStr)%string in
  destruct H as (Hr, Hx);

  rewrite Hr;
  clear Hr;
  try rewrite res_bind_value;
  try rewrite res_bind_id
  end end.

Tactic Notation "rewrite_scalar_mul" constr(a) constr(b) :=
  rewrite_scalar_mul_tac a b "x"%string.

Tactic Notation "rewrite_scalar_mul" constr(a) constr(b) "as" constr(x) :=
  rewrite_scalar_mul_tac a b x.

(* scalar_div *)
Ltac rewrite_scalar_div_tac a b xStr :=
  let T := constr:(scalar_ty_of a) in
  let xVal := constr:((to_Z a) / (to_Z b)) in

  let B0 := fresh "B0" in
  assert (B0: to_Z b <> 0);
  match goal with [ |- to_Z b <> 0 ] =>
    push_scalar_bounds_tac b;
    simpl; try lia
  | [ |- _ ] =>

  let B1 := fresh "B1" in
  assert (B1: scalar_min T <= xVal);
  match goal with [ |- scalar_min T <= xVal ] =>
    push_scalar_bounds_tac a;
    push_scalar_bounds_tac b;
    simpl; try lia
  | [ |- _ ] =>

  let B2 := fresh "B2" in
  assert (B2: xVal <= scalar_max T);
  match goal with [ |- xVal <= scalar_max T ] =>
    push_scalar_bounds_tac a;
    push_scalar_bounds_tac b;
    simpl; try lia
  | [ |- _ ] =>

  let H := fresh "H" in
  let x := string_to_ident xStr in
  destruct (S_div_bounded a b B0 (conj B1 B2)) as (x, H);
  clear B0 B1 B2;

  let Hr := fresh "Hr" in
  let Hx := string_to_ident ("H" ++ xStr)%string in
  destruct H as (Hr, Hx);

  rewrite Hr;
  clear Hr;
  try rewrite res_bind_value;
  try rewrite res_bind_id
  end end end.

Tactic Notation "rewrite_scalar_div" constr(a) constr(b) :=
  rewrite_scalar_div_tac a b "x"%string.

Tactic Notation "rewrite_scalar_div" constr(a) constr(b) "as" constr(x) :=
  rewrite_scalar_div_tac a b x.

(* vec_push_back *)
Ltac rewrite_vec_push_back_tac v x wStr :=
  let wVal := constr:(vec_push_back _ v x) in

  let B := fresh "B" in
  assert (B: vec_length v < usize_max);
  match goal with [ |- vec_length v < usize_max ] =>
    push_scalar_bounds_tac v;
    simpl; try lia
  | [ |- _ ] =>

  let H := fresh "H" in
  let w := string_to_ident wStr in
  destruct (bounded_vec_push_back v x B) as (w, H);
  clear B;

  let Hr := fresh "Hr" in
  let Hw := string_to_ident ("H" ++ wStr)%string in
  destruct H as (Hr, Hw);

  rewrite Hr;
  clear Hr;
  try rewrite res_bind_value;
  try rewrite res_bind_id
  end.

Tactic Notation "rewrite_vec_push_back" constr(v) constr(x) :=
rewrite_vec_push_back_tac v x "w"%string.

Tactic Notation "rewrite_vec_push_back" constr(v) constr(x) "as" constr(w) :=
  rewrite_vec_push_back_tac v x w.

(*  +-------+
    | Tests |
    +-------+
*)

Lemma vec_test {T} : 

Lemma add_assoc {a} :
  match (x <- usize_sub a (1%usize); Return x) with
  | Return v => ∃n, (1 + n)%nat = usize_to_nat a
  | Fail_ OutOfFuel => False
  | Fail_ Failure   => True
  end.
Proof.

(* Trade-off between String and List notations *)
rewrite_scalar_sub a (1%usize) as "w"%string.
- admit.
- admit.
Admitted.



Lemma MP {A B}: A -> (A -> B) -> B.
Admitted.

Ltac make_mp :=
  let h := fresh "hyp" in
  assert (h : True) by auto;
  match goal with
  | [ |- True ] => ()
  | _ =>

  apply (MP h)

  end.

Lemma MP2 {B}: (True -> B) -> B.

make_mp.






















End Primitives_Ext.
