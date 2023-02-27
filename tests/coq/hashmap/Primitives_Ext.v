
(* TODO: Cleanup imports and scopes *)
Require Export Primitives.
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
Require ltac2_string_to_ident.
Require ltac2_ident_to_string.

Module Primitives_Ext.

(* Improves "rewrite", which was before missing some terms without any good reason. *)
Set Keyed Unification.

Ltac string_to_ident s := ltac2_string_to_ident.string_to_ident s.

Notation ident_to_string id :=
  (ltac2_ident_to_string.ident_to_string id) (only parsing).

(*  +------------------------------+
    | Generic, intuitive utilities |
    +------------------------------+
*)

Lemma neg_impl {A B: Prop} : (A → B) → ~B → ~A.
intuition. Qed.

Lemma neg_equiv {A B: Prop} : A ↔ B → ~A ↔ ~B.
apply not_iff_compat. Qed.

Lemma orb_dis {A B: bool} : (A || B) = false ↔ A = false ∧ B = false.
destruct A, B ; intuition. Qed.

(* TODO: Is there a "≤" notation for "Z" (or only "Nat") ? *)
Lemma Ztrans_le_lt a b c : a < b → b <= c → a <= c.
intuition. Qed.

Lemma Zsucc_le_mono n m : n <= m → n <= Z.succ m.
intuition. Qed.

Lemma Zpred_le_mono n m : n <= m → Z.pred n <= m.
intuition. Qed.

Lemma Zle_antisym {n m} : (n <= m) ↔ (m >= n).
intuition. Qed.

Lemma Zeqb_sym {n m} : (n =? m) = (m =? n).
remember (n =? m) as B ; induction B ;
remember (m =? n) as C ; induction C ;
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

Definition res_fmap {A B} (x: result A) (f: A → B) : result B :=
    x' <- x; Return (f x').

Lemma res_bind_id {T} {x: result T} : (v <- x; Return v) = x.
Proof.
now destruct x ; simpl.
Qed.

(* Useful to simplify trivial bindings without mentioning f *)
Lemma res_bind_value {A B} {f: A → result B} (x: A) :
    (v <- Return x ; f v) = f x.
Proof.
trivial.
Qed.

(*  +------------------+
    | Vector utilities |
    +------------------+
*)

(* Uses proof irrelevance so vector underlying lists can be equated *)
Lemma vec_list_inj {T} {a b: vec T} : (vec_to_list a = vec_to_list b) → (a = b).
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

(* Generic lemma that can be defined for all primitive functions. *)
Lemma vec_push_back_fuel {T} (v: vec T) (x: T) :
  vec_push_back _ v x <> Fail_ OutOfFuel.
Proof.
unfold vec_push_back, vec_bind.
rewrite res_bind_value.
set (w := vec_to_list v ++ [x]).
destruct (Sumbool.sumbool_of_bool
(scalar_le_max Usize (Z.of_nat (Datatypes.length w)))) ; discriminate.
Qed.

Fixpoint replace_list {T} (l: list T) (n: nat) (x: T) :=
  match l with
  | [] => []
  | y :: t => match n with
    | 0%nat => x :: t
    | S n'  => y :: replace_list t n' x
    end
  end.

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
Lemma scalar_Z_inj {ty} {n m: scalar ty} : (to_Z n = to_Z m) → (n = m).
Proof.
destruct m, n.
apply ProofIrrelevanceTheory.subset_eq_compat.
Qed.

(* Usize lemmas can be generalized for positive scalars *)
Lemma usize_nat_inj {n m: usize} : (usize_to_nat n = usize_to_nat m) ↔ (n = m).
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
  scalar_in_bounds ty x = true ↔ scalar_min ty <= x <= scalar_max ty.
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

Lemma mk_scalar_success (ty: scalar_ty) {n: Z} : (scalar_min ty <= n) → (n <= scalar_max ty) → ∃x, mk_scalar ty n = Return x.
Proof.
intros Hmin Hmax.
exists (mk_bounded_scalar ty n Hmin Hmax).
apply mk_bounded_scalar_success.
Qed.

Lemma usize_peano_ind (P: usize → Prop) :
  P (0%usize) →
  (∀n, ∀b: to_Z n < usize_max, P n → P (bounded_scalar_succ n b)) →
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
- (* nat_ind: P P0 (f:∀n.Pn→PSn) → ∀n.Pn *)
  admit.
Admitted.

(* Not trivial to generalize due to eq_refl in %usize. The zero and successor case are done to ease recursion *)
Lemma usize_nat_zero {n: usize} : (usize_to_nat n = 0%nat) ↔ (n = 0 %usize).
Proof.
split ; intro H.
- now apply usize_nat_inj, H.
- now rewrite H.
Qed.

Lemma usize_nat_succ {n: usize} {m: nat} : (usize_to_nat n = S m) → (∃i, usize_sub n 1 %usize = Return i).
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

Lemma usize_to_nonzero {n: usize} : n <> 0%usize ↔ ∃m, usize_to_nat n = S m.
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
    (n s= m) = true ↔ n = m.
Proof.
unfold scalar_eqb.
split ; intro.
- now apply scalar_Z_inj, Z.eqb_eq.
- now apply Z.eqb_eq, f_equal.
Qed.

Lemma scalar_eqb_ne {ty} {n m: scalar ty} :
(n s= m) = false ↔ n <> m.
Proof.
rewrite <-(not_true_iff_false (n s= m)).
apply (neg_equiv scalar_eqb_eq).
Qed.

Lemma Z_eqb_ne {n m: Z} :
(n =? m) = false ↔ n <> m.
Proof.
rewrite <-(not_true_iff_false (n =? m)).
apply (neg_equiv (Z.eqb_eq _ _)).
Qed.

Lemma scalar_sub_fuel {ty} (n m: scalar ty) :
  scalar_sub n m <> Fail_ OutOfFuel.
Proof.
unfold scalar_sub, mk_scalar.
destruct (Sumbool.sumbool_of_bool (scalar_in_bounds ty (to_Z n - to_Z m))) ; discriminate.
Qed.

(*  +--------------------------+
    | Reasoning on Z and lists |
    +--------------------------+
*)

(* This is the currently fostered approach : it reduces the number of needed lemmas and allows to easily leverage lia.
*)

(* Small helper. TODO: taken from below, remove redundancy. *)
Ltac ltac_new_id2 prefix id suffix :=
  let old := constr:(ident_to_string id) in
  let new := constr:((prefix ++ old ++ suffix)%string) in
  string_to_ident new.

(* Written as a tactic to exploit proof by rewriting - I may miss another way: very hacky and fragile *)
Ltac scalar_success_tac X B :=
  let H := fresh in
  unfold mk_scalar;
  remember (Sumbool.sumbool_of_bool (scalar_in_bounds _ X)) as H;
  destruct H as [H|H];
  lazymatch goal with
  | [ H: _ = true |- _ ] =>
    now apply f_equal, scalar_Z_inj
  | [ H: _ = false |- _ ] =>
    exfalso;
    let Heq := ltac_new_id2 "Heq"%string H ""%string in
    clear Heq;
    now rewrite (proj2 (scalar_in_bounds_valid2 _ X) B) in H
  end.

Lemma S_scalar_bounds {ty} (n: scalar ty) :
  scalar_min ty <= to_Z n <= scalar_max ty.
Proof.
exact (proj2_sig n).
Qed.

Lemma V_vec_bounds {T} (v: vec T) :
  usize_min <= vec_length v <= usize_max.
Proof.
exact (vec_len_in_usize v).
Qed.

Lemma S_scalar_Z_inj {ty} (n m: scalar ty) :
  to_Z n = to_Z m → n = m.
Proof.
destruct m, n.
apply ProofIrrelevanceTheory.subset_eq_compat.
Qed.

Lemma S_mk_bounded ty (x: Z) :
  scalar_min ty <= x <= scalar_max ty →
  ∃n, mk_scalar ty x = Return n
   ∧ to_Z n = x.
Proof.
intro B.
pose (n := (exist _ x B): scalar ty).
exists n.
split. 2: reflexivity.
scalar_success_tac x B.
Qed.

Lemma S_add_bounded {ty} (n m: scalar ty) :
  scalar_min ty <= (to_Z n) + (to_Z m) <= scalar_max ty →
  ∃x, scalar_add n m = Return x
   ∧ to_Z x = (to_Z n) + (to_Z m).
Proof.
intro B.
pose (x := (exist _ (to_Z n + to_Z m) B): scalar ty).
exists x.
split. 2: reflexivity.
unfold scalar_add.
scalar_success_tac (to_Z n + to_Z m) B.
Qed.

(* Alternative shape for the lemma above. *)
Lemma S_add_bounded2 {T} (n m: scalar T) :
  scalar_min T <= (to_Z n) + (to_Z m) <= scalar_max T →
  match scalar_add n m with
  | Return x => to_Z x = (to_Z n) + (to_Z m)
  | Fail_ _ => False
  end.
Proof.
intro H.
destruct (S_add_bounded n m H) as (x, (eq, P)).
now rewrite eq.
Qed.

Lemma S_sub_bounded {ty} (n m: scalar ty) :
  scalar_min ty <= (to_Z n) - (to_Z m) <= scalar_max ty →
  ∃x, scalar_sub n m = Return x
   ∧ to_Z x = (to_Z n) - (to_Z m).
Proof.
(* TODO: Factorize common stuff more *)
intro B.
pose (x := (exist _ (to_Z n - to_Z m) B): scalar ty).
exists x.
split. 2: reflexivity.
unfold scalar_sub.
scalar_success_tac (to_Z n - to_Z m) B.
Qed.

Lemma S_mul_bounded {ty} (n m: scalar ty) :
  scalar_min ty <= (to_Z n) * (to_Z m) <= scalar_max ty →
  ∃x, scalar_mul n m = Return x
   ∧ to_Z x = (to_Z n) * (to_Z m).
Proof.
intro B.
pose (x := (exist _ (to_Z n * to_Z m) B): scalar ty).
exists x.
split. 2: reflexivity.
unfold scalar_mul.
scalar_success_tac (to_Z n * to_Z m) B.
Qed.

Lemma S_div_bounded {ty} (n m: scalar ty) :
  to_Z m <> 0 ∧ scalar_min ty <= (to_Z n) / (to_Z m) <= scalar_max ty →
  ∃x, scalar_div n m = Return x
   ∧ to_Z x = (to_Z n) / (to_Z m).
Proof.
intro B.
destruct B as (B0, B1).
pose (x := (exist _ (to_Z n / to_Z m) B1): scalar ty).
exists x.
split. 2: reflexivity.
unfold scalar_div.
remember (to_Z m =? 0) as b.
destruct b. 1: intuition.
scalar_success_tac (to_Z n / to_Z m) B1.
Qed.

Lemma S_rem_bounded {ty} (n m: scalar ty) :
  scalar_min ty <= Z.rem (to_Z n) (to_Z m) <= scalar_max ty →
  ∃x, scalar_rem n m = Return x
   ∧ to_Z x = Z.rem (to_Z n) (to_Z m).
Proof.
intro B.
pose (x := (exist _ (Z.rem (to_Z n) (to_Z m)) B): scalar ty).
exists x.
split. 2: reflexivity.
unfold scalar_rem.
scalar_success_tac (Z.rem (to_Z n) (to_Z m)) B.
Qed.

(* TODO: Complete proofs. *)
Lemma V_push_back_bounded {T} (v: vec T) (x: T) :
  vec_length v < usize_max →
  ∃w, vec_push_back T v x = Return w
   ∧ vec_to_list w = (vec_to_list v) ++ [x].
Proof.
Admitted.

Lemma V_index_mut_fwd_bounded {T} (v: vec T) (i: usize) :
  to_Z i < vec_length v →
  ∃x, vec_index_mut_fwd T v i = Return x
   ∧ nth_error (vec_to_list v) (usize_to_nat i) = Some x.
Proof.
Admitted.

Lemma V_index_mut_back_bounded {T} (v: vec T) (i: usize) (x: T) :
  to_Z i < vec_length v →
  ∃w, vec_index_mut_back T v i x = Return w
   ∧ vec_to_list w = replace_list (vec_to_list v) (usize_to_nat i) x.
Proof.
Admitted.

Lemma usize_nat_to_Z (n: usize) : Z.of_nat (usize_to_nat n) = to_Z n.
Proof.
unfold usize_to_nat.
apply Z2Nat.id.
apply (S_scalar_bounds n).
Qed.

(* Issues with trying to fit destruct_eqb in a monadic lemma :
- No premisses.
- Not triggered on a result type.
- No equation of the shape "∃x. ... = Return x".
- No postcondition rewrite rule.
At best, it only provides an "apply".

Where should it fit ?
- Separate the function accessing the 'head variable'.
- Add a typeclass to apply on 'head variable' more generally than the whole goal.

New roles for high-level tactics ?
- "oaSimpl" something applied recursively which simplifies & uniformises the context (including the goal).
- "oaStep" something applied once on the 'head variable' to progress on the goal.

It means that "oaStep" must be complexified to accomodate the 'match' shape.
*)
Lemma S_eqb_dec {ty} (n m: scalar ty) :
  True →
  ∃x, scalar_eqb n m = x
   ∧ (x = true ∧ n = m) ∨ (x = false ∧ n ≠ m).
Proof.
Admitted.

(* An apply + rewrite of the lemma above gives us grosso modo that, which is very close to "Z.eqb_dec" :

We want non-monadic lemmas which apply to the HV in "aeStep", and perhaps corresponding simplifying lemmas in "aeSimpl" :
- "aeStep" intro "Z.eqb_dec" ("bounded hyp" TC ?).
- "aeSimpl" destruct equations on booleans :
  + "?A = true ↔ ?B" ~> destruct A, get true ⊢ B and false ⊢ ¬B.
*)
Lemma S_eqb_dec2 {ty} (n m: scalar ty) :
  (n s= m) = true ↔ n = m.
Proof.
Admitted.

(*  +-------------------+
    | Tactics - helpers |
    +-------------------+
*)

(* TODO:
 - Induction vectors
 - Cleanup the ugly code
*)

(* Small helper to create a new id by encompassing one between two strings. *)
Ltac ltac_new_id prefix id suffix :=
  let old := constr:(ident_to_string id) in
  let new := constr:((prefix ++ old ++ suffix)%string) in
  string_to_ident new.

(* Registers the bounds of the given scalar in a new hypothesis. *)
Ltac intro_scalar_bounds n :=
  let H_id := ltac_new_id ""%string n "_bounds"%string in
  let H := fresh H_id in
  assert (H := S_scalar_bounds n);
  simpl in H.

(* Registers the bounds of the given vector in a new hypothesis. *)
Ltac intro_vec_bounds v :=
  let H_id := ltac_new_id ""%string v "_bounds"%string in
  let H := fresh H_id in
  assert (H := V_vec_bounds v);
  simpl in H.

(* Does not create an identifier based on n.
   Used for unknown scalar parameters which could be expressions.
   TODO: Match identifiers VS expressions to know which tactic to call.
   TODO: Search if the bounds is already in the hypothesis.
*)
Ltac intro_scalar_anon_bounds n :=
  let H := fresh in
  assert (H := S_scalar_bounds n);
  simpl in H.

Example example_intro_scalar_bounds (a: usize) : to_Z a <= usize_max.
Proof.
pose (a_bounds := tt).
intro_scalar_bounds a.
intro_scalar_anon_bounds (1%usize).
exact (proj2 a_bounds0).
Qed.

(*  +---------------------------+
    | Tactics - scalar rewrites |
    +---------------------------+
*)

(* A first tactic which tries to abstract over the "S_sub_bounded" lemma. It :
 - Adds the boundary prerequisites as additional goals.
 - Tries to resolve them automatically with "lia", some "simpl" applications and the boundaries of a & b.
 - Rewrites the main goal with "S_sub_bounded" existential variable.
 - "clear" some hypothesis and try monadic simplifications.
 *)
Ltac rewrite_scalar_sub_tac a b x :=
  (* Getting the scalar type *)
  let T := constr:(scalar_ty_of a) in
  let xVal := constr:((to_Z a) - (to_Z b)) in

  (* Proving or supposing the lower bound, using "lazymatch" by default to avoid backtracking in case of errors in a branch *)
  let B1 := fresh "B1" in
  assert (B1: scalar_min T <= xVal);
  lazymatch goal with [ |- scalar_min T <= xVal ] =>
    intro_scalar_anon_bounds a;
    intro_scalar_anon_bounds b;
    simpl; try lia
  | [ |- _ ] =>

  (* TODO: Avoid this redundancy (due to "lia" doing no partial progress) *)
  let B2 := fresh "B2" in
  assert (B2: xVal <= scalar_max T);
  lazymatch goal with [ |- xVal <= scalar_max T ] =>
    intro_scalar_anon_bounds a;
    intro_scalar_anon_bounds b;
    simpl; try lia
  | [ |- _ ] =>

  (* Apply the theorem about subtraction *)
  let H := fresh "H" in
  destruct (S_sub_bounded a b (conj B1 B2)) as (x, H);

  (* Remove previous bounds *)
  clear B1 B2;
  (* Obtain the properties about the result *)
  let Hx := ltac_new_id "H"%string x ""%string in
  let Hr := fresh "Hr" in
  destruct H as (Hr, Hx);

  (* Rewrite the expression then remove the rewriting rule *)
  rewrite Hr;
  clear Hr;
  
  (* Add bounds of the new scalar to the context *)
  intro_scalar_bounds x;

  (* Apply simplifications on the result monad *)
  try rewrite res_bind_value;
  try rewrite res_bind_id
  end end.

Tactic Notation "rewrite_scalar_sub" constr(a) constr(b) "as" simple_intropattern(x) :=
  rewrite_scalar_sub_tac a b x.

Tactic Notation "rewrite_scalar_sub" constr(a) constr(b) :=
  let x := fresh "x" in
  rewrite_scalar_sub_tac a b x.

Tactic Notation "rewrite_scalar_sub" "as" simple_intropattern(x) :=
  lazymatch goal with [ |- context[ scalar_sub ?A ?B ]] =>
    rewrite_scalar_sub A B as x
  end.

(* Other tactics, mainly implemented with copypaste *)

(* scalar_add *)
Ltac rewrite_scalar_add_tac a b x :=
  let T := constr:(scalar_ty_of a) in
  let xVal := constr:((to_Z a) + (to_Z b)) in

  let B1 := fresh "B1" in
  assert (B1: scalar_min T <= xVal);
  lazymatch goal with [ |- scalar_min T <= xVal ] =>
    intro_scalar_anon_bounds a;
    intro_scalar_anon_bounds b;
    simpl; try lia
  | [ |- _ ] =>

  let B2 := fresh "B2" in
  assert (B2: xVal <= scalar_max T);
  lazymatch goal with [ |- xVal <= scalar_max T ] =>
    intro_scalar_anon_bounds a;
    intro_scalar_anon_bounds b;
    simpl; try lia
  | [ |- _ ] =>

  let H := fresh "H" in
  destruct (S_add_bounded a b (conj B1 B2)) as (x, H);
  clear B1 B2;

  let Hx := ltac_new_id "H"%string x ""%string in
  let Hr := fresh "Hr" in
  destruct H as (Hr, Hx);

  rewrite Hr;
  clear Hr;
  intro_scalar_bounds x;

  try rewrite res_bind_value;
  try rewrite res_bind_id
  end end.

Tactic Notation "rewrite_scalar_add" constr(a) constr(b) :=
  let x := fresh "x" in
  rewrite_scalar_add_tac a b x.

Tactic Notation "rewrite_scalar_add" constr(a) constr(b) "as" simple_intropattern(x) :=
  rewrite_scalar_add_tac a b x.

Tactic Notation "rewrite_scalar_add" "as" simple_intropattern(x) :=
  lazymatch goal with [ |- context[ scalar_add ?A ?B ]] =>
    rewrite_scalar_add A B as x
  end.

(* scalar_mul *)
Ltac rewrite_scalar_mul_tac a b x :=
  let T := constr:(scalar_ty_of a) in
  let xVal := constr:((to_Z a) * (to_Z b)) in

  let B1 := fresh "B1" in
  assert (B1: scalar_min T <= xVal);
  lazymatch goal with [ |- scalar_min T <= xVal ] =>
    intro_scalar_anon_bounds a;
    intro_scalar_anon_bounds b;
    simpl; try lia
  | [ |- _ ] =>

  let B2 := fresh "B2" in
  assert (B2: xVal <= scalar_max T);
  lazymatch goal with [ |- xVal <= scalar_max T ] =>
    intro_scalar_anon_bounds a;
    intro_scalar_anon_bounds b;
    simpl; try lia
  | [ |- _ ] =>

  let H := fresh "H" in
  destruct (S_mul_bounded a b (conj B1 B2)) as (x, H);
  clear B1 B2;

  let Hx := ltac_new_id "H"%string x ""%string in
  let Hr := fresh "Hr" in
  destruct H as (Hr, Hx);

  rewrite Hr;
  clear Hr;
  intro_scalar_bounds x;
  
  try rewrite res_bind_value;
  try rewrite res_bind_id
  end end.

Tactic Notation "rewrite_scalar_mul" constr(a) constr(b) :=
  let x := fresh "x" in
  rewrite_scalar_mul_tac a b x.

Tactic Notation "rewrite_scalar_mul" constr(a) constr(b) "as" simple_intropattern(x) :=
  rewrite_scalar_mul_tac a b x.

Tactic Notation "rewrite_scalar_mul" "as" simple_intropattern(x) :=
  lazymatch goal with [ |- context[ scalar_mul ?A ?B ]] =>
    rewrite_scalar_mul A B as x
  end.

(* scalar_div *)
Ltac rewrite_scalar_div_tac a b x :=
  let T := constr:(scalar_ty_of a) in
  let xVal := constr:((to_Z a) / (to_Z b)) in

  let B0 := fresh "B0" in
  assert (B0: to_Z b <> 0);
  lazymatch goal with [ |- to_Z b <> 0 ] =>
    intro_scalar_anon_bounds b;
    simpl; try lia
  | [ |- _ ] =>

  let B1 := fresh "B1" in
  assert (B1: scalar_min T <= xVal);
  lazymatch goal with [ |- scalar_min T <= xVal ] =>
    intro_scalar_anon_bounds a;
    intro_scalar_anon_bounds b;
    simpl; try lia
  | [ |- _ ] =>

  let B2 := fresh "B2" in
  assert (B2: xVal <= scalar_max T);
  lazymatch goal with [ |- xVal <= scalar_max T ] =>
    intro_scalar_anon_bounds a;
    intro_scalar_anon_bounds b;
    simpl; try lia
  | [ |- _ ] =>

  let H := fresh "H" in
  destruct (S_div_bounded a b B0 (conj B1 B2)) as (x, H);
  clear B0 B1 B2;

  let Hx := ltac_new_id "H"%string x ""%string in
  let Hr := fresh "Hr" in
  destruct H as (Hr, Hx);

  rewrite Hr;
  clear Hr;
  intro_scalar_bounds x;
  
  try rewrite res_bind_value;
  try rewrite res_bind_id
  end end end.

Tactic Notation "rewrite_scalar_div" constr(a) constr(b) :=
  let x := fresh "x" in
  rewrite_scalar_div_tac a b x.

Tactic Notation "rewrite_scalar_div" constr(a) constr(b) "as" simple_intropattern(x) :=
  rewrite_scalar_div_tac a b x.

Tactic Notation "rewrite_scalar_div" "as" simple_intropattern(x) :=
  lazymatch goal with [ |- context[ scalar_div ?A ?B ]] =>
    rewrite_scalar_div A B as x
  end.

(* scalar_rem *)
Ltac rewrite_scalar_rem_tac a b x :=
  let T := constr:(scalar_ty_of a) in
  let xVal := constr:(Z.rem (to_Z a) (to_Z b)) in

  let B1 := fresh "B1" in
  assert (B1: scalar_min T <= xVal);
  lazymatch goal with [ |- scalar_min T <= xVal ] =>
    intro_scalar_anon_bounds a;
    intro_scalar_anon_bounds b;
    simpl; try lia
  | [ |- _ ] =>

  let B2 := fresh "B2" in
  assert (B2: xVal <= scalar_max T);
  lazymatch goal with [ |- xVal <= scalar_max T ] =>
    intro_scalar_anon_bounds a;
    intro_scalar_anon_bounds b;
    simpl; try lia
  | [ |- _ ] =>

  let H := fresh "H" in
  destruct (S_rem_bounded a b (conj B1 B2)) as (x, H);
  clear B1 B2;

  let Hx := ltac_new_id "H"%string x ""%string in
  let Hr := fresh "Hr" in
  destruct H as (Hr, Hx);

  rewrite Hr;
  clear Hr;
  intro_scalar_bounds x;
  
  try rewrite res_bind_value;
  try rewrite res_bind_id
  end end.

Tactic Notation "rewrite_scalar_rem" constr(a) constr(b) :=
  let x := fresh "x" in
  rewrite_scalar_rem_tac a b x.

Tactic Notation "rewrite_scalar_rem" constr(a) constr(b) "as" simple_intropattern(x) :=
  rewrite_scalar_rem_tac a b x.

Tactic Notation "rewrite_scalar_rem" "as" simple_intropattern(x) :=
  lazymatch goal with [ |- context[ scalar_rem ?A ?B ]] =>
    rewrite_scalar_rem A B as x
  end.

(*  +---------------------------+
    | Tactics - vector rewrites |
    +---------------------------+
*)

(* vec_push_back *)
Ltac rewrite_vec_push_back_tac v x w :=
  let wVal := constr:(vec_push_back _ v x) in

  let B := fresh "B" in
  assert (B: vec_length v < usize_max);
  lazymatch goal with [ |- vec_length v < usize_max ] =>
    let H := fresh "H" in
    assert (H := vec_len_in_usize v);
    simpl in H |- *; try lia
  | [ |- _ ] =>

  let H := fresh "H" in
  destruct (V_push_back_bounded v x B) as (w, H);
  clear B;

  let Hw := ltac_new_id "H"%string w ""%string in
  let Hr := fresh "Hr" in
  destruct H as (Hr, Hw);

  rewrite Hr;
  clear Hr;
  
  try rewrite res_bind_value;
  try rewrite res_bind_id
  end.

Tactic Notation "rewrite_vec_push_back" constr(v) constr(x) :=
  let w := fresh "w" in
  rewrite_vec_push_back_tac v x w.

Tactic Notation "rewrite_vec_push_back" constr(v) constr(x) "as" simple_intropattern(w) :=
  rewrite_vec_push_back_tac v x w.

Tactic Notation "rewrite_vec_push_back" "as" simple_intropattern(w) :=
  lazymatch goal with [ |- context[ vec_push_back _ ?V ?X ]] =>
    rewrite_vec_push_back V X as w
  end.

Ltac rewrite_vec_index_mut_fwd_tac v i x :=
  let xVal := constr:(vec_index_mut_fwd _ v i) in

  let B := fresh "B" in
  assert (B: to_Z i < vec_length v);
  lazymatch goal with [ |- to_Z i < vec_length v ] =>
    let H := fresh "H" in
    assert (H := vec_len_in_usize v);
    simpl in H |- *; try lia
  | [ |- _ ] =>

  (* TODO *)
  let H := fresh "H" in
  destruct (V_index_mut_fwd_bounded v i B) as (x, H);
  clear B;

  let Hx := ltac_new_id "H"%string x ""%string in
  let Hr := fresh "Hr" in
  destruct H as (Hr, Hx);

  rewrite Hr;
  clear Hr;
  
  try rewrite res_bind_value;
  try rewrite res_bind_id
  end.

Tactic Notation "rewrite_vec_index_mut_fwd" constr(v) constr(i) :=
  let x := fresh "x" in
  rewrite_vec_index_mut_fwd_tac v i x.

Tactic Notation "rewrite_vec_index_mut_fwd" constr(v) constr(i) "as" simple_intropattern(x) :=
  rewrite_vec_index_mut_fwd_tac v i x.

Tactic Notation "rewrite_vec_index_mut_fwd" "as" simple_intropattern(x) :=
  lazymatch goal with [ |- context[ vec_index_mut_fwd _ ?V ?I ]] =>
    rewrite_vec_index_mut_fwd V I as x
  end.

Ltac rewrite_vec_index_mut_back_tac v i x w :=
  let wVal := constr:(vec_index_mut_back _ v i x) in

  let B := fresh "B" in
  assert (B: to_Z i < vec_length v);
  lazymatch goal with [ |- to_Z i < vec_length v ] =>
    let H := fresh "H" in
    assert (H := vec_len_in_usize v);
    simpl in H |- *; try lia
  | [ |- _ ] =>

  (* TODO *)
  let H := fresh "H" in
  destruct (V_index_mut_back_bounded v i x B) as (w, H);
  clear B;

  let Hw := ltac_new_id "H"%string w ""%string in
  let Hr := fresh "Hr" in
  destruct H as (Hr, Hw);

  rewrite Hr;
  clear Hr;
  
  try rewrite res_bind_value;
  try rewrite res_bind_id
  end.

Tactic Notation "rewrite_vec_index_mut_back" constr(v) constr(i) constr(x) :=
  let w := fresh "w" in
  rewrite_vec_index_mut_back_tac v i x w.

Tactic Notation "rewrite_vec_index_mut_back" constr(v) constr(i) constr(x) "as" simple_intropattern(w) :=
  rewrite_vec_index_mut_back_tac v i x w.

Tactic Notation "rewrite_vec_index_mut_back" "as" simple_intropattern(w) :=
  lazymatch goal with [ |- context[ vec_index_mut_back _ ?V ?I ?X ]] =>
    rewrite_vec_index_mut_back V I X as w
  end.

(*  +-----------------------+
    | Tactics - comparisons |
    +-----------------------+
*)

Ltac destruct_eqb_tac a b h :=
  let B := fresh "B" in
  set (B := to_Z a =? to_Z b);
  assert (h: (to_Z a =? to_Z b) = B) by intuition;
  induction B;
  lazymatch goal with
  | [ h: (to_Z a =? to_Z b) = true |- _ ] =>
    rewrite Z.eqb_eq in h;
    (* TODO: simplification is duplicated to be able to match on expressions. Perhaps there is a way to avoid that ? *)
    simpl (to_Z a) in *;
    simpl (to_Z b) in *;
    try lia
  | [ h: (to_Z a =? to_Z b) = false |- _ ] =>
    rewrite Z_eqb_ne in h;
    simpl (to_Z a) in *;
    simpl (to_Z b) in *;
    try lia
  end.

Tactic Notation "destruct_eqb" constr(a) constr(b) :=
  let h := fresh in
  destruct_eqb_tac a b h.

Tactic Notation "destruct_eqb" constr(a) constr(b) "as" simple_intropattern(h) :=
  destruct_eqb_tac a b h.

Tactic Notation "destruct_eqb" "as" simple_intropattern(h) :=
  lazymatch goal with [ |- context[ (to_Z ?A) =? (to_Z ?B) ]] =>
    destruct_eqb A B as h
  end.

(* TODO: Define the same tactic for the other comparisons *)

(*  +----------------------+
    | Tactics - inductions |
    +----------------------+
*)

(* TODO: vec to list induction *)

(* Usize to nat induction.
   TODO: Support all unsigned scalars.
*)
Ltac induction_usize_as_nat_tac s n :=
  let HeqN := ltac_new_id "Heq"%string n ""%string in
  remember (usize_to_nat s) as n;
  apply eq_sym in HeqN;
  revert s HeqN;
  induction n; intros s HeqN;
  apply (f_equal Z.of_nat) in HeqN;
  rewrite usize_nat_to_Z in HeqN;
  simpl in HeqN.

Tactic Notation "induction_usize_to_nat" simple_intropattern(s) "as" simple_intropattern(n) :=
  induction_usize_as_nat_tac s n.

(* Unfold the fixpoint on the fuel, destruct the fuel, try to solve the case "fuel = 0" then refold the fixpoint because Coq unfold it a second time on the fuel destruction.
   TODO: We need to detect fuel parameters (to be usable in progress tactic, otherwise we expand ~ any function), do we assume that they are the only "nat" values ?
*)
Ltac siphon fuel :=
  (* Do we want to recursively unfold functions ?
     Here we only allow it once.
  *)
  let siphon f := (
    unfold f;
    destruct fuel;
    only 1: intuition;
    fold f
  ) in
  (* Not lazy to allow failing on some match *)
  lazymatch goal with
  (* TODO: How to match the already unfolded fixpoint ?
  | [ |- context[ (fix _ (match _ with _ => _ end)) fuel ] ] =>
    destruct fuel;
    only 1: intuition *)
  (* TODO: How to match the nth argument in generality ?
     To avoid duplicating branches. *)
  (* TODO: How to give a single body for multiple clauses ?
     To avoid factorizing the code in "siphon". *)
  | [ |- context[ ?F fuel ] ] => siphon F
  | [ |- context[ ?F _ fuel ] ] => siphon F
  | [ |- context[ ?F _ _ fuel ] ] => siphon F
  | [ |- context[ ?F _ _ _ fuel ] ] => siphon F
  | [ |- context[ ?F _ _ _ _ fuel ] ] => siphon F
  | [ |- context[ ?F _ _ _ _ _ fuel ] ] => siphon F
  | [ |- context[ ?F _ _ _ _ _ _ fuel ] ] => siphon F
  | [ |- context[ ?F _ _ _ _ _ _ _ fuel ] ] => siphon F
  | [ |- context[ ?F _ _ _ _ _ _ _ _ fuel ] ] => siphon F
  | [ |- context[ ?F _ _ _ _ _ _ _ _ _ fuel ] ] => siphon F
  end.

(*  +----------------------+
    | Tactics - dispatcher |
    +----------------------+
*)

(* The goal here is to have a single tactic to progress.
  Either it applies to a head normal term (but how to match it with ltac ?), or we specify the terms to which it applies.

  For now the second case is more easily testable. It means that given e.g. "a" and "b" we match "to_Z a =? to_Z b", "scalar_add a b", ... And apply the corresponding tactic each time.

  It's not clear however if it can really be useful.
*)

(* Introduce a term, with its bounds if it's a scalar. *)
Ltac aeIntro n :=
  intro n;
  match type of n with
  | scalar _ => intro_scalar_bounds n
  | vec _ => intro_vec_bounds n
  | _ => idtac
  end.

(* Simplify scalar & vec expressions.
   TODO: must fail when not applied.
   TODO: Vectors of known elements to lists.
   TODO: Targeted simplifications can be avoided if simpl of sacalars & vec is blocked.
   TODO: Make rewrite rules extandable by obtaining them from a typeclass or an autorewrite hint database (for e.g. "usize_nat_to_Z").
*)
Ltac aeSimpl :=
  repeat
 (rewrite usize_nat_to_Z in * ||
  rewrite res_bind_value in * ||
  rewrite res_bind_id in * ||
  lazymatch goal with
  (* Scalar constants *)
  | |- context[ to_Z (eval_result_refl ?A eq_refl) ] =>
      simpl (to_Z (eval_result_refl A eq_refl))
  | H: context[ to_Z (eval_result_refl ?A eq_refl) ] |- _ =>
      simpl (to_Z (eval_result_refl A eq_refl)) in H
  end).

(* Pick and apply a custom tactic to the given expression. *)
(* TODO: other operations (scalar_neg/cast/leb/..., vec_push/insert/index/...) *)
Ltac aeStepLeaf P n :=
  lazymatch P with
  | to_Z ?A =? to_Z ?B => destruct_eqb A B as n
  | scalar_add ?A ?B => rewrite_scalar_add A B as n
  | scalar_sub ?A ?B => rewrite_scalar_sub A B as n
  | scalar_mul ?A ?B => rewrite_scalar_mul A B as n
  | scalar_div ?A ?B => rewrite_scalar_div A B as n
  | scalar_rem ?A ?B => rewrite_scalar_rem A B as n
  | vec_push_back _ ?A ?B => rewrite_vec_push_back A B as n
  | vec_index_mut_fwd _ ?A ?B => rewrite_vec_index_mut_fwd A B as n
  | vec_index_mut_back _ ?A ?B ?C => rewrite_vec_index_mut_back A B C as n
  
  | _ => fail "no Aeneas lemma could be automatically applied"
  end.

(* TODO: Should we go under function arguments and if/match branches ?
*)
Ltac aeStepRec G n :=
  lazymatch G with
  (* Go under implications *)
  | forall _, _ => aeIntro n
  | _ → _ => aeIntro n
  (* TODO Desugarized match - Go under blocking eliminations *)
  | if ?A then _ else _ => aeStepRec A n
  | match ?A with _ => _ end => aeStepRec A n
  (* Go under the error monad *)
  | Primitives.bind ?A _ => aeStepRec A n
  (* Go under equation *)
  | ?A = ?B => aeStepRec A n || aeStepRec B n
  (* Try to apply a lemma *)
  | ?P => aeStepLeaf P n
  end.

Ltac aeStepGoal n :=
  lazymatch goal with
  (* Apply injective lemmas on scalar & vec equations *)
  | |- ?A = ?B =>
      match type of A with
      | scalar _ => apply scalar_Z_inj
      | vec _ => apply vec_list_inj
      | _ => aeStepRec A n || aeStepRec B n
      end
  (* Proceed normally *)
  | |- ?G => aeStepRec G n
  end;
  aeSimpl.

(* TODO: Find how to match an hypothesis by its name. *)
Ltac aeStepHyp h n :=
  lazymatch type of h with
  | ?H => aeStepRec H n
  end;
  aeSimpl.

(* TODO: Authorize "aeStep in *" by iterating on all hypothesis.
It does not seems trivial (at least 12y ago):
https://coq-club.inria.narkive.com/84wy4cCg/ltac-iteration-on-all-hypothesis#post4
*)

Tactic Notation "aeStep" :=
  let n := fresh in
  aeStepGoal n.

Tactic Notation "aeStep" "as" simple_intropattern(n) :=
  aeStepGoal n.

Tactic Notation "aeStep" "in" simple_intropattern(h) :=
  let n := fresh in
  aeStepHyp h n.

Tactic Notation "aeStep" "as" simple_intropattern(n) "in" simple_intropattern(h) :=
  aeStepHyp h n.

Tactic Notation "aeStep" "in" simple_intropattern(h) "as" simple_intropattern(n) :=
  aeStepHyp h n.

(*  +--------------+
    | Open version |
    +--------------+
*)
(*
The goal here is to develop a modularized tactic to progress on a given goal by simplifying & solving elements which may be given by the user.
To do that, a high-level "aeProgress" tactic will be built from 3 components:
- "aeStep" which inspects the goal head variable and lookup a lemma to apply to it.
- "aeSimpl" which uniformises the hypotheses by simplifying it and looking up bounds to introduce.
- "aeSolve" which aims to resolve the obtained goals.

For now, the prefix is changed to "oa" to avoid conflicts.

TODO:
- How to add various simplification rules/tactics to aeStep, and is it wanted ? (typically destruct_eqb, scalar_Z_inj).
- Is the typeclass approach still good if they proliferate ?
- 
*)

(*
Registers lemmas that are applied by the "oaStep" tactic.

The interface for monadic lemmas accept proofs of propositions of the following shape:
"T → T₁ → ... → Tₙ → ∀x₁:T₁...∀xₙ:Tₙ, Preconditions → ∃x:T, f x₁...xₙ = Return x ∧ Postconditions"

To avoid the issue with variadic arguments, we match the function applied to all of its arguments (minus the precondition).

The "polymorphic" qualifier is only needed for "T → Prop", which lives one universe above.
*)
Polymorphic Class MonadicLemma {T} (f: result T) := {
  monl_pre : Prop;
  monl_post : T → Prop;
  monl_lemma : monl_pre → ∃(x: T), f = Return x ∧ monl_post x;
}.

(* Non-monadic variant of "MonadicLemma". More versatile but less powerful : it only adds a lemma in hypothesis, assert its precondition then "destruct" the HV ("MonadicLemma" morally performs a "destruct" as well).
TODO: Rename "MonadicLemma" ⇝ "StepMonadicLemma", "ApplicableLemma" ⇝ "StepLemma" ? To make it clear that those are used by "oaStep" & that there are similar (modulo monadicity).
*)
Polymorphic Class ApplicableLemma {T} (e: T) := {
  appl_pre : Prop;
  appl_lemma : appl_pre → Prop;
}.

(* Instances for primitives. *)

Global Instance monadic_lemma_scalar_add T n m : MonadicLemma (@scalar_add T n m) :=
  {| monl_lemma := S_add_bounded n m; |}.

Global Instance monadic_lemma_scalar_mul T n m : MonadicLemma (@scalar_mul T n m) :=
  {| monl_lemma := S_mul_bounded n m; |}.

Global Instance monadic_lemma_scalar_sub T n m : MonadicLemma (@scalar_sub T n m) :=
  {| monl_lemma := S_sub_bounded n m; |}.

Global Instance monadic_lemma_scalar_div T n m : MonadicLemma (@scalar_div T n m) :=
  {| monl_lemma := S_div_bounded n m; |}.

Global Instance monadic_lemma_scalar_rem T n m : MonadicLemma (@scalar_rem T n m) :=
  {| monl_lemma := S_rem_bounded n m; |}.

Global Instance monadic_lemma_vec_push_back T v x : MonadicLemma (vec_push_back T v x) :=
  {| monl_lemma := V_push_back_bounded v x; |}.

Global Instance monadic_lemma_vec_index_mut_fwd T v i : MonadicLemma (vec_index_mut_fwd T v i) :=
  {| monl_lemma := V_index_mut_fwd_bounded v i; |}.

Global Instance monadic_lemma_vec_index_mut_back T v i x : MonadicLemma (vec_index_mut_back T v i x) :=
  {| monl_lemma := V_index_mut_back_bounded v i x; |}.

(*
Registers types which, when instantiated by hypothesis, should expose an additional hypothesis on them (typically, to project scalars and vectors to Z and lists respectfully).
*)
Polymorphic Class BoundedHypothesis T := {
  bo_hyp_prop : T → Prop;
  bo_hyp_lemma (x: T) : bo_hyp_prop x;
}.

(* Instances for primitives.

TODO: We may want to lift it in sum & product types (Bounded A & Bounded B => Bounded (A, B), ...).
*)

Global Instance bounded_hypothesis_scalar T : BoundedHypothesis (scalar T) :=
  {| bo_hyp_lemma := S_scalar_bounds; |}.

Global Instance bounded_hypothesis_vector T : BoundedHypothesis (vec T) :=
  {| bo_hyp_lemma := V_vec_bounds; |}.

(*
Registers types to simplify equation goals on their terms with the given injective function (typically, to project scalars on Z and vectors on lists).

TODO: It's not clear that it's really needed ... It helps to fully automatize scalar/vector-specific part but that's it.
Perhaps it should be added in "oaStep" with generic lemmas to 'apply'.
Also, same as above, we can lift it for sum & product types.
*)
Polymorphic Class InjectiveProjection T := {
  injp_type : Type;
  injp_fun : T → injp_type;
  injp_lemma (a b: T) : injp_fun a = injp_fun b → a = b;
}.

(* Instances for primitives. *)

Global Instance injective_projection_scalar T : InjectiveProjection (scalar T) :=
  {| injp_lemma := S_scalar_Z_inj; |}.

Global Instance injective_projection_vector T : InjectiveProjection (vec T) :=
  {| injp_lemma := @vec_list_inj _; |}.

(* Low-level tactic to only resolve typeclasses, without backtracking. It is strictly less powerful than e.g. "exact _". *)
Ltac tc_solve :=
  solve [once (typeclasses eauto)].

(* TODO: Test it. The name is a bit long ... *)
Notation monadic_oof_shape x P := match x with
  | Return v => P v
  | Fail_ OutOfFuel => True
  | Fail_ Failure => False
  end.

(* Allow to swap between two formulations of statements about results:
- The match shape, a convenient formulation for partial correctness.
- The existential formula of monadic lemmas, which can be used by "aoStepGoal".
*)
Lemma monadic_shape_to_instance {T} {x: result T} {P: T → Prop} :
  (match x with
  | Return a => P a
  | Fail_ OutOfFuel => True
  | Fail_ Failure   => False
  end)
  ↔
  (x ≠ Fail_ OutOfFuel →
  ∃ a, x = Return a ∧ P a).
Proof.
split; destruct x; intros.
- now exists t.
- now destruct e.
- assert (Return t ≠ Fail_ OutOfFuel) by easy.
  destruct (H H0) as (x, (A, B)).
  injection A.
  intro C. now rewrite C.
- destruct e. 2: trivial.
  assert (@Fail_ T Failure ≠ Fail_ OutOfFuel) by easy.
  now destruct (H H0).
Qed.

Lemma monadic_shape_to_instance_hyp {T} {x: result T} {P: Prop} {Q: T → Prop} :
  (P → match x with
  | Return a => Q a
  | Fail_ OutOfFuel => True
  | Fail_ Failure   => False
  end)
  ↔
  (P ∧ x ≠ Fail_ OutOfFuel →
  ∃ a, x = Return a ∧ Q a).
Proof.
split; intros.
- destruct H0. assert (p := H H0).
  now apply monadic_shape_to_instance.
- apply monadic_shape_to_instance. intro.
  now apply H.
Qed.

(* Can be used for automatic proof search. *)
Lemma weaken_oof_guard {A B} {f: result A} {g: A → result B} :
  (v ← f; g v) ≠ Fail_ OutOfFuel →
  f ≠ Fail_ OutOfFuel.
Proof.
destruct f. 1: easy.
now destruct e.
Qed.

Lemma monadic_oof_hyp {A} {f: result A} {P: A → Prop} :
  (f ≠ Fail_ OutOfFuel →
  match f with
  | Return x => P x
  | Fail_ OutOfFuel => True
  | Fail_ Failure   => False
  end) →
  match f with
  | Return x => P x
  | Fail_ OutOfFuel => True
  | Fail_ Failure   => False
  end.
Proof.
rewrite monadic_shape_to_instance_hyp. intro H.
assert (f ≠ Fail_ OutOfFuel) by intuition.
revert H.
rewrite <-monadic_shape_to_instance_hyp.
intro.
now apply H.
Qed.

(* Add bounds to all hypotheses that could have it. The function flow is a bit missed up due to various limitations. *)
Ltac oaAddBounds :=
  lazymatch goal with
  | H: ?A |- _ =>
    (* Continue when failing (see below) - e.g. no TC found.
    TODO: Find a cleaner mechanism.
    *)
    let TC := fresh "TC" in
    tryif pose (TC := (ltac:(tc_solve): BoundedHypothesis A))
    then (
      (* Create bounds. Done before checking that it already exists because we need its simplified type to do the match. *)
      let bounds := ltac_new_id ""%string H "_bounds"%string in
      assert (bounds := bo_hyp_lemma H);
      simpl in bounds;
      (* Push it on the goal. *)
      clear TC;
      let T := type of bounds in
      revert bounds;
      lazymatch goal with
      | B: T |- _ =>
        (* Bounds already exists : keep it, remove the new one to keep the previous name. *)
        intro;
        clear bounds;
        revert B;
        (* Continue. *)
        revert H;
        oaAddBounds;
        intro;
        pose (YES := 1)
      | _ =>
        (* Continue, then reintroduce the new bounds. *)
        revert H;
        oaAddBounds;
        intro;
        intro
      end
    )
    else (
      (* No "BoundedHypothesis" typeclass : continue. *)
      revert H;
      oaAddBounds;
      intro
    )
  (* No more hypothesis. *)
  | _ => idtac
  end.

(* Simplify the goal with "InjectiveProjection". *)
Ltac oaInjectEqGoal :=
  lazymatch goal with
  | |- @eq ?A ?x ?y =>
    let TC := fresh "TC" in
    let f := fresh "f" in
    pose (TC := (ltac:(tc_solve): InjectiveProjection A));
    pose (f := injp_lemma x y);
    simpl in f;
    apply f;
    clear f;
    clear TC
  end.

(* Uniformize the context and goal with various simplifications. TODO: put equalities in an "autorewrite" hint database. *)
Ltac oaSimpl :=
  oaAddBounds;
  try oaInjectEqGoal;
  try repeat (rewrite usize_nat_to_Z in *);
  try repeat (rewrite res_bind_value in *);
  try repeat (rewrite res_bind_id in *);
  repeat lazymatch goal with
  (* Scalar constants *)
  | |- context[ to_Z (eval_result_refl ?A eq_refl) ] =>
      simpl (to_Z (eval_result_refl A eq_refl))
  | H: context[ to_Z (eval_result_refl ?A eq_refl) ] |- _ =>
      simpl (to_Z (eval_result_refl A eq_refl)) in H
  end.
  
(* Solves the given goal with "lia" and other tactics or fails. *)
Ltac oaSolveGoal :=
  oaSimpl;
  easy || lia ||
  lazymatch goal with
  | |- _ ∧ _ => split; oaSolveGoal
  | _ => fail "couldn't solve the goal"
  end.

(* Applies an hypothesis about the fuel to the goal if needed, of the shape "... ≠ Fail_ OutOfFuel". *)
Ltac oaApplyOofHyp H_oof :=
  let rec_on_wedge H_oof := (
    split;
    lazymatch goal with
    | |- _ ≠ Fail_ OutOfFuel => oaApplyOofHyp H_oof
    | |- _ => idtac
    end
  ) in
  lazymatch goal with
  (* It's a left or right condition. *)
  | |- _ ∧ _ ≠ Fail_ OutOfFuel => rec_on_wedge H_oof
  | |- _ ≠ Fail_ OutOfFuel ∧ _ => rec_on_wedge H_oof
  (* The goal may be weaker than the hypothesis. *)
  | |- _ ≠ Fail_ OutOfFuel =>
    apply H_oof ||
    apply (weaken_oof_guard H_oof)
  | |- _ => idtac
  end.

(* TODO: "simpl"s in pre/L should only unfold the typeclass fields. *)
Ltac oaApplyMonadicLemma f res H_oof :=
  (* Lookup the monadic lemma via its typeclass *)
  let TC := fresh "TC" in
  pose (TC := (ltac:(tc_solve): MonadicLemma f));
  simpl in TC;

  (* Add a goal for preconditions *)
  let pre := fresh "pre" in
  assert (pre: monl_pre);
  lazymatch goal with
  | |- monl_pre =>
    simpl;
    oaApplyOofHyp H_oof;
    try oaSolveGoal
  | _ =>
    simpl in pre;
  
    (* Instantiate the lemma with its preconditions. *)
    let L := fresh "L" in
    assert (L := monl_lemma pre);
    simpl in L;

    (* Split it into the new variable, the equation and the postconditions. *)
    let H := fresh in
    destruct L as (res, H);
    let eq := fresh "eq" in
    let post := ltac_new_id "H"%string res ""%string in
    destruct H as (eq, post);

    (* Rewrite the function application then clear up the context.
    TODO: Add "try rewrite res_bind_value/id" for the rewritten HV.
    *)
    rewrite eq;
    clear eq;
    clear pre
  end;
  clear TC.

Ltac oaApplyNonMonadicLemma f res :=
  let TC := fresh "TC" in
  pose (TC := (ltac:(tc_solve): ApplicableLemma f));
  simpl in TC;
  
  (* Add a goal for preconditions. *)
  let pre := fresh "pre" in
  assert (pre: appl_pre);
  lazymatch goal with
  | |- appl_pre =>
    simpl;
    oaApplyOofHyp H_oof;
    try oaSolveGoal
  | ?A =>
    simpl in pre;
    
    (* Instantiate the lemma then destruct the HV. *)
    assert (res := appl_lemma pre);
    simpl in res;
    clear pre;
    destruct A
  end;
  clear TC.

(* Recursively reaches the head variable. *)
Ltac oaStepRec G n H_oof :=
  lazymatch G with
  (* Go under implications.
  TODO: We may want to fail because rewriting under abstractions won't work anyway.
  *)
  | ∀ _, ?A => oaStepRec A n H_oof
  | _ → ?A => oaStepRec A n H_oof
  (* Go under blocking elimination. *)
  | match ?A with _ => _ end => oaStepRec A n H_oof
  (* Go under the error monad. *)
  | Primitives.bind ?A _ => oaStepRec A n H_oof
  (* Go under the equation left side. *)
  | ?A = ?B => oaStepRec A n H_oof
  (* Try to apply a monadic lemma. *)
  | ?P => oaApplyMonadicLemma P n H_oof
  end.

(* Executes "t1" then "t2", even if "t1" fails (in which case an error is send).
TODO: How to re-throw an error instead of creating a new one ? We don't want to loose e.g. its error message.
*)
Tactic Notation "try_" tactic(t1) "finally" tactic(t2) :=
  tryif (t1)
  then  (t2)
  else ((t2); fail).

Ltac oaStep n :=
  (* Add a temporary hypothesis on oof for partial monadic goals. *)
  lazymatch goal with
  | |- match ?X with
      | Return v => _
      | Fail_ f => match f with
        | OutOfFuel => True
        | Failure => False
      end end =>
    let H_oof := fresh "oof_hyp" in
    apply monadic_oof_hyp;
    intro H_oof;
    try_ (oaStepRec X n H_oof)
    finally (clear H_oof)

  | |- ?G => 
    let H_oof := fresh "no_oof_hypothesis" in
    oaStepRec G n H_oof
  end.

(*  +-------+
    | Tests |
    +-------+
*)

Fixpoint usize_identity (fuel: nat) (s: usize) : result usize :=
  match fuel with
  | 0%nat => Fail_ OutOfFuel
  | S fuel =>
    if (s s= 0%usize) then Return 0%usize else
      x ← usize_sub s (1%usize);
      y ← usize_identity fuel x;
      usize_add y (1%usize)
  end.

Lemma usize_identity_shape fuel s :
  True ->
  match usize_identity fuel s with
  | Return v => s = v
  | Fail_ OutOfFuel => True
  | Fail_ Failure   => False
  end.
Proof.
intro TT.
(* induction *)
revert fuel.
induction_usize_to_nat s as S;
intro fuel;
siphon fuel;
destruct_eqb as Seq0.

(* 0 case *)
1: now oaSolveGoal.

(* successor case: *)
oaSimpl.
oaStep r.
simpl.

(* Apply IH *)
assert (B: usize_to_nat r = S). 1: {
  (* I'm sure there is a simple tactic for that ... *)
  cut (Z.of_nat (usize_to_nat r) = Z.of_nat S).
  now intuition.
  oaSolveGoal.
}
assert (H := IHS r B fuel).

destruct (usize_identity fuel r). 2: oaSolveGoal.
simpl.
rewrite <-H.

oaStep r0.
oaSolveGoal.
Qed.

(* Want to go both ways: shape <=> ¬oof → instance *)

Global Instance monadic_lemma_usize_identity fuel s : MonadicLemma (usize_identity fuel s) :=
  {| monl_lemma := proj1 monadic_shape_to_instance_hyp (usize_identity_shape fuel s); |}.

Definition add_ids fuel s :=
  a ← usize_identity fuel s;
  scalar_add a a.

Lemma add_ids_shape fuel s :
  to_Z s + to_Z s <= usize_max →
  match add_ids fuel s with
  | Fail_ OutOfFuel => True
  | Fail_ Failure   => False
  | Return a => to_Z a = to_Z s + to_Z s
  end.
Proof.
intro.
oaSimpl.
unfold add_ids.
oaStep n.

(* 
COPY-PASTED "oaAddBounds" applied to "s".
Why does it match the hypothesis here and not in "oaSimpl", which duplicates bounds ?
*)
let TC := fresh "TC" in
tryif pose (TC := (ltac:(tc_solve): BoundedHypothesis usize))
then (
  (* Create bounds. Done before checking that it already exists because we need its simplified type to do the match. *)
  let bounds := ltac_new_id ""%string s2 "_bounds"%string in
  assert (bounds := bo_hyp_lemma s);
  simpl in bounds;
  (* Push it on the goal. *)
  clear TC;
  let T := type of bounds in
  revert bounds;
  lazymatch goal with
  | B: T |- _ =>
    (* Bounds already exists : keep it, remove the new one to keep the previous name. *)
    intro;
    clear bounds;
    revert B;
    (* Continue. *)
    pose (YES := 1)
  | _ =>
    (* Continue, then reintroduce the new bounds. *)
    pose (NO := 0)
  end
)
else (
  (* No "BoundedHypothesis" typeclass : continue. *)
  pose (BRUH := -1)
).
intro.




oaSimpl. (* TODO: Why two bounds ? *)
rewrite <-Hn.
now oaStep m.
Qed.

(* Same lemma as above, but without the machinery above. *)
Lemma add_ids_shape2 fuel s :
  to_Z s + to_Z s <= usize_max →
  match add_ids fuel s with
  | Fail_ OutOfFuel => True
  | Fail_ Failure   => False
  | Return a => to_Z a = to_Z s + to_Z s
  end.
Proof.
intro.
oaSimpl.
unfold add_ids.
(* "oaStep" replaces this assert + destruct + 2: trivial. *)
assert (P := usize_identity_shape fuel s I).
destruct (usize_identity fuel s). 2: trivial.
simpl.
rewrite <-P.
now oaStep m.
Qed.

End Primitives_Ext.
