
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
Require ltac2_string_to_ident.
Require ltac2_ident_to_string.

Module Primitives_Ext.

Ltac string_to_ident s := ltac2_string_to_ident.string_to_ident s.

Notation ident_to_string id :=
  (ltac2_ident_to_string.ident_to_string id) (only parsing).

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

Lemma Z_eqb_ne {n m: Z} :
(n =? m) = false <-> n <> m.
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

(* Written as a tactic to exploit proof by rewriting - I may miss another way *)
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

Lemma S_scalar_Z_inj {ty} (n m: scalar ty) :
  to_Z n = to_Z m -> n = m.
Proof.
destruct m, n.
apply ProofIrrelevanceTheory.subset_eq_compat.
Qed.

Lemma S_mk_bounded ty (x: Z) :
  scalar_min ty <= x <= scalar_max ty ->
  ∃n, mk_scalar ty x = Return n
   /\ to_Z n = x.
Proof.
intro B.
pose (n := (exist _ x B): scalar ty).
exists n.
split. 2: reflexivity.
scalar_success_tac x B.
Qed.

Lemma S_add_bounded {ty} (n m: scalar ty) :
  scalar_min ty <= (to_Z n) + (to_Z m) <= scalar_max ty ->
  ∃x, scalar_add n m = Return x
   /\ to_Z x = (to_Z n) + (to_Z m).
Proof.
intro B.
pose (x := (exist _ (to_Z n + to_Z m) B): scalar ty).
exists x.
split. 2: reflexivity.
unfold scalar_add.
scalar_success_tac (to_Z n + to_Z m) B.
Qed.

Lemma S_sub_bounded {ty} (n m: scalar ty) :
  scalar_min ty <= (to_Z n) - (to_Z m) <= scalar_max ty ->
  ∃x, scalar_sub n m = Return x
   /\ to_Z x = (to_Z n) - (to_Z m).
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
  scalar_min ty <= (to_Z n) * (to_Z m) <= scalar_max ty ->
  ∃x, scalar_mul n m = Return x
   /\ to_Z x = (to_Z n) * (to_Z m).
Proof.
intro B.
pose (x := (exist _ (to_Z n * to_Z m) B): scalar ty).
exists x.
split. 2: reflexivity.
unfold scalar_mul.
scalar_success_tac (to_Z n * to_Z m) B.
Qed.

Lemma S_div_bounded {ty} (n m: scalar ty) :
  to_Z m <> 0 ->
  scalar_min ty <= (to_Z n) / (to_Z m) <= scalar_max ty ->
  ∃x, scalar_div n m = Return x
   /\ to_Z x = (to_Z n) / (to_Z m).
Proof.
intros B0 B.
pose (x := (exist _ (to_Z n / to_Z m) B): scalar ty).
exists x.
split. 2: reflexivity.
unfold scalar_div.
remember (to_Z m =? 0) as b.
destruct b. 1: intuition.
scalar_success_tac (to_Z n / to_Z m) B.
Qed.

Lemma S_rem_bounded {ty} (n m: scalar ty) :
  scalar_min ty <= Z.rem (to_Z n) (to_Z m) <= scalar_max ty ->
  ∃x, scalar_rem n m = Return x
   /\ to_Z x = Z.rem (to_Z n) (to_Z m).
Proof.
intro B.
pose (x := (exist _ (Z.rem (to_Z n) (to_Z m)) B): scalar ty).
exists x.
split. 2: reflexivity.
unfold scalar_rem.
scalar_success_tac (Z.rem (to_Z n) (to_Z m)) B.
Qed.

Lemma V_push_back_bounded {T} (v: vec T) (x: T) :
  vec_length v < usize_max ->
  ∃w, vec_push_back T v x = Return w
   /\ vec_to_list w = (vec_to_list v) ++ [x].
Proof.
Admitted.

Lemma V_index_mut_fwd_bounded {T} (v: vec T) (i: usize) :
  to_Z i < vec_length v ->
  ∃x, vec_index_mut_fwd T v i = Return x
   /\ nth_error (vec_to_list v) (usize_to_nat i) = Some x.
Proof.
Admitted.

Lemma V_index_mut_back_bounded {T} (v: vec T) (i: usize) (x: T) :
  to_Z i < vec_length v ->
  ∃w, vec_index_mut_back T v i x = Return w
   /\ vec_to_list w = replace_list (vec_to_list v) (usize_to_nat i) x.
Proof.
Admitted.

Lemma usize_nat_to_Z (n: usize) : Z.of_nat (usize_to_nat n) = to_Z n.
Proof.
unfold usize_to_nat.
apply Z2Nat.id.
apply (S_scalar_bounds n).
Qed.

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

(* Does not create an identifier based on n.
   Used for unknown scalar parameters which could be expressions.
   TODO: Match identifiers VS expressions to know which tactic to call.
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
  match goal with
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

Ltac make_progress :=
  lazymatch goal with
  | [ |- context[ to_Z ?A =? to_Z ?B ] ] => destruct_eqb A B
  | [ |- context[ scalar_add ?A ?B ] ] => rewrite_scalar_add A B
  | [ |- context[ scalar_sub ?A ?B ] ] => rewrite_scalar_sub A B
  | [ |- context[ scalar_mul ?A ?B ] ] => rewrite_scalar_mul A B
  | [ |- context[ scalar_div ?A ?B ] ] => rewrite_scalar_div A B
  | [ |- context[ vec_push_back _ ?A ?B ] ] => rewrite_vec_push_back A B
  end.
(* (λx.if x then y else z)a *)


(*  +-------+
    | Tests |
    +-------+
*)

Fixpoint usize_identity (fuel: nat) (s: usize) : result usize :=
  match fuel with
  | 0%nat => Fail_ OutOfFuel
  | S fuel =>
    if (s s= 0%usize) then Return 0%usize else
      x <- usize_sub s (1%usize);
      y <- usize_identity fuel x;
      usize_add y (1%usize)
  end.

Lemma usize_identity_shape fuel s :
  match usize_identity fuel s with
  | Return v => s = v
  | Fail_ OutOfFuel => True
  | Fail_ Failure   => False
  end.
Proof.
(* induction *)
revert fuel.
induction_usize_to_nat s as S;
intro fuel;
siphon fuel;
destruct_eqb s (0%usize) as Seq0.

(* 0 case *)
1: now apply scalar_Z_inj.

(* successor case: *)

intro_scalar_bounds s.
rewrite_scalar_sub s (1%usize) as r.
simpl (to_Z 1 %usize) in *.

(* Apply IH *)
assert (B: usize_to_nat r = S). 1: {
  (* I'm sure there is a simple tactic for that ... *)
  cut (Z.of_nat (usize_to_nat r) = Z.of_nat S).
  intuition.
  (* Can this fit in the induction ? *)
  rewrite usize_nat_to_Z.
  lia.
}
assert (H := IHS r B fuel).

destruct (usize_identity fuel r). 2: exact H.
rewrite res_bind_value.
rewrite <-H.

rewrite_scalar_add r (1%usize) as r0.
simpl (to_Z 1 %usize) in *.
apply scalar_Z_inj.
lia.
Qed.

End Primitives_Ext.
