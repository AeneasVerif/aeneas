
(* TODO: Cleanup imports and scope of exposed lemmas / tactics. *)
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

(* Improves the "rewrite" tactic, which was before missing some terms without any good reason. *)
Set Keyed Unification.

(* Imports string ↔ identifier converter utilities for tactics. *)
Ltac string_to_ident s := ltac2_string_to_ident.string_to_ident s.
Notation ident_to_string id :=
  (ltac2_ident_to_string.ident_to_string id) (only parsing).

(*  +-----------------+
    | Basic utilities |
    +-----------------+
*)

(* Used in the specification of "V_index_mut_back_bounded". *)
Fixpoint replace_list {T} (l: list T) (n: nat) (x: T) :=
  match l with
  | [] => []
  | y :: t => match n with
    | 0%nat => x :: t
    | S n'  => y :: replace_list t n' x
    end
  end.

(* Simple lemmas for proofs below. *)

Lemma neg_impl {A B: Prop} : (A → B) → ~B → ~A.
intuition. Qed.

Lemma neg_equiv {A B: Prop} : A ↔ B → ~A ↔ ~B.
apply not_iff_compat. Qed.

Lemma Zsucc_le_mono n m : n <= m → n <= Z.succ m.
intuition. Qed.

(* Hints used to rewrite lemmas in "aeSimpl".
TODO: Is there a more principled approach, or one reusing existing stuff ?
SSReflect (while having a greater scope) may be considered.
*)

Lemma simpl_bool_tautoT : (true = true) ↔ True.
intuition. Qed.
Lemma simpl_bool_tautoF : (false = false) ↔ True.
intuition. Qed.

Lemma simpl_bool_oxyTF : (true = false) ↔ False.
intuition. Qed.
Lemma simpl_bool_oxyFT : (false = true) ↔ False.
intuition. Qed.

Lemma simpl_tauto_implies (P: Prop) : (True → P) ↔ P.
intuition. Qed.
Lemma simpl_oxy_implies (P: Prop) : (False → P) ↔ True.
intuition. Qed.

Lemma simpl_conj_trivialR (P: Prop) : P ∧ True ↔ P.
intuition. Qed.
Lemma simpl_conj_trivialL (P: Prop) : True ∧ P ↔ P.
intuition. Qed.

Lemma simpl_disj_trivialR (P: Prop) : P ∨ False ↔ P.
intuition. Qed.
Lemma simpl_disj_trivialL (P: Prop) : False ∨ P ↔ P.
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

(*  +----------------------+
    | Arithmetic utilities |
    +----------------------+
*)

(* We want a lemma stating something like "to_Z ((mk_scalar T x)%return) = x", but this is not well-formed because of the implicit "eq_refl x" (working for constants but not a generic "x").

This rewriting rule is then hardcoded in "aeSimpl" (currently implicitly, by calling "simpl in *").
*)

(* Comparisons *)

(* Uses proof irrelevance so scalars with the same number can be equated *)
Lemma scalar_Z_inj {ty} {n m: scalar ty} : (to_Z n = to_Z m) → (n = m).
Proof.
destruct m, n.
apply ProofIrrelevanceTheory.subset_eq_compat.
Qed.

(* TODO: Usize lemmas should be generalized for positive scalars *)
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

(*  +--------------------------+
    | Reasoning on Z and lists |
    +--------------------------+
*)

(* Small helper. TODO: taken from below, remove redundancy. *)
Ltac ltac_new_id2 prefix id suffix :=
  let old := constr:(ident_to_string id) in
  let new := constr:((prefix ++ old ++ suffix)%string) in
  string_to_ident new.

(* Brittle tactic to shorten some following lemmas. *)
Ltac scalar_success_tac X B :=
  let H := fresh in
  unfold mk_scalar;
  remember (Sumbool.sumbool_of_bool (scalar_in_bounds _ X)) as H;
  destruct H as [H|H];
  (* We always use "lazymatch" instead of "match" because it fails fast, by propagating any failure instead of trying another branch. *)
  lazymatch goal with
  | [ H: _ = true |- _ ] =>
    now apply f_equal, scalar_Z_inj
  | [ H: _ = false |- _ ] =>
    exfalso;
    let Heq := ltac_new_id2 "Heq"%string H ""%string in
    clear Heq;
    now rewrite (proj2 (scalar_in_bounds_valid2 _ X) B) in H
  end.

Lemma S_bounds {ty} (n: scalar ty) :
  scalar_min ty <= to_Z n <= scalar_max ty.
Proof.
exact (proj2_sig n).
Qed.

Lemma V_bounds {T} (v: vec T) :
  usize_min <= vec_length v <= usize_max.
Proof.
exact (vec_len_in_usize v).
Qed.

(* Uses proof irrelevance to equate bounds. *)
Lemma S_to_Z_inj {ty} (n m: scalar ty) :
  to_Z n = to_Z m → n = m.
Proof.
destruct m, n.
apply ProofIrrelevanceTheory.subset_eq_compat.
Qed.

(* Also uses proof irrelevance. *)
Lemma V_to_list_inj {T} (a b: vec T) : (vec_to_list a = vec_to_list b) → (a = b).
Proof.
destruct a, b.
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

Lemma S_sub_bounded {ty} (n m: scalar ty) :
  scalar_min ty <= (to_Z n) - (to_Z m) <= scalar_max ty →
  ∃x, scalar_sub n m = Return x
   ∧ to_Z x = (to_Z n) - (to_Z m).
Proof.
(* TODO: Factorize common stuff more (see below). *)
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
apply (S_bounds n).
Qed.

(*
This lemma is tailored for "aeStep", which will destruct the boolean.

Issues with trying to fit "Z_eqb_dec" in a monadic lemma :
- No premisses.
- Not triggered on a result type.
- No equation of the shape "∃x. ... = Return x".
- No postcondition rewrite rule.
At best, it only provides an "apply".

This motivated the creation of the "StepLemma" typeclass, which copies "MonadicStepLemma" except that it's less constrained but leverages less work.

TODO: We may want to add rewrite rules to "aeSimpl" where e.g. "true = true → P" is replaced by "P". Tacle this kind of simplifications in general is a bit daunting, perhaps "SSReflect" can help here with computations on booleans.
*)
Lemma Z_eqb_dec (x y: Z) :
  ((x =? y) = true  → x = y) ∧
  ((x =? y) = false → x ≠ y).
Proof.
Admitted.

(*  +---------------------------+
    | Monadic lemma conversions |
    +---------------------------+
*)

(* Allow to swap between two formulations of statements about results:
- The match shape, a convenient formulation for partial correctness.
- The existential formula of monadic lemmas, which can be used by "aoStepGoal".
*)
Lemma eq_partial_monadic_lemma {T} {x: result T} {P: T → Prop} :
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

(* Same as "eq_partial_monadic_lemma" but with a precondition. *)
Lemma eq_partial_monadic_lemma_hyp {T} {x: result T} {P: Prop} {Q: T → Prop} :
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
  now apply eq_partial_monadic_lemma.
- apply eq_partial_monadic_lemma. intro.
  now apply H.
Qed.

(* Same as "eq_partial_monadic_lemma" but for total correctness. *)
Lemma eq_total_monadic_lemma {T} {x: result T} {P: T → Prop} :
  (match x with
  | Return a => P a
  | Fail_ _ => False
  end)
  ↔
  (∃ a, x = Return a ∧ P a).
Proof.
split; destruct x; intros.
- now exists t.
- now destruct e.
- destruct H, H.
  injection H.
  intro r. now rewrite r.
- destruct e, H, H; inversion H.
Qed.

Lemma eq_total_monadic_lemma_hyp {T} {x: result T} {P: Prop} {Q: T → Prop} :
  (P → match x with
  | Return a => Q a
  | Fail_ _ => False
  end)
  ↔ (P → ∃ a, x = Return a ∧ Q a).
Proof.
split; intros. 
- now apply eq_total_monadic_lemma, (H H0).
- now apply eq_total_monadic_lemma in H.
Qed.

(* Can be used for automatic proof search. *)
Lemma weaken_oof_guard {A B} {f: result A} {g: A → result B} :
  (v ← f; g v) ≠ Fail_ OutOfFuel →
  f ≠ Fail_ OutOfFuel.
Proof.
destruct f. 1: easy.
now destruct e.
Qed.

(* TODO: Do we want to generalize the "Fail_ OutOfFuel" proposition ? *)
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
rewrite eq_partial_monadic_lemma_hyp. intro H.
assert (f ≠ Fail_ OutOfFuel) by intuition.
revert H.
rewrite <-eq_partial_monadic_lemma_hyp.
intro.
now apply H.
Qed.

(*  +-------------------+
    | Tactics - helpers |
    +-------------------+
*)

(* Small helper to create a new id by encompassing one between two strings. *)
Ltac ltac_new_id prefix id suffix :=
  let old := constr:(ident_to_string id) in
  let new := constr:((prefix ++ old ++ suffix)%string) in
  string_to_ident new.

(* TODO: investigate vec to list induction. *)

(* Usize to nat induction.
   TODO: Support all unsigned scalars.
*)
Ltac induction_usize_to_nat_tac s n :=
  let HeqN := ltac_new_id "Heq"%string n ""%string in
  remember (usize_to_nat s) as n;
  apply eq_sym in HeqN;
  revert s HeqN;
  induction n; intros s HeqN;
  apply (f_equal Z.of_nat) in HeqN;
  rewrite usize_nat_to_Z in HeqN;
  simpl in HeqN.

Tactic Notation "induction_usize_to_nat" simple_intropattern(s) "as" simple_intropattern(n) :=
  induction_usize_to_nat_tac s n.

(* Unfold the fixpoint on the fuel, destruct the fuel, try to solve the case "fuel = 0" then refold the fixpoint because Coq unfold it a second time on the fuel destruction.
   TODO: Investigate how the fuel parameter can be omitted : can we access names, flags, or can we assume that a match pattern on "nat" is about fuel ?
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
  lazymatch goal with
  (* TODO: How to match the already unfolded fixpoint ?
  | [ |- context[ (fix _ (match _ with _ => _ end)) fuel ] ] =>
    destruct fuel;
    only 1: intuition *)
  (* TODO: How to match the nth argument in generality ?
     To avoid duplicating branches and limiting the number of arguments. *)
  (* TODO: How to give a single body for multiple clauses ?
     To avoid factorizing the code in "siphon". *)
  | [ |- context[ ?F _ _ _ _ _ _ _ _ _ fuel ] ] => siphon F
  | [ |- context[ ?F _ _ _ _ _ _ _ _ fuel ] ] => siphon F
  | [ |- context[ ?F _ _ _ _ _ _ _ fuel ] ] => siphon F
  | [ |- context[ ?F _ _ _ _ _ _ fuel ] ] => siphon F
  | [ |- context[ ?F _ _ _ _ _ fuel ] ] => siphon F
  | [ |- context[ ?F _ _ _ _ fuel ] ] => siphon F
  | [ |- context[ ?F _ _ _ fuel ] ] => siphon F
  | [ |- context[ ?F _ _ fuel ] ] => siphon F
  | [ |- context[ ?F _ fuel ] ] => siphon F
  | [ |- context[ ?F fuel ] ] => siphon F
  end.

(*  +--------------------+
    | High-level tactics |
    +--------------------+
*)

(*
TODO: Re-assess the role of an hypothetic "aeProgress" tactic which loop on the three tactics below.

The goal here is to develop a modularized tactic to progress on a given goal by simplifying & solving elements which may be given by the user.
To do that, a high-level "aeProgress" tactic will be built from 3 components:
- "aeStep" which inspects the goal head variable and lookup a (primarily monadic) lemma to apply to it.
- "aeSimpl" which uniformises the hypotheses by simplifying the context and looking up additional hypotheses to introduce.
- "aeSolve" which aims to resolve the obtained goals.

All tactic failures should be specified in their top-level comment.
*)

(*  +-------------+
    | Typeclasses |
    +-------------+
*)

(* Low-level tactic to only resolve typeclasses, without backtracking. It is strictly less powerful than e.g. "exact _". *)
Ltac tc_solve :=
  solve [once (typeclasses eauto)].

(*
Registers lemmas that are applied by the "aeStep" tactic.

The interface for monadic lemmas accept proofs of propositions on expressions "e" of the following shape:
"Preconditions(e) → ∃x:T, e = Return x ∧ Postconditions(e, x)"

The "polymorphic" qualifier is only needed for "T → Prop", which lives one universe above.
*)
Polymorphic Class StepMonadicLemma {T} (f: result T) := {
  stepm_pre : Prop;
  stepm_post : T → Prop;
  stepm_lemma : stepm_pre → ∃(x: T), f = Return x ∧ stepm_post x;
}.

(* Instances for primitives. *)

Global Instance step_monadic_lemma_scalar_add T n m : StepMonadicLemma (@scalar_add T n m) :=
  {| stepm_lemma := S_add_bounded n m; |}.

Global Instance step_monadic_lemma_scalar_mul T n m : StepMonadicLemma (@scalar_mul T n m) :=
  {| stepm_lemma := S_mul_bounded n m; |}.

Global Instance step_monadic_lemma_scalar_sub T n m : StepMonadicLemma (@scalar_sub T n m) :=
  {| stepm_lemma := S_sub_bounded n m; |}.

Global Instance step_monadic_lemma_scalar_div T n m : StepMonadicLemma (@scalar_div T n m) :=
  {| stepm_lemma := S_div_bounded n m; |}.

Global Instance step_monadic_lemma_scalar_rem T n m : StepMonadicLemma (@scalar_rem T n m) :=
  {| stepm_lemma := S_rem_bounded n m; |}.

Global Instance step_monadic_lemma_vec_push_back T v x : StepMonadicLemma (vec_push_back T v x) :=
  {| stepm_lemma := V_push_back_bounded v x; |}.

Global Instance monadic_lemma_vec_index_mut_fwd T v i : StepMonadicLemma (vec_index_mut_fwd T v i) :=
  {| stepm_lemma := V_index_mut_fwd_bounded v i; |}.

Global Instance monadic_lemma_vec_index_mut_back T v i x : StepMonadicLemma (vec_index_mut_back T v i x) :=
  {| stepm_lemma := V_index_mut_back_bounded v i x; |}.

(* Non-monadic variant of "StepMonadicLemma". More versatile but less powerful : it only adds a lemma in hypothesis, assert its precondition then "destruct" the HV ("StepMonadicLemma" morally performs a "destruct" as well).
*)
Class StepLemma {T} (e: T) := {
  step_pre : Prop;
  step_post : Prop;
  step_lemma : step_pre → step_post;
}.

(* Instances for primitives. *)

Global Instance step_lemma_Z_eqb x y : StepLemma (x =? y) :=
  {| step_lemma := λ(_:True), Z_eqb_dec x y; |}.

(*
TODO: The injection on scalars & vectors do not fit as "StepLemma" instances :
"aeStep" destructs the matched expression, which is not an inductive product here.

Instead, we'd need something even weaker than "StepLemma", which only applies a lemma.
*)

(*
Registers types which, when instantiated in an hypothesis, should create an additional hypothesis (typically, to obtain scalar and vector bounds).
*)
Polymorphic Class SimplHypothesis T := {
  simpl_hyp_prop : T → Prop;
  simpl_hyp_lemma (x: T) : simpl_hyp_prop x;
}.

(* Instances for primitives.

TODO: We may want to lift it in sum & product types (Bounded A & Bounded B => Bounded (A, B), ...).
*)

Global Instance simpl_hypothesis_scalar_bounds T : SimplHypothesis (scalar T) :=
  {| simpl_hyp_lemma := S_bounds; |}.

Global Instance simpl_hypothesis_vector_bounds T : SimplHypothesis (vec T) :=
  {| simpl_hyp_lemma := V_bounds; |}.

(* Add bounds to all hypotheses that could have it. The function flow is a bit missed up due to various limitations. *)
Ltac aeAddBounds :=
  lazymatch goal with
  | H: ?A |- _ =>
    (* Continue when failing (see below) - e.g. no TC found.
    TODO: Find a cleaner mechanism.
    *)
    let TC := fresh "TC" in
    tryif pose (TC := (ltac:(tc_solve): SimplHypothesis A))
    then (
      (* Create bounds. Done before checking that it already exists because we need its simplified type to do the match. *)
      let bounds := ltac_new_id ""%string H "_bounds"%string in
      assert (bounds := simpl_hyp_lemma H);
      (* TODO: How to parametrize this "simpl" ? *)
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
        aeAddBounds;
        intro;
        pose (YES := 1)
      | _ =>
        (* Continue, then reintroduce the new bounds. *)
        revert H;
        aeAddBounds;
        intro;
        intro
      end
    )
    else (
      (* No "SimplHypothesis" typeclass : continue. *)
      revert H;
      aeAddBounds;
      intro
    )
  (* No more hypothesis. *)
  | _ => idtac
  end.

(* Oriented equations for simplification : *)

Global Hint Rewrite usize_nat_to_Z:  ae_simpl_rewrite.

Global Hint Rewrite @res_bind_value: ae_simpl_rewrite.
Global Hint Rewrite @res_bind_id:    ae_simpl_rewrite.

(* Propositions. *)
Global Hint Rewrite simpl_bool_tautoT: ae_simpl_rewrite.
Global Hint Rewrite simpl_bool_tautoF: ae_simpl_rewrite.
Global Hint Rewrite simpl_bool_oxyTF: ae_simpl_rewrite.
Global Hint Rewrite simpl_bool_oxyFT: ae_simpl_rewrite.
Global Hint Rewrite simpl_tauto_implies: ae_simpl_rewrite.
Global Hint Rewrite simpl_oxy_implies: ae_simpl_rewrite.
Global Hint Rewrite simpl_conj_trivialR: ae_simpl_rewrite.
Global Hint Rewrite simpl_conj_trivialL: ae_simpl_rewrite.
Global Hint Rewrite simpl_disj_trivialR: ae_simpl_rewrite.
Global Hint Rewrite simpl_disj_trivialL: ae_simpl_rewrite.

(* Uniformize the context and goal with various simplifications, then "simpl"ify everything.
TODO: We may want to merge same hypotheses as well.
*)
Ltac aeSimpl :=
  aeAddBounds;
  autorewrite with ae_simpl_rewrite in *;
  (* "simpl in *" is a bit overboard to do those tasks :
  - We want to simplify e.g. projected scalar and vector constants (which need to be handling by tactics anyway).
  - We want to compute several things, e.g. scalar bounds.
  However, the more fine-grained alternatives are incomplete and more clunky.
  *)
  simpl in *.
  (* With the "impl in *" above, we don't have to simplify scalar constants specifically :
  repeat lazymatch goal with
  (* Scalar constants:
  
  We want a lemma stating something like "to_Z ((mk_scalar T x)%return) = x", but this is not well-formed because of the implicit "eq_refl x" (working for constants but not a generic "x").

  So, we can only state it in tactics, which is why this rewriting rule is hardcoded here.
  *)
  | |- context[ to_Z (eval_result_refl ?A eq_refl) ] =>
      simpl (to_Z (eval_result_refl A eq_refl))
  | H: context[ to_Z (eval_result_refl ?A eq_refl) ] |- _ =>
      simpl (to_Z (eval_result_refl A eq_refl)) in H
  end. *)
  
(* Solves the given goal with "lia" and other tactics or fails.
"intuition" is powerful but modifies the goal even on failure, which is not wanted for "aeSolve".
*)
Ltac aeSolve :=
  aeSimpl;
  easy || lia.

(* Applies an hypothesis about the fuel to the goal if needed, of the shape "... ≠ Fail_ OutOfFuel".
*)
Ltac aeApplyOofHyp H_oof :=
  let rec_on_wedge H_oof := (
    split;
    lazymatch goal with
    | |- (_ ≠ Fail_ OutOfFuel) => aeApplyOofHyp H_oof
    | |- _ => idtac
    end
  ) in
  lazymatch goal with
  (* It's a left or right condition. *)
  | |- _ ∧ (_ ≠ Fail_ OutOfFuel) => rec_on_wedge H_oof
  | |- (_ ≠ Fail_ OutOfFuel) ∧ _ => rec_on_wedge H_oof
  (* The goal may be weaker than the hypothesis. *)
  | |- (_ ≠ Fail_ OutOfFuel) =>
    apply H_oof ||
    apply (weaken_oof_guard H_oof)
  | |- _ => idtac
  end.

(* TODO: "simpl"s in pre/L should only unfold the typeclass fields. *)
Ltac aeApplyMonadicLemma res TC H_oof :=
  (* Add a goal for preconditions *)
  let pre := fresh "pre" in
  assert (pre: stepm_pre);
  lazymatch goal with
  | |- stepm_pre =>
    simpl;
    aeApplyOofHyp H_oof;
    try aeSolve;
    clear TC

  | _ =>
    simpl in pre;
  
    (* Instantiate the lemma with its preconditions. *)
    let L := fresh "L" in
    assert (L := stepm_lemma pre);

    (* Split it into the new variable, the equation and the postconditions. *)
    let H := fresh in
    destruct L as (res, H);
    let eq := fresh "eq" in
    let post := ltac_new_id "H"%string res ""%string in
    destruct H as (eq, post);
    simpl in post;

    (* Rewrite the function application then clear up the context.
    TODO: Add "try rewrite res_bind_value/id" for the rewritten HV ?
    *)
    rewrite eq;
    clear eq;
    clear pre;
    clear TC
  end.

Ltac aeApplyNonMonadicLemma res TC A :=
  (* Add a goal for preconditions. *)
  let pre := fresh "pre" in
  assert (pre: step_pre);
  lazymatch goal with
  | |- step_pre =>
    simpl;
    try aeSolve;
    clear TC

  | |- _ =>
    simpl in pre;
    
    (* Instantiate the lemma then destruct the HV.
    TODO: The destructed variable should be named "res",
    and the lemma "Hres".
    Do it in two times: set (res := P), destruct res.
    *)
    let post := ltac_new_id "H"%string res ""%string in
    assert (post := step_lemma pre);
    simpl in post;
    (* set res *)
    set (res := A) in post |- * at 1;
    simpl in res;
    clear TC;
    clear pre;
    destruct res
  end.

(* Try to apply a monadic lemma, then a non-monadic lemma.
FAIL if both couldn't be applied.
The typeclass instance is moved in "aeApply(Monadic)Lemma", which has the responsibility of clearing it.
*)
Ltac aeApplyLemma A res H_oof :=
  let TC := fresh "TC" in ((
    pose (TC := (ltac:(tc_solve): StepMonadicLemma A));
    aeApplyMonadicLemma res TC H_oof
  ) || (
    pose (TC := (ltac:(tc_solve): StepLemma A));
    aeApplyNonMonadicLemma res TC A
  )).

(* Recursively reaches the head variable.
Performs a depth-first
TODO: Do we want to try applying lemmas while reaching it ?
E.g. fetching a TC on "a = b" before going in "a" or "b".
TODO: Do we go in records, Prop/Type products, ... ?
*)
Ltac aeStepRec G res H_oof :=
  (lazymatch G with
  (* Go under implications.
  TODO: We may want to fail because rewriting under abstractions won't work anyway (or introduce it).
  *)
  | ∀ _, ?A => aeStepRec A res H_oof
  | _ → ?A => aeStepRec A res H_oof
  (* Go under blocking elimination. *)
  | match ?A with _ => _ end => aeStepRec A res H_oof
  (* Go under the error monad. *)
  | Primitives.bind ?A _ => aeStepRec A res H_oof
  (* Go under the equation left side. *)
  | ?A = ?B => aeStepRec A res H_oof || aeStepRec B res H_oof
  end)
  (* We cannot go further, so we need to apply a lemma on "G". *)
  || aeApplyLemma G res H_oof.

(* One of the 3 high-level tactics, along "aeSimpl" and "aeSolve".

Reach the smallest blocking term on the current goal, which will be called the 'head variable' or HV by abuse of language.
Then, it applies a lemma on the HV and tries to satisfy its precondition (if any) with "aeSolve".

TODO: We surely want to call "aeSimpl" automatically every time after "aeStep".
TODO: Match typeclasses in depth-first.
*)
Ltac aeStep res :=
  lazymatch goal with
  (* Add a temporary hypothesis on oof for partial monadic goals.
  TODO: Do we want to also support it for the other monadic shape (... ∧ oof → ∃x, f x = Return x ∧ ...) ?
  *)
  | |- match ?X with
      | Return v => _
      | Fail_ f => match f with
        | OutOfFuel => True
        | Failure => False
      end end =>
    let H_oof := fresh "oof_hyp" in
    apply monadic_oof_hyp;
    intro H_oof;
    aeStepRec X res H_oof;
    clear H_oof

  | |- ?G => 
    let H_oof := fresh "no_oof_hypothesis" in
    aeStepRec G res H_oof
  end.

(* "aeProgress" is a high-level tactic which combines "aeSimpl", "aeSolve" and "aeStep" tactics by calling them until it can't progress anymore.

To implement variadic arguments, the front-end tactic accept one argument but returns a continuation to accumulate the next ones.

It should progress as much as possible, e.g. for the case without parameters if the goal end up solved.
*)

(* We progress by repeatedly simplify then make one step, otherwise try to solve the current goal. *)
Ltac aeProgressOnce x :=
  aeSimpl;
  aeStep x || aeSolve.

(* Without identifiers, "aeProgress" loop as much as it can and does not fail. *)
Ltac aeProgressUnnamed :=
  try repeat (
    let x := fresh "x" in
    aeProgressOnce x
  );
  (* We finish with "aeSimpl" to clean up the last "aeStep". *)
  aeSimpl.

(* With identifiers, "aeProgress" is required to succeed.
Due to limitations to manipulate identifiers as 1st-class values (unless I missed something), they are recursively consumed from the stack by returning a continuation.
Because we cannot match on them, the number of remaining identifiers is explicitly given.
*)
Ltac aeProgressNamed n k x :=
  lazymatch n with
  | 0%nat => aeProgressOnce x; k
  | S ?m => aeProgressNamed m ltac:(aeProgressOnce x; k)
  end.

(* We match the number of arguments to easily inverse their order and pass their number. *)
Tactic Notation "aeProgress" :=
  aeProgressUnnamed.
Tactic Notation "aeProgress" simple_intropattern(a) :=
  aeProgressNamed 0%nat aeProgressUnnamed a.
Tactic Notation "aeProgress" simple_intropattern(a) simple_intropattern(b) :=
  aeProgressNamed 1%nat aeProgressUnnamed b a.
Tactic Notation "aeProgress" simple_intropattern(a) simple_intropattern(b) simple_intropattern(c) :=
  aeProgressNamed 2%nat aeProgressUnnamed c b a.
Tactic Notation "aeProgress" simple_intropattern(a) simple_intropattern(b) simple_intropattern(c) simple_intropattern(d) :=
  aeProgressNamed 3%nat aeProgressUnnamed d c b a.
Tactic Notation "aeProgress" simple_intropattern(a) simple_intropattern(b) simple_intropattern(c) simple_intropattern(d) simple_intropattern(e) :=
  aeProgressNamed 4%nat aeProgressUnnamed e d c b a.
Tactic Notation "aeProgress" simple_intropattern(a) simple_intropattern(b) simple_intropattern(c) simple_intropattern(d) simple_intropattern(e) simple_intropattern(f) :=
  aeProgressNamed 5%nat aeProgressUnnamed f e d c b a.
Tactic Notation "aeProgress" simple_intropattern(a) simple_intropattern(b) simple_intropattern(c) simple_intropattern(d) simple_intropattern(e) simple_intropattern(f) simple_intropattern(g) :=
    aeProgressNamed 6%nat aeProgressUnnamed g f e d c b a.

(*  +-------+
    | Tests |
    +-------+
*)

Module Examples.

Fixpoint usize_identity (fuel: nat) (s: usize) : result usize :=
  match fuel with
  | 0%nat => Fail_ OutOfFuel
  | S fuel =>
    if (scalar_eqb s 0%usize) then Return 0%usize else
      x ← usize_sub s (1%usize);
      y ← usize_identity fuel x;
      usize_add y (1%usize)
  end.

Lemma usize_identity_shape fuel s :
  match usize_identity fuel s with
  | Return v => to_Z s = to_Z v
  | Fail_ OutOfFuel => True
  | Fail_ Failure   => False
  end.
Proof.
(* Induction & common simplifications. *)
revert fuel.
induction_usize_to_nat s as S;
intro fuel;
siphon fuel;
aeProgress b r.

(* IH argument *)
assert (B: usize_to_nat r = S). 1: {
  cut (Z.of_nat (usize_to_nat r) = Z.of_nat S).
  - intuition.
  - aeSolve.
}
assert (H := IHS r B fuel).
destruct (usize_identity fuel r);
aeProgress.
Qed.

(* Want to go both ways: shape <=> ¬oof → instance *)

Global Instance monadic_lemma_usize_identity fuel s : StepMonadicLemma (usize_identity fuel s) :=
  {| stepm_lemma := proj1 eq_partial_monadic_lemma (usize_identity_shape fuel s); |}.

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
aeSimpl.
unfold add_ids.
aeStep n.

(*
This code is used to debug the bug of duplication of hypotheses in "aeSimpl".

COPY-PASTED "aeAddBounds" applied to "s".
Why does it match the hypothesis here and not in "aeSimpl", which duplicates bounds instead ?
*)
let TC := fresh "TC" in
tryif pose (TC := (ltac:(tc_solve): SimplHypothesis usize))
then (
  (* Create bounds. Done before checking that it already exists because we need its simplified type to do the match. *)
  let bounds := ltac_new_id ""%string s2 "_bounds"%string in
  assert (bounds := simpl_hyp_lemma s);
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
  (* No "SimplHypothesis" typeclass : continue. *)
  pose (BRUH := -1)
).
intro.


aeSimpl.
aeStep m.
aeSolve.
Qed.

(* Same lemma as above, but with "aeProgress". *)
Lemma add_ids_shape2 fuel s :
  to_Z s + to_Z s <= usize_max →
  match add_ids fuel s with
  | Fail_ OutOfFuel => True
  | Fail_ Failure   => False
  | Return a => to_Z a = to_Z s + to_Z s
  end.
Proof.
intro.
unfold add_ids.
aeProgress.
Qed.

End Examples.
End Primitives_Ext.
