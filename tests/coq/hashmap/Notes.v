
Require Import Coq.Unicode.Utf8.
Require Import Primitives_Ext.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

(* SSReflect settings *)
From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*    +----------------+
      | Hint databases |
      +----------------+
*)
Module Example_Hints.

(* Let's make a lemma on a new nat type addition: *)

Inductive int :=
  | _0 : int
  | _S : int -> int.

Fixpoint add (a b: int) : int :=
  match a with
  | _0    => b
  | _S a' => _S (add a' b)
  end.

Lemma add_zero_r a : add a _0 = a.
Proof.
induction a.
- reflexivity.
- simpl. now rewrite IHa.
Qed.

(* It cannot be proven with the 'auto' tactic alone. *)

Lemma add_zero_r0 a : add a _0 = a.
auto. Admitted.

(* However, we can register lemmas in databases that can be used by 'auto' with "Hint Resolve". Here, we implicitly create a new database "ints". *)

Global Hint Resolve add_zero_r: ints.

(* 'auto' can call lemmas of a given database. *)

Example e1 a : add a _0 = a.
auto with ints. Qed.

Example e2 a : a = add a _0.
auto with ints. Qed.

(* However, it's stuck if the same lemma need to be applied multiple times. *)

Example e3 a : add (add a _0) _0 = a.
auto with ints. Admitted.

(* To do that, we can register lemmas in a rewriting database with "Hint Rewrite". Note that this "ints" is not the same database as the one above. *)

Global Hint Rewrite ->add_zero_r0: ints.

Example e4 a : add a _0 = a.
now autorewrite with ints. Qed.

Example e5 a : a = add a _0.
now autorewrite with ints. Qed.

Example e6 a : add (add a _0) _0 = a.
now autorewrite with ints. Qed.

(* By default, 'auto' applies hints from the core database. *)

Global Hint Resolve add_zero_r: core.

Example e7 a : add a _0 = a.
auto. Qed.

(* Implications are also accepted by "auto", but not equivalences (neither by "autorewrite"). *)

Axiom ax_f: N → N.
Axiom ax_f_inj: ∀a b, ax_f a = ax_f b → a = b.

Global Hint Resolve ax_f_inj: core.

Example e8 a b: ax_f a = ax_f b → a = b.
auto.
Qed.

End Example_Hints.

(*    +------------------+
      | Constants issues |
      +------------------+

We cannot straightforwardly state properties about any constant, seemingly because the reduction is stuck under ∀.

However, may not want lemmas like that.

Example e1 ty (z: Z) : z = to_Z ((mk_scalar ty z)%return).

Example e2 (n: usize) :
  ∃z, (n = z%usize).
*)

(* Search *)

Search (S _ >= _).

(*    +---------------+
      | Ltac2 tactics |
      +---------------+
*)

(* Sources:
 - https://github.com/tchajed/ltac2-tutorial/blob/master/src/ltac2_tutorial.v
 - https://www.pédrot.fr/articles/coqpl2019.pdf
*)

(*    +---------------------+
      | Questions about Coq |
      +---------------------+
*)
(*
    On Ltac:

  How to match a fixpoint ?

  How to do a breath-first search ?
*)

(*    +-----------+
      | SSReflect |
      +-----------+
*)
(*
A new set of tactics and tacticals for Coq :
The reflection is for being able to easily switch between Prop and Bool.
It is small-scale because it's applied locally (not full reflection by default).
For that, some patterns are adopted eg. CoInductive props (see https://hal.inria.fr/inria-00407778/document).
The tactics act on the top of the goal (or 'proof stack').
That allows to not duplicate them for goal or hypothesis, e.g. :
"move=> x" = "intro x", "move: x" = "revert x".
Also lots of small shortcut, e.g. on rewrite :
 - "rewrite {} f" = "rewrite f; clear f"
 - "rewrite /f" = "unfold f"
 - "rewrite -[n.+1 + m]/(n + m).+1" ~= "change ((S n) + m) with (S (n + m))" (patterns for rewrite !)
Encourages some practices such as finishing (sub-)goals with "by ..." tactical for early error.
SSReflect also block "simpl" on several functions (e.g. addition in nat or Z).
However, it aims to compute better than by default :
e.g. on nat, "n <= m -> 51 + n <= 51 + m" is proven by computation (but is usually stuck).
*)

(*    +---------+
      | Lithium |
      +---------+
*)
(*
This is the REfinedC engine to automatize proofs on a deep embedding of C in Coq. The goal here is to understand its top-level tactic "liStep" which advances on the goal (we want something similar), especially how it relates to typeclass inference.
As in Iris & std++, the simplification on Z is disabled. We may want something similar on scalars & vectors to avoid expanding existentials, provided we have a specialized tactic to reduce constants (to_Z 1%usize ~> 1).
The "xxx_hook" ltac functions can be replaced with debug variants to print a trace.
It's a big engine which rebuilds most notions. Reduction comes from Iris's reduction.pm_eval.
The std++ file "base.v" is very instructive. In particular, it tells us that
- Usual "refine" uses are separated from the typeclass "refine", by using "notypeclasses refine" resp. "tc_solve" (which acts like "apply _" but only for typeclasses).
- The typeclasses such as "TCOr" copy the "or" connective. They are used when we want to leverage the typeclass search.
*)
(*
Mentions:
RefinedC does NOT mention "tc_solve/opaque", "SimplifyHyp/Goal", almost no "TCXXX" (one "TCForall2").
*)

(* Avoid the backtracking behavior of "typeclasses eauto", however typeclasses are usually resolved with comon tactics e.g. "exact _". *)
Ltac tc_solve :=
  solve [once (typeclasses eauto)].

(* Taken from "stdpp/base.v" *)

Inductive TCOr (P1 P2 : Prop) : Prop :=
  | TCOr_l: P1 -> TCOr P1 P2
  | TCOr_r: P2 -> TCOr P1 P2.
Existing Class TCOr.
Global Existing Instance TCOr_l | 9.
Global Existing Instance TCOr_r | 10.
Global Hint Mode TCOr ! ! : typeclass_instances.

Inductive TCAnd (P1 P2 : Prop) : Prop := TCAnd_intro : P1 -> P2 -> TCAnd P1 P2.
Existing Class TCAnd.
Global Existing Instance TCAnd_intro.
Global Hint Mode TCAnd ! ! : typeclass_instances.

Inductive TCTrue : Prop := TCTrue_intro : TCTrue.
Existing Class TCTrue.
Global Existing Instance TCTrue_intro.

Inductive TCEq {A} (x : A) : A -> Prop := TCEq_refl : TCEq x x.
Existing Class TCEq.
Global Existing Instance TCEq_refl.
Global Hint Mode TCEq ! - - : typeclass_instances.

Lemma tc_eq_refl {A} (x1 x2 : A) : TCEq x1 x2 <-> x1 = x2.
Proof. split; now destruct 1. Qed.

(* From "Lithium/simpl_instances.v" *)
Class SimplImpl (P : Prop) (Ps : Prop -> Prop) :=
  simpl_impl T: (Ps T) <-> (P -> T).
  
Global Instance simpl_and_impl (P1 P2 : Prop):
  SimplImpl (P1 /\ P2) (fun T => P1 -> P2 -> T).
Proof. split; intuition. Qed.

(* Tests *)

(* Issues:
- cannot precise lookup (any x:T)
- no information if the term is opaque
*)
Class SpecMap {T} (x: T) := {
  spec_lem : Prop;
  spec_val : spec_lem;
}.

Lemma nat_sub_add (a b: nat) : a >= b -> (a - b) + b = a.
Proof. lia. Qed.

Global Instance spec_nat_sub : SpecMap Nat.sub :=
  {| spec_lem := _;
     spec_val := nat_sub_add;
  |}.
  
Definition egg : SpecMap Nat.sub (* := ltac:(tc_solve)*) .
Proof.
pose (L := (ltac:(tc_solve): SpecMap Nat.sub)).
simpl in L.
exact L.
Defined.

Lemma nat_double_sub (a: nat) :
  (a - a) + a = a.
Proof.
(* Ideally, we get the instance for the good lemma and apply it. *)
set (L:= (ltac:(tc_solve): SpecMap Nat.sub)).
simpl in L.
assert (S := spec_val a a).
simpl in S.
Abort.

Lemma tc_or_refl {A B: Prop} : TCOr A B -> A \/ B.
Proof. intuition. Qed.
Lemma tc_and_refl {A B: Prop} : TCAnd A B -> A /\ B.
Proof. intuition. Qed.

Example tc_or_left_fail {A B: Prop} : A -> A \/ B.
Proof. Fail exact _. Abort.

Example tc_or_left {A B: Prop} : A -> A \/ B.
Proof. intro. apply tc_or_refl. revert H. exact _. Qed.

(*    +--------+
      | aeStep |
      +--------+
*)
(*
We want a high-level action which simplifies the goal w.r.t. data specific to Aeneas, which fetches and progress on the head variable (no "context [...]" query !).
Ideally, we would only need to add the needed lemmas for "lia" in the context and run "aeStep" until the next step is not specific to Aeneas.
Because we cannot seem to match "fix" in ltac, we can still aim to unfold/refold and match the fuel pattern.
We should avoid to "simpl" to even block it on Aeneas values (to avoid existential variables expansion), but manage to always simplify constants (e.g. "to_Z 2%usize", also perhaps "to_list [vec of known elements]").
*)

(*
Typeclass v2

Idea: typeclass as map between term (e.g. u32_add) and lemma to apply.
It allows us to avoid referring to the lemma of a function, only to the function itself.

Issues: does not help to see which functions are supported. For automation, we need to unfold the lemma obtained explicitely.
*)
