
Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Local Open Scope Primitives_scope.
Require Import Hashmap_Types.
Import Hashmap_Types.
Require Import Hashmap_Funs.
Import Hashmap_Funs.
Require Import Lia.
Require Import Coq.Unicode.Utf8.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Bool.Bool.

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
