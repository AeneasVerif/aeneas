
Require Import Primitives.
Import Primitives.
Require Import Primitives_Ext.
Import Primitives_Ext.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Local Open Scope Primitives_scope.
Require Export Hashmap_Types.
Import Hashmap_Types.
Require Export Hashmap_Funs.
Import Hashmap_Funs.
Require Import Lia.
Require Import Coq.Unicode.Utf8.
Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Bool.Bool.
Import ListNotations.

Module Hashmap_Properties.

(* Utilities for the hashmap *)

Definition key_id   := usize.
Definition hash_id  := usize.
Definition slot_id  := usize.
Definition chain_id := usize.

Definition chain_t T := list (usize * T).

Fixpoint list_t_to_chain {T} (l: List_t T) : chain_t T :=
    match l with
    | ListCons n x t => cons (n, x) (list_t_to_chain t)
    | ListNil => nil
    end.

Definition get_slots_len {T} (hm: Hash_map_t T) : usize :=
    vec_len (List_t T) hm.(Hash_map_slots).

(* Hash *)

Definition get_hash (k: key_id) : hash_id :=
    (hash_key_fwd k) %return.

Definition get_hash_pos {T} (hm: Hash_map_t T) (k: key_id) : result slot_id :=
    scalar_rem (get_hash k) (get_slots_len hm).

(* Given hm, i, j: give key-value pair *)
Definition get_kv {T} (hm: Hash_map_t T) (i: slot_id) (j: chain_id) : result (usize * T) :=
    let l := vec_to_list hm.(Hash_map_slots) in
    ch <- res_of_opt (nth_error l (usize_to_nat i));
    let kv := nth_error (list_t_to_chain ch) (usize_to_nat j) in
    res_of_opt kv.

Definition result_prop_bind {T} (x: result T) (p: T -> Prop) : Prop :=
    match x with
    | Fail_ Failure => True
    | Fail_ OutOfFuel => True
    | Return x => p x
    end.

(* The test from Hashmap_funs.v *)

Example hm_test1_success : ∃fuel,
  test1_fwd fuel = Return tt.
Proof.
unfold test1_fwd.
now exists (50%nat).
Qed.

(* Allocate slots *)

Definition slots_to_chains {T}(slots: vec (List_t T)) : list (chain_t T) :=
    List.map list_t_to_chain (vec_to_list slots).

Lemma hm_allocate_slots_shape (T: Type) (n: usize) (v: vec (List_t T)) (fuel: nat) :
    vec_length v + to_Z n <= usize_max ->
    match hash_map_allocate_slots_fwd T fuel v n with
    | Return v' => slots_to_chains v' =
      (slots_to_chains v) ++
      (repeat [] (usize_to_nat n))
    | Fail_ OutOfFuel => True
    | Fail_ Failure => False
    end.
Proof.
remember (usize_to_nat n) as N.
revert n HeqN fuel v.
induction N ; intros.

(* zero case *)
1: {
(* TODO: Coq unfolds the recursive def a second time with "destruct fuel" *)
unfold hash_map_allocate_slots_fwd.
destruct fuel. trivial.
fold hash_map_allocate_slots_fwd.

apply (f_equal Z.of_nat) in HeqN.
rewrite usize_nat_to_Z in HeqN.
simpl in HeqN.

unfold scalar_eqb.
simpl (to_Z 0 %usize).

remember (to_Z n =? 0) as B.
induction B ; apply eq_sym in HeqB.
 - now rewrite app_nil_r.
 - lia.
}

(* successor case *)
1: {
(* TODO: How to factorize repetitions properly in both cases ? *)
unfold hash_map_allocate_slots_fwd.
destruct fuel. trivial.
fold hash_map_allocate_slots_fwd.

(* Should be factorized with an induction tactic (same for the zero case). *)
assert (H_SN := HeqN).
apply (f_equal Z.of_nat) in HeqN.
rewrite usize_nat_to_Z in HeqN.
simpl in HeqN.

unfold scalar_eqb.
simpl (to_Z 0 %usize).

remember (to_Z n =? 0) as B.
induction B ; apply eq_sym in HeqB.
1: { lia. }

(* Annoying variable renaming then unfolding *)
set (v2 := @ListNil T).
rewrite_vec_push_back v v2 as "w"%string.
unfold v2 in *.

rewrite_scalar_sub n (1%usize) as "y"%string.

simpl in Hy |- *.

assert (P3: ((slots_to_chains v) ++ [[]]: list (chain_t T)) = slots_to_chains w).
1: {
  change ([[]]) with (map (@list_t_to_chain T) [ListNil]).
  unfold slots_to_chains.
  rewrite <-map_app.
  now rewrite <-Hw.
}
rewrite cons_app_sing.
rewrite app_assoc.

(* To show implicit parameters or remove notations :
    Set Printing Explicit/All.
*)

(* For some reason, "rewrite" doesn't find the subterm, so we massage the goal with "change". *)
change ((slots_to_chains v ++ [[]]) ++ repeat [] N) with ((fun v1 => v1 ++ repeat [] N) (slots_to_chains v ++ [[]])).
rewrite P3.

apply IHN.
- unfold usize_to_nat. lia.
- rewrite Hy.
  unfold vec_length.
  rewrite Hw.
  rewrite app_length.
  simpl.
  unfold vec_length in H.
  lia.
}
Qed.

Lemma hm_allocate_slots_inv (T: Type) (n: usize) (v: vec (List_t T)) (fuel: nat) :
    match hash_map_allocate_slots_fwd T fuel (vec_new _) n with
    | Return v' => slots_to_chains v' = repeat [] (usize_to_nat n)
    | Fail_ OutOfFuel => True
    | Fail_ Failure => False
    end.
Proof.
apply hm_allocate_slots_shape.
apply (S_scalar_bounds n).
Qed.

(* Hashmap length *)

Definition hm_length {T} (hm: Hash_map_t T) : usize :=
  hm.(Hash_map_num_entries).

Lemma hm_len_success {T} hm :
  hash_map_len_fwd T hm = Return (hm_length hm).
Proof.
reflexivity.
Qed.

(* Main invariants *)

Notation "x <-- c1 ; c2" := (result_prop_bind c1 (fun x => c2))
(at level 61, c1 at next level, right associativity).

Definition key_is_in_hash_slot {T} (hm: Hash_map_t T) (i: slot_id) (j: chain_id) : Prop :=
    kv <-- get_kv hm i j;
    p  <-- get_hash_pos hm (fst kv);
    (p = i).

Definition no_key_duplicate {T} (hm: Hash_map_t T) (i: slot_id) (j1 j2: chain_id) (p: j1 <> j2) : Prop :=
    kv1 <-- get_kv hm i j1;
    kv2 <-- get_kv hm i j2;
    (fst kv1 <> fst kv2).

Definition hm_invariants {T} (hm: Hash_map_t T) :=
    (∀i j, key_is_in_hash_slot hm i j) /\
    (∀i j1 j2 p, no_key_duplicate hm i j1 j2 p).

(* New hashmap *)

Lemma hm_new_success T fuel capacity max_load_dividend max_load_divisor :
     (0 < to_Z max_load_dividend
   /\ to_Z max_load_dividend < to_Z max_load_divisor
   /\ 0 < to_Z capacity
   /\ to_Z capacity * to_Z max_load_dividend >= to_Z max_load_divisor
   /\ to_Z capacity * to_Z max_load_dividend <= usize_max)
  ->
  match hash_map_new_with_capacity_fwd T fuel capacity max_load_dividend max_load_divisor with
  | Fail_ Failure   => False
  | Fail_ OutOfFuel => True
  | Return hm => hm_invariants hm
              /\ hm_length hm = 0%usize
  end.
Proof.
intro bounds.

unfold hash_map_new_with_capacity_fwd.
remember (hash_map_allocate_slots_fwd T fuel
(vec_new _) capacity) as S.
set (Hslots := hm_allocate_slots_shape T capacity (vec_new _) fuel).
rewrite <-HeqS in Hslots.
destruct S.
2: {
  simpl.
  destruct e.
  - admit.
  - trivial.
}
rewrite res_bind_value.

rewrite_scalar_mul capacity max_load_dividend as "x"%string.

rewrite_scalar_div x max_load_divisor as "y"%string.
1: { admit. }
1: { admit. }

split.
2: { now unfold hm_length. }

(* Invariants *)
unfold hm_invariants.

Admitted.

Example hm_new_no_fail T : ∃fuel,
  hm <- hash_map_new_fwd T fuel;
  Return tt = Return tt.
Proof.
exists (33%nat).
(* The simplification is too costly,
   but the reflexivity proof works.
*)
now cbv.
Qed.

End Hashmap_Properties.
