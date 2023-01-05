
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

(*  +-------------+
    | Definitions |
    +-------------+
*)

(* Utilities for the hashmap *)

Definition key_id   := usize.
Definition hash_id  := usize.
Definition slot_id  := usize.
Definition chain_id := usize.

Definition chain_t T := list (key_id * T).

Fixpoint to_chain {T} (l: List_t T) : chain_t T :=
    match l with
    | ListCons n x t => cons (n, x) (to_chain t)
    | ListNil => nil
    end.

Definition slots_to_chains {T} (slots: vec (List_t T)) : list (chain_t T) :=
  List.map to_chain (vec_to_list slots).

Fixpoint get_chain_value {T} (ch: chain_t T) (k: key_id) :
    option T :=
  match ch with
  | [] => None
  | (k', v) :: t => if (k s= k')
      then Some v
      else get_chain_value t k
  end.

Fixpoint update_chain {T} (ch: chain_t T) (k: key_id) (v: T) :
    chain_t T :=
  match ch with
  | [] => []
  | (k', v') :: t => if (k s= k')
      then (k', v)  :: t
      else (k', v') :: update_chain t k v
  end.

(* Hash *)

(* Allows hash_key_fwd to succeed while keeping its implementation opaque with the lemma below. *)
Definition get_hash (k: key_id) : hash_id :=
    (hash_key_fwd k) %return.

Lemma hash_key_success (k: key_id) :
  hash_key_fwd k = Return (get_hash k).
Proof.
reflexivity.
Qed.

Definition get_hash_pos {T} (slots: vec (List_t T)) (k: key_id) : result slot_id :=
  scalar_rem (get_hash k) (vec_len _ slots).

(* Given hm, i, j: give key-value pair *)
Definition get_kv {T} (chains: list (chain_t T)) (i: slot_id) (j: chain_id) : result (usize * T) :=
    ch <- res_of_opt (nth_error chains (usize_to_nat i));
    let kv := nth_error ch (usize_to_nat j) in
    res_of_opt kv.

Definition result_prop_bind {T} (x: result T) (p: T -> Prop) : Prop :=
    match x with
    | Fail_ Failure => True
    | Fail_ OutOfFuel => True
    | Return x => p x
    end.

Notation "x <-- c1 ; c2" := (result_prop_bind c1 (fun x => c2))
  (at level 61, c1 at next level, right associativity).
  
(* Hashmap length *)

Definition hm_length {T} (hm: Hash_map_t T) : usize :=
  hm.(Hash_map_num_entries).

Lemma hm_len_success {T} hm :
  hash_map_len_fwd T hm = Return (hm_length hm).
Proof.
reflexivity.
Qed.

(* Main invariants *)
(* Do we care keeping vec & scalars, i.e. size limits ? *)

Definition key_is_in_hash_slot {T} (s: vec (List_t T)) (i: slot_id) (j: chain_id) : Prop :=
    kv <-- get_kv (slots_to_chains s) i j;
    p  <-- get_hash_pos s (fst kv);
    (p = i).

Definition no_key_duplicate {T} (chains: list (chain_t T)) (i: slot_id) (j1 j2: chain_id) (p: j1 <> j2) : Prop :=
    kv1 <-- get_kv chains i j1;
    kv2 <-- get_kv chains i j2;
    (fst kv1 <> fst kv2).

Definition hm_invariants {T} (s: vec (List_t T)) :=
    (∀i j, key_is_in_hash_slot s i j) /\
    (∀i j1 j2 p, no_key_duplicate (slots_to_chains s) i j1 j2 p).

(* It may be easier to prove than no_key_duplicate *)
Definition no_key_duplicate_v2 {T} (chains: list (chain_t T)) : Prop :=
  NoDup (map fst (List.concat chains)).

(*  +----------------------------------+
    | Theorems - functional invariants |
    +----------------------------------+
*)

Definition update_chain_inv {T} (s0 s1: vec (List_t T)) (inv: hm_invariants s0) (i: slot_id) (k: key_id) (v: T) :
  (slots_to_chains s0 = slots_to_chains s0) ->
  hm_invariants s1

(*  +--------------------+
    | Theorems - hashmap |
    +--------------------+
*)

(* The test from Hashmap_funs.v *)

Example hm_test1_success : ∃fuel,
  test1_fwd fuel = Return tt.
Proof.
unfold test1_fwd.
now exists (50%nat).
Qed.

(* Allocate slots *)

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
revert fuel v.
induction_usize_to_nat n as N;
intros;
siphon fuel;
destruct_eqb as Hn0.

(* zero case *)
1: now rewrite app_nil_r.

(* successor case *)

rewrite_vec_push_back as w.
rewrite_scalar_sub as y.

simpl in Hy |- *.

assert (P3: ((slots_to_chains v) ++ [[]]: list (chain_t T)) = slots_to_chains w).
1: {
  change ([[]]) with (map (@to_chain T) [ListNil]).
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

Lemma hm_allocate_slots_fuel (T: Type) (n: usize) (v: vec (List_t T)) (fuel: nat) :
  vec_length v + to_Z n < usize_max ->
  Z.of_nat fuel < to_Z n ->
  hash_map_allocate_slots_fwd T fuel v n = Fail_ OutOfFuel.
Proof.
revert n v.
induction fuel. 1: reflexivity.
intros.

unfold hash_map_allocate_slots_fwd.
fold hash_map_allocate_slots_fwd.

destruct_eqb as Hn0.
rewrite_vec_push_back as w.
rewrite_scalar_sub as m.
simpl in Hm.

apply (IHfuel m w). 2: lia.

assert (vec_length w = vec_length v + 1). 2: lia.

unfold vec_length.
rewrite Hw.
rewrite app_length.
simpl.
lia.
Qed.

Lemma hm_allocate_slots_fail (T: Type) (n: usize) (v: vec (List_t T)) (fuel: nat) :
    vec_length v + to_Z n > usize_max ->
    Z.of_nat fuel >= to_Z n ->
    hash_map_allocate_slots_fwd T fuel v n = Fail_ Failure.
Proof.
revert fuel v.
induction_usize_to_nat n as N;
intros;
assert (vb := vec_len_in_usize v).

1: lia. (* Zero case *)

siphon fuel.
destruct_eqb as B.

(* Custom tactics cannot be used as they aim for success. *)
remember (vec_push_back (List_t T) v ListNil) as W.
destruct W ; apply eq_sym in HeqW.
2: { destruct e.
- reflexivity.
- exfalso. apply (vec_push_back_fuel _ _ HeqW).
}
rewrite res_bind_value.

remember (usize_sub n 1%usize) as M.
destruct M ; apply eq_sym in HeqM.
2: { destruct e.
- reflexivity.
- exfalso. apply (scalar_sub_fuel _ _ HeqM).
}
rewrite res_bind_value.
rewrite res_bind_id.

apply IHN.
- admit. (* exploit HeqM *)
- admit. (* exploit HeqW *)
- admit. (* exploit HeqM *)
Admitted.

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

assert (Hv: vec_length (vec_new (List_t T)) + to_Z capacity <= usize_max).
1: simpl ; now rewrite (proj2 (S_scalar_bounds _)).

assert (Hslots := hm_allocate_slots_shape T capacity (vec_new _) fuel Hv).

remember (hash_map_allocate_slots_fwd T fuel
(vec_new _) capacity) as S.

destruct S. 2: exact Hslots.
rewrite res_bind_value.

rewrite_scalar_mul capacity max_load_dividend as x.

assert (Hx1 := Z_div_pos (to_Z x) (to_Z max_load_divisor)).
assert (Hx2 := Z_div_lt (to_Z x) (to_Z max_load_divisor)).
rewrite_scalar_div x max_load_divisor as y.

(* Why do we need the subsequent change ? *)
set (hm := {|
Hash_map_num_entries := 0 %usize;
Hash_map_max_load_factor := (max_load_dividend, max_load_divisor);
Hash_map_max_load := y;
Hash_map_slots := v
|}).
change ({|
Hash_map_num_entries := 0 %usize;
Hash_map_max_load_factor := (max_load_dividend, max_load_divisor);
Hash_map_max_load := y;
Hash_map_slots := v
|}) with hm.

(* Invariants are easy as long as slots are empty *)
assert (G: ∀i, ∀j, get_kv hm i j = Fail_ Failure).
1: {
intros.
unfold get_kv.
simpl (Hash_map_slots hm).
simpl in Hslots.
rewrite Hslots.

remember ((usize_to_nat i) <? (usize_to_nat capacity))%nat as C.
destruct C ; apply eq_sym in HeqC.
- rewrite Nat.ltb_lt in HeqC.
  rewrite nth_error_repeat. 2: exact HeqC.
  destruct (usize_to_nat j) ; reflexivity.
- rewrite Nat.ltb_ge in HeqC.
  rewrite (proj2 (nth_error_None _ _)).
  + reflexivity.
  + now rewrite repeat_length.
}

(* The invariants *)
split. 2: now unfold hm_length.
split ; intros.
- unfold key_is_in_hash_slot.
  now rewrite G.
- unfold no_key_duplicate.
  now rewrite G.
Qed.

Example hm_new_no_fail T : ∃fuel,
  hm <- hash_map_new_fwd T fuel;
  Return tt = Return tt.
Proof.
exists (33%nat).
(* The simplification is too costly but the reflexivity proof works. *)
now cbv.
Qed.

(* Insertion *)

Lemma hm_insert_in_list_fwd_shape {T} fuel k v l :
  match hash_map_insert_in_list_fwd T fuel k v l with
  | Return b => Bool.Is_true b <->
      get_chain_value (to_chain l) k = None
  | Fail_ OutOfFuel => True
  | Fail_ Failure => False
  end.
Proof.
revert fuel k v.
induction l;
intros;
siphon fuel.

(* Nil case *)
2: intuition.

(* The tactic doesn't help here: we really want "(k s= s) = true" instead of "to_Z k = to_Z s", because we rewrite "s=" twice. *)
remember (s s= k) as B.
rewrite Zeqb_sym in HeqB.
destruct B ; apply eq_sym in HeqB.
- split. 1: intuition.
  intro H.
  unfold to_chain, get_chain_value in H.
  rewrite HeqB in H.
  inversion H.
- rewrite res_bind_id.
  simpl.
  rewrite HeqB.
  apply IHl.
Qed.

Lemma hm_insert_in_list_back_shape {T} fuel k v l :
  match hash_map_insert_in_list_back T fuel k v l with
  | Return l' => match get_chain_value (to_chain l) k with
    | None   => to_chain l' = (to_chain l) ++ [(k, v)]
    | Some _ => to_chain l' = update_chain (to_chain l) k v
  end
  | Fail_ OutOfFuel => True
  | Fail_ Failure => False
  end.
Proof.
revert fuel k v.
induction l;
intros;
siphon fuel.

(* Nil case *)
2: reflexivity.

remember (s s= k) as B.
destruct B ; apply eq_sym in HeqB.
1: { (* Lots of small changes on B... *)
simpl.
rewrite Zeqb_sym, HeqB.
rewrite Z.eqb_eq in HeqB.
apply scalar_Z_inj in HeqB.
now rewrite HeqB.
}

assert (H := IHl fuel k v).
set (hm := hash_map_insert_in_list_back T fuel k v l) in *.
destruct hm ; simpl. 2: auto.
rewrite Zeqb_sym, HeqB.
destruct (get_chain_value (to_chain l) k) ;
f_equal ; apply H.
Qed.

Lemma hm_insert_no_resize_shape {T} (fuel: nat) (self: Hash_map_t T) (key: usize) (value: T) :
  hm_invariants self ->
  match hash_map_insert_no_resize_fwd_back T fuel self key value with
  | Fail_ Failure   => False
  | Fail_ OutOfFuel => True
  | Return hm => hm_invariants hm
            (* /\ spec_on_values self hm *)
  end.
Proof.
intro inv.
unfold hash_map_insert_no_resize_fwd_back.

intro_scalar_bounds key.

(* TODO Should treat hash_key_fwd as an opaque but non-failing function, to keep the 'hash' value separated. *)
unfold hash_key_fwd.
rewrite res_bind_value.

(* TODO Need preconditions *)
(* TODO(minor) Tactics shouldn't duplicate bounds *)
rewrite_scalar_rem as pos. 1-2: admit.
(* TODO Another simplification from projection *)
unfold vec_len in Hpos. simpl in Hpos.

rewrite_vec_index_mut_fwd as slot. 1: admit.

assert (Hins := hm_insert_in_list_fwd_shape fuel key value slot).
remember (hash_map_insert_in_list_fwd T fuel key value slot) as ins.
destruct ins. 2: exact Hins.

rewrite res_bind_value.
destruct b.

(* Value inserted case *)
1: {
admit.
}
(* Value not inserted *)
1: {
assert (Hins2 := hm_insert_in_list_back_shape fuel key value slot).
remember (hash_map_insert_in_list_back T fuel key value slot) as ins2.
destruct ins2. 2: exact Hins2.
rename l into new_slot.
simpl.



rewrite_vec_index_mut_back as new_slots. 1: admit.

(*set (new_self := {|
    Hash_map_num_entries := Hash_map_num_entries self;
    Hash_map_max_load_factor := Hash_map_max_load_factor self;
    Hash_map_max_load := Hash_map_max_load self;
    Hash_map_slots := new_slots;
  |}).*)

destruct inv as (key_in, no_dup).
split ; intros.
- unfold key_is_in_hash_slot, get_kv, get_hash_pos, get_slots_len.
  simpl.
  admit.
- admit.
}
Admitted.

End Hashmap_Properties.
