
Require Import Primitives.
Import Primitives.
Require Import Primitives_Ext.
Import Primitives_Ext.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
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

(* Generic utilities - to put in Primitives_Ext *)

(* Like "injection" but on the goal :
   Given a constructor f, goes from a = b to f a = f b.
   The constructor takes the type explicitly, e.g. "@Some".
   There may already exist something like that somewhere ...
*)
Ltac injection_goal f :=
  lazymatch goal with [ |- ?a = ?b ] =>
    let T := type of a in
    let H := fresh in
    let eq := fresh in
    assert (H: f T a = f T b -> a = b);
    only 1: (intro eq; now injection eq);
    apply H; clear H
  end.

Definition option_map {A B} (f: A -> B) (o: option A) : option B :=
  match o with
  | None => None
  | Some a => Some (f a)
  end.

Lemma nat_eqb_refl (n: nat) : (n =? n)%nat = true.
Proof.
unfold Nat.eqb.
induction n.
- reflexivity.
- exact IHn.
Qed.

Lemma replace_list_len {T} (l: list T) (i: nat) (x: T) :
  List.length (replace_list l i x) = List.length l.
Proof.
revert i.
unfold replace_list.
induction l. 1: reflexivity.
intro. simpl.
destruct i. 1: reflexivity.
simpl.
now rewrite (IHl i).
Qed.

Lemma replace_list_map {A B} (l: list A) (i: nat) (x: A) (f: A -> B) :
  map f (replace_list l i x) = replace_list (map f l) i (f x).
Proof.
revert i.
induction l. 1: trivial.
intro.
destruct i. 1: trivial.
simpl. f_equal.
apply IHl.
Qed.

Lemma nth_error_repeat_dis {T} (n m: nat) (x: T) :
  nth_error (repeat x m) n = Some x \/
  nth_error (repeat x m) n = None.
Proof.
destruct (le_lt_dec m n)%nat as [H|H].
- right.
  assert (List.length (repeat x m) <= n)%nat by now rewrite repeat_length.
  now rewrite <-(proj2 (nth_error_None _ _) H0).
- left. exact (nth_error_repeat x H).
Qed.

Lemma nth_error_empty T (n: nat) :
  nth_error ([]: list T) n = None.
Proof.
now destruct n.
Qed.

Lemma nth_error_map {A B} (l: list A) (f: A -> B) (n: nat) :
  nth_error (map f l) n = option_map f (nth_error l n).
Proof.
revert n.
induction l; intro; destruct n; intuition.
apply IHl.
Qed.

(* Utilities for the hashmap *)

Definition key_id   := usize.
Definition hash_id  := usize.
Definition slot_id  := usize.
Definition chain_id := usize.

(* Hash *)

(* Allows hash_key_fwd to succeed while keeping its implementation opaque with the lemma below. *)
Definition get_hash (k: key_id) : hash_id :=
    (hash_key_fwd k) %return.

Arguments get_hash : simpl never.

Lemma hash_key_success (k: key_id) :
  hash_key_fwd k = Return (get_hash k).
Proof.
reflexivity.
Qed.

(* As a monadic lemma, without pre- nor post-conditions. *)
Lemma hash_key_success2 {k} :
  ∃x, hash_key_fwd k = Return x.

(* Hashmap length *)

Definition hm_length {T} (hm: Hash_map_t T) : usize :=
  hm.(Hash_map_num_entries).

Lemma hm_len_success {T} hm :
  hash_map_len_fwd T hm = Return (hm_length hm).
Proof.
reflexivity.
Qed.

(* Functional hashmap *)

(* The hashmap is represented as a list of slots *)
Definition chain_t T := list (nat * T).
Definition slots_t T := list (chain_t T).

(* Do we want to avoid optionals ?
Definition index_t {T} (l: list T) := { i: nat | (i < List.length l)%nat }. *)

Fixpoint clean_chain {T} (l: List_t T) : chain_t T :=
  match l with
  | ListCons n x t => (usize_to_nat n, x) :: clean_chain t
  | ListNil => nil
  end.

Definition clean_slots {T} (slots: vec (List_t T)) : slots_t T :=
  List.map clean_chain (vec_to_list slots).

Definition slot_values_count {T} (s: slots_t T) :=
  fold_left Nat.add (map (@List.length _) s) 0%nat.

Fixpoint get_chain_value {T} (ch: chain_t T) (k: nat) : option T :=
  match ch with
  | [] => None
  | (k', v) :: t => if (k =? k')%nat
      then Some v
      else get_chain_value t k
  end.

Fixpoint update_chain {T} (ch: chain_t T) (k: nat) (v: T) : chain_t T :=
  match ch with
  | [] => []
  | (k', v') :: t => if (k =? k')%nat
      then (k', v)  :: t
      else (k', v') :: update_chain t k v
  end.

Definition slot_update {T} (s: slots_t T) (i k: nat) (v: T) : slots_t T :=
  match nth_error s i with
  | None => s
  | Some ch => replace_list s i (update_chain ch k v)
  end.

Definition slot_insert {T} (s: slots_t T) (i: nat) (x: nat * T) : slots_t T :=
  match nth_error s i with
  | None => s
  | Some ch => replace_list s i (ch ++ [x])
  end.

(* Main invariants *)

Definition get_hash_pos {T} (s: slots_t T) (k: nat) : nat :=
  k mod (List.length s).

(* Given hm, i, j: give key-value pair *)
Definition get_kv {T} (s: slots_t T) (i j: nat) : option (nat * T) :=
  match nth_error s i with
  | None => None
  | Some ch => nth_error ch j
  end.

Definition option_prop_bind {T} (x: option T) (f: T -> Prop) : Prop :=
  match x with
  | None => True
  | Some x => f x
  end.

Notation "x <-- c1 ; c2" := (option_prop_bind c1 (fun x => c2))
  (at level 61, c1 at next level, right associativity).
  
Definition key_is_in_hash_slot {T} (s: slots_t T) (i j: nat) : Prop :=
  kv <-- get_kv s i j;
  (get_hash_pos s (fst kv) = i).

Definition no_key_duplicate {T} (s: slots_t T) (i j1 j2: nat) (p: j1 <> j2) : Prop :=
  kv1 <-- get_kv s i j1;
  kv2 <-- get_kv s i j2;
  (fst kv1 <> fst kv2).

Definition slots_invariants {T} (s: slots_t T) :=
  (∀i j, key_is_in_hash_slot s i j) /\
  (∀i j1 j2 p, no_key_duplicate s i j1 j2 p).

Definition hm_invariants {T} (hm: Hash_map_t T) :=
  slots_invariants (clean_slots (Hash_map_slots hm)).

(*  +----------------------------------+
    | Theorems - functional invariants |
    +----------------------------------+
*)

Lemma slot_update_len {T} (s: slots_t T) (i k: nat) (v: T) :
  List.length (slot_update s i k v) = List.length s.
Proof.
unfold slot_update.
destruct (nth_error s i). 2: reflexivity.
now rewrite replace_list_len.
Qed.

Lemma update_chain_len {T} (ch: chain_t T) (k: nat) (v: T) :
  List.length (update_chain ch k v) = List.length ch.
Proof.
induction ch. 1: trivial.
simpl.
destruct a.
destruct (k =? n)%nat. 1: trivial.
simpl.
now rewrite IHch.
Qed.

Lemma replace_list_eq {T} (l: list T) (i: nat) :
  match nth_error l i with
  | None => True
  | Some x => replace_list l i x = l
  end.
Proof.
revert l.
induction i; intro.
1: destruct l; reflexivity.

destruct l; simpl.
1: trivial.

assert (H := IHi l).
destruct (nth_error l i).
- now f_equal.
- trivial. 
Qed.

Lemma slot_update_count {T} (s: slots_t T) (i k: nat) (v: T) :
  slot_values_count (slot_update s i k v) = slot_values_count s.
Proof.
unfold slot_update.
remember (nth_error s i) as C.
destruct C. 2: trivial.
unfold slot_values_count.
f_equal.
rewrite replace_list_map.
rewrite update_chain_len.
set (length := Datatypes.length (A:=nat * T)).
assert (H := replace_list_eq (map length s) i).
remember (nth_error (map length s) i) as N.
destruct N; rewrite nth_error_map in HeqN.
- (* Rewrite issue : we isolate the rewrite target *)
  change ((fun x => Some n = option_map length x)(nth_error s i)) in HeqN.
  rewrite <-HeqC in HeqN. simpl in HeqN.
  injection HeqN. intro. now rewrite <-H0.
- (* Same issue here *)
  change ((fun x => None = option_map length x)(nth_error s i)) in HeqN.
  rewrite <-HeqC in HeqN.
  inversion HeqN.
Qed.

Lemma slot_insert_count {T} (s: slots_t T) (i: nat) (x: (nat * T)) :
  (* i < length s -> *)
  slot_values_count (slot_insert s i x) = S (slot_values_count s).
Proof.
admit.
Admitted.

Lemma slot_update_same_keys {T} (s: slots_t T) (i k: nat) (v: T) :
  ∀a b,
  match (get_kv s a b, get_kv (slot_update s i k v) a b) with
  | (None, None) => True
  | (Some kv1, Some kv2) => fst kv1 = fst kv2
  | _ => False
  end.
Proof.
intros.
remember (get_kv s a b) as X.
remember (get_kv (slot_update s i k v) a b) as Y.
destruct X, Y. 4: reflexivity.
1: {
unfold get_kv in *.
admit.
}
(* For 2-3: nth_error must have same shape on lists of same length. *)
admit.
admit.
Admitted.

Lemma inv_empty T (n: nat) : slots_invariants (repeat ([]: chain_t T) n).
Proof.
unfold slots_invariants.
split; intros;
try unfold key_is_in_hash_slot, no_key_duplicate, get_kv;
destruct (nth_error_repeat_dis i n ([]: chain_t T));
rewrite H;
try exact I;
now rewrite nth_error_empty.
Qed.

Lemma inv_update {T} (s: slots_t T) (i k: nat) (v: T) :
  slots_invariants s -> slots_invariants (slot_update s i k v).
Proof.
intro inv.
destruct inv as (inv0, inv1).

unfold slots_invariants.
split; intros.
- unfold key_is_in_hash_slot in *.
  assert (H0 := inv0 i0 j).
  assert (H1 := slot_update_same_keys s i k v i0 j).
  set (s' := slot_update s i k v) in *.
  destruct (get_kv s i0 j), (get_kv s' i0 j);
  simpl in *; try trivial. 2: now exfalso.
  rewrite <-H1. unfold get_hash_pos in *. simpl.
  unfold s'.
  now rewrite slot_update_len.
- unfold no_key_duplicate in *.
  assert (H0 := inv1 i0 j1 j2 p).
  assert (H1 := slot_update_same_keys s i k v i0 j1).
  assert (H2 := slot_update_same_keys s i k v i0 j2).
  set (s' := slot_update s i k v) in *.
  now destruct (get_kv s i0 j1),  (get_kv s i0 j2),
           (get_kv s' i0 j1), (get_kv s' i0 j2);
  simpl in *; intuition.
Qed.

Lemma inv_insert {T} (s: slots_t T) (i: nat) (x: nat * T) :
  slots_invariants s -> slots_invariants (slot_insert s i x).
Proof.
Admitted.

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
    | Return v' => clean_slots v' =
      (clean_slots v) ++
      (repeat [] (usize_to_nat n))
    | Fail_ OutOfFuel => True
    | Fail_ Failure => False
    end.
Proof.
revert fuel v.
induction_usize_to_nat n as N;
intros;
siphon fuel;
aeStep as Hn0.

(* zero case *)
1: now rewrite app_nil_r.

(* successor case *)
aeStep as w.
aeStep as y.

simpl.

assert (P3: ((clean_slots v) ++ [[]]: list (chain_t T)) = clean_slots w).
1: {
  change ([[]]) with (map (@clean_chain T) [ListNil]).
  unfold clean_slots.
  rewrite <-map_app.
  now rewrite <-Hw.
}
rewrite cons_app_sing.
rewrite app_assoc.

(* To show implicit parameters or remove notations :
    Set Printing Explicit/All.
*)
(* For some reason, "rewrite" doesn't find the subterm, so we massage the goal with "change". *)
change ((clean_slots v ++ [[]]) ++ repeat [] N) with ((fun v1 => v1 ++ repeat [] N) (clean_slots v ++ [[]])).
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
    | Return v' => clean_slots v' = repeat [] (usize_to_nat n)
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

aeStep as Hn0.
aeStep as w.
aeStep as m.

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
(* TODO: Replace by "simpl". However, the rewrite then doesn't work as expected, no idea why for now. *)
rewrite res_bind_value.

remember (usize_sub n 1%usize) as M.
destruct M ; apply eq_sym in HeqM.
2: { destruct e.
- reflexivity.
- exfalso. apply (scalar_sub_fuel _ _ HeqM).
}
aeSimpl.

apply IHN.
- admit. (* exploit HeqM *)
- admit. (* exploit HeqW *)
- admit. (* exploit HeqM *)
Admitted.

(* New hashmap *)

Lemma hm_new_inv T fuel capacity max_load_dividend max_load_divisor :
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
aeSimpl.

aeStep as x.

assert (Hx1 := Z_div_pos (to_Z x) (to_Z max_load_divisor)).
assert (Hx2 := Z_div_lt (to_Z x) (to_Z max_load_divisor)).
aeStep as y.

(* Invariants *)
unfold hm_length, hm_invariants.
split. 2: now aeStep.
simpl clean_slots.
simpl in Hslots.
rewrite Hslots.
apply inv_empty.
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
      get_chain_value (clean_chain l) (usize_to_nat k) = None
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

aeStep as B.
- apply scalar_Z_inj in B. rewrite B.
  split. 1: intuition.
  intro H.
  unfold clean_chain, get_chain_value in H.
  now rewrite nat_eqb_refl in H.
- simpl.
  (* Annoying small things *)
  assert (H: (usize_to_nat k =? usize_to_nat s)%nat = false). {
    apply not_true_iff_false.
    rewrite Nat.eqb_eq.
    intro. apply B.
    apply usize_nat_inj in H.
    now rewrite H.
  }
  rewrite H.
  apply IHl.
Qed.

Lemma hm_insert_in_list_back_shape {T} fuel k v l :
  let k' := usize_to_nat k in 
  match hash_map_insert_in_list_back T fuel k v l with
  | Return l' => match get_chain_value (clean_chain l) k' with
    | None   => clean_chain l' = (clean_chain l) ++ [(k', v)]
    | Some _ => clean_chain l' = update_chain (clean_chain l) k' v
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

aeStep as B.
- apply scalar_Z_inj in B. rewrite B.
  unfold k'. simpl.
  now rewrite nat_eqb_refl.
- assert (H := IHl fuel k v).
  set (hm := hash_map_insert_in_list_back T fuel k v l) in *.
  destruct hm ; simpl. 2: auto.
  unfold k' in *.
  assert (H0: (usize_to_nat k =? usize_to_nat s)%nat = false). {
    apply not_true_iff_false.
    rewrite Nat.eqb_eq.
    intro. apply B.
    apply usize_nat_inj in H0.
    now rewrite H0.
  }
  rewrite H0.
  destruct (get_chain_value (clean_chain l) (usize_to_nat k)) ;
  f_equal ; apply H.
Qed.
(*
Fixpoint slot_find_rec {T} (s: slots_t T) (i k: nat) : option (nat * T) :=
  match s with
  | [] => None
  | ch :: s' => match get_chain_value ch k with
    | None => slot_find_rec s' (S i) k
    | Some v => Some (i, v)
  end end.

Definition slot_find {T} (s: slots_t T) (k: nat) : option (nat * T) := slot_find_rec s 0%nat k.


Lemma slot_find_some {T} (s: slots_t T) (i k: nat) (v: T) :
  slot_find s k = Some (i, v) ->
  get_chain_value (nth_error s i) k = v.
Proof.

Qed.

Fixpoint slot_find2 {T} (s: slots_t T) (k: nat) : option (nat * T) :=
  option_map snd (find (fun kv => (fst kv =? k)%nat) (List.concat s)).

Definition slot_insert_or_update {T} (s: slots_t T) (i k: nat) (v: T) : slots_t T :=
  match nth_error s i with
  | None => s
  | Some ch => slot_update s i k v
  end.

Notation clean_hm hm := (clean_slots (Hash_map_slots hm)).

Lemma hm_insert_no_resize_shape {T} (fuel: nat) (self: Hash_map_t T) (key: usize) (value: T) :
    (0 < vec_length (Hash_map_slots self)
  /\ to_Z (Hash_map_num_entries self) < usize_max)
  ->
  match hash_map_insert_no_resize_fwd_back T fuel self key value with
  | Fail_ Failure   => False
  | Fail_ OutOfFuel => True
  | Return hm => ∃i, (i < List.length (clean_hm self))%nat /\
  clean_hm hm = slot_insert_or_update (clean_hm self) (usize_to_nat key) i value
  end.
Proof.
intro bounds.
unfold hash_map_insert_no_resize_fwd_back.

intro_scalar_bounds key.

(* Keep the hash opaque for clarity *)
rewrite hash_key_success.
rewrite res_bind_value.
set (hash := get_hash key).
intro_scalar_bounds hash.

(* TODO Need preconditions *)
(* TODO(minor) Tactics shouldn't duplicate bounds *)
assert (B := Zrem_lt_pos (to_Z hash) (vec_length (Hash_map_slots self))).
rewrite_scalar_rem as pos.

(* TODO Another simplification from projection *)
unfold vec_len in Hpos. simpl in Hpos.

rewrite_vec_index_mut_fwd as slot.

assert (Hins := hm_insert_in_list_fwd_shape fuel key value slot).
remember (hash_map_insert_in_list_fwd T fuel key value slot) as ins.
destruct ins. 2: intuition.

rewrite res_bind_value.
destruct b.
1: {
rewrite_scalar_add as size.
assert (Hins2 := hm_insert_in_list_back_shape fuel key value slot).
remember (hash_map_insert_in_list_back T fuel key value slot) as ins2.
destruct ins2. 2: intuition.
rename l into new_slot.
simpl in Hins, Hins2 |- *.

rewrite_vec_index_mut_back as new_slots.

destruct Hins. clear H0.
assert (H0 := H I). clear H.

exists (usize_to_nat pos).
split. 1: { admit. (* nat <-> Z issues *) }

unfold clean_slots. simpl.
unfold slot_insert_or_update.
rewrite Hnew_slots.
set (s := vec_to_list (Hash_map_slots self)).
unfold slot_find.

remember (get_chain_value (clean_chain slot) (usize_to_nat key)) as ch in Hins2.
destruct ch. 1: { exfalso. rewrite H0 in Heqch. inversion Heqch. }

unfold hm_invariants. simpl.
assert (clean_slots new_slots = slot_insert (clean_slots (Hash_map_slots self)) (usize_to_nat pos) (usize_to_nat key, value)).
2: { rewrite H. now apply inv_insert. }
}
Qed.
  *)

Notation slots_count_nat hm := (List.length (clean_slots (Hash_map_slots hm))).
Notation slots_count_Z hm := (vec_length (Hash_map_slots hm)).

Lemma slots_count_eq {T} (hm: Hash_map_t T) : Z.of_nat (slots_count_nat hm) = slots_count_Z hm.
Proof.
unfold vec_length, clean_slots.
now rewrite List.map_length.
Qed.

Notation entries_count_Z hm := (to_Z (Hash_map_num_entries hm)).

Lemma hm_insert_no_resize_inv {T} (fuel: nat) (self: Hash_map_t T) (key: usize) (value: T) :
    (0 < slots_count_Z self
  /\ entries_count_Z self < usize_max)
  -> hm_invariants self
  -> match hash_map_insert_no_resize_fwd_back T fuel self key value with
  | Fail_ Failure   => False
  | Fail_ OutOfFuel => True
  | Return hm => hm_invariants hm
    /\ slots_count_Z hm = slots_count_Z self
    /\ (entries_count_Z hm = entries_count_Z self
     \/ entries_count_Z hm = entries_count_Z self + 1)
  end.
Proof.
intros bounds inv.
unfold hash_map_insert_no_resize_fwd_back.

intro_scalar_bounds key.

(* Keep the hash opaque for clarity *)
rewrite hash_key_success.
simpl.
set (hash := get_hash key).
intro_scalar_bounds hash.

assert (B := Zrem_lt_pos (to_Z hash) (vec_length (Hash_map_slots self))).
aeStep as pos.

(* TODO Another simplification from projection
   TODO Unfolding leaks under "to_Z".
*)
unfold vec_len in Hpos. simpl in Hpos.

aeStep as slot.

assert (Hins := hm_insert_in_list_fwd_shape fuel key value slot).
remember (hash_map_insert_in_list_fwd T fuel key value slot) as ins.
destruct ins. 2: intuition.

simpl.
destruct b.

(* Value inserted *)
1: {
aeStep as size.
assert (Hins2 := hm_insert_in_list_back_shape fuel key value slot).
remember (hash_map_insert_in_list_back T fuel key value slot) as ins2.
destruct ins2. 2: intuition.
rename l into new_slot.
simpl in Hins, Hins2 |- *.

aeStep as new_slots.

destruct Hins. clear H0.
assert (H0 := H I). clear H.
remember (get_chain_value (clean_chain slot) (usize_to_nat key)) as ch in Hins2.
destruct ch. 1: { exfalso. rewrite H0 in Heqch. inversion Heqch. }

unfold hm_invariants. simpl.
assert (clean_slots new_slots = slot_insert (clean_slots (Hash_map_slots self)) (usize_to_nat pos) (usize_to_nat key, value)).
2: {
  rewrite H.
  split. now apply inv_insert.
  split.
  - unfold vec_length.
    rewrite Hnew_slots.
    now rewrite replace_list_len.
  - simpl in Hsize. lia.
}

(* The functional proof, part I *)
unfold clean_slots.
rewrite Hnew_slots.
rewrite replace_list_map.
unfold slot_insert.
set (s := vec_to_list (Hash_map_slots self)) in *.
set (i := usize_to_nat pos) in *.
remember (nth_error (map clean_chain s) i) as C.
destruct C.
2: {
  exfalso.
  rewrite nth_error_map, Hslot in HeqC.
  inversion HeqC.
}
f_equal.
rewrite Hins2.
f_equal.
injection_goal @Some.
rewrite HeqC.
rewrite nth_error_map.
rewrite Hslot.
reflexivity.
}
(* Value not inserted.
   TODO: Should factorize with the first branch.
*)
1: {
assert (Hins2 := hm_insert_in_list_back_shape fuel key value slot).
remember (hash_map_insert_in_list_back T fuel key value slot) as ins2.
destruct ins2. 2: intuition.
rename l into new_slot.
simpl in Hins, Hins2 |- *.

aeStep as new_slots.

destruct Hins. clear H.
remember (get_chain_value (clean_chain slot) (usize_to_nat key)) as ch in Hins2.
destruct ch. 2: { exfalso. now apply H0. }

unfold hm_invariants. simpl.
assert (clean_slots new_slots = slot_update (clean_slots (Hash_map_slots self)) (usize_to_nat pos) (usize_to_nat key) value).
2: {
  rewrite H.
  split. now apply inv_update.
  split.
  - unfold vec_length.
    rewrite Hnew_slots.
    now rewrite replace_list_len.
  - lia.
}

(* The functional proof, part II (mostly copied) *)
unfold clean_slots.
rewrite Hnew_slots.
rewrite replace_list_map.
unfold slot_update.
set (s := vec_to_list (Hash_map_slots self)) in *.
set (i := usize_to_nat pos) in *.
remember (nth_error (map clean_chain s) i) as C.
destruct C.
2: {
  exfalso.
  rewrite nth_error_map, Hslot in HeqC.
  inversion HeqC.
}
f_equal.
rewrite Hins2.
f_equal.
injection_goal @Some.
rewrite HeqC.
rewrite nth_error_map.
rewrite Hslot.
reflexivity.
}
Qed.

Fixpoint list_t_length {T} (l: List_t T) :=
  match l with
  | ListNil => 0%nat
  | ListCons _ _ t => S (list_t_length t)
  end.

Lemma hm_move_elements_from_list_inv {T} (fuel: nat) (self: Hash_map_t T) (l: List_t T) :
    (0 < vec_length (Hash_map_slots self)
  /\ entries_count_Z self + Z.of_nat (list_t_length l) <= usize_max)
  -> hm_invariants self
  -> match hash_map_move_elements_from_list_fwd_back T fuel self l with
  | Fail_ Failure   => False
  | Fail_ OutOfFuel => True
  | Return hm => hm_invariants hm /\
      slots_count_Z hm = slots_count_Z self
  end.
Proof.
revert fuel self.
induction l;
intros fuel self bounds inv;
siphon fuel.
2: split; trivial.

simpl in *.
assert (B0: 0 < vec_length (Hash_map_slots self)
∧ entries_count_Z self < usize_max) by lia.
assert (H := hm_insert_no_resize_inv fuel self s t B0 inv).

remember (hash_map_insert_no_resize_fwd_back T fuel self s t) as R.
destruct R. 2: trivial.
aeSimpl.
destruct H as (invH, (s_count, e_count)).

rewrite <-s_count.
apply IHl. 2: intuition.

lia.
Qed.

End Hashmap_Properties.
