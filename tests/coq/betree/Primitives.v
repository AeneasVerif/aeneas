Require Import Lia.
Require Coq.Strings.Ascii.
Require Coq.Strings.String.
Require Import Coq.Program.Equality.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znat.
Require Import List.
Import ListNotations.

Module Primitives.

  (* TODO: use more *)
Declare Scope Primitives_scope.

(*** Result *)

Inductive error :=
  | Failure
  | OutOfFuel.

Inductive result A :=
  | Return : A -> result A
  | Fail_ : error -> result A.

Arguments Return {_} a.
Arguments Fail_ {_}.

Definition bind {A B} (m: result A) (f: A -> result B) : result B :=
  match m with
  | Fail_ e => Fail_ e
  | Return x => f x
  end.

Definition return_ {A: Type} (x: A) : result A := Return x.
Definition fail_ {A: Type} (e: error) : result A := Fail_ e.

Notation "x <- c1 ; c2" := (bind c1 (fun x => c2))
  (at level 61, c1 at next level, right associativity).

(** Monadic assert *)
Definition massert (b: bool) : result unit :=
  if b then Return tt else Fail_ Failure.

(** Normalize and unwrap a successful result (used for globals) *)
Definition eval_result_refl {A} {x} (a: result A) (p: a = Return x) : A :=
  match a as r return (r = Return x -> A) with
  | Return a' => fun _  => a'
  | Fail_ e   => fun p' =>
      False_rect _ (eq_ind (Fail_ e)
          (fun e : result A =>
          match e with
          | Return _ => False
          | Fail_ e => True
          end)
        I (Return x) p')
  end p.

Notation "x %global" := (eval_result_refl x eq_refl) (at level 40).
Notation "x %return" := (eval_result_refl x eq_refl) (at level 40).

(* Sanity check *)
Check (if true then Return (1 + 2) else Fail_ Failure)%global = 3.

(*** Misc *)


Definition string := Coq.Strings.String.string.
Definition char := Coq.Strings.Ascii.ascii.
Definition char_of_byte := Coq.Strings.Ascii.ascii_of_byte.

Definition mem_replace_fwd (a : Type) (x : a) (y : a) : a := x .
Definition mem_replace_back (a : Type) (x : a) (y : a) : a := y .

(*** Scalars *)

Definition i8_min   : Z := -128%Z.
Definition i8_max   : Z := 127%Z.
Definition i16_min  : Z := -32768%Z.
Definition i16_max  : Z := 32767%Z.
Definition i32_min  : Z := -2147483648%Z.
Definition i32_max  : Z := 2147483647%Z.
Definition i64_min  : Z := -9223372036854775808%Z.
Definition i64_max  : Z := 9223372036854775807%Z.
Definition i128_min : Z := -170141183460469231731687303715884105728%Z.
Definition i128_max : Z := 170141183460469231731687303715884105727%Z.
Definition u8_min   : Z := 0%Z.
Definition u8_max   : Z := 255%Z.
Definition u16_min  : Z := 0%Z.
Definition u16_max  : Z := 65535%Z.
Definition u32_min  : Z := 0%Z.
Definition u32_max  : Z := 4294967295%Z.
Definition u64_min  : Z := 0%Z.
Definition u64_max  : Z := 18446744073709551615%Z.
Definition u128_min : Z := 0%Z.
Definition u128_max : Z := 340282366920938463463374607431768211455%Z.

(** The bounds of [isize] and [usize] vary with the architecture. *)
Axiom isize_min : Z.
Axiom isize_max : Z.
Definition usize_min : Z := 0%Z.
Axiom usize_max : Z.

Open Scope Z_scope.

(** We provide those lemmas to reason about the bounds of [isize] and [usize] *)
Axiom isize_min_bound : isize_min <= i32_min.
Axiom isize_max_bound : i32_max <= isize_max.
Axiom usize_max_bound : u32_max <= usize_max.

Inductive scalar_ty :=
  | Isize
  | I8
  | I16
  | I32
  | I64
  | I128
  | Usize
  | U8
  | U16
  | U32
  | U64
  | U128
.

Definition scalar_min (ty: scalar_ty) : Z :=
  match ty with
  | Isize => isize_min
  | I8 => i8_min
  | I16 => i16_min
  | I32 => i32_min
  | I64 => i64_min
  | I128 => i128_min
  | Usize => usize_min
  | U8 => u8_min
  | U16 => u16_min
  | U32 => u32_min
  | U64 => u64_min
  | U128 => u128_min
end.

Definition scalar_max (ty: scalar_ty) : Z :=
  match ty with
  | Isize => isize_max
  | I8 => i8_max
  | I16 => i16_max
  | I32 => i32_max
  | I64 => i64_max
  | I128 => i128_max
  | Usize => usize_max
  | U8 => u8_max
  | U16 => u16_max
  | U32 => u32_max
  | U64 => u64_max
  | U128 => u128_max
end.

(** We use the following conservative bounds to make sure we can compute bound
    checks in most situations *)
Definition scalar_min_cons (ty: scalar_ty) : Z :=
  match ty with
  | Isize => i32_min
  | Usize => u32_min
  | _ => scalar_min ty
end.

Definition scalar_max_cons (ty: scalar_ty) : Z :=
  match ty with
  | Isize => i32_max
  | Usize => u32_max
  | _ => scalar_max ty
end.

Lemma scalar_min_cons_valid : forall ty, scalar_min ty <= scalar_min_cons ty .
Proof.
  destruct ty; unfold scalar_min_cons, scalar_min; try lia.
  - pose isize_min_bound; lia.
  - apply Z.le_refl.
Qed.

Lemma scalar_max_cons_valid : forall ty, scalar_max ty >= scalar_max_cons ty .
Proof.
  destruct ty; unfold scalar_max_cons, scalar_max; try lia.
  - pose isize_max_bound; lia.
  - pose usize_max_bound. lia.
Qed.

Definition scalar (ty: scalar_ty) : Type :=
 { x: Z | scalar_min ty <= x <= scalar_max ty }.

Definition to_Z {ty} (x: scalar ty) : Z := proj1_sig x.

(** Bounds checks: we start by using the conservative bounds, to make sure we
    can compute in most situations, then we use the real bounds (for [isize]
    and [usize]). *)
Definition scalar_ge_min (ty: scalar_ty) (x: Z) : bool :=
  Z.leb (scalar_min_cons ty) x || Z.leb (scalar_min ty) x.

Definition scalar_le_max (ty: scalar_ty) (x: Z) : bool :=
  Z.leb x (scalar_max_cons ty) || Z.leb x (scalar_max ty).

Lemma scalar_ge_min_valid (ty: scalar_ty) (x: Z) :
  scalar_ge_min ty x = true -> scalar_min ty <= x .
Proof.
  unfold scalar_ge_min.
  pose (scalar_min_cons_valid ty).
  lia.
Qed.

Lemma scalar_le_max_valid (ty: scalar_ty) (x: Z) :
  scalar_le_max ty x = true -> x <= scalar_max ty .
Proof.
  unfold scalar_le_max.
  pose (scalar_max_cons_valid ty).
  lia.
Qed.

Definition scalar_in_bounds (ty: scalar_ty) (x: Z) : bool :=
  scalar_ge_min ty x && scalar_le_max ty x .

Lemma scalar_in_bounds_valid (ty: scalar_ty) (x: Z) :
  scalar_in_bounds ty x = true -> scalar_min ty <= x <= scalar_max ty .
Proof.
  unfold scalar_in_bounds.
  intros H.
  destruct (scalar_ge_min ty x) eqn:Hmin.
  - destruct (scalar_le_max ty x) eqn:Hmax.
    + pose (scalar_ge_min_valid ty x Hmin).
      pose (scalar_le_max_valid ty x Hmax).
      lia.
    + inversion H.
  - inversion H.
Qed.

Import Sumbool.

Definition mk_scalar (ty: scalar_ty) (x: Z) : result (scalar ty) :=
  match sumbool_of_bool (scalar_in_bounds ty x) with
  | left H => Return (exist _ x (scalar_in_bounds_valid _ _ H))
  | right _ => Fail_ Failure
  end.

Definition scalar_add {ty} (x y: scalar ty) : result (scalar ty) := mk_scalar ty (to_Z x + to_Z y).

Definition scalar_sub {ty} (x y: scalar ty) : result (scalar ty) := mk_scalar ty (to_Z x - to_Z y).

Definition scalar_mul {ty} (x y: scalar ty) : result (scalar ty) := mk_scalar ty (to_Z x * to_Z y).

Definition scalar_div {ty} (x y: scalar ty) : result (scalar ty) :=
  if to_Z y =? 0 then Fail_ Failure else
  mk_scalar ty (to_Z x / to_Z y).

Definition scalar_rem {ty} (x y: scalar ty) : result (scalar ty) := mk_scalar ty (Z.rem (to_Z x) (to_Z y)).
  
Definition scalar_neg {ty} (x: scalar ty) : result (scalar ty) := mk_scalar ty (-(to_Z x)).

(** Cast an integer from a [src_ty] to a [tgt_ty] *)
(* TODO: check the semantics of casts in Rust *)
Definition scalar_cast (src_ty tgt_ty : scalar_ty) (x : scalar src_ty) : result (scalar tgt_ty) :=
  mk_scalar tgt_ty (to_Z x).

(** Comparisons *)
Definition scalar_leb {ty : scalar_ty} (x : scalar ty) (y : scalar ty) : bool :=
  Z.leb (to_Z x) (to_Z y) .

Definition scalar_ltb {ty : scalar_ty} (x : scalar ty) (y : scalar ty) : bool :=
  Z.ltb (to_Z x) (to_Z y) .

Definition scalar_geb {ty : scalar_ty} (x : scalar ty) (y : scalar ty) : bool :=
  Z.geb (to_Z x) (to_Z y) .

Definition scalar_gtb {ty : scalar_ty} (x : scalar ty) (y : scalar ty) : bool :=
  Z.gtb (to_Z x) (to_Z y) .

Definition scalar_eqb {ty : scalar_ty} (x : scalar ty) (y : scalar ty) : bool :=
  Z.eqb (to_Z x) (to_Z y) .

Definition scalar_neqb {ty : scalar_ty} (x : scalar ty) (y : scalar ty) : bool :=
  negb (Z.eqb (to_Z x) (to_Z y)) .


(** The scalar types *)
Definition isize := scalar Isize.
Definition i8    := scalar I8.
Definition i16   := scalar I16.
Definition i32   := scalar I32.
Definition i64   := scalar I64.
Definition i128  := scalar I128.
Definition usize := scalar Usize.
Definition u8    := scalar U8.
Definition u16   := scalar U16.
Definition u32   := scalar U32.
Definition u64   := scalar U64.
Definition u128  := scalar U128.

(** Negaion *)
Definition isize_neg := @scalar_neg Isize.
Definition i8_neg    := @scalar_neg I8.
Definition i16_neg   := @scalar_neg I16.
Definition i32_neg   := @scalar_neg I32.
Definition i64_neg   := @scalar_neg I64.
Definition i128_neg  := @scalar_neg I128.

(** Division *)
Definition isize_div := @scalar_div Isize.
Definition i8_div    := @scalar_div I8.
Definition i16_div   := @scalar_div I16.
Definition i32_div   := @scalar_div I32.
Definition i64_div   := @scalar_div I64.
Definition i128_div  := @scalar_div I128.
Definition usize_div := @scalar_div Usize.
Definition u8_div    := @scalar_div U8.
Definition u16_div   := @scalar_div U16.
Definition u32_div   := @scalar_div U32.
Definition u64_div   := @scalar_div U64.
Definition u128_div  := @scalar_div U128.

(** Remainder *)
Definition isize_rem := @scalar_rem Isize.
Definition i8_rem    := @scalar_rem I8.
Definition i16_rem   := @scalar_rem I16.
Definition i32_rem   := @scalar_rem I32.
Definition i64_rem   := @scalar_rem I64.
Definition i128_rem  := @scalar_rem I128.
Definition usize_rem := @scalar_rem Usize.
Definition u8_rem    := @scalar_rem U8.
Definition u16_rem   := @scalar_rem U16.
Definition u32_rem   := @scalar_rem U32.
Definition u64_rem   := @scalar_rem U64.
Definition u128_rem  := @scalar_rem U128.

(** Addition *)
Definition isize_add := @scalar_add Isize.
Definition i8_add    := @scalar_add I8.
Definition i16_add   := @scalar_add I16.
Definition i32_add   := @scalar_add I32.
Definition i64_add   := @scalar_add I64.
Definition i128_add  := @scalar_add I128.
Definition usize_add := @scalar_add Usize.
Definition u8_add    := @scalar_add U8.
Definition u16_add   := @scalar_add U16.
Definition u32_add   := @scalar_add U32.
Definition u64_add   := @scalar_add U64.
Definition u128_add  := @scalar_add U128.

(** Substraction *)
Definition isize_sub := @scalar_sub Isize.
Definition i8_sub    := @scalar_sub I8.
Definition i16_sub   := @scalar_sub I16.
Definition i32_sub   := @scalar_sub I32.
Definition i64_sub   := @scalar_sub I64.
Definition i128_sub  := @scalar_sub I128.
Definition usize_sub := @scalar_sub Usize.
Definition u8_sub    := @scalar_sub U8.
Definition u16_sub   := @scalar_sub U16.
Definition u32_sub   := @scalar_sub U32.
Definition u64_sub   := @scalar_sub U64.
Definition u128_sub  := @scalar_sub U128.

(** Multiplication *)
Definition isize_mul := @scalar_mul Isize.
Definition i8_mul    := @scalar_mul I8.
Definition i16_mul   := @scalar_mul I16.
Definition i32_mul   := @scalar_mul I32.
Definition i64_mul   := @scalar_mul I64.
Definition i128_mul  := @scalar_mul I128.
Definition usize_mul := @scalar_mul Usize.
Definition u8_mul    := @scalar_mul U8.
Definition u16_mul   := @scalar_mul U16.
Definition u32_mul   := @scalar_mul U32.
Definition u64_mul   := @scalar_mul U64.
Definition u128_mul  := @scalar_mul U128.

(** Small utility *)
Definition usize_to_nat (x: usize) : nat := Z.to_nat (to_Z x).

(** Notations *)
Notation "x %isize" := ((mk_scalar Isize x)%return) (at level 9).
Notation "x %i8"    := ((mk_scalar I8    x)%return) (at level 9).
Notation "x %i16"   := ((mk_scalar I16   x)%return) (at level 9).
Notation "x %i32"   := ((mk_scalar I32   x)%return) (at level 9).
Notation "x %i64"   := ((mk_scalar I64   x)%return) (at level 9).
Notation "x %i128"  := ((mk_scalar I128  x)%return) (at level 9).
Notation "x %usize" := ((mk_scalar Usize x)%return) (at level 9).
Notation "x %u8"    := ((mk_scalar U8    x)%return) (at level 9).
Notation "x %u16"   := ((mk_scalar U16   x)%return) (at level 9).
Notation "x %u32"   := ((mk_scalar U32   x)%return) (at level 9).
Notation "x %u64"   := ((mk_scalar U64   x)%return) (at level 9).
Notation "x %u128"  := ((mk_scalar U128  x)%return) (at level 9).

Notation "x s= y" := (scalar_eqb x y)  (at level 80) : Primitives_scope.
Notation "x s<> y" := (scalar_neqb x y) (at level 80) : Primitives_scope.
Notation "x s<= y" := (scalar_leb x y)  (at level 80) : Primitives_scope.
Notation "x s< y" := (scalar_ltb x y)  (at level 80) : Primitives_scope.
Notation "x s>= y" := (scalar_geb x y)  (at level 80) : Primitives_scope.
Notation "x s> y" := (scalar_gtb x y)  (at level 80) : Primitives_scope.

(*** Vectors *)

Definition vec T := { l: list T | Z.of_nat (length l) <= usize_max }.

Definition vec_to_list {T: Type} (v: vec T) : list T := proj1_sig v.

Definition vec_length {T: Type} (v: vec T) : Z := Z.of_nat (length (vec_to_list v)).

Lemma le_0_usize_max : 0 <= usize_max.
Proof.
  pose (H := usize_max_bound).
  unfold u32_max in H.
  lia.
Qed.

Definition vec_new (T: Type) : vec T := (exist _ [] le_0_usize_max).

Lemma vec_len_in_usize {T} (v: vec T) : usize_min <= vec_length v <= usize_max.
Proof.
  unfold vec_length, usize_min.
  split.
  - lia.
  - apply (proj2_sig v).
Qed.

Definition vec_len (T: Type) (v: vec T) : usize :=
  exist _ (vec_length v) (vec_len_in_usize v).

Fixpoint list_update {A} (l: list A) (n: nat) (a: A)
  : list A :=
  match l with
  | []     => []
  | x :: t => match n with
    | 0%nat => a :: t
    | S m => x :: (list_update t m a)
end end.

Definition vec_bind {A B} (v: vec A) (f: list A -> result (list B)) : result (vec B) :=
  l <- f (vec_to_list v) ;
  match sumbool_of_bool (scalar_le_max Usize (Z.of_nat (length l))) with
  | left H => Return (exist _ l (scalar_le_max_valid _ _ H))
  | right _ => Fail_ Failure
  end.

(* The **forward** function shouldn't be used *)
Definition vec_push_fwd (T: Type) (v: vec T) (x: T) : unit := tt.

Definition vec_push_back (T: Type) (v: vec T) (x: T) : result (vec T) :=
  vec_bind v (fun l => Return (l ++ [x])).

(* The **forward** function shouldn't be used *)
Definition vec_insert_fwd (T: Type) (v: vec T) (i: usize) (x: T) : result unit :=
  if to_Z i <? vec_length v then Return tt else Fail_ Failure.

Definition vec_insert_back (T: Type) (v: vec T) (i: usize) (x: T) : result (vec T) :=
  vec_bind v (fun l =>
    if to_Z i <? Z.of_nat (length l)
    then Return (list_update l (usize_to_nat i) x)
    else Fail_ Failure).

(* The **backward** function shouldn't be used *)
Definition vec_index_fwd (T: Type) (v: vec T) (i: usize) : result T :=
  match nth_error (vec_to_list v) (usize_to_nat i) with
  | Some n => Return n
  | None   => Fail_ Failure
  end.

Definition vec_index_back (T: Type) (v: vec T) (i: usize) (x: T) : result unit :=
  if to_Z i <? vec_length v then Return tt else Fail_ Failure.

(* The **backward** function shouldn't be used *)
Definition vec_index_mut_fwd (T: Type) (v: vec T) (i: usize) : result T :=
  match nth_error (vec_to_list v) (usize_to_nat i) with
  | Some n => Return n
  | None   => Fail_ Failure
  end.

Definition vec_index_mut_back (T: Type) (v: vec T) (i: usize) (x: T) : result (vec T) :=
  vec_bind v (fun l =>
    if to_Z i <? Z.of_nat (length l)
    then Return (list_update l (usize_to_nat i) x)
    else Fail_ Failure).

End Primitives.
