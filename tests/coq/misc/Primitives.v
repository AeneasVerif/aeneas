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
  | Ok : A -> result A
  | Fail_ : error -> result A.

Arguments Ok {_} a.
Arguments Fail_ {_}.

Definition bind {A B} (m: result A) (f: A -> result B) : result B :=
  match m with
  | Fail_ e => Fail_ e
  | Ok x => f x
  end.

Definition return_ {A: Type} (x: A) : result A := Ok x.
Definition fail_ {A: Type} (e: error) : result A := Fail_ e.

Notation "x <- c1 ; c2" := (bind c1 (fun x => c2))
  (at level 61, c1 at next level, right associativity).

(** Monadic assert *)
Definition massert (b: bool) : result unit :=
  if b then Ok tt else Fail_ Failure.

(** Normalize and unwrap a successful result (used for globals) *)
Definition eval_result_refl {A} {x} (a: result A) (p: a = Ok x) : A :=
  match a as r return (r = Ok x -> A) with
  | Ok a' => fun _  => a'
  | Fail_ e   => fun p' =>
      False_rect _ (eq_ind (Fail_ e)
          (fun e : result A =>
          match e with
          | Ok _ => False
          | Fail_ e => True
          end)
        I (Ok x) p')
  end p.

Notation "x %global" := (eval_result_refl x eq_refl) (at level 40).
Notation "x %return" := (eval_result_refl x eq_refl) (at level 40).

(* Sanity check *)
Check (if true then Ok (1 + 2) else Fail_ Failure)%global = 3.

(*** Misc *)

Definition string := Coq.Strings.String.string.
Definition char := Coq.Strings.Ascii.ascii.
Definition char_of_byte := Coq.Strings.Ascii.ascii_of_byte.

Definition core_mem_replace {a : Type} (x : a) (y : a) : a * a := (x, x) .

Record mut_raw_ptr (T : Type) := { mut_raw_ptr_v : T }.
Record const_raw_ptr (T : Type) := { const_raw_ptr_v : T }.

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
  | left H => Ok (exist _ x (scalar_in_bounds_valid _ _ H))
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

Axiom scalar_xor : forall {ty}, scalar ty -> scalar ty -> scalar ty. (* TODO *)
Axiom scalar_or : forall {ty}, scalar ty -> scalar ty -> scalar ty. (* TODO *)
Axiom scalar_and : forall {ty}, scalar ty -> scalar ty -> scalar ty. (* TODO *)
Axiom scalar_shl : forall {ty0 ty1}, scalar ty0 -> scalar ty1 -> result (scalar ty0). (* TODO *)
Axiom scalar_shr : forall {ty0 ty1}, scalar ty0 -> scalar ty1 -> result (scalar ty0). (* TODO *)
Axiom scalar_not : forall {ty}, scalar ty -> scalar ty. (* TODO *)

(** Cast an integer from a [src_ty] to a [tgt_ty] *)
(* TODO: check the semantics of casts in Rust *)
Definition scalar_cast (src_ty tgt_ty : scalar_ty) (x : scalar src_ty) : result (scalar tgt_ty) :=
  mk_scalar tgt_ty (to_Z x).

(* This can't fail, but for now we make all casts faillible (easier for the translation) *)
Definition scalar_cast_bool (tgt_ty : scalar_ty) (x : bool) : result (scalar tgt_ty) :=
  mk_scalar tgt_ty (if x then 1 else 0).

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

(** Xor *)
Definition u8_xor := @scalar_xor U8.
Definition u16_xor := @scalar_xor U16.
Definition u32_xor := @scalar_xor U32.
Definition u64_xor := @scalar_xor U64.
Definition u128_xor := @scalar_xor U128.
Definition usize_xor := @scalar_xor Usize.
Definition i8_xor := @scalar_xor I8.
Definition i16_xor := @scalar_xor I16.
Definition i32_xor := @scalar_xor I32.
Definition i64_xor := @scalar_xor I64.
Definition i128_xor := @scalar_xor I128.
Definition isize_xor := @scalar_xor Isize.

(** Or *)
Definition u8_or := @scalar_or U8.
Definition u16_or := @scalar_or U16.
Definition u32_or := @scalar_or U32.
Definition u64_or := @scalar_or U64.
Definition u128_or := @scalar_or U128.
Definition usize_or := @scalar_or Usize.
Definition i8_or := @scalar_or I8.
Definition i16_or := @scalar_or I16.
Definition i32_or := @scalar_or I32.
Definition i64_or := @scalar_or I64.
Definition i128_or := @scalar_or I128.
Definition isize_or := @scalar_or Isize.

(** And *)
Definition u8_and := @scalar_and U8.
Definition u16_and := @scalar_and U16.
Definition u32_and := @scalar_and U32.
Definition u64_and := @scalar_and U64.
Definition u128_and := @scalar_and U128.
Definition usize_and := @scalar_and Usize.
Definition i8_and := @scalar_and I8.
Definition i16_and := @scalar_and I16.
Definition i32_and := @scalar_and I32.
Definition i64_and := @scalar_and I64.
Definition i128_and := @scalar_and I128.
Definition isize_and := @scalar_and Isize.

(** Shift left *)
Definition u8_shl {ty} := @scalar_shl U8 ty.
Definition u16_shl {ty} := @scalar_shl U16 ty.
Definition u32_shl {ty} := @scalar_shl U32 ty.
Definition u64_shl {ty} := @scalar_shl U64 ty.
Definition u128_shl {ty} := @scalar_shl U128 ty.
Definition usize_shl {ty} := @scalar_shl Usize ty.
Definition i8_shl {ty} := @scalar_shl I8 ty.
Definition i16_shl {ty} := @scalar_shl I16 ty.
Definition i32_shl {ty} := @scalar_shl I32 ty.
Definition i64_shl {ty} := @scalar_shl I64 ty.
Definition i128_shl {ty} := @scalar_shl I128 ty.
Definition isize_shl {ty} := @scalar_shl Isize ty.

(** Shift right *)
Definition u8_shr {ty} := @scalar_shr U8 ty.
Definition u16_shr {ty} := @scalar_shr U16 ty.
Definition u32_shr {ty} := @scalar_shr U32 ty.
Definition u64_shr {ty} := @scalar_shr U64 ty.
Definition u128_shr {ty} := @scalar_shr U128 ty.
Definition usize_shr {ty} := @scalar_shr Usize ty.
Definition i8_shr {ty} := @scalar_shr I8 ty.
Definition i16_shr {ty} := @scalar_shr I16 ty.
Definition i32_shr {ty} := @scalar_shr I32 ty.
Definition i64_shr {ty} := @scalar_shr I64 ty.
Definition i128_shr {ty} := @scalar_shr I128 ty.
Definition isize_shr {ty} := @scalar_shr Isize ty.

(** Not *)
Definition u8_not := @scalar_not U8.
Definition u16_not := @scalar_not U16.
Definition u32_not := @scalar_not U32.
Definition u64_not := @scalar_not U64.
Definition u128_not := @scalar_not U128.
Definition usize_not := @scalar_not Usize.
Definition i8_not := @scalar_not I8.
Definition i16_not := @scalar_not I16.
Definition i32_not := @scalar_not I32.
Definition i64_not := @scalar_not I64.
Definition i128_not := @scalar_not I128.
Definition isize_not := @scalar_not Isize.

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

(** Constants *)
Definition core_u8_max    := u8_max %u32.
Definition core_u16_max   := u16_max %u32.
Definition core_u32_max   := u32_max %u32.
Definition core_u64_max   := u64_max %u64.
Definition core_u128_max  := u64_max %u128.
Axiom core_usize_max : usize. (** TODO *)
Definition core_i8_max    := i8_max %i32.
Definition core_i16_max   := i16_max %i32.
Definition core_i32_max   := i32_max %i32.
Definition core_i64_max   := i64_max %i64.
Definition core_i128_max  := i64_max %i128.
Axiom core_isize_max : isize. (** TODO *)

(*** core *)

(** Trait declaration: [core::clone::Clone] *)
Record core_clone_Clone (self : Type) := {
  core_clone_Clone_clone : self -> result self
}.

Definition core_clone_impls_CloneUsize_clone (x : usize) : usize := x.
Definition core_clone_impls_CloneU8_clone (x : u8) : u8 := x.
Definition core_clone_impls_CloneU16_clone (x : u16) : u16 := x.
Definition core_clone_impls_CloneU32_clone (x : u32) : u32 := x.
Definition core_clone_impls_CloneU64_clone (x : u64) : u64 := x.
Definition core_clone_impls_CloneU128_clone (x : u128) : u128 := x.

Definition core_clone_impls_CloneIsize_clone (x : isize) : isize := x.
Definition core_clone_impls_CloneI8_clone (x : i8) : i8 := x.
Definition core_clone_impls_CloneI16_clone (x : i16) : i16 := x.
Definition core_clone_impls_CloneI32_clone (x : i32) : i32 := x.
Definition core_clone_impls_CloneI64_clone (x : i64) : i64 := x.
Definition core_clone_impls_CloneI128_clone (x : i128) : i128 := x.

Definition core_clone_CloneUsize : core_clone_Clone usize := {|
  core_clone_Clone_clone := fun x => Ok (core_clone_impls_CloneUsize_clone x)
|}.

Definition core_clone_CloneU8 : core_clone_Clone u8 := {|
  core_clone_Clone_clone := fun x => Ok (core_clone_impls_CloneU8_clone x)
|}.

Definition core_clone_CloneU16 : core_clone_Clone u16 := {|
  core_clone_Clone_clone := fun x => Ok (core_clone_impls_CloneU16_clone x)
|}.

Definition core_clone_CloneU32 : core_clone_Clone u32 := {|
  core_clone_Clone_clone := fun x => Ok (core_clone_impls_CloneU32_clone x)
|}.

Definition core_clone_CloneU64 : core_clone_Clone u64 := {|
  core_clone_Clone_clone := fun x => Ok (core_clone_impls_CloneU64_clone x)
|}.

Definition core_clone_CloneU128 : core_clone_Clone u128 := {|
  core_clone_Clone_clone := fun x => Ok (core_clone_impls_CloneU128_clone x)
|}.

Definition core_clone_CloneIsize : core_clone_Clone isize := {|
  core_clone_Clone_clone := fun x => Ok (core_clone_impls_CloneIsize_clone x)
|}.

Definition core_clone_CloneI8 : core_clone_Clone i8 := {|
  core_clone_Clone_clone := fun x => Ok (core_clone_impls_CloneI8_clone x)
|}.

Definition core_clone_CloneI16 : core_clone_Clone i16 := {|
  core_clone_Clone_clone := fun x => Ok (core_clone_impls_CloneI16_clone x)
|}.

Definition core_clone_CloneI32 : core_clone_Clone i32 := {|
  core_clone_Clone_clone := fun x => Ok (core_clone_impls_CloneI32_clone x)
|}.

Definition core_clone_CloneI64 : core_clone_Clone i64 := {|
  core_clone_Clone_clone := fun x => Ok (core_clone_impls_CloneI64_clone x)
|}.

Definition core_clone_CloneI128 : core_clone_Clone i128 := {|
  core_clone_Clone_clone := fun x => Ok (core_clone_impls_CloneI128_clone x)
|}.

Definition core_clone_impls_CloneBool_clone (b : bool) : bool := b.

Definition core_clone_CloneBool : core_clone_Clone bool := {|
  core_clone_Clone_clone := fun b => Ok (core_clone_impls_CloneBool_clone b)
|}.

Record core_marker_Copy (Self : Type) := mkcore_marker_Copy {
  cloneInst : core_clone_Clone Self;
}.

Arguments mkcore_marker_Copy { _ }.
Arguments cloneInst { _ } _.

Definition core_marker_CopyU8 : core_marker_Copy u8 := {|
  cloneInst := core_clone_CloneU8;
|}.

Definition core_marker_CopyU16 : core_marker_Copy u16 := {|
  cloneInst := core_clone_CloneU16;
|}.

Definition core_marker_CopyU32 : core_marker_Copy u32 := {|
  cloneInst := core_clone_CloneU32;
|}.

Definition core_marker_CopyU64 : core_marker_Copy u64 := {|
  cloneInst := core_clone_CloneU64;
|}.

Definition core_marker_CopyU128 : core_marker_Copy u128 := {|
  cloneInst := core_clone_CloneU128;
|}.

Definition core_marker_CopyUsize : core_marker_Copy usize := {|
  cloneInst := core_clone_CloneUsize;
|}.

Definition core_marker_CopyI8 : core_marker_Copy i8 := {|
  cloneInst := core_clone_CloneI8;
|}.

Definition core_marker_CopyI16 : core_marker_Copy i16 := {|
  cloneInst := core_clone_CloneI16;
|}.

Definition core_marker_CopyI32 : core_marker_Copy i32 := {|
  cloneInst := core_clone_CloneI32;
|}.

Definition core_marker_CopyI64 : core_marker_Copy i64 := {|
  cloneInst := core_clone_CloneI64;
|}.

Definition core_marker_CopyI128 : core_marker_Copy i128 := {|
  cloneInst := core_clone_CloneI128;
|}.

Definition core_marker_CopyIsize : core_marker_Copy isize := {|
  cloneInst := core_clone_CloneIsize;
|}.

(** [core::option::{core::option::Option<T>}::unwrap] *)
Definition core_option_Option_unwrap {T : Type} (x : option T) : result T :=
  match x with
  | None => Fail_ Failure
  | Some x => Ok x
  end.

(*** core::ops *)

(* Trait declaration: [core::ops::index::Index] *)
Record core_ops_index_Index (Self Idx : Type) := mk_core_ops_index_Index {
  core_ops_index_Index_Output : Type;
  core_ops_index_Index_index : Self -> Idx -> result core_ops_index_Index_Output;
}.
Arguments mk_core_ops_index_Index {_ _}.
Arguments core_ops_index_Index_Output {_ _}.
Arguments core_ops_index_Index_index {_ _}.

(* Trait declaration: [core::ops::index::IndexMut] *)
Record core_ops_index_IndexMut (Self Idx : Type) := mk_core_ops_index_IndexMut {
  core_ops_index_IndexMut_indexInst : core_ops_index_Index Self Idx;
  core_ops_index_IndexMut_index_mut :
    Self ->
    Idx ->
    result (core_ops_index_IndexMut_indexInst.(core_ops_index_Index_Output) *
            (core_ops_index_IndexMut_indexInst.(core_ops_index_Index_Output) -> Self));
}.
Arguments mk_core_ops_index_IndexMut {_ _}.
Arguments core_ops_index_IndexMut_indexInst {_ _}.
Arguments core_ops_index_IndexMut_index_mut {_ _}.

(* Trait declaration [core::ops::deref::Deref] *)
Record core_ops_deref_Deref (Self : Type) := mk_core_ops_deref_Deref {
  core_ops_deref_Deref_target : Type;
  core_ops_deref_Deref_deref : Self -> result core_ops_deref_Deref_target;
}.
Arguments mk_core_ops_deref_Deref {_}.
Arguments core_ops_deref_Deref_target {_}.
Arguments core_ops_deref_Deref_deref {_}.

(* Trait declaration [core::ops::deref::DerefMut] *)
Record core_ops_deref_DerefMut (Self : Type) := mk_core_ops_deref_DerefMut {
  core_ops_deref_DerefMut_derefInst : core_ops_deref_Deref Self;
  core_ops_deref_DerefMut_deref_mut :
    Self ->
    result (core_ops_deref_DerefMut_derefInst.(core_ops_deref_Deref_target) *
            (core_ops_deref_DerefMut_derefInst.(core_ops_deref_Deref_target) -> Self));
}.
Arguments mk_core_ops_deref_DerefMut {_}.
Arguments core_ops_deref_DerefMut_derefInst {_}.
Arguments core_ops_deref_DerefMut_deref_mut {_}.

Record core_ops_range_Range (T : Type) := mk_core_ops_range_Range {
  core_ops_range_Range_start : T;
  core_ops_range_Range_end_ : T;
}.
Arguments mk_core_ops_range_Range {_}.
Arguments core_ops_range_Range_start {_}.
Arguments core_ops_range_Range_end_ {_}.

(*** [alloc] *)

Definition alloc_boxed_Box_deref {T : Type} (x : T) : result T := Ok x.
Definition alloc_boxed_Box_deref_mut {T : Type} (x : T) : result (T * (T -> T)) :=
  Ok (x, fun x => x).

(* Trait instance *)
Definition alloc_boxed_Box_coreopsDerefInst (Self : Type) : core_ops_deref_Deref Self := {|
  core_ops_deref_Deref_target := Self;
  core_ops_deref_Deref_deref := alloc_boxed_Box_deref;
|}.

(* Trait instance *)
Definition alloc_boxed_Box_coreopsDerefMutInst (Self : Type) : core_ops_deref_DerefMut Self := {|
  core_ops_deref_DerefMut_derefInst := alloc_boxed_Box_coreopsDerefInst Self;
  core_ops_deref_DerefMut_deref_mut := alloc_boxed_Box_deref_mut;
|}.


(*** Arrays *)
Definition array T (n : usize) := { l: list T | Z.of_nat (length l) = to_Z n}.

Lemma le_0_usize_max : 0 <= usize_max.
Proof.
  pose (H := usize_max_bound).
  unfold u32_max in H.
  lia.
Qed.

Lemma eqb_imp_eq (x y : Z) : Z.eqb x y = true -> x = y.
Proof.
  lia.
Qed.

(* TODO: finish the definitions *)
Axiom mk_array : forall {T : Type} (n : usize) (l : list T), array T n.

(* For initialization *)
Axiom array_repeat : forall {T : Type} (n : usize) (x : T), array T n.

Axiom array_index_usize : forall {T : Type} {n : usize} (x : array T n) (i : usize), result T.
Axiom array_update_usize : forall {T : Type} {n : usize} (x : array T n) (i : usize) (nx : T), result (array T n).
Axiom array_update : forall {T : Type} {n : usize} (x : array T n) (i : usize) (nx : T), array T n.

Definition array_index_mut_usize {T : Type} {n : usize} (a : array T n) (i : usize) :
  result (T * (T -> array T n)) :=
  match array_index_usize a i with
  | Fail_ e => Fail_ e
  | Ok x => Ok (x, array_update a i)
  end.

(*** Slice *)
Definition slice T := { l: list T | Z.of_nat (length l) <= usize_max}.

Axiom slice_len : forall {T : Type} (s : slice T), usize.
Axiom slice_index_usize : forall {T : Type} (x : slice T) (i : usize), result T.
Axiom slice_update_usize : forall {T : Type} (x : slice T) (i : usize) (nx : T), result (slice T).
Axiom slice_update : forall {T : Type} (x : slice T) (i : usize) (nx : T), slice T.

Definition slice_index_mut_usize {T : Type} (s : slice T) (i : usize) :
  result (T * (T -> slice T)) :=
  match slice_index_usize s i with
  | Fail_ e => Fail_ e
  | Ok x => Ok (x, slice_update s i)
  end.

(*** Subslices *)

Axiom array_to_slice : forall {T : Type} {n : usize} (x : array T n), result (slice T).
Axiom array_from_slice : forall {T : Type} {n : usize} (x : array T n) (s : slice T), array T n.

Definition array_to_slice_mut {T : Type} {n : usize} (a : array T n) :
  result (slice T * (slice T -> array T n)) :=
  match array_to_slice a with
  | Fail_ e => Fail_ e
  | Ok x => Ok (x, array_from_slice a)
  end.

Axiom array_subslice: forall {T : Type} {n : usize} (x : array T n) (r : core_ops_range_Range usize), result (slice T).
Axiom array_update_subslice: forall {T : Type} {n : usize} (x : array T n) (r : core_ops_range_Range usize) (ns : slice T), result (array T n).

Axiom slice_subslice: forall {T : Type} (x : slice T) (r : core_ops_range_Range usize), result (slice T).
Axiom slice_update_subslice: forall {T : Type} (x : slice T) (r : core_ops_range_Range usize) (ns : slice T), result (slice T).

(*** Vectors *)

Definition alloc_vec_Vec T := { l: list T | Z.of_nat (length l) <= usize_max }.

Definition alloc_vec_Vec_to_list {T: Type} (v: alloc_vec_Vec T) : list T := proj1_sig v.

Definition alloc_vec_Vec_length {T: Type} (v: alloc_vec_Vec T) : Z := Z.of_nat (length (alloc_vec_Vec_to_list v)).

Definition alloc_vec_Vec_new (T: Type) : alloc_vec_Vec T := (exist _ [] le_0_usize_max).

Lemma alloc_vec_Vec_len_in_usize {T} (v: alloc_vec_Vec T) : usize_min <= alloc_vec_Vec_length v <= usize_max.
Proof.
  unfold alloc_vec_Vec_length, usize_min.
  split.
  - lia.
  - apply (proj2_sig v).
Qed.

Definition alloc_vec_Vec_len {T: Type} (v: alloc_vec_Vec T) : usize :=
  exist _ (alloc_vec_Vec_length v) (alloc_vec_Vec_len_in_usize v).

Fixpoint list_update {A} (l: list A) (n: nat) (a: A)
  : list A :=
  match l with
  | []     => []
  | x :: t => match n with
    | 0%nat => a :: t
    | S m => x :: (list_update t m a)
end end.

Definition alloc_vec_Vec_bind {A B} (v: alloc_vec_Vec A) (f: list A -> result (list B)) : result (alloc_vec_Vec B) :=
  l <- f (alloc_vec_Vec_to_list v) ;
  match sumbool_of_bool (scalar_le_max Usize (Z.of_nat (length l))) with
  | left H => Ok (exist _ l (scalar_le_max_valid _ _ H))
  | right _ => Fail_ Failure
  end.

Definition alloc_vec_Vec_push {T: Type} (v: alloc_vec_Vec T) (x: T) : result (alloc_vec_Vec T) :=
  alloc_vec_Vec_bind v (fun l => Ok (l ++ [x])).

Definition alloc_vec_Vec_insert {T: Type} (v: alloc_vec_Vec T) (i: usize) (x: T) : result (alloc_vec_Vec T) :=
  alloc_vec_Vec_bind v (fun l =>
    if to_Z i <? Z.of_nat (length l)
    then Ok (list_update l (usize_to_nat i) x)
    else Fail_ Failure).

(* Helper *)
Axiom alloc_vec_Vec_index_usize : forall {T : Type} (v : alloc_vec_Vec T) (i : usize), result T.

(* Helper *)
Axiom alloc_vec_Vec_update_usize : forall {T : Type} (v : alloc_vec_Vec T) (i : usize) (x : T), result (alloc_vec_Vec T).
Axiom alloc_vec_Vec_update : forall {T : Type} (v : alloc_vec_Vec T) (i : usize) (x : T), alloc_vec_Vec T.

Definition alloc_vec_Vec_index_mut_usize {T : Type} (v: alloc_vec_Vec T) (i: usize) :
  result (T * (T -> alloc_vec_Vec T)) :=
  match alloc_vec_Vec_index_usize v i with
  | Ok x =>
    Ok (x, alloc_vec_Vec_update v i)
  | Fail_ e => Fail_ e
  end.

(* Trait declaration: [core::slice::index::private_slice_index::Sealed] *)
Definition core_slice_index_private_slice_index_Sealed (self : Type) := unit.

(* Trait declaration: [core::slice::index::SliceIndex] *)
Record core_slice_index_SliceIndex (Self T : Type) := mk_core_slice_index_SliceIndex {
  core_slice_index_SliceIndex_sealedInst : core_slice_index_private_slice_index_Sealed Self;
  core_slice_index_SliceIndex_Output : Type;
  core_slice_index_SliceIndex_get : Self -> T -> result (option core_slice_index_SliceIndex_Output);
  core_slice_index_SliceIndex_get_mut :
    Self -> T -> result (option core_slice_index_SliceIndex_Output * (option core_slice_index_SliceIndex_Output -> T));
  core_slice_index_SliceIndex_get_unchecked : Self -> const_raw_ptr T -> result (const_raw_ptr core_slice_index_SliceIndex_Output);
  core_slice_index_SliceIndex_get_unchecked_mut : Self -> mut_raw_ptr T -> result (mut_raw_ptr core_slice_index_SliceIndex_Output);
  core_slice_index_SliceIndex_index : Self -> T -> result core_slice_index_SliceIndex_Output;
  core_slice_index_SliceIndex_index_mut :
    Self -> T -> result (core_slice_index_SliceIndex_Output * (core_slice_index_SliceIndex_Output -> T));
}.
Arguments mk_core_slice_index_SliceIndex {_ _}.
Arguments core_slice_index_SliceIndex_sealedInst {_ _}.
Arguments core_slice_index_SliceIndex_Output {_ _}.
Arguments core_slice_index_SliceIndex_get {_ _}.
Arguments core_slice_index_SliceIndex_get_mut {_ _}.
Arguments core_slice_index_SliceIndex_get_unchecked {_ _}.
Arguments core_slice_index_SliceIndex_get_unchecked_mut {_ _}.
Arguments core_slice_index_SliceIndex_index {_ _}.
Arguments core_slice_index_SliceIndex_index_mut {_ _}.

(* [core::slice::index::[T]::index]: forward function *)
Definition core_slice_index_Slice_index
  {T Idx : Type} (inst : core_slice_index_SliceIndex Idx (slice T))
  (s : slice T) (i : Idx) : result inst.(core_slice_index_SliceIndex_Output) :=
  x <- inst.(core_slice_index_SliceIndex_get) i s;
  match x with
  | None => Fail_ Failure
  | Some x => Ok x
  end.

(* [core::slice::index::Range:::get]: forward function *)
Axiom core_slice_index_RangeUsize_get : forall {T : Type} (i : core_ops_range_Range usize) (s : slice T), result (option (slice T)).

(* [core::slice::index::Range::get_mut]: forward function *)
Axiom core_slice_index_RangeUsize_get_mut :
  forall {T : Type},
    core_ops_range_Range usize -> slice T ->
    result (option (slice T) * (option (slice T) -> slice T)).

(* [core::slice::index::Range::get_unchecked]: forward function *)
Definition core_slice_index_RangeUsize_get_unchecked
  {T : Type} :
  core_ops_range_Range usize -> const_raw_ptr (slice T) -> result (const_raw_ptr (slice T)) :=
  (* Don't know what the model should be - for now we always fail to make
     sure code which uses it fails *)
  fun _ _ => Fail_ Failure.

(* [core::slice::index::Range::get_unchecked_mut]: forward function *)
Definition core_slice_index_RangeUsize_get_unchecked_mut
  {T : Type} :
  core_ops_range_Range usize -> mut_raw_ptr (slice T) -> result (mut_raw_ptr (slice T)) :=
  (* Don't know what the model should be - for now we always fail to make
    sure code which uses it fails *)
  fun _ _ => Fail_ Failure.

(* [core::slice::index::Range::index]: forward function *)
Axiom core_slice_index_RangeUsize_index :
  forall {T : Type}, core_ops_range_Range usize -> slice T -> result (slice T).

(* [core::slice::index::Range::index_mut]: forward function *)
Axiom core_slice_index_RangeUsize_index_mut :
  forall {T : Type}, core_ops_range_Range usize -> slice T -> result (slice T * (slice T -> slice T)).

(* [core::slice::index::[T]::index_mut]: forward function *)
Axiom core_slice_index_Slice_index_mut :
  forall {T Idx : Type} (inst : core_slice_index_SliceIndex Idx (slice T)),
  slice T -> Idx ->
  result (inst.(core_slice_index_SliceIndex_Output) *
          (inst.(core_slice_index_SliceIndex_Output) -> slice T)).

(* [core::array::[T; N]::index]: forward function *)
Axiom core_array_Array_index :
  forall {T Idx : Type} {N : usize} (inst : core_ops_index_Index (slice T) Idx)
  (a : array T N) (i : Idx), result inst.(core_ops_index_Index_Output).

(* [core::array::[T; N]::index_mut]: forward function *)
Axiom core_array_Array_index_mut :
  forall {T Idx : Type} {N : usize} (inst : core_ops_index_IndexMut (slice T) Idx)
  (a : array T N) (i : Idx),
  result (inst.(core_ops_index_IndexMut_indexInst).(core_ops_index_Index_Output) *
          (inst.(core_ops_index_IndexMut_indexInst).(core_ops_index_Index_Output) -> array T N)).

(* Trait implementation: [core::slice::index::private_slice_index::Range] *)
Definition core_slice_index_private_slice_index_SealedRangeUsizeInst
  : core_slice_index_private_slice_index_Sealed (core_ops_range_Range usize) := tt.

(* Trait implementation: [core::slice::index::Range] *)
Definition core_slice_index_SliceIndexRangeUsizeSliceTInst (T : Type) :
  core_slice_index_SliceIndex (core_ops_range_Range usize) (slice T) := {|
  core_slice_index_SliceIndex_sealedInst := core_slice_index_private_slice_index_SealedRangeUsizeInst;
  core_slice_index_SliceIndex_Output := slice T;
  core_slice_index_SliceIndex_get := core_slice_index_RangeUsize_get;
  core_slice_index_SliceIndex_get_mut := core_slice_index_RangeUsize_get_mut;
  core_slice_index_SliceIndex_get_unchecked := core_slice_index_RangeUsize_get_unchecked;
  core_slice_index_SliceIndex_get_unchecked_mut := core_slice_index_RangeUsize_get_unchecked_mut;
  core_slice_index_SliceIndex_index := core_slice_index_RangeUsize_index;
  core_slice_index_SliceIndex_index_mut := core_slice_index_RangeUsize_index_mut;
|}.

(* Trait implementation: [core::slice::index::[T]] *)
Definition core_ops_index_IndexSliceTIInst {T Idx : Type}
  (inst : core_slice_index_SliceIndex Idx (slice T)) :
  core_ops_index_Index (slice T) Idx := {|
  core_ops_index_Index_Output := inst.(core_slice_index_SliceIndex_Output);
  core_ops_index_Index_index := core_slice_index_Slice_index inst;
|}.

(* Trait implementation: [core::slice::index::[T]] *)
Definition core_ops_index_IndexMutSliceTIInst {T Idx : Type}
  (inst : core_slice_index_SliceIndex Idx (slice T)) :
  core_ops_index_IndexMut (slice T) Idx := {|
  core_ops_index_IndexMut_indexInst := core_ops_index_IndexSliceTIInst inst;
  core_ops_index_IndexMut_index_mut := core_slice_index_Slice_index_mut inst;
|}.

(* Trait implementation: [core::array::[T; N]] *)
Definition core_ops_index_IndexArrayInst {T Idx : Type} (N : usize)
  (inst : core_ops_index_Index (slice T) Idx) :
  core_ops_index_Index (array T N) Idx := {|
  core_ops_index_Index_Output := inst.(core_ops_index_Index_Output);
  core_ops_index_Index_index := core_array_Array_index inst;
|}.

(* Trait implementation: [core::array::[T; N]] *)
Definition core_ops_index_IndexMutArrayInst {T Idx : Type} (N : usize)
  (inst : core_ops_index_IndexMut (slice T) Idx) :
  core_ops_index_IndexMut (array T N) Idx := {|
  core_ops_index_IndexMut_indexInst := core_ops_index_IndexArrayInst N inst.(core_ops_index_IndexMut_indexInst);
  core_ops_index_IndexMut_index_mut := core_array_Array_index_mut inst;
|}.

(* [core::slice::index::usize::get]: forward function *)
Axiom core_slice_index_usize_get : forall {T : Type}, usize -> slice T -> result (option T).

(* [core::slice::index::usize::get_mut]: forward function *)
Axiom core_slice_index_usize_get_mut :
  forall {T : Type}, usize -> slice T -> result (option T * (option T -> slice T)).

(* [core::slice::index::usize::get_unchecked]: forward function *)
Axiom core_slice_index_usize_get_unchecked :
  forall {T : Type}, usize -> const_raw_ptr (slice T) -> result (const_raw_ptr T).

(* [core::slice::index::usize::get_unchecked_mut]: forward function *)
Axiom core_slice_index_usize_get_unchecked_mut :
  forall {T : Type}, usize -> mut_raw_ptr (slice T) -> result (mut_raw_ptr T).

(* [core::slice::index::usize::index]: forward function *)
Axiom core_slice_index_usize_index : forall {T : Type}, usize -> slice T -> result T.

(* [core::slice::index::usize::index_mut]: forward function *)
Axiom core_slice_index_usize_index_mut :
  forall {T : Type}, usize -> slice T -> result (T * (T -> slice T)).

(* Trait implementation: [core::slice::index::private_slice_index::usize] *)
Definition core_slice_index_private_slice_index_SealedUsizeInst
  : core_slice_index_private_slice_index_Sealed usize := tt.

(* Trait implementation: [core::slice::index::usize] *)
Definition core_slice_index_SliceIndexUsizeSliceTInst (T : Type) :
  core_slice_index_SliceIndex usize (slice T) := {|
  core_slice_index_SliceIndex_sealedInst := core_slice_index_private_slice_index_SealedUsizeInst;
  core_slice_index_SliceIndex_Output := T;
  core_slice_index_SliceIndex_get := core_slice_index_usize_get;
  core_slice_index_SliceIndex_get_mut := core_slice_index_usize_get_mut;
  core_slice_index_SliceIndex_get_unchecked := core_slice_index_usize_get_unchecked;
  core_slice_index_SliceIndex_get_unchecked_mut := core_slice_index_usize_get_unchecked_mut;
  core_slice_index_SliceIndex_index := core_slice_index_usize_index;
  core_slice_index_SliceIndex_index_mut := core_slice_index_usize_index_mut;
|}.

(* [alloc::vec::Vec::index]: forward function *)
Axiom alloc_vec_Vec_index : forall {T Idx : Type} (inst : core_slice_index_SliceIndex Idx (slice T))
  (Self : alloc_vec_Vec T) (i : Idx), result inst.(core_slice_index_SliceIndex_Output).

(* [alloc::vec::Vec::index_mut]: forward function *)
Axiom alloc_vec_Vec_index_mut : forall {T Idx : Type} (inst : core_slice_index_SliceIndex Idx (slice T))
  (Self : alloc_vec_Vec T) (i : Idx),
  result (inst.(core_slice_index_SliceIndex_Output) *
          (inst.(core_slice_index_SliceIndex_Output) -> alloc_vec_Vec T)).

(* Trait implementation: [alloc::vec::Vec] *)
Definition alloc_vec_Vec_coreopsindexIndexInst {T Idx : Type}
  (inst : core_slice_index_SliceIndex Idx (slice T)) :
  core_ops_index_Index (alloc_vec_Vec T) Idx := {|
  core_ops_index_Index_Output := inst.(core_slice_index_SliceIndex_Output);
  core_ops_index_Index_index := alloc_vec_Vec_index inst;
|}.

(* Trait implementation: [alloc::vec::Vec] *)
Definition alloc_vec_Vec_coreopsindexIndexMutInst {T Idx : Type}
  (inst : core_slice_index_SliceIndex Idx (slice T)) :
  core_ops_index_IndexMut (alloc_vec_Vec T) Idx := {|
  core_ops_index_IndexMut_indexInst := alloc_vec_Vec_coreopsindexIndexInst inst;
  core_ops_index_IndexMut_index_mut := alloc_vec_Vec_index_mut inst;
|}.

(*** Theorems *)

Axiom alloc_vec_Vec_index_eq : forall {a : Type} (v : alloc_vec_Vec a) (i : usize) (x : a),
  alloc_vec_Vec_index (core_slice_index_SliceIndexUsizeSliceTInst a) v i =
    alloc_vec_Vec_index_usize v i.

Axiom alloc_vec_Vec_index_mut_eq : forall {a : Type} (v : alloc_vec_Vec a) (i : usize) (x : a),
  alloc_vec_Vec_index_mut (core_slice_index_SliceIndexUsizeSliceTInst a) v i =
    alloc_vec_Vec_index_mut_usize v i.

End Primitives.
