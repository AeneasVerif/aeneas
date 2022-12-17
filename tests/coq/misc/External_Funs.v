(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [external]: function definitions *)
Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Local Open Scope Primitives_scope.
Require Export External_Types.
Import External_Types.
Require Export External_Opaque.
Import External_Opaque.
Module External_Funs.

(** [external::swap] *)
Definition swap_fwd
  (T : Type) (x : T) (y : T) (st : state) : result (state * unit) :=
  p <- core_mem_swap_fwd T x y st;
  let (st0, _) := p in
  p0 <- core_mem_swap_back0 T x y st st0;
  let (st1, _) := p0 in
  p1 <- core_mem_swap_back1 T x y st st1;
  let (st2, _) := p1 in
  Return (st2, tt)
.

(** [external::swap] *)
Definition swap_back
  (T : Type) (x : T) (y : T) (st : state) (st0 : state) :
  result (state * (T * T))
  :=
  p <- core_mem_swap_fwd T x y st;
  let (st1, _) := p in
  p0 <- core_mem_swap_back0 T x y st st1;
  let (st2, x0) := p0 in
  p1 <- core_mem_swap_back1 T x y st st2;
  let (_, y0) := p1 in
  Return (st0, (x0, y0))
.

(** [external::test_new_non_zero_u32] *)
Definition test_new_non_zero_u32_fwd
  (x : u32) (st : state) : result (state * Core_num_nonzero_non_zero_u32_t) :=
  p <- core_num_nonzero_non_zero_u32_new_fwd x st;
  let (st0, opt) := p in
  core_option_option_unwrap_fwd Core_num_nonzero_non_zero_u32_t opt st0
.

(** [external::test_vec] *)
Definition test_vec_fwd : result unit :=
  let v := vec_new u32 in
  v0 <- vec_push_back u32 v (0%u32);
  let _ := v0 in
  Return tt
.

(** Unit test for [external::test_vec] *)
Check (test_vec_fwd )%return.

(** [external::custom_swap] *)
Definition custom_swap_fwd
  (T : Type) (x : T) (y : T) (st : state) : result (state * T) :=
  p <- core_mem_swap_fwd T x y st;
  let (st0, _) := p in
  p0 <- core_mem_swap_back0 T x y st st0;
  let (st1, x0) := p0 in
  p1 <- core_mem_swap_back1 T x y st st1;
  let (st2, _) := p1 in
  Return (st2, x0)
.

(** [external::custom_swap] *)
Definition custom_swap_back
  (T : Type) (x : T) (y : T) (st : state) (ret : T) (st0 : state) :
  result (state * (T * T))
  :=
  p <- core_mem_swap_fwd T x y st;
  let (st1, _) := p in
  p0 <- core_mem_swap_back0 T x y st st1;
  let (st2, _) := p0 in
  p1 <- core_mem_swap_back1 T x y st st2;
  let (_, y0) := p1 in
  Return (st0, (ret, y0))
.

(** [external::test_custom_swap] *)
Definition test_custom_swap_fwd
  (x : u32) (y : u32) (st : state) : result (state * unit) :=
  p <- custom_swap_fwd u32 x y st; let (st0, _) := p in Return (st0, tt)
.

(** [external::test_custom_swap] *)
Definition test_custom_swap_back
  (x : u32) (y : u32) (st : state) (st0 : state) :
  result (state * (u32 * u32))
  :=
  custom_swap_back u32 x y st (1%u32) st0
.

(** [external::test_swap_non_zero] *)
Definition test_swap_non_zero_fwd
  (x : u32) (st : state) : result (state * u32) :=
  p <- swap_fwd u32 x (0%u32) st;
  let (st0, _) := p in
  p0 <- swap_back u32 x (0%u32) st st0;
  let (st1, p1) := p0 in
  let (x0, _) := p1 in
  if x0 s= 0%u32 then Fail_ Failure else Return (st1, x0)
.

End External_Funs .
