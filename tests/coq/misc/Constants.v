(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [constants] *)
Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import List.
Import ListNotations.
Local Open Scope Primitives_scope.
Module Constants.

(** [constants::X0]
    Source: 'tests/src/constants.rs', lines 8:0-8:22 *)
Definition x0_body : result u32 := Ok 0%u32.
Definition x0 : u32 := x0_body%global.

(** [constants::X1]
    Source: 'tests/src/constants.rs', lines 10:0-10:29 *)
Definition x1_body : result u32 := Ok core_num_U32_MAX.
Definition x1 : u32 := x1_body%global.

(** [constants::X2]
    Source: 'tests/src/constants.rs', lines 13:0-16:2 *)
Definition x2_body : result u32 := Ok 3%u32.
Definition x2 : u32 := x2_body%global.

(** [constants::incr]:
    Source: 'tests/src/constants.rs', lines 20:0-22:1 *)
Definition incr (n : u32) : result u32 :=
  u32_add n 1%u32.

(** [constants::X3]
    Source: 'tests/src/constants.rs', lines 18:0-18:29 *)
Definition x3_body : result u32 := incr 32%u32.
Definition x3 : u32 := x3_body%global.

(** [constants::mk_pair0]:
    Source: 'tests/src/constants.rs', lines 26:0-28:1 *)
Definition mk_pair0 (x : u32) (y1 : u32) : result (u32 * u32) :=
  Ok (x, y1).

(** [constants::Pair]
    Source: 'tests/src/constants.rs', lines 39:0-42:1 *)
Record Pair_t (T1 : Type) (T2 : Type) :=
mkPair_t {
  pair_x : T1; pair_y : T2;
}
.

Arguments mkPair_t { _ } { _ }.
Arguments pair_x { _ } { _ }.
Arguments pair_y { _ } { _ }.

(** [constants::mk_pair1]:
    Source: 'tests/src/constants.rs', lines 30:0-32:1 *)
Definition mk_pair1 (x : u32) (y1 : u32) : result (Pair_t u32 u32) :=
  Ok {| pair_x := x; pair_y := y1 |}
.

(** [constants::P0]
    Source: 'tests/src/constants.rs', lines 34:0-34:42 *)
Definition p0_body : result (u32 * u32) := mk_pair0 0%u32 1%u32.
Definition p0 : (u32 * u32) := p0_body%global.

(** [constants::P1]
    Source: 'tests/src/constants.rs', lines 35:0-35:46 *)
Definition p1_body : result (Pair_t u32 u32) := mk_pair1 0%u32 1%u32.
Definition p1 : Pair_t u32 u32 := p1_body%global.

(** [constants::P2]
    Source: 'tests/src/constants.rs', lines 36:0-36:34 *)
Definition p2_body : result (u32 * u32) := Ok (0%u32, 1%u32).
Definition p2 : (u32 * u32) := p2_body%global.

(** [constants::P3]
    Source: 'tests/src/constants.rs', lines 37:0-37:51 *)
Definition p3_body : result (Pair_t u32 u32) :=
  Ok {| pair_x := 0%u32; pair_y := 1%u32 |}
.
Definition p3 : Pair_t u32 u32 := p3_body%global.

(** [constants::Wrap]
    Source: 'tests/src/constants.rs', lines 52:0-54:1 *)
Record Wrap_t (T : Type) := mkWrap_t { wrap_value : T; }.

Arguments mkWrap_t { _ }.
Arguments wrap_value { _ }.

(** [constants::{constants::Wrap<T>}::new]:
    Source: 'tests/src/constants.rs', lines 57:4-59:5 *)
Definition wrap_new {T : Type} (value : T) : result (Wrap_t T) :=
  Ok {| wrap_value := value |}
.

(** [constants::Y]
    Source: 'tests/src/constants.rs', lines 44:0-44:38 *)
Definition y_body : result (Wrap_t i32) := wrap_new 2%i32.
Definition y : Wrap_t i32 := y_body%global.

(** [constants::unwrap_y]:
    Source: 'tests/src/constants.rs', lines 46:0-48:1 *)
Definition unwrap_y : result i32 :=
  Ok y.(wrap_value).

(** [constants::YVAL]
    Source: 'tests/src/constants.rs', lines 50:0-50:33 *)
Definition yval_body : result i32 := unwrap_y.
Definition yval : i32 := yval_body%global.

(** [constants::get_z1::Z1]
    Source: 'tests/src/constants.rs', lines 65:4-65:22 *)
Definition get_z1_z1_body : result i32 := Ok 3%i32.
Definition get_z1_z1 : i32 := get_z1_z1_body%global.

(** [constants::get_z1]:
    Source: 'tests/src/constants.rs', lines 64:0-67:1 *)
Definition get_z1 : result i32 :=
  Ok get_z1_z1.

(** [constants::add]:
    Source: 'tests/src/constants.rs', lines 69:0-71:1 *)
Definition add (a : i32) (b : i32) : result i32 :=
  i32_add a b.

(** [constants::Q1]
    Source: 'tests/src/constants.rs', lines 77:0-77:22 *)
Definition q1_body : result i32 := Ok 5%i32.
Definition q1 : i32 := q1_body%global.

(** [constants::Q2]
    Source: 'tests/src/constants.rs', lines 78:0-78:23 *)
Definition q2_body : result i32 := Ok q1.
Definition q2 : i32 := q2_body%global.

(** [constants::Q3]
    Source: 'tests/src/constants.rs', lines 79:0-79:31 *)
Definition q3_body : result i32 := add q2 3%i32.
Definition q3 : i32 := q3_body%global.

(** [constants::get_z2]:
    Source: 'tests/src/constants.rs', lines 73:0-75:1 *)
Definition get_z2 : result i32 :=
  i <- get_z1; i1 <- add i q3; add q1 i1.

(** [constants::S1]
    Source: 'tests/src/constants.rs', lines 83:0-83:23 *)
Definition s1_body : result u32 := Ok 6%u32.
Definition s1 : u32 := s1_body%global.

(** [constants::S2]
    Source: 'tests/src/constants.rs', lines 84:0-84:30 *)
Definition s2_body : result u32 := incr s1.
Definition s2 : u32 := s2_body%global.

(** [constants::S3]
    Source: 'tests/src/constants.rs', lines 85:0-85:35 *)
Definition s3_body : result (Pair_t u32 u32) := Ok p3.
Definition s3 : Pair_t u32 u32 := s3_body%global.

(** [constants::S4]
    Source: 'tests/src/constants.rs', lines 86:0-86:47 *)
Definition s4_body : result (Pair_t u32 u32) := mk_pair1 7%u32 8%u32.
Definition s4 : Pair_t u32 u32 := s4_body%global.

(** [constants::V]
    Source: 'tests/src/constants.rs', lines 89:0-91:1 *)
Record V_t (T : Type) (N : usize) := mkV_t { v_x : array T N; }.

Arguments mkV_t { _ } { _ }.
Arguments v_x { _ } { _ }.

(** [constants::{constants::V<T, N>}#1::LEN]
    Source: 'tests/src/constants.rs', lines 94:4-94:29 *)
Definition v_len_body (T : Type) (N : usize) : result usize := Ok N.
Definition v_len (T : Type) (N : usize) : usize := (v_len_body T N)%global.

(** [constants::use_v]:
    Source: 'tests/src/constants.rs', lines 97:0-99:1 *)
Definition use_v (T : Type) (N : usize) : result usize :=
  Ok (v_len T N).

End Constants.
