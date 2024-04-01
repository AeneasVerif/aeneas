(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [external]: function definitions *)
module External.Funs
open Primitives
include External.Types
include External.FunsExternal

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** [external::swap]:
    Source: 'src/external.rs', lines 6:0-6:46 *)
let swap (t : Type0) (x : t) (y : t) (st : state) : result (state & (t & t)) =
  core_mem_swap t x y st

(** [external::test_new_non_zero_u32]:
    Source: 'src/external.rs', lines 11:0-11:60 *)
let test_new_non_zero_u32
  (x : u32) (st : state) : result (state & core_num_nonzero_NonZeroU32_t) =
  let* (st1, o) = core_num_nonzero_NonZeroU32_new x st in
  core_option_Option_unwrap core_num_nonzero_NonZeroU32_t o st1

(** [external::test_vec]:
    Source: 'src/external.rs', lines 17:0-17:17 *)
let test_vec : result unit =
  let* _ = alloc_vec_Vec_push u32 (alloc_vec_Vec_new u32) 0 in Ok ()

(** Unit test for [external::test_vec] *)
let _ = assert_norm (test_vec = Ok ())

(** [external::custom_swap]:
    Source: 'src/external.rs', lines 24:0-24:66 *)
let custom_swap
  (t : Type0) (x : t) (y : t) (st : state) :
  result (state & (t & (t -> state -> result (state & (t & t)))))
  =
  let* (st1, (x1, y1)) = core_mem_swap t x y st in
  let back_'a = fun ret st2 -> Ok (st2, (ret, y1)) in
  Ok (st1, (x1, back_'a))

(** [external::test_custom_swap]:
    Source: 'src/external.rs', lines 29:0-29:59 *)
let test_custom_swap
  (x : u32) (y : u32) (st : state) : result (state & (u32 & u32)) =
  let* (st1, (_, custom_swap_back)) = custom_swap u32 x y st in
  let* (_, (x1, y1)) = custom_swap_back 1 st1 in
  Ok (st1, (x1, y1))

(** [external::test_swap_non_zero]:
    Source: 'src/external.rs', lines 35:0-35:44 *)
let test_swap_non_zero (x : u32) (st : state) : result (state & u32) =
  let* (st1, p) = swap u32 x 0 st in
  let (x1, _) = p in
  if x1 = 0 then Fail Failure else Ok (st1, x1)

