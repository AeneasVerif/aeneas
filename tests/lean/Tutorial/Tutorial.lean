-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [tutorial]
import Base
open Primitives
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace tutorial

/- [tutorial::zero]: loop 0:
   Source: 'src/lib.rs', lines 6:4-11:1 -/
divergent def zero_loop
  (x : alloc.vec.Vec U32) (i : Usize) : Result (alloc.vec.Vec U32) :=
  let i1 := alloc.vec.Vec.len U32 x
  if i < i1
  then
    do
    let (_, index_mut_back) ←
      alloc.vec.Vec.index_mut U32 Usize
        (core.slice.index.SliceIndexUsizeSliceTInst U32) x i
    let i2 ← i + 1#usize
    let x1 ← index_mut_back 0#u32
    zero_loop x1 i2
  else Result.ok x

/- [tutorial::zero]:
   Source: 'src/lib.rs', lines 5:0-5:28 -/
def zero (x : alloc.vec.Vec U32) : Result (alloc.vec.Vec U32) :=
  zero_loop x 0#usize

/- [tutorial::add_no_overflow]: loop 0:
   Source: 'src/lib.rs', lines 19:4-24:1 -/
divergent def add_no_overflow_loop
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) (i : Usize) :
  Result (alloc.vec.Vec U32)
  :=
  let i1 := alloc.vec.Vec.len U32 x
  if i < i1
  then
    do
    let i2 ←
      alloc.vec.Vec.index U32 Usize (core.slice.index.SliceIndexUsizeSliceTInst
        U32) y i
    let (i3, index_mut_back) ←
      alloc.vec.Vec.index_mut U32 Usize
        (core.slice.index.SliceIndexUsizeSliceTInst U32) x i
    let i2 : U32 := i2
    let i3 : U32 := i3
    let i4 ← i3 + i2
    let i5 ← i + 1#usize
    let x1 ← index_mut_back i4
    add_no_overflow_loop x1 y i5
  else Result.ok x

/- [tutorial::add_no_overflow]:
   Source: 'src/lib.rs', lines 18:0-18:50 -/
def add_no_overflow
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) :
  Result (alloc.vec.Vec U32)
  :=
  add_no_overflow_loop x y 0#usize

/- [tutorial::max]:
   Source: 'src/lib.rs', lines 26:0-26:37 -/
def max (x : Usize) (y : Usize) : Result Usize :=
  if x > y
  then Result.ok x
  else Result.ok y

/- [tutorial::get_or_zero]:
   Source: 'src/lib.rs', lines 30:0-30:45 -/
def get_or_zero (y : alloc.vec.Vec U32) (i : Usize) : Result U32 :=
  let i1 := alloc.vec.Vec.len U32 y
  if i < i1
  then
    alloc.vec.Vec.index U32 Usize (core.slice.index.SliceIndexUsizeSliceTInst
      U32) y i
  else Result.ok 0#u32

/- [core::num::{u32}#8::overflowing_add]:
   Source: '/rustc/library/core/src/num/uint_macros.rs', lines 2182:8-2182:69
   Name pattern: core::num::{u32}::overflowing_add -/
axiom core.num.U32.overflowing_add : U32 → U32 → Result (U32 × Bool)

/- [tutorial::add_with_carry]: loop 0:
   Source: 'src/lib.rs', lines 39:4-50:1 -/
divergent def add_with_carry_loop
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) (c0 : U8) (i : Usize) :
  Result (U8 × (alloc.vec.Vec U32))
  :=
  let i1 := alloc.vec.Vec.len U32 x
  if i < i1
  then
    do
    let i2 ←
      alloc.vec.Vec.index U32 Usize (core.slice.index.SliceIndexUsizeSliceTInst
        U32) x i
    let i3 ← Scalar.cast .U32 c0
    let p ← core.num.U32.overflowing_add i2 i3
    let (sum, c1) := p
    let i4 ←
      alloc.vec.Vec.index U32 Usize (core.slice.index.SliceIndexUsizeSliceTInst
        U32) y i
    let p1 ← core.num.U32.overflowing_add sum i4
    let (sum1, c2) := p1
    let i5 ← Scalar.cast_bool .U8 c1
    let i6 ← Scalar.cast_bool .U8 c2
    let c01 ← i5 + i6
    let (_, index_mut_back) ←
      alloc.vec.Vec.index_mut U32 Usize
        (core.slice.index.SliceIndexUsizeSliceTInst U32) x i
    let i7 ← i + 1#usize
    let x1 ← index_mut_back sum1
    add_with_carry_loop x1 y c01 i7
  else Result.ok (c0, x)

/- [tutorial::add_with_carry]:
   Source: 'src/lib.rs', lines 37:0-37:55 -/
def add_with_carry
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) :
  Result (U8 × (alloc.vec.Vec U32))
  :=
  add_with_carry_loop x y 0#u8 0#usize

/- [tutorial::add]: loop 0:
   Source: 'src/lib.rs', lines 60:4-76:1 -/
divergent def add_loop
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) (max1 : Usize) (c0 : U8)
  (i : Usize) :
  Result (alloc.vec.Vec U32)
  :=
  if i < max1
  then
    do
    let yi ← get_or_zero y i
    let i1 ←
      alloc.vec.Vec.index U32 Usize (core.slice.index.SliceIndexUsizeSliceTInst
        U32) x i
    let i2 ← Scalar.cast .U32 c0
    let p ← core.num.U32.overflowing_add i1 i2
    let (sum, c1) := p
    let p1 ← core.num.U32.overflowing_add sum yi
    let (sum1, c2) := p1
    let i3 ← Scalar.cast_bool .U8 c1
    let i4 ← Scalar.cast_bool .U8 c2
    let c01 ← i3 + i4
    let (_, index_mut_back) ←
      alloc.vec.Vec.index_mut U32 Usize
        (core.slice.index.SliceIndexUsizeSliceTInst U32) x i
    let i5 ← i + 1#usize
    let x1 ← index_mut_back sum1
    add_loop x1 y max1 c01 i5
  else
    if c0 != 0#u8
    then do
         let i1 ← Scalar.cast .U32 c0
         alloc.vec.Vec.push U32 x i1
    else Result.ok x

/- [tutorial::add]:
   Source: 'src/lib.rs', lines 55:0-55:38 -/
def add
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) :
  Result (alloc.vec.Vec U32)
  :=
  do
  let i := alloc.vec.Vec.len U32 x
  let i1 := alloc.vec.Vec.len U32 y
  let max1 ← max i i1
  let x1 ← alloc.vec.Vec.resize U32 core.clone.CloneU32 x max1 0#u32
  add_loop x1 y max1 0#u8 0#usize

end tutorial
