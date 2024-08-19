-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [tutorial]
import Base
open Primitives
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace tutorial

/- [tutorial::choose]:
   Source: 'src/lib.rs', lines 1:0-1:70 -/
def choose
  (T : Type) (b : Bool) (x : T) (y : T) :
  Result (T × (T → Result (T × T)))
  :=
  if b
  then let back := fun ret => Result.ok (ret, y)
       Result.ok (x, back)
  else let back := fun ret => Result.ok (x, ret)
       Result.ok (y, back)

/- [tutorial::mul2_add1]:
   Source: 'src/lib.rs', lines 9:0-9:31 -/
def mul2_add1 (x : U32) : Result U32 :=
  do
  let i ← x + x
  i + 1#u32

/- [tutorial::mul2_add1_add]:
   Source: 'src/lib.rs', lines 13:0-13:43 -/
def mul2_add1_add (x : U32) (y : U32) : Result U32 :=
  do
  let i ← mul2_add1 x
  i + y

/- [tutorial::incr]:
   Source: 'src/lib.rs', lines 17:0-17:31 -/
def incr (x : U32) : Result U32 :=
  x + 1#u32

/- [tutorial::use_incr]:
   Source: 'src/lib.rs', lines 21:0-21:17 -/
def use_incr : Result Unit :=
  do
  let x ← incr 0#u32
  let x1 ← incr x
  let _ ← incr x1
  Result.ok ()

/- [tutorial::CList]
   Source: 'src/lib.rs', lines 30:0-30:17 -/
inductive CList (T : Type) :=
| CCons : T → CList T → CList T
| CNil : CList T

/- [tutorial::list_nth]:
   Source: 'src/lib.rs', lines 35:0-35:56 -/
divergent def list_nth (T : Type) (l : CList T) (i : U32) : Result T :=
  match l with
  | CList.CCons x tl =>
    if i = 0#u32
    then Result.ok x
    else do
         let i1 ← i - 1#u32
         list_nth T tl i1
  | CList.CNil => Result.fail .panic

/- [tutorial::list_nth_mut]:
   Source: 'src/lib.rs', lines 50:0-50:68 -/
divergent def list_nth_mut
  (T : Type) (l : CList T) (i : U32) :
  Result (T × (T → Result (CList T)))
  :=
  match l with
  | CList.CCons x tl =>
    if i = 0#u32
    then
      let back := fun ret => Result.ok (CList.CCons ret tl)
      Result.ok (x, back)
    else
      do
      let i1 ← i - 1#u32
      let (t, list_nth_mut_back) ← list_nth_mut T tl i1
      let back :=
        fun ret =>
          do
          let tl1 ← list_nth_mut_back ret
          Result.ok (CList.CCons x tl1)
      Result.ok (t, back)
  | CList.CNil => Result.fail .panic

/- [tutorial::list_nth1]: loop 0:
   Source: 'src/lib.rs', lines 65:0-74:1 -/
divergent def list_nth1_loop (T : Type) (l : CList T) (i : U32) : Result T :=
  match l with
  | CList.CCons x tl =>
    if i = 0#u32
    then Result.ok x
    else do
         let i1 ← i - 1#u32
         list_nth1_loop T tl i1
  | CList.CNil => Result.fail .panic

/- [tutorial::list_nth1]:
   Source: 'src/lib.rs', lines 65:0-65:65 -/
@[reducible]
def list_nth1 (T : Type) (l : CList T) (i : U32) : Result T :=
  list_nth1_loop T l i

/- [tutorial::i32_id]:
   Source: 'src/lib.rs', lines 76:0-76:29 -/
divergent def i32_id (i : I32) : Result I32 :=
  if i = 0#i32
  then Result.ok 0#i32
  else do
       let i1 ← i - 1#i32
       let i2 ← i32_id i1
       i2 + 1#i32

/- [tutorial::even]:
   Source: 'src/lib.rs', lines 85:0-85:28 -/
mutual divergent def even (i : U32) : Result Bool :=
  if i = 0#u32
  then Result.ok true
  else do
       let i1 ← i - 1#u32
       odd i1

/- [tutorial::odd]:
   Source: 'src/lib.rs', lines 94:0-94:27 -/
divergent def odd (i : U32) : Result Bool :=
  if i = 0#u32
  then Result.ok false
  else do
       let i1 ← i - 1#u32
       even i1

end

/- Trait declaration: [tutorial::Counter]
   Source: 'src/lib.rs', lines 105:0-105:17 -/
structure Counter (Self : Type) where
  incr : Self → Result (Usize × Self)

/- [tutorial::{tutorial::Counter for usize}::incr]:
   Source: 'src/lib.rs', lines 110:4-110:31 -/
def CounterUsize.incr (self : Usize) : Result (Usize × Usize) :=
  do
  let self1 ← self + 1#usize
  Result.ok (self, self1)

/- Trait implementation: [tutorial::{tutorial::Counter for usize}]
   Source: 'src/lib.rs', lines 109:0-109:22 -/
@[reducible]
def CounterUsize : Counter Usize := {
  incr := CounterUsize.incr
}

/- [tutorial::use_counter]:
   Source: 'src/lib.rs', lines 117:0-117:59 -/
def use_counter
  (T : Type) (CounterInst : Counter T) (cnt : T) : Result (Usize × T) :=
  CounterInst.incr cnt

/- [tutorial::list_nth_mut1]: loop 0:
   Source: 'src/lib.rs', lines 123:0-132:1 -/
divergent def list_nth_mut1_loop
  (T : Type) (l : CList T) (i : U32) :
  Result (T × (T → Result (CList T)))
  :=
  match l with
  | CList.CCons x tl =>
    if i = 0#u32
    then
      let back := fun ret => Result.ok (CList.CCons ret tl)
      Result.ok (x, back)
    else
      do
      let i1 ← i - 1#u32
      let (t, back) ← list_nth_mut1_loop T tl i1
      let back1 :=
        fun ret => do
                   let tl1 ← back ret
                   Result.ok (CList.CCons x tl1)
      Result.ok (t, back1)
  | CList.CNil => Result.fail .panic

/- [tutorial::list_nth_mut1]:
   Source: 'src/lib.rs', lines 123:0-123:77 -/
@[reducible]
def list_nth_mut1
  (T : Type) (l : CList T) (i : U32) :
  Result (T × (T → Result (CList T)))
  :=
  list_nth_mut1_loop T l i

/- [tutorial::list_tail]: loop 0:
   Source: 'src/lib.rs', lines 134:0-139:1 -/
divergent def list_tail_loop
  (T : Type) (l : CList T) :
  Result ((CList T) × (CList T → Result (CList T)))
  :=
  match l with
  | CList.CCons t tl =>
    do
    let (c, back) ← list_tail_loop T tl
    let back1 :=
      fun ret => do
                 let tl1 ← back ret
                 Result.ok (CList.CCons t tl1)
    Result.ok (c, back1)
  | CList.CNil => Result.ok (CList.CNil, Result.ok)

/- [tutorial::list_tail]:
   Source: 'src/lib.rs', lines 134:0-134:68 -/
@[reducible]
def list_tail
  (T : Type) (l : CList T) :
  Result ((CList T) × (CList T → Result (CList T)))
  :=
  list_tail_loop T l

/- [tutorial::append_in_place]:
   Source: 'src/lib.rs', lines 141:0-141:67 -/
def append_in_place
  (T : Type) (l0 : CList T) (l1 : CList T) : Result (CList T) :=
  do
  let (_, list_tail_back) ← list_tail T l0
  list_tail_back l1

/- [tutorial::zero]: loop 0:
   Source: 'src/lib.rs', lines 152:4-157:1 -/
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
   Source: 'src/lib.rs', lines 151:0-151:28 -/
def zero (x : alloc.vec.Vec U32) : Result (alloc.vec.Vec U32) :=
  zero_loop x 0#usize

/- [tutorial::add_no_overflow]: loop 0:
   Source: 'src/lib.rs', lines 165:4-170:1 -/
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
    let i4 ← i3 + i2
    let i5 ← i + 1#usize
    let x1 ← index_mut_back i4
    add_no_overflow_loop x1 y i5
  else Result.ok x

/- [tutorial::add_no_overflow]:
   Source: 'src/lib.rs', lines 164:0-164:50 -/
def add_no_overflow
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) :
  Result (alloc.vec.Vec U32)
  :=
  add_no_overflow_loop x y 0#usize

/- [tutorial::add_with_carry]: loop 0:
   Source: 'src/lib.rs', lines 177:4-188:1 -/
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
   Source: 'src/lib.rs', lines 175:0-175:55 -/
def add_with_carry
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) :
  Result (U8 × (alloc.vec.Vec U32))
  :=
  add_with_carry_loop x y 0#u8 0#usize

/- [tutorial::max]:
   Source: 'src/lib.rs', lines 190:0-190:37 -/
def max (x : Usize) (y : Usize) : Result Usize :=
  if x > y
  then Result.ok x
  else Result.ok y

/- [tutorial::get_or_zero]:
   Source: 'src/lib.rs', lines 194:0-194:45 -/
def get_or_zero (y : alloc.vec.Vec U32) (i : Usize) : Result U32 :=
  let i1 := alloc.vec.Vec.len U32 y
  if i < i1
  then
    alloc.vec.Vec.index U32 Usize (core.slice.index.SliceIndexUsizeSliceTInst
      U32) y i
  else Result.ok 0#u32

/- [tutorial::add]: loop 0:
   Source: 'src/lib.rs', lines 208:4-224:1 -/
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
   Source: 'src/lib.rs', lines 203:0-203:38 -/
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
