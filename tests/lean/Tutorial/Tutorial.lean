-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [tutorial]
import Aeneas
open Aeneas.Std Result Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace tutorial

/- [tutorial::choose]:
   Source: 'src/lib.rs', lines 1:0-7:1 -/
def choose
  {T : Type} (b : Bool) (x : T) (y : T) : Result (T × (T → (T × T))) :=
  if b
  then let back := fun ret => (ret, y)
       ok (x, back)
  else let back := fun ret => (x, ret)
       ok (y, back)

/- [tutorial::mul2_add1]:
   Source: 'src/lib.rs', lines 9:0-11:1 -/
def mul2_add1 (x : U32) : Result U32 :=
  do
  let i ← x + x
  i + 1#u32

/- [tutorial::mul2_add1_add]:
   Source: 'src/lib.rs', lines 13:0-15:1 -/
def mul2_add1_add (x : U32) (y : U32) : Result U32 :=
  do
  let i ← mul2_add1 x
  i + y

/- [tutorial::incr]:
   Source: 'src/lib.rs', lines 17:0-19:1 -/
def incr (x : U32) : Result U32 :=
  x + 1#u32

/- [tutorial::use_incr]:
   Source: 'src/lib.rs', lines 21:0-26:1 -/
def use_incr : Result Unit :=
  do
  let x ← incr 0#u32
  let x1 ← incr x
  let _ ← incr x1
  ok ()

/- [tutorial::CList]
   Source: 'src/lib.rs', lines 30:0-33:1 -/
inductive CList (T : Type) where
| CCons : T → CList T → CList T
| CNil : CList T

/- [tutorial::list_nth]:
   Source: 'src/lib.rs', lines 35:0-48:1 -/
def list_nth {T : Type} (l : CList T) (i : U32) : Result T :=
  match l with
  | CList.CCons x tl =>
    if i = 0#u32
    then ok x
    else do
         let i1 ← i - 1#u32
         list_nth tl i1
  | CList.CNil => fail panic
partial_fixpoint

/- [tutorial::list_nth_mut]:
   Source: 'src/lib.rs', lines 50:0-63:1 -/
def list_nth_mut
  {T : Type} (l : CList T) (i : U32) : Result (T × (T → CList T)) :=
  match l with
  | CList.CCons x tl =>
    if i = 0#u32
    then let back := fun ret => CList.CCons ret tl
         ok (x, back)
    else
      do
      let i1 ← i - 1#u32
      let (t, list_nth_mut_back) ← list_nth_mut tl i1
      let back := fun ret => let tl1 := list_nth_mut_back ret
                             CList.CCons x tl1
      ok (t, back)
  | CList.CNil => fail panic
partial_fixpoint

/- [tutorial::list_nth1]: loop 0:
   Source: 'src/lib.rs', lines 66:4-74:1 -/
def list_nth1_loop {T : Type} (l : CList T) (i : U32) : Result T :=
  match l with
  | CList.CCons x tl =>
    if i = 0#u32
    then ok x
    else do
         let i1 ← i - 1#u32
         list_nth1_loop tl i1
  | CList.CNil => fail panic
partial_fixpoint

/- [tutorial::list_nth1]:
   Source: 'src/lib.rs', lines 65:0-74:1 -/
@[reducible]
def list_nth1 {T : Type} (l : CList T) (i : U32) : Result T :=
  list_nth1_loop l i

/- [tutorial::i32_id]:
   Source: 'src/lib.rs', lines 76:0-83:1 -/
def i32_id (i : I32) : Result I32 :=
  if i = 0#i32
  then ok 0#i32
  else do
       let i1 ← i - 1#i32
       let i2 ← i32_id i1
       i2 + 1#i32
partial_fixpoint

/- [tutorial::even]:
   Source: 'src/lib.rs', lines 85:0-92:1 -/
mutual def even (i : U32) : Result Bool :=
  if i = 0#u32
  then ok true
  else do
       let i1 ← i - 1#u32
       odd i1
partial_fixpoint

/- [tutorial::odd]:
   Source: 'src/lib.rs', lines 94:0-101:1 -/
def odd (i : U32) : Result Bool :=
  if i = 0#u32
  then ok false
  else do
       let i1 ← i - 1#u32
       even i1
partial_fixpoint

end

/- Trait declaration: [tutorial::Counter]
   Source: 'src/lib.rs', lines 105:0-107:1 -/
structure Counter (Self : Type) where
  incr : Self → Result (Usize × Self)

/- [tutorial::{tutorial::Counter for usize}::incr]:
   Source: 'src/lib.rs', lines 110:4-114:5 -/
def CounterUsize.incr (self : Usize) : Result (Usize × Usize) :=
  do
  let self1 ← self + 1#usize
  ok (self, self1)

/- Trait implementation: [tutorial::{tutorial::Counter for usize}]
   Source: 'src/lib.rs', lines 109:0-115:1 -/
@[reducible]
def CounterUsize : Counter Usize := {
  incr := CounterUsize.incr
}

/- [tutorial::use_counter]:
   Source: 'src/lib.rs', lines 117:0-119:1 -/
def use_counter
  {T : Type} (CounterInst : Counter T) (cnt : T) : Result (Usize × T) :=
  CounterInst.incr cnt

/- [tutorial::list_nth_mut1]: loop 0:
   Source: 'src/lib.rs', lines 124:4-132:1 -/
def list_nth_mut1_loop
  {T : Type} (l : CList T) (i : U32) : Result (T × (T → CList T)) :=
  match l with
  | CList.CCons x tl =>
    if i = 0#u32
    then let back := fun ret => CList.CCons ret tl
         ok (x, back)
    else
      do
      let i1 ← i - 1#u32
      let (t, back) ← list_nth_mut1_loop tl i1
      let back1 := fun ret => let tl1 := back ret
                              CList.CCons x tl1
      ok (t, back1)
  | CList.CNil => fail panic
partial_fixpoint

/- [tutorial::list_nth_mut1]:
   Source: 'src/lib.rs', lines 123:0-132:1 -/
@[reducible]
def list_nth_mut1
  {T : Type} (l : CList T) (i : U32) : Result (T × (T → CList T)) :=
  list_nth_mut1_loop l i

/- [tutorial::list_tail]: loop 0:
   Source: 'src/lib.rs', lines 135:4-137:5 -/
def list_tail_loop
  {T : Type} (l : CList T) : Result ((CList T) × (CList T → CList T)) :=
  match l with
  | CList.CCons t tl =>
    do
    let (c, back) ← list_tail_loop tl
    let back1 := fun ret => let tl1 := back ret
                            CList.CCons t tl1
    ok (c, back1)
  | CList.CNil => ok (CList.CNil, fun ret => ret)
partial_fixpoint

/- [tutorial::list_tail]:
   Source: 'src/lib.rs', lines 134:0-139:1 -/
@[reducible]
def list_tail
  {T : Type} (l : CList T) : Result ((CList T) × (CList T → CList T)) :=
  list_tail_loop l

/- [tutorial::append_in_place]:
   Source: 'src/lib.rs', lines 141:0-144:1 -/
def append_in_place
  {T : Type} (l0 : CList T) (l1 : CList T) : Result (CList T) :=
  do
  let (_, list_tail_back) ← list_tail l0
  ok (list_tail_back l1)

/- [tutorial::reverse]: loop 0:
   Source: 'src/lib.rs', lines 148:4-152:5 -/
def reverse_loop {T : Type} (l : CList T) (out : CList T) : Result (CList T) :=
  match l with
  | CList.CCons hd tl => reverse_loop tl (CList.CCons hd out)
  | CList.CNil => ok out
partial_fixpoint

/- [tutorial::reverse]:
   Source: 'src/lib.rs', lines 146:0-154:1 -/
@[reducible]
def reverse {T : Type} (l : CList T) : Result (CList T) :=
  reverse_loop l CList.CNil

/- [tutorial::zero]: loop 0:
   Source: 'src/lib.rs', lines 164:4-167:5 -/
def zero_loop
  (x : alloc.vec.Vec U32) (i : Usize) : Result (alloc.vec.Vec U32) :=
  let i1 := alloc.vec.Vec.len x
  if i < i1
  then
    do
    let (_, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSliceInst U32) x
        i
    let i2 ← i + 1#usize
    let x1 := index_mut_back 0#u32
    zero_loop x1 i2
  else ok x
partial_fixpoint

/- [tutorial::zero]:
   Source: 'src/lib.rs', lines 162:0-168:1 -/
@[reducible]
def zero (x : alloc.vec.Vec U32) : Result (alloc.vec.Vec U32) :=
  zero_loop x 0#usize

/- [tutorial::add_no_overflow]: loop 0:
   Source: 'src/lib.rs', lines 177:4-180:5 -/
def add_no_overflow_loop
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) (i : Usize) :
  Result (alloc.vec.Vec U32)
  :=
  let i1 := alloc.vec.Vec.len x
  if i < i1
  then
    do
    let i2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSliceInst U32) y i
    let (i3, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSliceInst U32) x
        i
    let i4 ← i3 + i2
    let i5 ← i + 1#usize
    let x1 := index_mut_back i4
    add_no_overflow_loop x1 y i5
  else ok x
partial_fixpoint

/- [tutorial::add_no_overflow]:
   Source: 'src/lib.rs', lines 175:0-181:1 -/
@[reducible]
def add_no_overflow
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) :
  Result (alloc.vec.Vec U32)
  :=
  add_no_overflow_loop x y 0#usize

/- [tutorial::add_with_carry]: loop 0:
   Source: 'src/lib.rs', lines 190:4-197:5 -/
def add_with_carry_loop
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) (c0 : U8) (i : Usize) :
  Result (U8 × (alloc.vec.Vec U32))
  :=
  let i1 := alloc.vec.Vec.len x
  if i < i1
  then
    do
    let i2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSliceInst U32) x i
    let i3 ← (↑(UScalar.cast .U32 c0) : Result U32)
    let (sum, c1) ←
      (↑(core.num.U32.overflowing_add i2 i3) : Result (U32 × Bool))
    let i4 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSliceInst U32) y i
    let (sum1, c2) ←
      (↑(core.num.U32.overflowing_add sum i4) : Result (U32 × Bool))
    let i5 ← (↑(UScalar.cast_fromBool .U8 c1) : Result U8)
    let i6 ← (↑(UScalar.cast_fromBool .U8 c2) : Result U8)
    let c01 ← i5 + i6
    let (_, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSliceInst U32) x
        i
    let i7 ← i + 1#usize
    let x1 := index_mut_back sum1
    add_with_carry_loop x1 y c01 i7
  else ok (c0, x)
partial_fixpoint

/- [tutorial::add_with_carry]:
   Source: 'src/lib.rs', lines 186:0-199:1 -/
@[reducible]
def add_with_carry
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) :
  Result (U8 × (alloc.vec.Vec U32))
  :=
  add_with_carry_loop x y 0#u8 0#usize

/- [tutorial::max]:
   Source: 'src/lib.rs', lines 201:0-203:1 -/
def max (x : Usize) (y : Usize) : Result Usize :=
  if x > y
  then ok x
  else ok y

/- [tutorial::get_or_zero]:
   Source: 'src/lib.rs', lines 205:0-207:1 -/
def get_or_zero (y : alloc.vec.Vec U32) (i : Usize) : Result U32 :=
  let i1 := alloc.vec.Vec.len y
  if i < i1
  then alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSliceInst U32) y i
  else ok 0#u32

/- [tutorial::add]: loop 0:
   Source: 'src/lib.rs', lines 221:4-229:5 -/
def add_loop
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) (max1 : Usize) (c0 : U8)
  (i : Usize) :
  Result (alloc.vec.Vec U32)
  :=
  if i < max1
  then
    do
    let yi ← get_or_zero y i
    let i1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSliceInst U32) x i
    let i2 ← (↑(UScalar.cast .U32 c0) : Result U32)
    let (sum, c1) ←
      (↑(core.num.U32.overflowing_add i1 i2) : Result (U32 × Bool))
    let (sum1, c2) ←
      (↑(core.num.U32.overflowing_add sum yi) : Result (U32 × Bool))
    let i3 ← (↑(UScalar.cast_fromBool .U8 c1) : Result U8)
    let i4 ← (↑(UScalar.cast_fromBool .U8 c2) : Result U8)
    let c01 ← i3 + i4
    let (_, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSliceInst U32) x
        i
    let i5 ← i + 1#usize
    let x1 := index_mut_back sum1
    add_loop x1 y max1 c01 i5
  else
    if c0 != 0#u8
    then
      do
      let i1 ← (↑(UScalar.cast .U32 c0) : Result U32)
      alloc.vec.Vec.push x i1
    else ok x
partial_fixpoint

/- [tutorial::add]:
   Source: 'src/lib.rs', lines 214:0-235:1 -/
def add
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) :
  Result (alloc.vec.Vec U32)
  :=
  do
  let i := alloc.vec.Vec.len x
  let i1 := alloc.vec.Vec.len y
  let max1 ← max i i1
  let x1 ← alloc.vec.Vec.resize core.clone.CloneU32 x max1 0#u32
  add_loop x1 y max1 0#u8 0#usize

end tutorial
