import Base
open Primitives Result

namespace Primitives

end Primitives

namespace Tutorial

-- TODO: move, use natural numbers, etc.
@[simp]
theorem index_update_eq_unsigned_scalar
  {α : Type u} [Inhabited α] (l: List α) (i: Scalar ty) (x: α) :
  ¬ ty.isSigned → i.val < l.length → (l.update i.val x).index i.val = x := by
  intros
  apply List.index_update_eq <;> (try simp [*])
  cases ty <;> simp_all <;> scalar_tac


-- TODO: specialize the theorems for the cases unsigned scalar
-- TODO: use natural numbers
-- TODO: theorems for .toNat
-- Ex.: (x.val + n).toNat = x.toNat + n.toNat

-- TODO: use simp with discharger to simplify array expressions
-- TODO: introduce gindex (for ghost index)

def times4 (x : U32) : Result U32 := do
  let x1 ← x + x
  x1 + x1

def times16 (x : U32) : Result U32 := do
  let x1 ← times4 x
  times4 x1

#check U32.add_spec

-- Without progress
theorem times4_spec (x : U32) (h : 4 * x.val ≤ U32.max) :
  times4 x = ok (4 * x)#u32 := by
  rw [times4]
  have ⟨ x1, hEq1, hPost1 ⟩ := @U32.add_spec x x (by scalar_tac)
  simp [hEq1]
  have ⟨ x2, hEq2, hPost2 ⟩ := @U32.add_spec x1 x1 (by scalar_tac)
  simp [hEq2]
  scalar_tac

-- With progress
@[pspec]
theorem times4_spec1 (x : U32) (h : 4 * x.val ≤ U32.max) :
  times4 x = ok (4 * x)#u32 := by
  rw [times4]
  progress
  progress
  scalar_tac

theorem times16_spec (x : U32) (h : 16 * x.val ≤ U32.max) :
  times16 x = ok (16 * x)#u32 := by
  rw [times16]
  progress
  progress
  scalar_tac

/- [demo::incr]:
   Source: 'tests/src/demo.rs', lines 23:0-23:31 -/
def incr (x : U32) : Result U32 :=
  x + 1#u32

/- [demo::use_incr]:
   Source: 'tests/src/demo.rs', lines 27:0-27:17 -/
def use_incr : Result Unit :=
  do
  let x ← incr 0#u32
  let x1 ← incr x
  let _ ← incr x1
  Result.ok ()

divergent def i32_id (n : I32) : Result I32 :=
  if n = 0#i32 then ok 0#i32
  else do
    let n1 ← n - 1#i32
    let n2 ← i32_id n1
    n2 + 1#i32

theorem i32_id_spec (n : I32) (h : 0 ≤ n.val) :
  i32_id n = ok n := by
  rw [i32_id]
  split
  . simp [*]
  . progress as ⟨ n1 ⟩
    progress
    progress as ⟨ n2 ⟩
    scalar_tac
termination_by n.toNat
decreasing_by simp_wf; scalar_tac

mutual

divergent def even (n : U32) : Result Bool :=
  if n = 0#u32 then ok true
  else do
    let n ← n - 1#u32
    odd n

divergent def odd (n : U32) : Result Bool :=
  if n = 0#u32 then ok false
  else do
    let n ← n - 1#u32
    even n

end

mutual

theorem even_spec (n : U32) :
  ∃ b, even n = ok b ∧ (b ↔ Even n.val) := by
  rw [even]
  split
  . simp [*]
  . progress as ⟨ n' ⟩
    progress as ⟨ b ⟩
    simp [*]
    simp [Int.even_sub]
termination_by n.toNat
decreasing_by simp_wf; scalar_tac

theorem odd_spec (n : U32) :
  ∃ b, odd n = ok b ∧ (b ↔ Odd n.val) := by
  rw [odd]
  split
  . simp [*]
  . progress as ⟨ n' ⟩
    progress as ⟨ b ⟩
    simp [*]
    simp [Int.even_sub]
termination_by n.toNat
decreasing_by simp_wf; scalar_tac

end

/- [demo::CList]
   Source: 'tests/src/demo.rs', lines 36:0-36:17 -/
inductive CList (T : Type) :=
| CCons : T → CList T → CList T
| CNil : CList T

/- [demo::list_nth]:
   Source: 'tests/src/demo.rs', lines 41:0-41:56 -/
divergent def list_nth (T : Type) (l : CList T) (i : U32) : Result T :=
  match l with
  | CList.CCons x tl =>
    if i = 0#u32
    then Result.ok x
    else do
         let i1 ← i - 1#u32
         list_nth T tl i1
  | CList.CNil => Result.fail .panic

-- TODO: list_nth1 (with a loop)

/- [demo::list_tail]:
   Source: 'tests/src/demo.rs', lines 90:0-90:64 -/
divergent def list_tail
  (T : Type) (l : CList T) :
  Result ((CList T) × (CList T → Result (CList T)))
  :=
  match l with
  | CList.CCons t tl =>
    do
    let (c, list_tail_back) ← list_tail T tl
    let back :=
      fun ret =>
        do
        let tl1 ← list_tail_back ret
        Result.ok (CList.CCons t tl1)
    Result.ok (c, back)
  | CList.CNil => Result.ok (CList.CNil, Result.ok)

open CList

@[simp] def CList.to_list {α : Type} (x : CList α) : List α :=
  match x with
  | CNil => []
  | CCons hd tl => hd :: tl.to_list

theorem list_nth_spec {T : Type} [Inhabited T] (l : CList T) (i : U32)
  (h : i.val < l.to_list.length) :
  ∃ x, list_nth T l i = ok x ∧
  x = l.to_list.index ↑i
  := by
  rw [list_nth]
  match l with
  | CNil =>
    simp_all; scalar_tac
  | CCons hd tl =>
    simp_all
    if hi: i = 0#u32 then
      simp_all
    else
      simp_all
      progress as ⟨ i1 ⟩
      progress as ⟨ x ⟩
      simp_all

theorem list_tail_spec {T : Type} [Inhabited T] (l : CList T) :
  ∃ back, list_tail T l = ok (CList.CNil, back) ∧
  ∀ tl', ∃ l', back tl' = ok l' ∧ l'.to_list = l.to_list ++ tl'.to_list := by
  rw [list_tail]
  match l with
  | CNil =>
    simp_all
  | CCons hd tl =>
    simp_all
    progress as ⟨ back ⟩
    simp
    -- Proving the backward function
    intro tl'
    progress
    simp_all

/- Trait declaration: [demo::Counter]
   Source: 'tests/src/demo.rs', lines 99:0-99:17 -/
structure Counter (Self : Type) where
  incr : Self → Result (Usize × Self)

/- [demo::{demo::Counter for usize}::incr]:
   Source: 'tests/src/demo.rs', lines 104:4-104:31 -/
def CounterUsize.incr (self : Usize) : Result (Usize × Usize) :=
  do
  let self1 ← self + 1#usize
  Result.ok (self, self1)

/- Trait implementation: [demo::{demo::Counter for usize}]
   Source: 'tests/src/demo.rs', lines 103:0-103:22 -/
def CounterUsize : Counter Usize := {
  incr := CounterUsize.incr
}

/- [demo::use_counter]:
   Source: 'tests/src/demo.rs', lines 111:0-111:59 -/
def use_counter
  (T : Type) (CounterInst : Counter T) (cnt : T) : Result (Usize × T) :=
  CounterInst.incr cnt


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

set_option maxHeartbeats 1000000

abbrev Bignum U32 := alloc.vec.Vec U32

@[simp]
def toInt_aux (l : List U32) : ℤ :=
  match l with
  | [] => 0
  | x :: l =>
    x + 2 ^ 32 * toInt_aux l

@[reducible]
def toInt (x : alloc.vec.Vec U32) : ℤ := toInt_aux x.val

@[pspec]
theorem zero_loop_spec
  (x : alloc.vec.Vec U32) (i : Usize) (h : i.val ≤ x.length) :
  ∃ x',
    zero_loop x i = ok x' ∧
    x'.length = x.length ∧
    (∀ j, 0 ≤ j → j < i.val → x'.val.index j = x.val.index j) ∧
    (∀ j, i.val ≤ j → j < x.length → x'.val.index j = 0#u32) := by
  rw [zero_loop]
  simp
  split
  . progress as ⟨ _ ⟩
    progress as ⟨ i1 ⟩
    progress as ⟨ x1 ⟩
    progress as ⟨ x2, _, hSame, hZero ⟩
    simp_all
    split_conjs
    . intro j h0 h1
      replace hSame := hSame j (by scalar_tac) (by scalar_tac)
      simp_all
    . intro j h0 h1
      -- TODO: we want a shortcut for this
      cases h: (¬ j = i.val : Bool) <;> simp_all
      . have := hSame j (by scalar_tac) (by scalar_tac)
        simp_all
      . apply hZero j (by scalar_tac) (by scalar_tac)
  . simp; scalar_tac
termination_by (x.length - i.val).toNat
decreasing_by scalar_decr_tac

/- [tutorial::zero]:
   Source: 'src/lib.rs', lines 5:0-5:28 -/
def zero (x : alloc.vec.Vec U32) : Result (alloc.vec.Vec U32) :=
  zero_loop x 0#usize

theorem all_nil_impl_toInt_eq_zero
  (l : List U32) (h : ∀ (j : ℕ), j < l.length → l.index j = 0#u32) :
  toInt_aux l = 0 := by
  match l with
  | [] => simp
  | hd :: tl =>
    have h1 := h 0
    simp_all
    apply all_nil_impl_toInt_eq_zero
    intro j h2
    have := h (j + 1)
    simp_all

theorem zero_spec (x : alloc.vec.Vec U32) :
  ∃ x',
    zero x = ok x' ∧
    x'.length = x.length ∧
    toInt x' = 0 := by
    rw [zero]
    progress as ⟨ x', hLength, hSame, hZero ⟩
    simp_all
    apply all_nil_impl_toInt_eq_zero
    simp_all

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
    let i4 ← i3 + i2
    let i5 ← i + 1#usize
    let x1 ← index_mut_back i4
    add_no_overflow_loop x1 y i5
  else Result.ok x

@[simp]
def List.isplitAt (l : List α) (i : ℤ) : List α × List α :=
  match l with
  | [] => ([], [])
  | hd :: tl =>
    if i = 0 then ([], hd :: tl)
    else
      let (l0, l1) := isplitAt tl (i - 1)
      (hd :: l0, l1)

-- Here, we're using ring_nf
@[simp]
theorem toInt_aux_append (l0 l1 : List U32) :
  toInt_aux (l0 ++ l1) = toInt_aux l0 + 2 ^ (32 * l0.length) * toInt_aux l1 := by
  match l0 with
  | [] => simp
  | hd :: tl =>
    have := toInt_aux_append tl l1
    simp_all
    scalar_eq_nf

@[simp]
theorem toInt_aux_update (l : List U32) (i : Int) (x : U32) (h0 : 0 ≤ i) (h1 : i < l.length) :
  toInt_aux (l.update i x) = toInt_aux l + 2 ^ (32 * i.toNat) * (x - l.index i) := by
  cases l with
  | nil => simp at *; scalar_tac
  | cons hd tl =>
    simp_all
    -- TODO: simplify this
    cases h : (i = 0 : Bool) <;> simp_all
    . have := toInt_aux_update tl (i - 1) x (by scalar_tac) (by scalar_tac)
      simp_all
      scalar_nf at *
      scalar_eq_nf
      have : (2 ^ ((i.toNat - 1) * 32) * 4294967296  : Int) = 2 ^ (32 * i.toNat) := by
        scalar_nf
        have : i.toNat = i.toNat - 1 + 1 := by scalar_tac
        conv => rhs; rw [this]
        scalar_nf
      simp [mul_assoc, *]
      scalar_eq_nf
    . scalar_eq_nf

@[simp]
theorem toInt_aux_idrop (l : List U32) (i : Int) (h0 : 0 ≤ i) (h1 : i < l.length) :
  toInt_aux (l.idrop i) = l.index i + 2 ^ 32 * toInt_aux (l.idrop (i + 1)) := by
  cases l with
  | nil => simp at *; scalar_tac
  | cons hd tl =>
    simp_all
    -- TODO: simplify this
    cases h : (i = 0 : Bool) <;> simp_all
    have := toInt_aux_idrop tl (i - 1) (by scalar_tac) (by scalar_tac)
    simp_all
    scalar_nf at *
    have : 0 < 1 + i := by scalar_tac
    simp [*]

@[simp]
theorem UScalar.add_nat_toNat (h : ¬ ty.isSigned) (x : Scalar ty) (n : Nat) :
  (x.val + n).toNat = x.val.toNat + n := by
  cases ty <;> simp_all <;> scalar_tac

@[simp]
theorem UScalar.nat_add_toNat (h : ¬ ty.isSigned) (x : Scalar ty) (n : Nat) :
  (n + x.val).toNat = x.val.toNat + n := by
  cases ty <;> simp_all <;> scalar_tac

@[simp]
theorem UScalar.add_pos_toNat (h : ¬ ty.isSigned) (x : Scalar ty) (n : Int) (h' : 0 ≤ n) :
  (x.val + n).toNat = x.val.toNat + n.toNat := by
  cases ty <;> simp_all <;> scalar_tac

@[simp]
theorem UScalar.pos_add_toNat (h : ¬ ty.isSigned) (x : Scalar ty) (n : Int) (h' : 0 ≤ n) :
  (n + x.val).toNat = n.toNat + x.val.toNat := by
  cases ty <;> simp_all <;> scalar_tac

set_option maxHeartbeats 5000000

@[pspec]
theorem add_no_overflow_loop_spec
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) (i : Usize)
  (hLength : x.length = y.length)
  -- No overflow occurs when we add the individual thunks
  (hNoOverflow : ∀ (j : Int), i.val ≤ j → j < x.length → (x.val.index j).val + (y.val.index j).val ≤ U32.max)
  (hi : i.val ≤ x.length) :
  ∃ x', add_no_overflow_loop x y i = ok x' ∧
  x'.length = x.length ∧
  toInt x' = toInt x + 2 ^ (32 * i.toNat) * toInt_aux (y.val.idrop i.val) := by
  rw [add_no_overflow_loop]
  simp
  split
  . progress as ⟨ yv ⟩
    progress as ⟨ xv ⟩
    progress as ⟨ sum ⟩
    . have := hNoOverflow i.val (by scalar_tac) (by scalar_tac)
      scalar_tac
    . progress as ⟨ i' ⟩
      progress as ⟨ x1 ⟩
      progress as ⟨ x2 ⟩
      . -- This precondition is not proven automatically
        intro j h0 h1
        -- TODO: this is annoying
        -- TODO: aesop?
        have : i.val < j := by scalar_tac
        simp_all
        apply hNoOverflow j (by scalar_tac) (by scalar_tac)
      . -- Postcondition
        have : 0 ≤ i.val := by scalar_tac -- TODO: annoying
        simp_all [toInt]
        scalar_nf
  . simp_all
termination_by (x.length - i.val).toNat
decreasing_by scalar_decr_tac

/- [tutorial::add_no_overflow]:
   Source: 'src/lib.rs', lines 18:0-18:50 -/
def add_no_overflow
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) :
  Result (alloc.vec.Vec U32)
  :=
  add_no_overflow_loop x y 0#usize

theorem add_no_overflow_spec (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32)
  (hLength : x.length = y.length)
  (hNoOverflow : ∀ (j : Int), 0 ≤ j → j < x.length → (x.val.index j).val + (y.val.index j).val ≤ U32.max) :
  ∃ x', add_no_overflow x y = ok x' ∧
  x'.length = y.length ∧
  toInt x' = toInt x + toInt y := by
  rw [add_no_overflow]
  progress as ⟨ x' ⟩
  simp_all [toInt]

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

@[pspec]
theorem add_with_carry_loop_spec
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) (c0 : U8) (i : Usize)
  (hLength : x.length = y.length)
  (hi : i.val ≤ x.length)
  (hCarryLe : c0.val ≤ 1) :
  ∃ x' c1, add_with_carry_loop x y c0 i = ok (c1, x') ∧
  x'.length = x.length ∧
  c1.val ≤ 1 ∧
  toInt x' + c1.val * 2 ^ (32 * x'.length) =
    toInt x + 2 ^ (32 * i.toNat) * toInt_aux (y.val.idrop i.val) + c0.val * 2 ^ (32 * i.toNat) := by
  rw [add_with_carry_loop]
  simp
  split
  . progress as ⟨ xi ⟩
    progress as ⟨ c0u ⟩
    . -- TODO: automation with scalar tac, and more precise lemmas
      simp
      scalar_tac
    . progress as ⟨ s1, c1, hConv1 ⟩
      progress as ⟨ yi ⟩
      progress as ⟨ s2, c2, hConv2 ⟩
      progress as ⟨ c1u ⟩
      progress as ⟨ c2u ⟩
      progress as ⟨ c3 ⟩
      progress as ⟨ _ ⟩
      progress as ⟨ i1 ⟩
      progress as ⟨ x1 ⟩
      progress as ⟨ c4, x2 ⟩
      -- Proving the post-condition
      simp_all [toInt]
      have hxUpdate := toInt_aux_update x.val i.val s2 (by scalar_tac) (by scalar_tac)
      simp [hxUpdate]; clear hxUpdate
      have hyDrop := toInt_aux_idrop y.val i.val (by scalar_tac) (by scalar_tac)
      simp [hyDrop]; clear hyDrop
      scalar_eq_nf
      split at hConv1 <;>
      split at hConv2 <;>
      simp_all <;>
      scalar_eq_nf <;> simp [U32.max] <;> scalar_eq_nf
  . simp_all
    scalar_tac
termination_by (x.length - i.val).toNat
decreasing_by scalar_decr_tac

/- [tutorial::add_with_carry]:
   Source: 'src/lib.rs', lines 37:0-37:55 -/
def add_with_carry
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) :
  Result (U8 × (alloc.vec.Vec U32))
  :=
  add_with_carry_loop x y 0#u8 0#usize

@[pspec]
theorem add_with_carry_spec
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32)
  (hLength : x.length = y.length) :
  ∃ x' c, add_with_carry x y = ok (c, x') ∧
  x'.length = x.length ∧
  c.val ≤ 1 ∧
  toInt x' + c.val * 2 ^ (32 * x'.length) = toInt x + toInt y := by
  rw [add_with_carry]
  progress as ⟨ c, x' ⟩
  simp_all

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

end Tutorial
