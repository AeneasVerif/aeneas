import Base
open Primitives Result

set_option maxHeartbeats 1000000

namespace Primitives

end Primitives

namespace Tutorial.Exercises

/- [tutorial::mul2_add1]:
   Source: 'src/lib.rs', lines 11:0-11:31 -/
def mul2_add1 (x : U32) : Result U32 :=
  do
  let i ← x + x
  i + 1#u32

#check U32.add_spec

/-- Theorem about `mul2_add1`: without the `progress` tactic -/
-- @[pspec]
theorem mul2_add1_spec (x : U32) (h : 2 * ↑x + 1 ≤ U32.max)
  : ∃ y, mul2_add1 x = ok y ∧
  ↑y = 2 * ↑x + (1 : Int)
  := by
  rw [mul2_add1]
  have ⟨ x1, hEq1, hPost1 ⟩ := @U32.add_spec x x (by scalar_tac)
  simp [hEq1]
  have ⟨ x2, hEq2, hPost2 ⟩ := @U32.add_spec x1 1#u32 (by scalar_tac)
  simp [hEq2]
  scalar_tac

/-- Theorem about `mul2_add1`: with the `progress` tactic -/
-- @[pspec]
theorem mul2_add1_spec' (x : U32) (h : 2 * ↑x + 1 ≤ U32.max)
  : ∃ y, mul2_add1 x = ok y ∧
  ↑y = 2 * ↑x + (1 : Int)
  := by
  rw [mul2_add1]
  progress with U32.add_spec as ⟨ i ⟩
  progress as ⟨ i' ⟩
  scalar_tac

/- [tutorial::mul2_add1_add]:
   Source: 'src/lib.rs', lines 15:0-15:43 -/
def mul2_add1_add (x : U32) (y : U32) : Result U32 :=
  do
  let i ← mul2_add1 x
  i + y

/-- Theorem about `mul2_add1_add` -/
theorem mul2_add1_add_spec (x : U32) (y : U32) (h : 2 * ↑x + 1 + ↑y ≤ U32.max) :
  ∃ z, mul2_add1_add x y = ok z ∧
  ↑z = 2 * ↑x + (1 : Int) + ↑y := by
  rw [mul2_add1_add]
  progress with mul2_add1_spec as ⟨ i ⟩
  progress as ⟨ i' ⟩
  scalar_tac

/- [tutorial::CList]
   Source: 'src/lib.rs', lines 32:0-32:17 -/
inductive CList (T : Type) :=
| CCons : T → CList T → CList T
| CNil : CList T

open CList

-- Convert a "custom" list to a standard Lean list
@[simp] def CList.to_list {α : Type} (x : CList α) : List α :=
  match x with
  | CNil => []
  | CCons hd tl => hd :: tl.to_list

/- [tutorial::list_nth]:
   Source: 'src/lib.rs', lines 37:0-37:56 -/
divergent def list_nth (T : Type) (l : CList T) (i : U32) : Result T :=
  match l with
  | CList.CCons x tl =>
    if i = 0#u32
    then Result.ok x
    else do
         let i1 ← i - 1#u32
         list_nth T tl i1
  | CList.CNil => Result.fail .panic

/-- Theorem about `list_nth` -/
theorem list_nth_spec {T : Type} [Inhabited T] (l : CList T) (i : U32)
  (h : i.val < l.to_list.length) :
  ∃ x, list_nth T l i = ok x ∧
  x = l.to_list.index i.toNat
  := by
  rw [list_nth]
  split
  . split
    . simp_all
    . simp_all
      progress as ⟨ i1 ⟩
      progress as ⟨ x ⟩
      simp_all
  . simp_all
    scalar_tac

/- [tutorial::i32_id]:
   Source: 'src/lib.rs', lines 78:0-78:29 -/
divergent def i32_id (i : I32) : Result I32 :=
  if i = 0#i32
  then Result.ok 0#i32
  else do
       let i1 ← i - 1#i32
       let i2 ← i32_id i1
       i2 + 1#i32

/-- Theorem about `i32_id` -/
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
decreasing_by
  simp_wf; scalar_tac
  -- Remark: `scalar_decr_tac` does the same

/- [tutorial::even]:
   Source: 'src/lib.rs', lines 87:0-87:28 -/
mutual divergent def even (i : U32) : Result Bool :=
  if i = 0#u32
  then Result.ok true
  else do
       let i1 ← i - 1#u32
       odd i1

/- [tutorial::odd]:
   Source: 'src/lib.rs', lines 96:0-96:27 -/
divergent def odd (i : U32) : Result Bool :=
  if i = 0#u32
  then Result.ok false
  else do
       let i1 ← i - 1#u32
       even i1

end

mutual

/-- The proof about `even` -/
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
decreasing_by scalar_decr_tac

/-- The proof about `odd` -/
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
decreasing_by scalar_decr_tac

end

/- [tutorial::list_nth_mut1]: loop 0:
   Source: 'src/lib.rs', lines 107:0-116:1 -/
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
   Source: 'src/lib.rs', lines 107:0-107:77 -/
@[reducible]
def list_nth_mut1
  (T : Type) (l : CList T) (i : U32) :
  Result (T × (T → Result (CList T)))
  :=
  list_nth_mut1_loop T l i

/-- Theorem about `list_nth_mut1` -/
theorem list_nth_mut1_spec {T: Type} [Inhabited T] (l : CList T) (i : U32)
  (h : i.val < l.to_list.length) :
  ∃ x back, list_nth_mut1 T l i = ok (x, back) ∧
  x = l.to_list.index i.toNat ∧
  ∀ x', ∃ l', back x' = ok l' ∧ l'.to_list = l.to_list.update i.toNat x' := by
  rw [list_nth_mut1, list_nth_mut1_loop]
  split
  . split
    . simp
      split_conjs
      . simp_all
      . intro x
        simp_all
    . simp_all
      progress as ⟨ i1 ⟩
      progress as ⟨ tl1, back ⟩
      simp
      split_conjs
      . simp_all
      . -- Backward function
        intro x'
        progress as ⟨ tl2 ⟩
        simp_all
  . simp_all
    scalar_tac

/- [tutorial::list_tail]: loop 0:
   Source: 'src/lib.rs', lines 118:0-123:1 -/
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
   Source: 'src/lib.rs', lines 118:0-118:68 -/
@[reducible]
def list_tail
  (T : Type) (l : CList T) :
  Result ((CList T) × (CList T → Result (CList T)))
  :=
  list_tail_loop T l

/- [tutorial::append_in_place]:
   Source: 'src/lib.rs', lines 125:0-125:67 -/
def append_in_place
  (T : Type) (l0 : CList T) (l1 : CList T) : Result (CList T) :=
  do
  let (_, list_tail_back) ← list_tail T l0
  list_tail_back l1

/-- Theorem about `list_tail` -/
@[pspec]
theorem list_tail_spec {T : Type} (l : CList T) :
  ∃ back, list_tail T l = ok (CList.CNil, back) ∧
  ∀ tl', ∃ l', back tl' = ok l' ∧ l'.to_list = l.to_list ++ tl'.to_list := by
  rw [list_tail, list_tail_loop]
  split
  . simp_all
    progress as ⟨ back ⟩
    simp
    -- Proving the backward function
    intro tl'
    progress
    simp_all
  . simp_all

/-- Theorem about `append_in_place` -/
@[pspec]
theorem append_in_place_spec {T : Type} (l0 l1 : CList T) :
  ∃ l2, append_in_place T l0 l1 = ok l2 ∧
  l2.to_list = l0.to_list ++ l1.to_list := by
  rw [append_in_place]
  progress as ⟨ tl, back ⟩
  progress as ⟨ l2 ⟩
  simp_all


/- Big numbers -/

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


-- Auxiliary definitions to interpret a vector of u32 as a mathematical integer
@[simp]
def toInt_aux (l : List U32) : ℤ :=
  match l with
  | [] => 0
  | x :: l =>
    x + 2 ^ 32 * toInt_aux l

@[reducible]
def toInt (x : alloc.vec.Vec U32) : ℤ := toInt_aux x.val

-- TODO: have := lemma x (by tactic)
/-- The theorem about `zero_loop` -/
@[pspec]
theorem zero_loop_spec
  (x : alloc.vec.Vec U32) (i : Usize) (h : i.val ≤ x.length) :
  ∃ x',
    zero_loop x i = ok x' ∧
    x'.length = x.length ∧
    (∀ j, j < i.toNat → x'.val.index j = x.val.index j) ∧
    (∀ j, i.toNat ≤ j → j < x.length → x'.val.index j = 0#u32) := by
  rw [zero_loop]
  simp
  split
  . progress as ⟨ _ ⟩
    progress as ⟨ i1 ⟩
    progress as ⟨ x1 ⟩
    progress as ⟨ x2, _, hSame, hZero ⟩
    simp_all
    split_conjs
    . intro j h0
      replace hSame := hSame j (by scalar_tac)
      simp_all
    . intro j h0 h1
      dcases j = i.toNat <;> simp_all
      have := hZero j (by scalar_tac)
      simp_all
  . simp; scalar_tac
termination_by (x.length - i.val).toNat
decreasing_by scalar_decr_tac

/- [tutorial::zero]:
   Source: 'src/lib.rs', lines 5:0-5:28 -/
def zero (x : alloc.vec.Vec U32) : Result (alloc.vec.Vec U32) :=
  zero_loop x 0#usize

/-- You will need this lemma for the proof of `zero_spec`

    Advice: do the proof of `zero_spec` first, then come back to prove this lemma.
-/
theorem all_nil_impl_toInt_eq_zero
  (l : List U32) (h : ∀ (j : ℕ), j < l.length → l.index j = 0#u32) :
  toInt_aux l = 0 := by
  match l with
  | [] => simp
  | hd :: tl =>
    have h1 := h 0
    simp at *
    simp [*]
    apply all_nil_impl_toInt_eq_zero
    intro j h2
    have := h (j + 1) (by simp [*])
    simp at this
    simp_all

/-- The theorem about `zero` -/
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

/-- You will need this lemma for the proof of `add_no_overflow_loop_spec`.

    Advice: do the proof of `add_no_overflow_loop_spec` first, then come back to prove this lemma.
 -/
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

/-- You will need this lemma for the proof of `add_no_overflow_loop_spec`.

    Advice: do the proof of `add_no_overflow_loop_spec` first, then come back to prove this lemma.
 -/
@[simp]
theorem toInt_aux_update (l : List U32) (i : Nat) (x : U32) (h0 : i < l.length) :
  toInt_aux (l.update i x) = toInt_aux l + 2 ^ (32 * i) * (x - l.index i) := by
  cases l with
  | nil => simp at *
  | cons hd tl =>
    simp_all
    dcases i = 0 <;> simp_all
    . scalar_eq_nf
    . have := toInt_aux_update tl (i - 1) x (by scalar_tac)
      simp_all
      scalar_nf at *
      scalar_eq_nf
      /- Note that we coerce the righ-hand side (also works with the left-hand side) so that
         it gets interpreted as an ℤ and not a ℕ. It is important: `(2 : ℕ) ^ ...` is not (at all)
         the same as `2 : ℤ`.
       -/
      have : 2 ^ (i * 32) = (2 ^ ((i - 1) * 32) * 4294967296 : Int) := by
        scalar_nf
        have : i = i - 1 + 1 := by scalar_tac
        /- This is slightly technical: we use a "conversion" to apply the rewriting only
           to the left-hand-side of the goal. Also note that we're using `rw` instead of
           `simp` otherwise the rewriting will be applied indefinitely (we can apply `i = i - 1 + 1``
           to `i - 1 + 1`, etc.).

           If you don't want to go into too many technicalities, you can also do:
           ```
           have : i * 32 = (i - 1) * 32 + 32 := by scalar_tac
           simp [*]
           ```
         -/
        conv => lhs; rw [this]
        scalar_nf
      simp [mul_assoc, *]
      scalar_eq_nf

/-- You will need this lemma for the proof of `add_no_overflow_loop_spec`.

    Advice: do the proof of `add_no_overflow_loop_spec` first, then come back to prove this lemma.
 -/
@[simp]
theorem toInt_aux_drop (l : List U32) (i : Nat) (h0 : i < l.length) :
  toInt_aux (l.drop i) = l.index i + 2 ^ 32 * toInt_aux (l.drop (i + 1)) := by
  cases l with
  | nil => simp at *
  | cons hd tl =>
    simp_all
    dcases i = 0 <;> simp_all
    have := toInt_aux_drop tl (i - 1) (by scalar_tac)
    simp_all
    scalar_nf at *
    have : 1 + (i - 1) = i := by scalar_tac
    simp [*]

/-- The proof about `add_no_overflow_loop` -/
@[pspec]
theorem add_no_overflow_loop_spec
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) (i : Usize)
  (hLength : x.length = y.length)
  -- No overflow occurs when we add the individual thunks
  (hNoOverflow : ∀ (j : Nat), i.toNat ≤ j → j < x.length → (x.val.index j).val + (y.val.index j).val ≤ U32.max)
  (hi : i.val ≤ x.length) :
  ∃ x', add_no_overflow_loop x y i = ok x' ∧
  x'.length = x.length ∧
  toInt x' = toInt x + 2 ^ (32 * i.toNat) * toInt_aux (y.val.drop i.toNat) := by
  rw [add_no_overflow_loop]
  simp
  split
  . progress as ⟨ yv ⟩
    progress as ⟨ xv ⟩
    progress as ⟨ sum ⟩
    . have := hNoOverflow i.toNat (by scalar_tac) (by scalar_tac)
      scalar_tac
    . progress as ⟨ i' ⟩
      progress as ⟨ x1 ⟩
      progress as ⟨ x2 ⟩
      . -- This precondition is not proven automatically
        intro j h0 h1
        simp_all
        -- Simplifying (x.update ...).index:
        have := List.index_update_neq x.val i.toNat j sum (by scalar_tac)
        simp [*]
        apply hNoOverflow j (by scalar_tac) (by scalar_tac)
      . -- Postcondition
        /- Note that you don't have to manually call the lemmas `toInt_aux_update`
           and `toInt_aux_drop` below if you first do:
           ```
           have : i.toNat < x.length := by scalar_tac
           ```
           (simp_all will automatically apply the lemmas and prove the
            the precondition sby using the context)
         -/
        simp_all [toInt]
        scalar_eq_nf
        -- Simplifying: toInt_aux ((↑x).update (↑i).toNat sum)
        have := toInt_aux_update x.val i.toNat sum (by scalar_tac)
        simp [*]; scalar_eq_nf
        -- Simplifying: toInt_aux (List.drop (1 + (↑i).toNat) ↑y
        have := toInt_aux_drop y.val i.toNat (by scalar_tac)
        simp [*]; scalar_eq_nf
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

/-- The proof about `add_no_overflow` -/
theorem add_no_overflow_spec (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32)
  (hLength : x.length = y.length)
  (hNoOverflow : ∀ (j : Nat), j < x.length → (x.val.index j).val + (y.val.index j).val ≤ U32.max) :
  ∃ x', add_no_overflow x y = ok x' ∧
  x'.length = y.length ∧
  toInt x' = toInt x + toInt y := by
  rw [add_no_overflow]
  progress as ⟨ x' ⟩ <;>
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

/-- The proof about `add_with_carry_loop` -/
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
    toInt x + 2 ^ (32 * i.toNat) * toInt_aux (y.val.drop i.toNat) + c0.val * 2 ^ (32 * i.toNat) := by
  rw [add_with_carry_loop]
  simp
  split
  . progress as ⟨ xi ⟩
    progress as ⟨ c0u ⟩
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
      have hxUpdate := toInt_aux_update x.val i.toNat s2 (by scalar_tac)
      simp [hxUpdate]; clear hxUpdate
      have hyDrop := toInt_aux_drop y.val i.toNat (by scalar_tac)
      simp [hyDrop]; clear hyDrop
      scalar_eq_nf
      split at hConv1 <;>
      split at hConv2 <;>
      simp_all <;>
      scalar_eq_nf <;> simp [U32.max] <;> scalar_eq_nf
  . simp_all
termination_by (x.length - i.val).toNat
decreasing_by scalar_decr_tac

/- [tutorial::add_with_carry]:
   Source: 'src/lib.rs', lines 37:0-37:55 -/
def add_with_carry
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) :
  Result (U8 × (alloc.vec.Vec U32))
  :=
  add_with_carry_loop x y 0#u8 0#usize

/-- The proof about `add_with_carry` -/
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

/- Bonus exercises -/

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

end Tutorial.Exercises
