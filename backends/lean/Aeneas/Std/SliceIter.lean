/- Arrays/Slices -/
import Aeneas.Std.Slice
import Aeneas.Std.Core.Iter

namespace Aeneas.Std

open Result Error core.ops.range WP

attribute [-simp] List.getElem!_eq_getElem?_getD


@[rust_type "core::slice::iter::Iter"]
structure core.slice.iter.Iter (T : Type) where
  /- We need to remember the slice and an index inside the slice (this is necessary)
     for double ended iterators) -/
  slice : Slice T
  i : Nat

@[rust_type "core::slice::iter::IterMut" (mutRegions := #[0]) (body := .opaque)]
structure core.slice.iter.IterMut (T : Type) where
  /- We need to remember the slice and an index inside the slice (this is necessary)
     for double ended iterators) -/
  slice : Slice T
  i : Nat := 0

@[rust_fun "core::slice::{[@T]}::iter"]
def core.slice.Slice.iter {T : Type} (s : Slice T) : Result (core.slice.iter.Iter T) :=
  ok ⟨ s, 0 ⟩

@[rust_fun "core::slice::{[@T]}::contains"]
def core.slice.Slice.contains {T : Type} (partialEqInst : core.cmp.PartialEq T T)
  (s : Slice T) (x : T) : Result Bool :=
  List.anyM (partialEqInst.eq x) s.val

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::IterMut<'a, @T>, &'a mut @T>}::next"]
def core.slice.iter.IteratorIterMut.next
  {T : Type}
  (it : core.slice.iter.IterMut T) :
  Result ((Option T) × (core.slice.iter.IterMut T) ×
          (core.slice.iter.IterMut T → Option T → core.slice.iter.IterMut T)) :=
  if h: it.i < it.slice.len then
    let x := it.slice[it.i]
    let i := it.i
    let it := { it with i := i + 1 }
    let back it' x :=
      match x with
      | none => it'
      | some x => { it' with slice := it'.slice.setAtNat i x }
    ok (some x, it, back)
  else ok (none, it, fun it _ => it)

@[rust_fun "core::slice::{[@T]}::iter_mut"]
def core.slice.Slice.iter_mut {T : Type} (slice : Slice T) :
  Result ((core.slice.iter.IterMut T) × (core.slice.iter.IterMut T → Slice T)) :=
  ok ({slice}, fun it => it.slice)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::next"]
def core.slice.iter.IteratorSliceIter.next
  {T : Type} (it : core.slice.iter.Iter T) : Result ((Option T) × (core.slice.iter.Iter T)) :=
  if h : it.i < it.slice.len then
    let x := it.slice[it.i]
    let it := { it with i := it.i + 1}
    ok (some x, it)
  else ok (none, it)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::step_by"]
def core.slice.iter.IteratorSliceIter.step_by {T} (slice : core.slice.iter.Iter T) (steps : Usize) :
  Result (core.iter.adapters.step_by.StepBy (core.slice.iter.Iter T)) :=
  if steps.val = 0 then .fail .panic
  else ok (⟨ slice, steps ⟩)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::enumerate"]
def core.slice.iter.IteratorSliceIter.enumerate {T} (slice : core.slice.iter.Iter T) :
  Result (core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter T)) :=
  .ok { iter := slice, count := 0#usize }

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::take"]
def core.slice.iter.IteratorSliceIter.take {T} (slice : core.slice.iter.Iter T) (n : Usize) :
  Result (core.iter.adapters.take.Take (core.slice.iter.Iter T)) :=
  ok ⟨ slice, n ⟩

@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>"]
def core.iter.traits.iterator.IteratorSliceIter (T : Type) :
  core.iter.traits.iterator.Iterator (core.slice.iter.Iter T) T := {
  next := core.slice.iter.IteratorSliceIter.next
  step_by := core.slice.iter.IteratorSliceIter.step_by
  enumerate := core.slice.iter.IteratorSliceIter.enumerate
  take := core.slice.iter.IteratorSliceIter.take
}

@[rust_type "core::slice::iter::ChunksExact" (body := .opaque)]
structure core.slice.iter.ChunksExact (T : Type) where
  chunks : List (Slice T)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, @T>, &'a [@T]>}::next"]
def core.slice.iter.IteratorChunksExact.next
  {T : Type} (self : core.slice.iter.ChunksExact T) :
  Result ((Option (Slice T)) × (core.slice.iter.ChunksExact T)) :=
  match self.chunks with
  | [] => ok (none, self)
  | chunk :: chunks => ok (some chunk, { chunks })

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, @T>, &'a [@T]>}::step_by"]
def core.slice.iter.IteratorChunksExact.step_by
  {T : Type} (self : slice.iter.ChunksExact T) (steps : Usize) :
  Result (core.iter.adapters.step_by.StepBy (slice.iter.ChunksExact T)) :=
  if steps.val = 0 then .fail .panic
  else ok (⟨ self, steps ⟩)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, @T>, &'a [@T]>}::enumerate"]
def core.slice.iter.IteratorChunksExact.enumerate {T : Type} (self : core.slice.iter.ChunksExact T) :
  Result (core.iter.adapters.enumerate.Enumerate (core.slice.iter.ChunksExact T)) :=
  .ok { iter := self, count := 0#usize }

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, @T>, &'a [@T]>}::take"]
def core.slice.iter.IteratorChunksExact.take {T : Type} (self : core.slice.iter.ChunksExact T) (n : Usize) :
  Result (core.iter.adapters.take.Take (core.slice.iter.ChunksExact T)) :=
  ok ⟨ self, n ⟩

@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, @T>, &'a [@T]>"]
def core.iter.traits.iterator.IteratorChunksExact (T : Type) :
  core.iter.traits.iterator.Iterator (core.slice.iter.ChunksExact T) (Slice T)
  := {
  next := core.slice.iter.IteratorChunksExact.next
  step_by := core.slice.iter.IteratorChunksExact.step_by
  enumerate := core.slice.iter.IteratorChunksExact.enumerate
  take := core.slice.iter.IteratorChunksExact.take
}

@[rust_fun "core::slice::{[@T]}::chunks_exact"]
def core.slice.Slice.chunks_exact {T : Type} (s : Slice T) (chunk_size : Std.Usize) :
  Result (core.slice.iter.ChunksExact T) :=
  if chunk_size.val > 0 && s.len % chunk_size.val = 0 then
    ok ⟨ List.map (fun s => ⟨ s, by sorry ⟩) (s.val.toChunks chunk_size.val) ⟩
  else fail .panic


-- ============================================================================
-- StepBy tests
-- ============================================================================

private def mkSliceIter (l : List Nat) (h : l.length ≤ Usize.max := by scalar_tac) :
    core.slice.iter.Iter Nat :=
  { slice := ⟨l, h⟩, i := 0 }

private def collectStepBy (sbi : core.iter.adapters.step_by.StepBy (core.slice.iter.Iter Nat))
    (fuel : Nat := 100) : Result (List Nat) :=
  match fuel with
  | 0 => .ok []
  | fuel + 1 => do
    let (opt, sbi) ←
      core.iter.adapters.step_by.IteratorStepBy.next
        (core.iter.traits.iterator.IteratorSliceIter Nat) sbi
    match opt with
    | none => .ok []
    | some x => do
      let rest ← collectStepBy sbi fuel
      .ok (x :: rest)

-- step_by(0) panics
#assert
  match core.slice.iter.IteratorSliceIter.step_by (mkSliceIter [1, 2, 3]) 0#usize with
  | .fail .panic => true
  | _ => false

-- step_by(1) returns all elements
#assert (do
  let sbi ← core.slice.iter.IteratorSliceIter.step_by (mkSliceIter [0, 1, 2, 3, 4]) 1#usize
  collectStepBy sbi) == .ok [0, 1, 2, 3, 4]

-- step_by(2) returns every other element
#assert (do
  let sbi ← core.slice.iter.IteratorSliceIter.step_by (mkSliceIter [0, 1, 2, 3, 4]) 2#usize
  collectStepBy sbi) == .ok [0, 2, 4]

-- step_by(3)
#assert (do
  let sbi ← core.slice.iter.IteratorSliceIter.step_by (mkSliceIter [0, 1, 2, 3, 4, 5, 6]) 3#usize
  collectStepBy sbi) == .ok [0, 3, 6]

-- step_by larger than collection: returns only first element
#assert (do
  let sbi ← core.slice.iter.IteratorSliceIter.step_by (mkSliceIter [0, 1, 2]) 10#usize
  collectStepBy sbi) == .ok [0]

-- step_by on empty iterator
#assert (do
  let sbi ← core.slice.iter.IteratorSliceIter.step_by (mkSliceIter []) 2#usize
  collectStepBy sbi) == .ok []

-- step_by(1) on single element
#assert (do
  let sbi ← core.slice.iter.IteratorSliceIter.step_by (mkSliceIter [42]) 1#usize
  collectStepBy sbi) == .ok [42]

-- step_by(2) on single element
#assert (do
  let sbi ← core.slice.iter.IteratorSliceIter.step_by (mkSliceIter [42]) 2#usize
  collectStepBy sbi) == .ok [42]

-- step_by equal to length: returns only first element
#assert (do
  let sbi ← core.slice.iter.IteratorSliceIter.step_by (mkSliceIter [0, 1, 2]) 3#usize
  collectStepBy sbi) == .ok [0]

-- step_by = length - 1
#assert (do
  let sbi ← core.slice.iter.IteratorSliceIter.step_by (mkSliceIter [0, 1, 2]) 2#usize
  collectStepBy sbi) == .ok [0, 2]

-- step_by(2) on two elements: returns only first
#assert (do
  let sbi ← core.slice.iter.IteratorSliceIter.step_by (mkSliceIter [0, 1]) 2#usize
  collectStepBy sbi) == .ok [0]

-- step_by(2) on three elements: returns first and third
#assert (do
  let sbi ← core.slice.iter.IteratorSliceIter.step_by (mkSliceIter [0, 1, 2]) 2#usize
  collectStepBy sbi) == .ok [0, 2]

-- step_by(4) on longer sequence
#assert (do
  let sbi ← core.slice.iter.IteratorSliceIter.step_by
    (mkSliceIter [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]) 4#usize
  collectStepBy sbi) == .ok [0, 4, 8]

-- Verify that step_by(0) on the generic Iterator.step_by.default also panics
#assert
  match core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter [1]) 0#usize with
  | .fail .panic => true
  | _ => false

-- Nested step_by: step_by(2) then step_by(2) on [0..8] gives [0, 4]
private def collectNestedStepBy
    (sbi : core.iter.adapters.step_by.StepBy
      (core.iter.adapters.step_by.StepBy (core.slice.iter.Iter Nat)))
    (fuel : Nat := 100) : Result (List Nat) :=
  match fuel with
  | 0 => .ok []
  | fuel + 1 => do
    let (opt, sbi) ←
      (core.iter.traits.iterator.IteratorStepBy
        (core.iter.traits.iterator.IteratorStepBy
          (core.iter.traits.iterator.IteratorSliceIter Nat))).next sbi
    match opt with
    | none => .ok []
    | some x => do
      let rest ← collectNestedStepBy sbi fuel
      .ok (x :: rest)

#assert (do
  let sbi ← core.slice.iter.IteratorSliceIter.step_by
    (mkSliceIter [0, 1, 2, 3, 4, 5, 6, 7]) 2#usize
  let sbi2 ← core.iter.adapters.step_by.IteratorStepBy.step_by
    (core.iter.traits.iterator.IteratorSliceIter Nat) sbi 2#usize
  collectNestedStepBy sbi2) == .ok [0, 4]

/-! ## Slice iterator loop ↔ `List.foldl`

Aeneas translates `for b in slice { state = action(state, b); }` into a
`loop` that calls `IteratorSliceIter.next` and threads `state` through.
The lemma `slice_iter_loop_eq_foldl` collapses such a loop to a pure
`slice.val.foldl f init`, given a per-element spec for `action`. -/

theorem slice_iter_loop_eq_foldl
    {T α : Type} [Inhabited α]
    (slice₀ : Slice T) (init : α) (f : α → T → α)
    (action : T → α → Result α)
    (haction : ∀ b s, action b s ⦃ s' => s' = f s b ⦄) :
    loop (fun (p : core.slice.iter.Iter T × α) =>
      do let (o, it') ← core.slice.iter.IteratorSliceIter.next p.1
         match o with
         | none => ok (.done p.2)
         | some b => do let st' ← action b p.2; ok (.cont (it', st')))
      (({ slice := slice₀, i := 0 } : core.slice.iter.Iter T), init)
    ⦃ result => result = slice₀.val.foldl f init ⦄ := by
  apply loop.spec_decr_nat
    (measure := fun (p : core.slice.iter.Iter T × α) =>
      slice₀.val.length + 1 - p.1.i)
    (inv := fun (p : core.slice.iter.Iter T × α) =>
      p.1.slice = slice₀ ∧ p.1.i ≤ slice₀.val.length ∧
      p.2 = (slice₀.val.take p.1.i).foldl f init)
  · rintro ⟨it, st⟩ ⟨hslice, hi, hst⟩
    simp only at hslice hi hst
    simp only [core.slice.iter.IteratorSliceIter.next]
    by_cases hlt : it.i < it.slice.len.val
    · have hlt' : it.i < slice₀.val.length := by
        have : it.slice.len.val = slice₀.val.length := by rw [hslice]; simp
        omega
      have hslice_get : it.slice[it.i] = slice₀.val[it.i]'hlt' := by
        subst hslice; rfl
      simp only [hlt, ↓reduceDIte, bind_tc_ok, hslice_get]
      apply spec_bind (haction (slice₀.val[it.i]'hlt') st)
      intro st' hst'
      simp only [spec_ok]
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · exact hslice
      · simp; omega
      · rw [hst', hst]
        have htake : slice₀.val.take (it.i + 1) =
                     slice₀.val.take it.i ++ [slice₀.val[it.i]'hlt'] := by
          rw [List.take_add_one]
          simp [List.getElem?_eq_getElem hlt']
        rw [htake, List.foldl_append]
        simp
      · simp; omega
    · have hlen : it.slice.len.val = slice₀.val.length := by rw [hslice]; simp
      have hge : it.i ≥ slice₀.val.length := by omega
      simp only [hlt, ↓reduceDIte, bind_tc_ok, spec_ok]
      rw [hst, List.take_of_length_le (by omega)]
  · refine ⟨rfl, ?_, ?_⟩
    · simp
    · simp

end Aeneas.Std
