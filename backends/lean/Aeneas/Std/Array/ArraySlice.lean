import Aeneas.Std.Array.Array
import Aeneas.Std.Slice
import Aeneas.Std.Range

/-! Array definitions which mention slices -/

namespace Aeneas.Std

open Result Error core.ops.range

attribute [-simp] List.getElem!_eq_getElem?_getD

/-! Array to slice/subslices -/

@[progress_pure_def]
def Array.to_slice {α : Type u} {n : Usize} (v : Array α n) : Slice α :=
  ⟨ v.val, by scalar_tac ⟩

def Array.from_slice {α : Type u} {n : Usize} (a : Array α n) (s : Slice α) : Array α n :=
  if h: s.val.length = n.val then
    ⟨ s.val, by simp [*] ⟩
  else a -- Unreachable case

@[simp]
theorem Array.from_slice_val {α : Type u} {n : Usize} (a : Array α n) (ns : Slice α) (h : ns.val.length = n.val) :
  (from_slice a ns).val = ns.val
  := by simp [from_slice, *]

@[progress_pure_def]
def Array.to_slice_mut {α : Type u} {n : Usize} (a : Array α n) :
  Slice α × (Slice α → Array α n) :=
  (Array.to_slice a, Array.from_slice a)

def Array.subslice {α : Type u} {n : Usize} (a : Array α n) (r : Range Usize) : Result (Slice α) :=
  -- TODO: not completely sure here
  if r.start.val < r.end_.val ∧ r.end_.val ≤ a.val.length then
    ok ⟨ a.val.slice r.start.val r.end_.val,
          by
            have := a.val.slice_length_le r.start.val r.end_.val
            scalar_tac ⟩
  else
    fail panic

@[progress]
theorem Array.subslice_spec {α : Type u} {n : Usize} [Inhabited α] (a : Array α n) (r : Range Usize)
  (h0 : r.start.val < r.end_.val) (h1 : r.end_.val ≤ a.val.length) :
  ∃ s, subslice a r = ok s ∧
  s.val = a.val.slice r.start.val r.end_.val ∧
  (∀ i, i + r.start.val < r.end_.val → s.val[i]! = a.val[r.start.val + i]!)
  := by
  simp only [subslice, true_and, h0, h1, ↓reduceIte, ok.injEq, exists_eq_left', true_and]
  intro i _
  have := List.getElem!_slice r.start.val r.end_.val i a.val (by scalar_tac)
  simp only [this]


def Array.update_subslice {α : Type u} {n : Usize} (a : Array α n) (r : Range Usize) (s : Slice α) : Result (Array α n) :=
  -- TODO: not completely sure here
  if h: r.start.val < r.end_.val ∧ r.end_.val ≤ a.length ∧ s.val.length = r.end_.val - r.start.val then
    ok ⟨ a.val.setSlice! r.start s.val, by scalar_tac ⟩
  else
    fail panic

-- TODO: it is annoying to write `.val` everywhere. We could leverage coercions,
-- but: some symbols like `+` are already overloaded to be notations for monadic
-- operations/
-- We should introduce special symbols for the monadic arithmetic operations
-- (the user will never write those symbols directly).
@[progress]
theorem Array.update_subslice_spec {α : Type u} {n : Usize} [Inhabited α] (a : Array α n) (r : Range Usize) (s : Slice α)
  (_ : r.start.val < r.end_.val) (_ : r.end_.val ≤ a.length) (_ : s.length = r.end_.val - r.start.val) :
  ∃ na, update_subslice a r s = ok na ∧
  (∀ i, i < r.start.val → na[i]! = a[i]!) ∧
  (∀ i, r.start.val ≤ i → i < r.end_.val → na[i]! = s[i - r.start.val]!) ∧
  (∀ i, r.end_.val ≤ i → i < n.val → na[i]! = a[i]!) := by
  simp [update_subslice]
  split <;> simp only [reduceCtorEq, false_and, exists_false, ok.injEq, exists_eq_left']
  . simp_lists
  . scalar_tac

/- [core::array::[T; N]::index]: forward function -/
def core.array.Array.index
  {T I Output : Type} {N : Usize} (inst : core.ops.index.Index (Slice T) I Output)
  (a : Array T N) (i : I) : Result Output :=
  inst.index a.to_slice i

/- [core::array::[T; N]::index_mut]: forward function -/
def core.array.Array.index_mut
  {T I Output : Type} {N : Usize} (inst : core.ops.index.IndexMut (Slice T) I Output)
  (a : Array T N) (i : I) :
  Result (Output × (Output → Array T N)) := do
  let (s, back) ← inst.index_mut a.to_slice i
  ok (s, fun o => Array.from_slice a (back o))

/- Trait implementation: [core::array::[T; N]] -/
def core.ops.index.IndexArrayInst {T I Output : Type} {N : Usize}
  (inst : core.ops.index.Index (Slice T) I Output) :
  core.ops.index.Index (Array T N) I Output := {
  index := core.array.Array.index inst
}

/- Trait implementation: [core::array::[T; N]] -/
def core.ops.index.IndexMutArrayInst {T I Output : Type} {N : Usize}
  (inst : core.ops.index.IndexMut (Slice T) I Output) :
  core.ops.index.IndexMut (Array T N) I Output := {
  indexInst := core.ops.index.IndexArrayInst inst.indexInst
  index_mut := core.array.Array.index_mut inst
}

/- [core::array::TryFromSliceError] -/
def core.array.TryFromSliceError := ()

end Aeneas.Std
