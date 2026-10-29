module

public import Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Model

@[expose] public section

namespace Aeneas.Std

universe u v

namespace Block

theorem view_depth {ty : Type u} {r : Std.Block.{u}} {i : Nat} {c : Cell ty}
    (hv : Std.Block.view ty r i c) {b : Nat}
    (hlo : i * Heap.size ty ≤ b) (hhi : b < (i + 1) * Heap.size ty) :
    ((Std.Block.bytes r)[b]?).map Cell.depth = some c.depth := by
  obtain ⟨byte, hb, hd, _⟩ := Std.Block.view_bytes _ _ _ _ hv b hlo hhi
  rw [hb]
  exact congrArg some hd

theorem view_borrowed_byte {ty : Type u} {r : Std.Block.{u}} {i b : Nat}
    (hv : Std.Block.view ty r i .borrowed)
    (hlo : i * Heap.size ty ≤ b) (hhi : b < (i + 1) * Heap.size ty) :
    (Std.Block.bytes r)[b]? = some .borrowed := by
  obtain ⟨byte, hb, hd, _⟩ := Std.Block.view_bytes _ _ _ _ hv b hlo hhi
  cases byte
  · simp at hd
  · exact hb

theorem align_pos (ty : Type u) : 0 < (Heap.align ty).val := by
  obtain ⟨k, hk⟩ := (Heap.align ty).property
  rw [hk]
  exact Nat.two_pow_pos k

theorem aligned_stride (ty : Type u) (i : Nat) :
    (Heap.align ty).val ∣ i * Heap.size ty := by
  obtain ⟨n, hn⟩ := Heap.size_aligned ty
  exact ⟨i * n, by rw [hn, Nat.mul_left_comm]⟩

theorem Views.bound {ty : Type u} {r : Std.Block.{u}} {start : Nat} {cs : List (Cell ty)}
    (h : Std.Block.Views ty r start cs) (hne : cs ≠ []) :
    start + cs.length ≤ Std.Block.extent ty r := by
  have hp := List.length_pos_iff.mpr hne
  have hi : cs.length - 1 < cs.length := by grind
  have hb := Std.Block.view_bound ty r _ _ (h _ hi)
  grind

theorem Views.unique {ty : Type u} {r : Std.Block.{u}} {start : Nat}
    {a b : List (Cell ty)} (ha : Std.Block.Views ty r start a) (hb : Std.Block.Views ty r start b)
    (hl : a.length = b.length) : a = b := by
  apply List.ext_getElem hl
  intro i hi hi'
  exact Std.Block.view_unique ty r _ _ _ (ha i hi) (hb i hi')

theorem Updates.extent {ty : Type u} {start : Nat} {cs : List (Cell ty)}
    {r r' : Std.Block.{u}} (h : Std.Block.Updates ty start cs r r') (U : Type u) :
    Std.Block.extent U r' = Std.Block.extent U r := by
  induction h
  · rfl
  · rename_i hs ht ih
    exact ih.trans (Std.Block.set_extent _ _ _ _ _ hs U)

theorem Updates.bytes_length {ty : Type u} {start : Nat} {cs : List (Cell ty)}
    {r r' : Std.Block.{u}} (h : Std.Block.Updates ty start cs r r') :
    (Std.Block.bytes r').length = (Std.Block.bytes r).length := by
  induction h
  · rfl
  · rename_i hs ht ih
    exact ih.trans (Std.Block.set_bytes_length _ _ _ _ _ hs)

theorem Updates.frame {ty U : Type u} {start j : Nat} {cs : List (Cell ty)}
    {r r' : Std.Block.{u}} (h : Std.Block.Updates ty start cs r r')
    (hd : ∀ i, i < cs.length → CellsDisjoint ty (start + i) U j)
    (value : Cell U) : Std.Block.view U r' j value ↔ Std.Block.view U r j value := by
  induction h
  · rfl
  · rename_i i c cs r r₁ r₂ hs ht ih
    have hhead := hd 0 (by simp)
    have htail : ∀ k, k < cs.length →
        CellsDisjoint ty (i + 1 + k) U j := by
      intro k hk
      simpa [Nat.add_assoc, Nat.add_comm 1 k] using hd (k + 1) (by simp; grind)
    exact (ih htail).trans (Std.Block.set_frame _ _ _ _ _ hs U j (by simpa using hhead) value)

theorem Updates.outside {ty : Type u} {start j : Nat} {cs : List (Cell ty)}
    {r r' : Std.Block.{u}} (h : Std.Block.Updates ty start cs r r')
    (hout : j < start ∨ start + cs.length ≤ j) (value : Cell ty) :
    Std.Block.view ty r' j value ↔ Std.Block.view ty r j value := by
  apply h.frame
  intro i hi
  exact Std.Block.disjoint_same ty (by grind)

theorem Updates.views {ty : Type u} {start : Nat} {cs : List (Cell ty)}
    {r r' : Std.Block.{u}} (h : Std.Block.Updates ty start cs r r') : Std.Block.Views ty r' start cs := by
  induction h
  · intro i hi
    simp at hi
  · rename_i i c cs r r₁ r₂ hs ht ih
    intro j hj
    cases j
    · simpa using (ht.outside (Or.inl (Nat.lt_succ_self i)) c).mpr
        (Std.Block.set_view _ _ _ _ _ hs)
    · rename_i j
      have hj' : j < cs.length := by simpa using hj
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using ih j hj'

theorem Updates.exists (ty : Type u) (start : Nat) (cs : List (Cell ty)) (r : Std.Block.{u})
    (hb : start + cs.length ≤ Std.Block.extent ty r) :
    ∃ r', Std.Block.Updates ty start cs r r' := by
  induction cs generalizing start r
  · exact ⟨r, .nil start r⟩
  · rename_i c cs ih
    have hi : start < Std.Block.extent ty r := by simp only [List.length_cons] at hb; grind
    obtain ⟨r₁, hs⟩ := Std.Block.set_exists ty start r hi c
    have hb' : start + 1 + cs.length ≤ Std.Block.extent ty r₁ := by
      rw [Std.Block.set_extent _ _ _ _ _ hs ty]
      simp only [List.length_cons] at hb
      grind
    obtain ⟨r₂, ht⟩ := ih (start + 1) r₁ hb'
    exact ⟨r₂, .cons hs ht⟩

end Block

namespace Heap

variable {Block : Type v} theorem inv_empty : (empty : Heap Block).Inv := fun _ _ => rfl

@[simp] theorem cells_storeRepr (s : Heap Block) (base other : BasePtr) (r : Block) :
    (s.storeRepr base r).cells other =
      if other = base then (s.cells base).map (fun _ => r) else s.cells other := by
  by_cases h : other = base
  · subst other
    simp [storeRepr, cells, update, Option.map_map, Function.comp_def]
  · simp [storeRepr, cells, update, h]

@[simp] theorem cells_remove (s : Heap Block) (base other : BasePtr) :
    (s.remove base).cells other = if other = base then none else s.cells other := by
  by_cases h : other = base
  · simp [remove, cells, update, h]
  · simp [remove, cells, update, h]

@[simp] theorem cells_createRepr (s : Heap Block) (r : Block) (own : Bool)
    (a : Alignment) (base : BasePtr) :
    (s.createRepr r own a).cells base = if base = s.next then some r else s.cells base := by
  by_cases h : base = s.next
  · simp [createRepr, cells, update, h]
  · simp [createRepr, cells, update, h]

@[simp] theorem allocated_storeRepr (s : Heap Block) (base other : BasePtr) (r : Block) :
    (s.storeRepr base r).allocated other = s.allocated other := by
  by_cases h : other = base
  · subst other
    simp [storeRepr, allocated, update, Option.map_map, Function.comp_def]
  · simp [storeRepr, allocated, update, h]

@[simp] theorem alignment_storeRepr (s : Heap Block) (base other : BasePtr) (r : Block) :
    (s.storeRepr base r).alignment other = s.alignment other := by
  by_cases h : other = base
  · subst other
    simp [storeRepr, alignment, update, Option.map_map, Function.comp_def]
  · simp [storeRepr, alignment, update, h]

@[simp] theorem allocated_createRepr (s : Heap Block) (r : Block) (own : Bool)
    (a : Alignment) (base : BasePtr) :
    (s.createRepr r own a).allocated base =
      if base = s.next then own else s.allocated base := by
  by_cases h : base = s.next
  · simp [createRepr, allocated, update, h]
  · simp [createRepr, allocated, update, h]

@[simp] theorem alignment_createRepr (s : Heap Block) (r : Block) (own : Bool)
    (a : Alignment) (base : BasePtr) :
    (s.createRepr r own a).alignment base =
      if base = s.next then some a else s.alignment base := by
  by_cases h : base = s.next
  · simp [createRepr, alignment, update, h]
  · simp [createRepr, alignment, update, h]

@[simp] theorem allocated_remove (s : Heap Block) (base other : BasePtr) :
    (s.remove base).allocated other =
      if other = base then false else s.allocated other := by
  by_cases h : other = base
  · simp [remove, allocated, update, h]
  · simp [remove, allocated, update, h]

@[simp] theorem alignment_remove (s : Heap Block) (base other : BasePtr) :
    (s.remove base).alignment other =
      if other = base then none else s.alignment other := by
  by_cases h : other = base
  · simp [remove, alignment, update, h]
  · simp [remove, alignment, update, h]

@[simp] theorem aligned_storeRepr (s : Heap Std.Block.{u}) (base other : BasePtr)
    (r : Std.Block.{u}) (ty : Type u) :
    Aligned ty (s.storeRepr base r) other ↔ Aligned ty s other := by
  simp [Aligned]

@[simp] theorem aligned_createRepr (s : Heap Std.Block.{u}) (r : Std.Block.{u}) (own : Bool)
    (ty : Type u) :
    Aligned ty (s.createRepr r own (Heap.align ty)) s.next := by
  simp [Aligned, alignment, createRepr, update]

theorem Inv.base_lt {s : Heap Block} (h : s.Inv) {base : BasePtr} {r : Block}
    (hc : s.cells base = some r) : base < s.next := by
  apply Nat.lt_of_not_ge
  intro hn
  have hf := h base hn
  simp [cells, hf] at hc

theorem Inv.storeRepr {s : Heap Block} (h : s.Inv)
    (base : BasePtr) (r : Block) (hb : base < s.next) : (s.storeRepr base r).Inv := by
  intro other ho
  change s.next ≤ other at ho
  have hne : other ≠ base := by grind
  simpa [Heap.storeRepr, update, hne] using h other ho

theorem Inv.createRepr {s : Heap Block} (h : s.Inv) (r : Block) (own : Bool)
    (a : Alignment) : (s.createRepr r own a).Inv := by
  intro base hb
  change s.next + 1 ≤ base at hb
  have hne : base ≠ s.next := by grind
  have hle : s.next ≤ base := by grind
  simpa [Heap.createRepr, update, hne] using h base hle

theorem Inv.remove {s : Heap Block} (h : s.Inv) (base : BasePtr) :
    (s.remove base).Inv := by
  intro other ho
  change s.next ≤ other at ho
  by_cases he : other = base
  · simp [Heap.remove, update, he]
  · simpa [Heap.remove, update, he] using h other ho

theorem writable_of_view {ty : Type u} {r : Std.Block.{u}} {i : Nat} {c : Cell ty}
    (hv : Std.Block.view ty r i c) (hw : c.writable) : Writable ty r i := by
  refine ⟨Std.Block.view_bound _ _ _ _ hv, ?_, ?_⟩
  · intro b hlo hhi
    obtain ⟨byte, hb, hd, _⟩ := Std.Block.view_bytes _ _ _ _ hv b hlo hhi
    exact ⟨byte, hb, hd.trans hw⟩
  · intro other ho
    have he := Std.Block.view_unique _ _ _ _ _ ho hv
    simpa [he] using hw

theorem replaceRange.inv {s s' : Heap Std.Block.{u}} {p : RawPtr ty}
    {old new : List (Cell ty)} (h : replaceRange s p old new s') (hi : s.Inv) :
    s'.Inv := by
  by_cases he : old = []
  · have hs : s' = s := ((ite_eq_left he).mp h).2
    simpa [hs] using hi
  · obtain ⟨_, r, r', hs, _, _, _, rfl⟩ := (ite_eq_right he).mp h
    exact hi.storeRepr _ _ (hi.base_lt hs)

theorem newCells.exists (cs : List (Cell ty)) (own : Bool)
    (s : Heap Std.Block.{u}) (hi : s.Inv) : ∃ p s', newCells cs own s p s' := by
  obtain ⟨r, hr⟩ := Std.Block.create_exists ty cs
  exact ⟨⟨s.next, 0⟩, s.createRepr r own (Heap.align ty),
    hi, rfl, r, hr, rfl⟩

end Heap
end Aeneas.Std
