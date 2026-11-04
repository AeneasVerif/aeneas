module

public import Aeneas.Std.Heap

/-! Core laws for the replacement model. No Rust refinement or legacy separation
contract is assumed here. Computational regressions live in `HeapTests.lean`. -/

public section

namespace Aeneas.Std

theorem Repr.encodeList_complete (repr : Repr T) (values : List T) :
    ∃ data, repr.encodeList values data := by
  induction values with
  | nil => exact ⟨[], trivial⟩
  | cons value values ih =>
    obtain ⟨bytes, hb⟩ := repr.encode_complete value
    obtain ⟨data, hd⟩ := ih
    exact ⟨bytes :: data, hb, hd⟩

theorem Repr.pointer_roundTrip (p : RawPtr T) :
    (Repr.pointer T).decode (Repr.pointerEncoding p) = some p :=
  (Repr.pointer T).encode_decode p _ rfl

theorem Repr.u8_write_data (value : U8) (bytes : Vector Byte 1)
    (h : Repr.u8.encode value bytes) : bytes = #v[Byte.data value] := h

theorem Repr.encoding_no_forgery (repr : Repr T) (value : T)
    (bytes : Vector Byte repr.size) (i : Fin repr.size) (p : RawPtr Unit) (lane : Nat)
    (encoded : repr.encode value bytes) (empty : ∀ p, ¬ repr.Carries value p)
    (pointer : bytes[i.val] = .pointer p lane) : False := by
  exact empty p ⟨bytes, encoded, i, lane, pointer⟩

theorem Repr.data_not_pointer (data : Vector U8 pointerWidth) :
    Repr.decodePointer (T := T) (data.map Byte.data) = none := by
  simp [Repr.decodePointer]

theorem Cell.writer_excludes_shared (byte other : Byte) (depth : Nat) :
    Cell.compatible (.shared 0 byte) (.shared depth other) = false := rfl

theorem Cell.shared_uninit_read (depth : Nat) :
    Cell.read (.shared depth .uninit) = some .uninit := rfl

theorem Cell.shared_uninit_not_writable (depth : Nat) (byte : Byte) :
    Cell.write (.shared (depth + 1) .uninit) byte = none := rfl

namespace Heap

theorem compatible_writer_excludes (a b : Block) (byte : Byte) (cell : Cell) (i j : Nat)
    (ha : a.active = true) (hb : b.active = true) (hc : compatible a b = true)
    (hi : (.shared 0 byte, i) ∈ a.repr.zipIdx) (hj : (cell, j) ∈ b.repr.zipIdx)
    (address : a.bptr.val + i = b.bptr.val + j) : cell = .borrowed := by
  simp only [compatible, ha, hb, Bool.not_true, Bool.false_or] at hc
  have row := List.all_eq_true.mp hc (.shared 0 byte, i) hi
  have entry := List.all_eq_true.mp row (cell, j) hj
  cases cell
  · simp [address, Cell.compatible] at entry
  · rfl

theorem fresh (s : Heap) (h : s.Inv) : s.allocations s.next = none :=
  h.1 s.next (Nat.le_refl _)

theorem commit_success (s s₁ : Heap) (h : commit s = some s₁) :
    s₁ = s ∧ s₁.check = true := by
  unfold commit at h
  split at h
  · cases h
    exact ⟨rfl, ‹s.check = true›⟩
  · contradiction

theorem commit_Inv (s s₁ : Heap)
    (support : ∀ id, s.next ≤ id → s.allocations id = none)
    (h : commit s = some s₁) : s₁.Inv := by
  obtain ⟨hs, hc⟩ := commit_success s s₁ h
  subst s₁
  exact ⟨support, hc⟩

theorem storeRepr_support (s : Heap) (id : Nat) (bytes : List Cell)
    (h : s.Inv) (hid : id < s.next) :
    ∀ j, (s.storeRepr id bytes).next ≤ j →
      (s.storeRepr id bytes).allocations j = none := by
  intro j hj
  change s.next ≤ j at hj
  have hji : j ≠ id := by grind
  simp [storeRepr, update, hji, h.1 j hj]

theorem createRepr_fresh (s : Heap) (block : Block) (id : Nat) (s₁ : Heap)
    (h : createRepr s block = some (id, s₁)) :
    id = s.next ∧ s₁.next = s.next + 1 ∧ s₁.check = true := by
  unfold createRepr at h
  split at h
  · cases hc : commit
      { allocations := update s.allocations s.next (some block), next := s.next + 1 }
    · simp [hc] at h
    · simp only [hc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hi, hs⟩ := h
      subst id
      subst s₁
      obtain ⟨heq, hcheck⟩ := commit_success _ _ hc
      exact ⟨rfl, congrArg Heap.next heq, hcheck⟩
  · contradiction

theorem createRepr_Inv (s : Heap) (block : Block) (id : Nat) (s₁ : Heap)
    (hinv : s.Inv) (h : createRepr s block = some (id, s₁)) : s₁.Inv := by
  unfold createRepr at h
  split at h
  · cases hc : commit
      { allocations := update s.allocations s.next (some block), next := s.next + 1 }
    · simp [hc] at h
    · simp only [hc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, hs⟩ := h
      subst s₁
      apply commit_Inv _ _ _ hc
      intro j hj
      have hne : j ≠ s.next := by grind
      have hjold : s.next ≤ j := by grind
      simp [update, hne, hinv.1 j hjold]
  · contradiction

theorem modify_Inv (repr : Repr T) (p : RawPtr T) (s s₁ : Heap)
    (change : ∀ {r}, Vector Cell r → Nat → Option (Vector Cell r))
    (hinv : s.Inv) (h : modify repr p change s = some s₁) : s₁.Inv := by
  unfold modify at h
  cases hb : s.allocations p.provenance
  · simp [hb] at h
  · rename_i block
    rw [hb] at h
    change (if s.live block && block.bptr.val ≤ p.address.val &&
        repr.align.val ∣ p.address.val then
      (change block.bytes (p.offsetFrom block.bptr)).bind fun bytes =>
        commit (s.storeRepr p.provenance bytes.toList)
      else none) = some s₁ at h
    split at h
    ·
      cases hc : change block.bytes (p.offsetFrom block.bptr)
      · simp [hc] at h
      · simp only [hc, Option.bind_some] at h
        have hid : p.provenance < s.next := by
          by_cases hn : p.provenance < s.next
          · exact hn
          · have he := hinv.1 p.provenance (Nat.le_of_not_gt hn)
            rw [hb] at he
            contradiction
        exact commit_Inv _ _ (storeRepr_support s p.provenance _ hinv hid) h
    · contradiction

end Heap
end Aeneas.Std
