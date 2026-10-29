module

public import Aeneas.Std.Heap.Borrowing
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Repr

/-! Authorization is byte-wise, including across types. Readable bytes may have
different sharing depths. No general pointer-invalidation law is assumed. -/

@[expose] public section

namespace Aeneas.Std

theorem Cell.write.writable {cell : Cell ty} {value : ty} {result : Cell ty}
    (h : cell.write value = some result) : cell.writable := by
  cases cell
  · rename_i depth payload
    cases depth
    · rfl
    · cases h
  · cases h

namespace Repr

theorem read.denied_by_byte (repr : Repr ty) (bytes : Vector (Cell U8) r) (i b : Nat)
    (hlo : i * repr.size ≤ b) (hhi : b < (i + 1) * repr.size)
    (byte : Cell U8) (hp : bytes.toList[b]? = some byte) (hn : byte.read = none) :
    repr.read bytes i = none := by
  cases he : repr.read bytes i
  · rfl
  · rename_i value
    unfold read at he
    split at he
    · rename_i hb
      obtain ⟨data, hr, _⟩ := Option.bind_eq_some_iff.mp he
      have hk : b - i * repr.size < repr.size := by grind [Nat.add_mul]
      have hs := select_getElem? repr bytes i hb.2 (b - i * repr.size) hk
      have hindex : i * repr.size + (b - i * repr.size) = b := by grind
      rw [hindex, hp, Vector.getElem?_eq_getElem hk] at hs
      obtain ⟨v, hv⟩ := vector_mapM_enabled hr (b - i * repr.size) hk
      rw [Option.some.inj hs, hn] at hv
      cases hv
    · cases he

theorem write.denied_by_byte (repr : Repr ty) (bytes : Vector (Cell U8) r) (i b : Nat)
    (hlo : i * repr.size ≤ b) (hhi : b < (i + 1) * repr.size)
    (byte : Cell U8) (hp : bytes.toList[b]? = some byte) (hn : ¬ byte.writable)
    (value : ty) (data : Vector U8 repr.size) (decoded : repr.decode data = some value) :
    repr.write bytes i value data decoded = none := by
  cases he : repr.write bytes i value data decoded
  · rfl
  · unfold write at he
    split at he
    · rename_i hb
      split at he
      · rename_i result hc
        have hk : b - i * repr.size < repr.size := by grind [Nat.add_mul]
        have hs := select_getElem? repr bytes i hb.2 (b - i * repr.size) hk
        have hindex : i * repr.size + (b - i * repr.size) = b := by grind
        rw [hindex, hp, Vector.getElem?_eq_getElem hk] at hs
        obtain ⟨v, hv⟩ := vector_mapM_enabled hc (b - i * repr.size) hk
        simp only [Vector.getElem_zip] at hv
        exact (hn (Option.some.inj hs ▸ Cell.write.writable hv)).elim
      · cases he
    · cases he

end Repr

namespace Heap

theorem read.denied_by_byte {s : Heap} {repr : Repr ty} {p : RawPtr ty} {block : Block}
    (hs : s.allocations p.base = some block) (b : Nat)
    (hlo : p.index.val * repr.size ≤ b) (hhi : b < (p.index.val + 1) * repr.size)
    (byte : Cell U8) (hp : block.repr[b]? = some byte) (hn : byte.read = none) :
    read repr p s = none := by
  have hr := Repr.read.denied_by_byte repr block.bytes p.index.val b hlo hhi byte
    (by simpa [Block.bytes] using hp) hn
  by_cases ha : repr.align.val ∣ block.alignment.val
  · simp [read, hs, ha, hr]
  · simp [read, hs, ha]

theorem write.denied_by_byte {s : Heap} {repr : Repr ty} {p : RawPtr ty} {block : Block}
    (hs : s.allocations p.base = some block) (b : Nat)
    (hlo : p.index.val * repr.size ≤ b) (hhi : b < (p.index.val + 1) * repr.size)
    (byte : Cell U8) (hp : block.repr[b]? = some byte) (hn : ¬ byte.writable)
    (value : ty) (data : Vector U8 repr.size) (decoded : repr.decode data = some value) :
    write repr p value data decoded s = none := by
  have hw := Repr.write.denied_by_byte repr block.bytes p.index.val b hlo hhi byte
    (by simpa [Block.bytes] using hp) hn value data decoded
  by_cases ha : repr.align.val ∣ block.alignment.val
  · simp [write, modify, hs, ha, hw]
  · simp [write, modify, hs, ha]

theorem freeBlock.denied_by_byte {s : Heap} {repr : Repr ty} {p : RawPtr ty} {block : Block}
    (hs : s.allocations p.base = some block) (b : Nat) (byte : Cell U8)
    (hp : block.repr[b]? = some byte) (hn : ¬ byte.writable) (count : Nat) (own : Bool) :
    freeBlock repr p count own s = none := by
  have hbad : ¬ (p.index.val = 0 ∧ block.owned = own ∧
      repr.align.val ∣ block.alignment.val ∧ block.repr.length = count * repr.size ∧
      block.repr.all (fun c => c.depth == some 0) = true) := by
    intro hg
    have hb := List.getElem?_eq_some_iff.mp hp
    have hm : byte ∈ block.repr := hb.2 ▸ List.getElem_mem hb.1
    have hx := List.all_eq_true.mp hg.2.2.2.2 byte hm
    exact (hn (beq_iff_eq.mp hx)).elim
  simp only [freeBlock, hs, hbad, ite_false]

end Heap
end Aeneas.Std
