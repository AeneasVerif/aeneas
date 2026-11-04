module

public import Aeneas.Std.Heap.Borrowing
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Repr

/-! Authorization is byte-wise, including across types. Readable bytes may have
different sharing depths. No general pointer-invalidation law is assumed. -/

@[expose] public section

namespace Aeneas.Std

theorem Cell.write.writable {cell : Cell} {value : Byte} {result : Cell}
    (h : cell.write value = some result) : cell.writable := by
  cases cell
  · rename_i depth payload
    cases depth
    · rfl
    · cases h
  · cases h

namespace Repr

theorem read.denied_by_byte (repr : Repr ty)
    (bytes : Vector Cell r) (i b : Nat)
    (hlo : i ≤ b) (hhi : b < (i + repr.size))
    (byte : Cell) (hp : bytes.toList[b]? = some byte) (hn : byte.read = none) :
    repr.read bytes i = none := by
  cases he : repr.read bytes i
  · rfl
  · rename_i value
    unfold read at he
    split at he
    · rename_i hb
      obtain ⟨data, hr, _⟩ := Option.bind_eq_some_iff.mp he
      unfold Repr.readBytes at hr
      have hk : b - i < repr.size := by grind [Nat.add_mul]
      have hs := select_getElem? repr bytes i hb.2 (b - i) hk
      have hindex : i + (b - i) = b := by grind
      rw [hindex, hp, Vector.getElem?_eq_getElem hk] at hs
      obtain ⟨v, hv⟩ := vector_mapM_enabled hr (b - i) hk
      rw [Option.some.inj hs, hn] at hv
      cases hv
    · cases he

theorem write.denied_by_byte (repr : Repr ty) (bytes : Vector Cell r) (i b : Nat)
    (hlo : i ≤ b) (hhi : b < (i + repr.size))
    (byte : Cell) (hp : bytes.toList[b]? = some byte) (hn : ¬ byte.writable)
    (value : ty) (data : Vector Byte repr.size) (decoded : repr.encode value data) :
    repr.write bytes i value data decoded = none := by
  cases he : repr.write bytes i value data decoded
  · rfl
  · unfold write at he
    split at he
    · rename_i hb
      obtain ⟨result, hc, _⟩ := Option.map_eq_some_iff.mp he
      unfold Repr.writeBytes at hc
      have hk : b - i < repr.size := by grind [Nat.add_mul]
      have hs := select_getElem? repr bytes i hb.2 (b - i) hk
      have hindex : i + (b - i) = b := by grind
      rw [hindex, hp, Vector.getElem?_eq_getElem hk] at hs
      obtain ⟨v, hv⟩ := vector_mapM_enabled hc (b - i) hk
      simp only [Vector.getElem_zip] at hv
      exact (hn (Option.some.inj hs ▸ Cell.write.writable hv)).elim
    · cases he

end Repr

namespace Heap

theorem read.denied_by_byte {s : Heap} {repr : Repr ty} {p : RawPtr ty} {block : Block}
    (hs : s.allocations p.provenance = some block) (b : Nat)
    (hlo : (p.offsetFrom block.bptr) ≤ b) (hhi : b < ((p.offsetFrom block.bptr) + repr.size))
    (byte : Cell) (hp : block.repr[b]? = some byte) (hn : byte.read = none) :
    read repr p s = none := by
  have hr := Repr.read.denied_by_byte repr block.bytes (p.offsetFrom block.bptr) b hlo hhi byte
    (by simpa [Block.bytes] using hp) hn
  simp [read, hs, hr]

theorem write.denied_by_byte {s : Heap} {repr : Repr ty} {p : RawPtr ty} {block : Block}
    (hs : s.allocations p.provenance = some block) (b : Nat)
    (hlo : (p.offsetFrom block.bptr) ≤ b) (hhi : b < ((p.offsetFrom block.bptr) + repr.size))
    (byte : Cell) (hp : block.repr[b]? = some byte) (hn : ¬ byte.writable)
    (value : ty) (data : Vector Byte repr.size) (decoded : repr.encode value data) :
    write repr p value data decoded s = none := by
  have hw := Repr.write.denied_by_byte repr block.bytes (p.offsetFrom block.bptr) b hlo hhi byte
    (by simpa [Block.bytes] using hp) hn value data decoded
  simp [write, modify, hs, hw]

theorem freeBlock.denied_by_byte {s : Heap} {repr : Repr ty} {p : RawPtr ty} {block : Block}
    (hs : s.allocations p.provenance = some block) (b : Nat) (byte : Cell)
    (hp : block.repr[b]? = some byte) (hn : ¬ byte.writable) (count : Nat) (own : Bool) :
    freeBlock repr p count own s = none := by
  have hbad : block.repr.all (fun c => c.depth == some 0) ≠ true := by
    intro hg
    have hb := List.getElem?_eq_some_iff.mp hp
    have hm : byte ∈ block.repr := hb.2 ▸ List.getElem_mem hb.1
    have hx := List.all_eq_true.mp hg byte hm
    exact (hn (beq_iff_eq.mp hx)).elim
  cases own
  · simp only [freeBlock, Bool.false_eq_true, ite_false, endExposureAt, hs]
    dsimp only [Bind.bind, Option.bind]
    split
    · rename_i guard
      simp only [Bool.and_eq_true] at guard
      grind
    · rfl
  · have denied : returnOwned repr p count s = none := by
      simp only [returnOwned, hs]
      dsimp only [Bind.bind, Option.bind]
      cases hr : s.allocations block.root
      · simp
      · dsimp only [Bind.bind, Option.bind]
        split
        · rename_i guard
          simp only [Bool.and_eq_true] at guard
          grind
        · rfl
    simp [freeBlock, dealloc, hs, denied]

end Heap
end Aeneas.Std
