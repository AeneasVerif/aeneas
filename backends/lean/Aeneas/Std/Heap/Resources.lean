module

public import Aeneas.Std.Heap.Separation
import all Aeneas.Std.Heap.Separation
import all Aeneas.Std.Heap.Model

/-! Byte fragments and their connection to typed reads. Encodings in assertions
are witnesses, not a global encoder or extra heap metadata. -/

@[expose] public section

namespace Aeneas.Std.SepLogic

def cellsHeap (alignment : Alignment) (base : BasePtr) (start : Nat)
    (cells : List (Cell U8)) : Fragment :=
  fun r => ∃ (i : Nat) (hi : i < cells.length),
    r = .cell base (start + i) alignment cells[i]

def allocHeap (repr : Repr ty) (base : BasePtr) (count : Nat) (own : Bool) : Fragment :=
  Fragment.single (.cleanup base (count * repr.size) repr.align own)

def block (repr : Repr ty) (p : RawPtr ty) (cells : List (Cell U8)) : Assertion :=
  fun h => h = cellsHeap repr.align p.base (p.index.val * repr.size) cells

def alloc (repr : Repr ty) (p : RawPtr ty) (count : Nat) (own : Bool) : Assertion :=
  fun h => p.index.val = 0 ∧ h = allocHeap repr p.base count own

def pointsTo (repr : Repr ty) (p : RawPtr ty) (value : ty) (depth : Nat := 0) : Assertion :=
  fun h => ∃ data : Vector U8 repr.size, repr.decode data = some value ∧
    block repr p (data.map (Cell.shared depth ∘ some)).toList h

@[simp] theorem cellsHeap_nil (alignment : Alignment) (base : BasePtr) (start : Nat) :
    cellsHeap alignment base start [] = ∅ := by
  funext r
  apply propext
  constructor
  · rintro ⟨i, hi, _⟩
    exact (Nat.not_lt_zero i hi).elim
  · exact False.elim

theorem cellsHeap_append (alignment : Alignment) (base : BasePtr) (start : Nat)
    (a b : List (Cell U8)) :
    cellsHeap alignment base start (a ++ b) =
      cellsHeap alignment base start a ∪ cellsHeap alignment base (start + a.length) b := by
  funext r
  apply propext
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases ha : i < a.length
    · left
      exact ⟨i, ha, by simp [List.getElem_append_left ha]⟩
    · right
      have hb : i - a.length < b.length := by simp only [List.length_append] at hi; grind
      refine ⟨i - a.length, hb, ?_⟩
      have he : a.length + (i - a.length) = i := by grind
      simp [Nat.add_assoc, he, List.getElem_append_right (Nat.le_of_not_gt ha)]
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨i, by simp; grind, by simp [List.getElem_append_left hi]⟩
    · refine ⟨a.length + i, by simp; grind, ?_⟩
      simp [Nat.add_assoc]

theorem disjoint_cellsHeap_append (alignment : Alignment) (base : BasePtr) (start : Nat)
    (a b : List (Cell U8)) :
    (cellsHeap alignment base start a).Disjoint
      (cellsHeap alignment base (start + a.length) b) := by
  rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
  right
  simp only [Resource.key, ne_eq, Option.some.injEq]
  grind

theorem matches_cellsHeap {s : Heap} {alignment : Alignment} {base : BasePtr}
    {start : Nat} {cells : List (Cell U8)} :
    Fragment.Matches s (cellsHeap alignment base start cells) ↔
      ∀ (i : Nat) (hi : i < cells.length), ∃ block,
        s.allocations base = some block ∧ alignment.val ∣ block.alignment.val ∧
        block.repr[start + i]? = some cells[i] := by
  constructor
  · intro h i hi
    exact h _ ⟨i, hi, rfl⟩
  · rintro h _ ⟨i, hi, rfl⟩
    exact h i hi

theorem bytes_of_matches {s : Heap} {repr : Repr ty} {p : RawPtr ty}
    {data : Vector (Cell U8) repr.size} (hsize : 0 < repr.size)
    (hm : Fragment.Matches s (cellsHeap repr.align p.base (p.index.val * repr.size) data.toList)) :
    ∃ (block : Block) (hi : (p.index.val + 1) * repr.size ≤ block.repr.length),
      s.allocations p.base = some block ∧ repr.align.val ∣ block.alignment.val ∧
      repr.select block.bytes p.index.val hi = data := by
  obtain ⟨block, hs, ha, _⟩ := matches_cellsHeap.mp hm 0 (by simpa using hsize)
  have hp : ∀ (i : Nat) (hi : i < repr.size),
      block.repr[p.index.val * repr.size + i]? = some data[i] := by
    intro i hi
    obtain ⟨actual, hs', _, hv⟩ := matches_cellsHeap.mp hm i (by simpa using hi)
    have he : actual = block := Option.some.inj (hs'.symm.trans hs)
    simpa [he] using hv
  have hb : (p.index.val + 1) * repr.size ≤ block.repr.length := by
    have hx := hp (repr.size - 1) (by grind)
    have hh := List.getElem?_eq_some_iff.mp hx |>.1
    grind [Nat.add_mul]
  refine ⟨block, hb, hs, ha, ?_⟩
  apply Vector.toList_inj.mp
  apply List.ext_getElem?
  intro i
  rw [Repr.select_toList]
  by_cases hi : i < repr.size
  · simpa [hi, Block.bytes] using hp i hi
  · simp [hi]
    grind

theorem read_of_pointsTo {s : Heap} {repr : Repr ty} {p : RawPtr ty}
    {value : ty} {depth : Nat} {h : Fragment} (hs : 0 < repr.size)
    (hp : pointsTo repr p value depth h) (hm : Fragment.Matches s h) :
    Heap.read repr p s = some value := by
  obtain ⟨data, hd, rfl⟩ := hp
  obtain ⟨block, hi, hl, ha, he⟩ := bytes_of_matches hs hm
  simp [Heap.read, hl, ha, Repr.read, hs, hi, he, Repr.readBytes_shared, hd]

theorem disjoint_cellsHeap_congr {alignment : Alignment} {base : BasePtr} {start : Nat}
    {old new : List (Cell U8)} {F : Fragment}
    (hl : old.length = new.length) (hd : (cellsHeap alignment base start old).Disjoint F) :
    (cellsHeap alignment base start new).Disjoint F := by
  rintro _ ⟨i, hi, rfl⟩ r hr
  have hi' : i < old.length := by grind
  exact hd _ ⟨i, hi', rfl⟩ r hr

theorem matches_update {s : Heap} {repr : Repr ty} {p : RawPtr ty} {block : Block}
    (hl : s.allocations p.base = some block) (ha : repr.align.val ∣ block.alignment.val)
    (hi : (p.index.val + 1) * repr.size ≤ block.repr.length)
    (data : Vector (Cell U8) repr.size) :
    Fragment.Matches (s.storeRepr p.base (repr.update block.bytes p.index.val hi data).toList)
      (cellsHeap repr.align p.base (p.index.val * repr.size) data.toList) := by
  rw [matches_cellsHeap]
  intro i hi'
  refine ⟨{ block with repr := (repr.update block.bytes p.index.val hi data).toList },
    by simp [hl], ha, ?_⟩
  simpa using Repr.update_inside repr block.bytes p.index.val hi data i (by simpa using hi')

theorem matches_update_frame {s : Heap} {repr : Repr ty} {p : RawPtr ty}
    {block : Block} {old data : Vector (Cell U8) repr.size} {F : Fragment}
    (hl : s.allocations p.base = some block)
    (hi : (p.index.val + 1) * repr.size ≤ block.repr.length)
    (hd : (cellsHeap repr.align p.base (p.index.val * repr.size) old.toList).Disjoint F)
    (hm : Fragment.Matches s F) :
    Fragment.Matches (s.storeRepr p.base (repr.update block.bytes p.index.val hi data).toList) F := by
  intro resource hr
  have hh := hm resource hr
  by_cases hb : resource.base = p.base
  · cases resource
    · rename_i base index alignment value
      obtain ⟨actual, hs, ha, hv⟩ := hh
      change base = p.base at hb
      subst base
      have he : actual = block := Option.some.inj (hs.symm.trans hl)
      subst actual
      have hout : index < p.index.val * repr.size ∨ (p.index.val + 1) * repr.size ≤ index := by
        by_cases hlt : index < p.index.val * repr.size
        · exact .inl hlt
        right
        by_cases hge : (p.index.val + 1) * repr.size ≤ index
        · exact hge
        have hidx : index - p.index.val * repr.size < old.toList.length := by
          simp only [Vector.length_toList]
          grind [Nat.add_mul]
        have hc := hd _ ⟨index - p.index.val * repr.size, hidx, rfl⟩ _ hr
        have he : p.index.val * repr.size + (index - p.index.val * repr.size) = index := by grind
        simp [Resource.Compatible, Resource.base, Resource.key, he] at hc
      refine ⟨{ block with repr := (repr.update block.bytes p.index.val hi data).toList },
        by simp [hl], ha, ?_⟩
      rw [Repr.update_outside _ _ _ _ _ index hout]
      simpa [Block.bytes] using hv
    · rename_i base size alignment own
      obtain ⟨actual, hs, hn, ha, ho⟩ := hh
      change base = p.base at hb
      subst base
      have he : actual = block := Option.some.inj (hs.symm.trans hl)
      subst actual
      exact ⟨{ block with repr := (repr.update block.bytes p.index.val hi data).toList },
        by simp [hl], by simpa only [Vector.length_toList] using hn, ha, ho⟩
  · cases resource
    · rename_i base index alignment value
      obtain ⟨actual, hs, ha, hv⟩ := hh
      change base ≠ p.base at hb
      exact ⟨actual, by simpa [hb] using hs, ha, hv⟩
    · rename_i base size alignment own
      obtain ⟨actual, hs, hn, ha, ho⟩ := hh
      change base ≠ p.base at hb
      exact ⟨actual, by simpa [hb] using hs, hn, ha, ho⟩

end Aeneas.Std.SepLogic
