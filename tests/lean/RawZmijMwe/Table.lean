module

public import RawRyuMwe.TableCopy
import all Aeneas.Std.Core.PtrMovement
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Resources

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic scalar_mwe

namespace raw_zmij_mwe

def pairWord (pair : Usize) : U16 := if pair.val = 0 then 12336#u16 else 14129#u16

def table_ptr (p : RawPtr U8) (pair : Usize) : Result (RawPtr U16) := do
  massert (pair < 2#usize)
  RawPtr.add u16Repr (p.cast U16) pair

theorem table_ptr.spec (p : RawPtr U8) (pair : Usize) (bound : pair.val < 2)
    (h F : Fragment) (s₀ : Heap)
    (hp : storageAt p (raw_ryu_mwe.pairs.map Byte.data) 1 h)
    (hm : Fragment.Matches s₀ (h ∪ F)) (hi : s₀.Inv) :
    HeapWP.Spec (table_ptr p pair)
      (fun q s₁ => q.provenance = p.provenance ∧
        q.address.val = p.address.val + 2 * pair.val ∧ s₁ = s₀) s₀ := by
  obtain ⟨blk, lookup, live, base, _, repr, _⟩ :=
    whole_storage p _ 1 h s₀ hp ((Fragment.matches_union _ _ _).mp hm).1
  have len : blk.repr.length = 4 := by simp [repr, raw_ryu_mwe.pairs]
  have valid := hi.validBlock lookup
  simp only [Heap.validBlock, Bool.and_eq_true] at valid
  have bounded := valid.1.1
  simp only [Heap.bounded, Bool.and_eq_true, decide_eq_true_eq, base, len] at bounded
  have fits : p.address.val + 2 * pair.val < 2 ^ UScalarTy.numBits .Usize := by agrind
  let q : RawPtr U16 := ⟨p.provenance, ⟨BitVec.ofNat _ (p.address.val + 2 * pair.val)⟩⟩
  have addr : q.address.val = p.address.val + 2 * pair.val := by
    change (p.address.val + 2 * pair.val) % _ = _
    exact Nat.mod_eq_of_lt fits
  have fitInt : (p.address.val : Int) + (pair.val : Int) * 2 <
      2 ^ System.Platform.numBits := by
    norm_cast
    simpa [Nat.mul_comm] using fits
  have run : Heap.offset u16Repr (p.cast U16) pair.val s₀ = some q := by
    have upper : (pair.val : Int) * 2 ≤ 4 := by agrind
    simp [Heap.offset, u16Repr, codec, RawPtr.cast, lookup, live, base, len,
      fitInt, q, Int.toNat_add, Int.toNat_mul, Nat.mul_comm, upper]
  unfold table_ptr
  have assertion : massert (pair < 2#usize) ⦃ (_ : Unit) => True ⦄ := by
    step*
  apply HeapWP.Spec.bind (HeapWP.Spec.of_spec assertion s₀)
  rintro _ s₁ ⟨_, stateEq⟩
  subst s₁
  apply HeapWP.Spec.checkedModify.mpr
  refine ⟨⟨q, s₀, run, rfl⟩, ?_⟩
  rintro result s₁ ⟨hr, rfl⟩
  have eq := Option.some.inj (hr.symm.trans run)
  subst result
  exact ⟨rfl, addr, rfl⟩

theorem table_word (p : RawPtr U8) (q : RawPtr U16) (pair : Usize)
    (bound : pair.val < 2) (aligned : 2 ∣ p.address.val)
    (prov : q.provenance = p.provenance)
    (addr : q.address.val = p.address.val + 2 * pair.val)
    (h : Fragment) (s : Heap)
    (hp : storageAt p (raw_ryu_mwe.pairs.map Byte.data) 1 h)
    (hm : Fragment.Matches s h) :
    ∃ cells, pointsTo u16Repr q p.address (pairWord pair) 1 cells ∧
      Fragment.Matches s cells := by
  obtain ⟨blk, lookup, live, base, _, repr, _⟩ := whole_storage p _ 1 h s hp hm
  let bytes := (bytes16 (pairWord pair)).map Byte.data
  let cells := cellsHeap p.address q.provenance (q.offsetFrom p.address)
    (bytes.map (Cell.shared 1)).toList
  have offset : q.offsetFrom p.address = 2 * pair.val := by
    simp [RawPtr.offsetFrom, addr]
  refine ⟨cells, ⟨bytes, rfl, ?_, ?_, rfl⟩, ?_⟩
  · simp [addr]
  · change 2 ∣ q.address.val
    rw [addr]
    exact Nat.dvd_add aligned (dvd_mul_right 2 pair.val)
  · apply matches_cellsHeap.mpr
    intro i hi
    refine ⟨blk, prov ▸ lookup, live, base, ?_⟩
    have ib : i < 2 := by simpa [bytes] using hi
    have pc : pair.val = 0 ∨ pair.val = 1 := by agrind
    have ic : i = 0 ∨ i = 1 := by agrind
    rcases pc with pc | pc
    · rcases ic with rfl | rfl
      · simp [repr, offset, bytes, pairWord, pc, raw_ryu_mwe.pairs, bytes16,
          raw_memory_views.u16Bytes]
        rfl
      · simp [repr, offset, bytes, pairWord, pc, raw_ryu_mwe.pairs, bytes16,
          raw_memory_views.u16Bytes]
        rfl
    · rcases ic with rfl | rfl
      · simp [repr, offset, bytes, pairWord, pc, raw_ryu_mwe.pairs, bytes16,
          raw_memory_views.u16Bytes]
        rfl
      · simp [repr, offset, bytes, pairWord, pc, raw_ryu_mwe.pairs, bytes16,
          raw_memory_views.u16Bytes]
        rfl

def read_digits2 (pair : Usize) (address : BasePtr) : Result U16 := do
  let p ← exposeBytes (raw_ryu_mwe.pairs.map Byte.data) 1 address
  let q ← table_ptr p pair
  let value ← RawPtr.read u16Repr q
  closeBytes p 4 1
  pure value

/-- **Spec theorem for `raw_zmij_mwe::read_digits2`**
    The static's alignment is explicit; a byte type alone does not supply it. -/
theorem read_digits2.spec (pair : Usize) (address : BasePtr)
    (bound : pair.val < 2) (aligned : 2 ∣ address.val)
    (F : Fragment) (s₀ : Heap) (hm : Fragment.Matches s₀ F) (hi : s₀.Inv) :
    HeapWP.Spec (read_digits2 pair address)
      (fun value s₁ => value = pairWord pair ∧ s₁.Inv ∧ Fragment.Matches s₁ F) s₀ := by
  unfold read_digits2
  apply HeapWP.Spec.bind (exposeBytes.spec _ 1 address s₀ F hi hm)
  rintro p s₁ ⟨placement, _, h, hd, hm₁, hi₁, hp⟩
  apply HeapWP.Spec.bind (table_ptr.spec p pair bound h F s₁ hp hm₁ hi₁)
  rintro q s₂ ⟨prov, addr, stateEq⟩
  subst s₂
  obtain ⟨cells, point, matchCells⟩ := table_word p q pair bound (by simpa [placement] using aligned)
    prov addr h s₁ hp ((Fragment.matches_union _ _ _).mp hm₁).1
  have read := read_of_pointsTo (by decide : 0 < u16Repr.size) point matchCells
  have reading : HeapWP.Spec (RawPtr.read u16Repr q)
      (fun value s₂ => value = pairWord pair ∧ s₂ = s₁) s₁ := by
    apply HeapWP.Spec.checkedModify.mpr
    refine ⟨⟨_, s₁, read, rfl⟩, ?_⟩
    rintro value s₂ ⟨hr, rfl⟩
    exact ⟨Option.some.inj (hr.symm.trans read), rfl⟩
  apply HeapWP.Spec.bind reading
  rintro value s₂ ⟨rfl, stateEq⟩
  subst s₂
  apply HeapWP.Spec.bind (closeBytes.state_spec p _ 1 h F s₁ hp hd hm₁ hi₁)
  rintro _ s₃ ⟨hi₃, hm₃, _, _⟩
  exact (HeapWP.Spec.pure _ _ _).mpr ⟨rfl, hi₃, hm₃⟩

/- The static reference is represented by its copied scalar value and a matching
   return for the temporary shared view; the underlying allocation is not freed. -/
def digits2 (pair : Usize) (address : BasePtr) : Result (U16 × Result Unit) := do
  let p ← exposeBytes (raw_ryu_mwe.pairs.map Byte.data) 1 address
  let q ← table_ptr p pair
  let values ← RawPtr.shareRange u16Repr q 1
  match values with
  | [value] => pure (value, do
      RawPtr.endShareRange u16Repr q [value]
      closeBytes p 4 1)
  | _ => Result.fail .undef

/-- **Spec theorem for `raw_zmij_mwe::digits2`**
    Exact selected scalar and a proved, actual shared-reference return. -/
theorem digits2.spec (pair : Usize) (address : BasePtr)
    (bound : pair.val < 2) (aligned : 2 ∣ address.val)
    (F : Fragment) (s₀ : Heap) (hm : Fragment.Matches s₀ F) (hi : s₀.Inv) :
    HeapWP.Spec (digits2 pair address)
      (fun result s₁ => result.1 = pairWord pair ∧
        HeapWP.Spec result.2 (fun _ s₂ => s₂.Inv ∧ Fragment.Matches s₂ F) s₁) s₀ := by
  unfold digits2
  apply HeapWP.Spec.bind (exposeBytes.spec _ 1 address s₀ F hi hm)
  rintro p s₁ ⟨placement, _, h, hd, hm₁, hi₁, hp⟩
  apply HeapWP.Spec.bind (table_ptr.spec p pair bound h F s₁ hp hm₁ hi₁)
  rintro q s₂ ⟨prov, addr, stateEq⟩
  subst s₂
  obtain ⟨cells, point, matchCells⟩ := table_word p q pair bound (by simpa [placement] using aligned)
    prov addr h s₁ hp ((Fragment.matches_union _ _ _).mp hm₁).1
  apply HeapWP.Spec.bind (HeapWP.shareRange_single_return.spec u16Repr q p.address (pairWord pair)
    1 (by decide) cells ∅ s₁ point (Fragment.disjoint_empty_right _)
      (by simpa using matchCells) hi₁)
  rintro values s₂ ⟨rfl, _, returning⟩
  apply (HeapWP.Spec.pure _ _ _).mpr
  refine ⟨rfl, ?_⟩
  apply HeapWP.Spec.bind returning
  rintro _ s₃ stateEq
  subst s₃
  apply HeapWP.Spec.mono (closeBytes.state_spec p _ 1 h F s₁ hp hd hm₁ hi₁)
  rintro _ s₄ ⟨hi₄, hm₄, _, _⟩
  exact ⟨hi₄, hm₄⟩

end raw_zmij_mwe
