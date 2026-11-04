module

public import RawMemoryViews.Nested
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Resources
import all Aeneas.Std.Heap.Repr
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Alloc.Boxed
import all Aeneas.Std.Primitives

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic
open scoped Aeneas.Std.HeapWP

namespace raw_memory_views

set_option maxHeartbeats 1000000

def outerValues (middle : Vector U8 12) : Vector U8 16 :=
  Vector.replicate 2 1#u8 ++ middle ++ Vector.replicate 2 1#u8

def edgeCells : List Cell := List.replicate 2 (.shared 0 (.data 1#u8))

private theorem outer_parts (p : RawPtr (Vector U8 16)) (q r : RawPtr U8)
    (middle : Vector U8 12)
    (qprov : q.provenance = p.provenance) (qaddr : q.address.val = p.address.val + 2)
    (rprov : r.provenance = p.provenance) (raddr : r.address.val = p.address.val + 14)
    (h : Fragment) :
    pointsTo (byteVectorRepr 16) p p.address (outerValues middle) 0 h ↔
      (block Aeneas.Std.Repr.u8 (p.cast U8) p.address edgeCells ∗
        (pointsToRange Aeneas.Std.Repr.u8 q p.address middle ∗
          block Aeneas.Std.Repr.u8 r p.address edgeCells)) h := by
  rw [byteVector_pointsTo]
  have cells : (((outerValues middle).map Aeneas.Std.Byte.data).map (Cell.shared 0)).toList =
      edgeCells ++ ((middle.map Aeneas.Std.Byte.data).map (Cell.shared 0)).toList ++ edgeCells := by
    simp only [Vector.toList_map]
    unfold outerValues
    erw [Vector.toList_append, Vector.toList_append]
    simp [edgeCells]
  unfold writableBytes
  rw [cells, List.append_assoc]
  rw [block_append Aeneas.Std.Repr.u8 (p.cast U8) q p.address edgeCells
    (((middle.map Aeneas.Std.Byte.data).map (Cell.shared 0)).toList ++ edgeCells)
    qprov (by simpa [edgeCells, RawPtr.cast] using qaddr) (by simp [Aeneas.Std.Repr.u8])]
  have inner : block Aeneas.Std.Repr.u8 q p.address
      (((middle.map Aeneas.Std.Byte.data).map (Cell.shared 0)).toList ++ edgeCells) =
      (pointsToRange Aeneas.Std.Repr.u8 q p.address middle ∗
        block Aeneas.Std.Repr.u8 r p.address edgeCells) := by
    funext f
    apply propext
    rw [block_append Aeneas.Std.Repr.u8 q r p.address _ edgeCells
      (rprov.trans qprov.symm) (by simp; agrind) (by simp [Aeneas.Std.Repr.u8])]
    have ranges : pointsToRange Aeneas.Std.Repr.u8 q p.address middle =
        block Aeneas.Std.Repr.u8 q p.address
          ((middle.map Aeneas.Std.Byte.data).map (Cell.shared 0)).toList := by
      funext fragment
      exact propext (u8_range q p.address middle 0 fragment)
    rw [ranges]
  rw [inner]

def nested_views_tail (outer : RawPtr (Vector U8 16)) (middle : RawPtr U8) :
    Result (Vector U8 16) := do
  update_middle_raw middle
  alloc.boxed.Box.from_raw (byteVectorRepr 16) outer

theorem nested_views_tail.spec (p : RawPtr (Vector U8 16)) (q : RawPtr U8)
    (qprov : q.provenance = p.provenance) (qaddr : q.address.val = p.address.val + 2)
    (s₀ : Heap) (authority : RootReturn s₀ p.provenance) :
    HeapWP.TripleAt
      (alloc (byteVectorRepr 16) p p.address 1 true ∗
        pointsTo (byteVectorRepr 16) p p.address (outerValues (Vector.replicate 12 1#u8)))
      (nested_views_tail p q)
      (fun result h => result = outerValues middleResult ∧ empty h) s₀ := by
  rintro h F ⟨owned, whole, disjoint, joined, owner, point⟩ hd hm hi
  have wholeMatch : Fragment.Matches s₀ whole := by
    simp only [joined, Fragment.matches_union] at hm
    exact hm.1.2
  have bytes := (byteVector_pointsTo p p.address _ whole).mp point
  have fit := writableBytes_fits (p.cast U8) p.address _ whole s₀ bytes wholeMatch hi 14 (by decide)
  change p.address.val + 14 < 2 ^ UScalarTy.numBits .Usize at fit
  let r : RawPtr U8 := ⟨p.provenance, ⟨BitVec.ofNat _ (p.address.val + 14)⟩⟩
  have raddr : r.address.val = p.address.val + 14 := by
    change (BitVec.ofNat _ _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit]
  obtain ⟨front, rest, frontApart, wholeEq, frontCells,
    middle, last, middleApart, restEq, middleCells, lastCells⟩ :=
    (outer_parts p q r _ qprov qaddr rfl raddr whole).mp point
  let frame := owned ∪ (front ∪ (last ∪ F))
  have ownerApart := disjoint
  have external := hd
  rw [wholeEq, restEq] at ownerApart
  rw [joined, wholeEq, restEq] at external
  rw [restEq] at frontApart
  simp only [Fragment.disjoint_union_right] at ownerApart frontApart
  simp only [Fragment.disjoint_union_left] at external
  have middleFrame : middle.Disjoint frame := by
    exact Fragment.disjoint_union_right.mpr ⟨ownerApart.2.1.symm,
      Fragment.disjoint_union_right.mpr ⟨frontApart.1.symm,
        Fragment.disjoint_union_right.mpr ⟨middleApart, external.2.2.1⟩⟩⟩
  have middleMatch : Fragment.Matches s₀ (middle ∪ frame) := by
    simp only [joined, wholeEq, restEq, frame, Fragment.matches_union] at hm ⊢
    tauto
  unfold nested_views_tail
  apply HeapWP.Spec.bind (update_middle_raw.spec q p.address (Vector.replicate 12 1#u8)
    middle frame s₀ middleCells middleFrame middleMatch hi (qprov ▸ authority))
  rintro _ s₁ ⟨authority₁, middle₁, hd₁, hm₁, hi₁, middleCells₁⟩
  have middleApart₁ := hd₁
  simp only [frame, Fragment.disjoint_union_right] at middleApart₁
  let whole₁ := front ∪ (middle₁ ∪ last)
  have point₁ : pointsTo (byteVectorRepr 16) p p.address (outerValues middleResult) 0 whole₁ := by
    apply (outer_parts p q r _ qprov qaddr rfl raddr whole₁).mpr
    refine ⟨front, middle₁ ∪ last, ?_, rfl, frontCells, middle₁, last,
      middleApart₁.2.2.1, rfl, middleCells₁, lastCells⟩
    exact Fragment.disjoint_union_right.mpr ⟨middleApart₁.2.1.symm, frontApart.2⟩
  have ownerWhole : owned.Disjoint whole₁ :=
    Fragment.disjoint_union_right.mpr ⟨ownerApart.1,
      Fragment.disjoint_union_right.mpr ⟨middleApart₁.1.symm, ownerApart.2.2⟩⟩
  have allFrame : (owned ∪ whole₁).Disjoint F := by
    simp only [whole₁, Fragment.disjoint_union_left]
    exact ⟨external.1, external.2.1, middleApart₁.2.2.2, external.2.2.2⟩
  have allMatch : Fragment.Matches s₁ ((owned ∪ whole₁) ∪ F) := by
    simp only [whole₁, frame, Fragment.matches_union] at hm₁ ⊢
    tauto
  exact HeapWP.fromRaw.spec (byteVectorRepr 16) p p.address (outerValues middleResult)
    s₁ (by decide) (qprov ▸ authority₁) (owned ∪ whole₁) F
    ⟨owned, whole₁, ownerWhole, rfl, owner, point₁⟩ allFrame allMatch hi₁

/- The sixteen-byte array is represented by the isomorphic sized vector.
   The raw operations and both backward calls are retained. -/
def nested_views : Result (Vector U8 16) := do
  let outer ← alloc.boxed.Box.into_raw (byteVectorRepr 16) (outerValues (Vector.replicate 12 1#u8))
  let middle ← RawPtr.add Aeneas.Std.Repr.u8 (outer.cast U8) 2#usize
  nested_views_tail outer middle

/-- **Spec theorem for `raw_memory_views::nested_views`**
    Both nested backward computations run before reclaiming the original Box.
    The first and last two bytes remain one; all twelve middle bytes have
    their exact specified values on success. Either exposure may abort with OOM;
    enabledness of the backward returns is proved on continuing paths. -/
theorem nested_views.spec (s₀ : Heap) (F : Fragment)
    (hi : s₀.Inv) (hm : Fragment.Matches s₀ F) :
    HeapWP.Spec nested_views
      (fun result s₁ => result = outerValues middleResult ∧ Fragment.Matches s₁ F ∧ s₁.Inv) s₀ := by
  unfold nested_views
  have exposed := HeapWP.intoRaw_return.spec (byteVectorRepr 16)
    (outerValues (Vector.replicate 12 1#u8)) s₀ F hi hm
  apply HeapWP.Spec.bind exposed
  rintro p s₁ ⟨authority, _, h₁, hd₁, hm₁, hi₁, a, b, apart, joined, owner, point⟩
  have bytes := (byteVector_pointsTo p p.address _ b).mp point
  have byteMatch : Fragment.Matches s₁ b := by
    simp only [joined, Fragment.matches_union] at hm₁
    exact hm₁.1.2
  have fit := writableBytes_fits (p.cast U8) p.address _ b s₁ bytes byteMatch hi₁ 2 (by decide)
  have add := HeapWP.frame (R := alloc (byteVectorRepr 16) p p.address 1 true)
    (add_writable.spec (p.cast U8) p.address
      ((outerValues (Vector.replicate 12 1#u8)).map Aeneas.Std.Byte.data)
      2#usize (by decide) (by decide) fit)
      h₁ F s₁ ⟨b, a, apart.symm, by rw [joined, Fragment.union_comm], bytes, owner⟩ hd₁ hm₁ hi₁
  obtain ⟨enabled, post⟩ := HeapWP.Spec.checkedModify.mp add
  have addition := HeapWP.Spec.checkedModify.mpr
    ⟨enabled, fun q s₂ run => And.intro run (post q s₂ run)⟩
  apply HeapWP.Spec.bind addition
  rintro q s₂ ⟨⟨offset, same⟩, h₂, hd₂, hm₂, hi₂, hp₂⟩
  subst s₂
  obtain ⟨qprov, qaddr, hp₂⟩ :
      q.provenance = p.provenance ∧ q.address.val = p.address.val + 2 ∧
        (writableBytes (p.cast U8) p.address
          ((outerValues (Vector.replicate 12 1#u8)).map Aeneas.Std.Byte.data) ∗
          alloc (byteVectorRepr 16) p p.address 1 true) h₂ := by
    simpa only [sep_and_left, RawPtr.cast, show (2#usize).val = 2 by simp] using hp₂
  have typed : (alloc (byteVectorRepr 16) p p.address 1 true ∗
      pointsTo (byteVectorRepr 16) p p.address (outerValues (Vector.replicate 12 1#u8))) h₂ := by
    apply (sep_comm _ _ _).mp
    exact sep_mono (fun f hf => (byteVector_pointsTo p p.address _ f).mpr hf)
      (fun _ hf => hf) hp₂
  apply HeapWP.Spec.mono (nested_views_tail.spec p q qprov qaddr s₁ authority
 h₂ F typed hd₂ hm₂ hi₂)
  rintro result s₃ ⟨empty, _, frame, inv, resultEq, rfl⟩
  exact ⟨resultEq, by simpa using frame, inv⟩

end raw_memory_views
