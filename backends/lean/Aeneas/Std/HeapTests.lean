module

import Aeneas.Std.Heap.Provenance
import Aeneas.Std.Heap.Effects
import Aeneas.Std.Heap.Borrowing
import Aeneas.Std.Scalar.Core
public meta import Aeneas.Std.Heap.Model
public meta import Aeneas.Std.Scalar.Core

/-! Executable regressions for the concrete-address/provenance replacement.
Native checks are not premises of the generic, kernel-checked core laws. -/

namespace Aeneas.Std.HeapTests

def addr (n : Nat) : Usize := ⟨BitVec.ofNat _ n⟩
def byte (n : Nat) : U8 := ⟨BitVec.ofNat _ n⟩
def enc (values : List U8) : List (Vector Byte 1) :=
  values.map fun value => #v[Byte.data value]
def require (condition : Bool) : Option Unit := if condition then some () else none
def shift (p : RawPtr T) (offset : Nat) : RawPtr T := ⟨p.base, addr offset⟩
def put (p : RawPtr U8) (value : U8) (s : Heap) : Option Heap :=
  Heap.write Repr.u8 p value #v[Byte.data value] rfl s

def nestedSlices : Option (List U8) := do
  let values := (List.range 8).map byte
  let (a, s₀) ← Heap.newBlock Repr.u8 (enc values) true (addr 256) none Heap.empty
  let s₁ ← Heap.borrowRange Repr.u8 a 8 s₀
  let (b, s₂) ← Heap.newBlock Repr.u8 (enc (values.drop 1 |>.take 6))
    false (addr 257) (some a.base) s₁
  let s₃ ← Heap.borrowRange Repr.u8 (shift b 1) 4 s₂
  let (c, s₄) ← Heap.newBlock Repr.u8 (enc (values.drop 2 |>.take 4))
    false (addr 258) (some a.base) s₃
  require ((Heap.dealloc Repr.u8 a 8 s₄).isNone &&
    (Heap.read Repr.u8 (shift b 1) s₄).isNone && (put (shift a 2) (byte 99) s₄).isNone)
  let s₅ ← (([90, 91, 92, 93].map byte).zipIdx).foldlM
    (fun s (value, i) => put (shift c i) value s) s₄
  let inner ← Heap.readRange Repr.u8 c 4 s₅
  let s₆ ← Heap.endExposureAt Repr.u8 c 4 0 s₅
  let s₇ ← Heap.endBorrowRange Repr.u8 (shift b 1) (enc inner) s₆
  let middle ← Heap.readRange Repr.u8 b 6 s₇
  require (middle == [1, 90, 91, 92, 93, 6].map byte)
  let s₈ ← Heap.endExposureAt Repr.u8 b 6 0 s₇
  let s₉ ← Heap.endBorrowRange Repr.u8 a (enc ([byte 0] ++ middle ++ [byte 7])) s₈
  let result ← Heap.readRange Repr.u8 a 8 s₉
  let _ ← Heap.dealloc Repr.u8 a 8 s₉
  some result

example : nestedSlices = some ([0, 1, 90, 91, 92, 93, 6, 7].map byte) := by native_decide

def sharedAliases : Option Unit := do
  let data := enc [byte 7, byte 8]
  let (a, s₀) ← Heap.newBlock Repr.u8 data true (addr 256) none Heap.empty
  let s₁ ← Heap.shareRange Repr.u8 a 2 s₀
  let (b, s₂) ← Heap.newSharedExposure Repr.u8 data (addr 256) (some a.base) s₁
  let s₃ ← Heap.shareRange Repr.u8 b 2 s₂
  let (c, s₄) ← Heap.newSharedExposure Repr.u8 data (addr 256) (some a.base) s₃
  require ((Heap.endShareRange Repr.u8 a 2 s₄).isNone &&
    (Heap.newSharedExposure Repr.u8 (enc [byte 9, byte 8])
      (addr 256) (some a.base) s₄).isNone &&
    Heap.ptrEq s₄ a b == some true && a.base != b.base)
  let s₅ ← Heap.endSharedExposure Repr.u8 c 2 s₄
  let s₆ ← Heap.endShareRange Repr.u8 b 2 s₅
  let s₇ ← Heap.endSharedExposure Repr.u8 b 2 s₆
  let s₈ ← Heap.endShareRange Repr.u8 a 2 s₇
  let s₉ ← put a (byte 9) s₈
  require (Heap.read Repr.u8 a s₉ == some (byte 9))

example : sharedAliases = some () := by native_decide

def uninitializedShares : Option Unit := do
  let (a, s₀) ← Heap.alloc Repr.u8 1 (addr 256) Heap.empty
  let s₁ ← Heap.share Repr.u8 a s₀
  require ((Heap.read Repr.u8 a s₁).isNone && (put a (byte 7) s₁).isNone &&
    (Heap.borrow Repr.u8 a s₁).isNone && (Heap.dealloc Repr.u8 a 1 s₁).isNone)
  let (b, s₂) ← Heap.newSharedExposure Repr.u8 [#v[Byte.uninit]]
    (addr 256) (some a.base) s₁
  require ((Heap.endShare Repr.u8 a s₂).isNone)
  let s₃ ← Heap.endSharedExposure Repr.u8 b 1 s₂
  let s₄ ← Heap.endShare Repr.u8 a s₃
  let s₅ ← put a (byte 7) s₄
  let _ ← Heap.dealloc Repr.u8 a 1 s₅
  some ()

example : uninitializedShares = some () := by native_decide

def pointerStorage : Option Unit := do
  let (target, s₀) ← Heap.newBlock Repr.u8 (enc [byte 7])
    true (addr 258) none Heap.empty
  let (slot, s₁) ← Heap.newBlock (Repr.pointer U8) [Repr.pointerEncoding target]
    true (addr 512) none s₀
  let (copy, s₂) ← Heap.alloc (Repr.pointer U8) 1 (addr 520) s₁
  let s₃ ← Heap.copyBytes slot copy 8 s₂
  let loaded ← Heap.read (Repr.pointer U8) copy s₃
  require (loaded == target && s₃.next == s₂.next &&
    Heap.read Repr.u8 (slot.cast U8) s₃ == some (byte 2))
  let s₄ ← put (slot.cast U8) (byte 2) s₃
  require ((Heap.read (Repr.pointer U8) slot s₄).isNone &&
    Heap.read (Repr.pointer U8) copy s₄ == some target)
  let s₅ ← Heap.dealloc Repr.u8 target 1 s₄
  require (Heap.read (Repr.pointer U8) copy s₅ == some target &&
    (Heap.read Repr.u8 target s₅).isNone &&
    Heap.read Repr.u8 (copy.cast U8) s₅ == some (byte 2))
  let (replacement, s₆) ← Heap.newBlock Repr.u8 (enc [byte 9])
    true (addr 258) none s₅
  require (Heap.ptrEq s₆ target replacement == some true &&
    target.base != replacement.base &&
    (Heap.read Repr.u8 target s₆).isNone &&
    Heap.read Repr.u8 replacement s₆ == some (byte 9))

example : pointerStorage = some () := by native_decide

def laneCoherence : Option Unit := do
  let (a, s₀) ← Heap.newBlock Repr.u8 (enc [byte 7]) true (addr 258) none Heap.empty
  let s₁ ← Heap.share Repr.u8 a s₀
  let (b, s₂) ← Heap.newSharedExposure Repr.u8 (enc [byte 7])
    (addr 258) (some a.base) s₁
  let first := Repr.pointerEncoding a
  let mixed := first.set 1 (.pointer (b.cast Unit) 1)
  let same := first.set 1 (.pointer (a.cast Unit) 1)
  require (Heap.ptrEq s₂ a b == some true &&
    (Repr.decodePointer (T := U8) mixed).isNone &&
    Repr.decodePointer (T := U8) same == some a)

example : laneCoherence = some () := by native_decide

def owningReturn : Option Unit := do
  let data := enc [byte 7]
  let (a, s₀) ← Heap.newBlock Repr.u8 data true (addr 256) none Heap.empty
  let s₁ ← Heap.returnOwned Repr.u8 a 1 s₀
  require ((Heap.read Repr.u8 a s₁).isNone && s₁.address a == some (addr 256) &&
    ((s₁.allocations a.base).map Block.alive).getD false)
  let (b, s₂) ← Heap.newBlock Repr.u8 data true (addr 256) (some a.base) s₁
  require (b.base == a.base + 1 && Heap.ptrEq s₂ a b == some true &&
    (Heap.read Repr.u8 a s₂).isNone)
  let s₃ ← Heap.dealloc Repr.u8 b 1 s₂
  require (!((s₃.allocations a.base).map Block.alive).getD true &&
    s₃.address a == some (addr 256) && (Heap.read Repr.u8 b s₃).isNone)
  let (_, _) ← Heap.newBlock Repr.u8 data true (addr 256) none s₃
  some ()

example : owningReturn = some () := by native_decide

/- A foreign-root alias cannot bypass owner cleanup, even while fully borrowed. -/
def rootAndLoanGuards : Option Unit := do
  let (a, s₀) ← Heap.newBlock Repr.u8 (enc [byte 7]) true (addr 256) none Heap.empty
  let s₁ ← Heap.borrow Repr.u8 a s₀
  require ((Heap.newBlock Repr.u8 (enc [byte 7]) false (addr 256) none s₁).isNone)
  let (b, s₂) ← Heap.newBlock Repr.u8 (enc [byte 7])
    false (addr 256) (some a.base) s₁
  let s₃ ← Heap.borrow Repr.u8 b s₂
  let s₄ ← Heap.endBorrow Repr.u8 a #v[Byte.data (byte 7)] s₃
  require ((Heap.dealloc Repr.u8 a 1 s₄).isNone)

example : rootAndLoanGuards = some () := by native_decide

/-- Direct premature restoration remains possible: matching continuation order
is a stated boundary assumption, not a dynamically authenticated loan tree. -/
example : (do
    let (a, s₀) ← Heap.alloc Repr.u8 1 (addr 256) Heap.empty
    let s₁ ← Heap.borrow Repr.u8 a s₀
    let (_, s₂) ← Heap.newBlock Repr.u8 (enc [byte 7])
      false (addr 256) (some a.base) s₁
    let s₃ ← Heap.borrow Repr.u8 ⟨1, addr 0⟩ s₂
    let s₄ ← Heap.endBorrow Repr.u8 a #v[Byte.data (byte 7)] s₃
    Heap.read Repr.u8 a s₄) = some (byte 7) := by native_decide

def padded : Repr U8 where
  size := 2
  align := ⟨2, ⟨1, rfl⟩⟩
  decode := fun addresses bytes => bytes[0].numeric addresses
  encodes := fun value bytes =>
    bytes[0] = .data value ∧ ∃ padding : U8, bytes[1] = .data padding
  pointers := fun _ => []
  aligned := by decide
  complete := fun value => ⟨#v[Byte.data value, Byte.data (byte 0)], rfl, byte 0, rfl⟩
  encode_decode := by
    intro addresses value bytes h
    simp [h.1, Byte.numeric]
  encodes_support := by
    intro value bytes i h
    obtain ⟨h0, padding, h1⟩ := h
    have hi : i.val = 0 ∨ i.val = 1 := by grind
    rcases hi with hi | hi
    · simp [hi, h0]
    · simp [hi, h1]

def jointChoice : Option Unit := do
  let data := [#v[Byte.data (byte 7), Byte.data (byte 0)]]
  let (a, s₀) ← Heap.newBlock padded data true (addr 256) none Heap.empty
  let s₁ ← Heap.shareRange padded a 1 s₀
  require ((Heap.newSharedExposure padded [#v[Byte.data (byte 7), Byte.data (byte 1)]]
    (addr 256) (some a.base) s₁).isNone)
  let (_, s₂) ← Heap.newSharedExposure padded data (addr 256) (some a.base) s₁
  require (s₂.check)

example : jointChoice = some () := by native_decide

def alignmentAndBounds : Option Unit := do
  let (a, s₀) ← Heap.newBlock Repr.u8 (enc ([0, 1, 2, 3].map byte))
    true (addr 256) none Heap.empty
  let s₁ ← Heap.borrowRange Repr.u8 a 4 s₀
  let (b, s₂) ← Heap.newBlock Repr.u8 (enc ([1, 2, 3].map byte))
    false (addr 257) (some a.base) s₁
  require ((Heap.read padded (b.cast U8) s₂).isNone &&
    Heap.read padded (shift b 1) s₂ == some (byte 2) &&
    Heap.distance Repr.u8 (shift b 1) a s₂ == some 2)
  let finish ← Heap.offset Repr.u8 b 3 s₂
  require (s₂.address finish == some (addr 260) &&
    (Heap.read Repr.u8 finish s₂).isNone &&
    (Heap.offset Repr.u8 finish 1 s₂).isNone &&
    (Heap.offset Repr.u8 b (-1) s₂).isNone &&
    (Heap.alloc Repr.u8 2 (addr (2 ^ UScalarTy.numBits .Usize - 2)) Heap.empty).isNone)

example : alignmentAndBounds = some () := by native_decide

def copyInitializationAndAtomicity : Option Unit := do
  let (source, s₀) ← Heap.alloc Repr.u8 2 (addr 256) Heap.empty
  let (destination, s₁) ← Heap.newBlock Repr.u8 (enc [byte 7, byte 8])
    true (addr 512) none s₀
  let s₂ ← Heap.share Repr.u8 (shift destination 1) s₁
  require ((Heap.copyBytes source destination 2 s₂).isNone &&
    Heap.readRange Repr.u8 destination 2 s₂ == some [byte 7, byte 8])
  let s₃ ← Heap.endShare Repr.u8 (shift destination 1) s₂
  let s₄ ← Heap.copyBytes source destination 2 s₃
  require ((Heap.read Repr.u8 destination s₄).isNone &&
    ((s₄.cells destination.base).getD []).all (fun c => c == .shared 0 .uninit))

example : copyInitializationAndAtomicity = some () := by native_decide

def pointerLoanTarget : RawPtr U8 := ⟨0, addr 0⟩
def pointerLoanSlot : Block :=
  ⟨addr 512, 1, (Repr.pointerEncoding pointerLoanTarget).toList.map (Cell.shared 1),
    true, true, true⟩
def pointerLoanHeap : Heap :=
  ⟨fun id => if id = 0 then
      some ⟨addr 258, 0, [.shared 0 (.data (byte 7))], true, true, true⟩
    else if id = 1 then some pointerLoanSlot else none, 2⟩
def pointerLoanAlias : RawPtr U8 := ⟨2, ⟨0⟩⟩
def pointerLoanBytes : Vector Byte 1 :=
  #v[Byte.pointer (pointerLoanTarget.cast Unit) 0]
def pointerLoanResult : Heap :=
  { allocations := update pointerLoanHeap.allocations 2
      (some ⟨addr 512, 1, [.shared 1 (.pointer (pointerLoanTarget.cast Unit) 0)],
        false, true, true⟩)
    next := 3 }

/-- Same-address shared exposure preserves pointer metadata without treating
those lanes as admissible scalar writes. This is an actual State-relation witness. -/
example : State.newSharedExposure Repr.u8 [byte 2]
    pointerLoanHeap pointerLoanAlias pointerLoanResult := by
  refine ⟨[pointerLoanBytes], addr 512, some 1, ?_, ?_⟩
  · change State.exposes Repr.u8 pointerLoanHeap (addr 512).val
      (byte 2) pointerLoanBytes ∧ True
    refine ⟨⟨?_, ?_⟩, trivial⟩
    · native_decide
    · intro i
      have hlt : i.val < 1 := i.isLt
      have hi : i.val = 0 := by grind
      have he : i = ⟨0, by decide⟩ := Fin.ext hi
      subst i
      change Byte.pointer (pointerLoanTarget.cast Unit) 0 ≠ Byte.uninit ∧ _
      refine ⟨by decide, .inr ?_⟩
      exact ⟨1, pointerLoanSlot, 0, 1, rfl, by native_decide, rfl, rfl⟩
  · have hv : pointerLoanResult.check = true := by native_decide
    have ha : Repr.u8.align.val ∣ (addr 512).val := Nat.one_dvd _
    unfold Heap.newSharedExposure
    rw [ite_eq_left ha]
    unfold Heap.createRepr
    change ((Heap.commit pointerLoanResult).map (fun s => (2, s))).map
      (fun (id, s) => (⟨id, ⟨0⟩⟩, s)) = some (pointerLoanAlias, pointerLoanResult)
    rw [Heap.commit, ite_eq_left hv]
    rfl

/-- Typed scalar writes still cannot encode the pointer fragment just exposed. -/
theorem pointerLane_not_scalar : ¬ Repr.u8.encodes (byte 2) pointerLoanBytes := by
  change pointerLoanBytes ≠ #v[Byte.data (byte 2)]
  intro h
  have he := congrArg (fun bytes : Vector Byte 1 => bytes[0]) h
  change Byte.pointer (pointerLoanTarget.cast Unit) 0 = Byte.data (byte 2) at he
  cases he

/-- The safe mutable-loan boundary rejects representation-crossing numerical
borrows until it can distinguish untouched storage from same-value writes. -/
def pointerMutableLoanSlot : Block :=
  { pointerLoanSlot with
    repr := (Repr.pointerEncoding pointerLoanTarget).toList.map (Cell.shared 0) }
def pointerMutableLoanHeap : Heap :=
  { pointerLoanHeap with
    allocations := update pointerLoanHeap.allocations 1 (some pointerMutableLoanSlot) }

example : pointerMutableLoanHeap.check = true ∧
    (Heap.borrowRange Repr.u8 ⟨1, addr 0⟩ 1 pointerMutableLoanHeap).isSome = true := by
  native_decide

example : ¬ State.mutableValues Repr.u8 ⟨1, addr 0⟩ [byte 2] pointerMutableLoanHeap := by
  rintro ⟨blk, hb, values⟩
  have he : blk = pointerMutableLoanSlot := by
    simpa [pointerMutableLoanHeap, update] using hb.symm
  subst blk
  obtain ⟨bytes, bounds, hread, encoded⟩ := values 0 (by decide)
  have hselect : Repr.u8.select pointerMutableLoanSlot.bytes
      ((addr 0).val + 0 * Repr.u8.size) bounds =
      pointerLoanBytes.map (Cell.shared 0) := by
    apply Vector.toList_inj.mp
    rw [Repr.select_toList]
    native_decide
  have initialized : ∀ i : Fin 1, pointerLoanBytes[i.val] ≠ .uninit := by
    intro i
    simp [pointerLoanBytes]
  have hr : Repr.readBytes 1
      (Repr.u8.select pointerMutableLoanSlot.bytes ((addr 0).val + 0 * Repr.u8.size) bounds) =
        some pointerLoanBytes := by
    rw [hselect]
    exact Repr.readBytes_shared pointerLoanBytes 0 initialized
  have hbytes := Option.some.inj (hr.symm.trans hread)
  rw [← hbytes] at encoded
  exact pointerLane_not_scalar encoded

def symbolicSwap : Option Unit := do
  let (target, s₀) ← Heap.newBlock Repr.u8 (enc [byte 7])
    true (addr 258) none Heap.empty
  let (slot, s₁) ← Heap.newBlock (Repr.pointer U8) [Repr.pointerEncoding target]
    true (addr 512) none s₀
  let s₂ ← Heap.swapBytes Repr.u8 (slot.cast U8) (slot.cast U8) s₁
  require (Heap.read (Repr.pointer U8) slot s₂ == some target)
  let (other, s₃) ← Heap.alloc (Repr.pointer U8) 1 (addr 520) s₂
  let s₄ ← Heap.swapBytes (Repr.pointer U8) slot other s₃
  require ((Heap.read (Repr.pointer U8) slot s₄).isNone &&
    Heap.read (Repr.pointer U8) other s₄ == some target)
  let (values, s₅) ← Heap.newBlock Repr.u8 (enc ([1, 2, 3, 4].map byte))
    true (addr 768) none s₄
  let s₆ ← Heap.swapBytes padded values (shift values 2) s₅
  require (Heap.readRange Repr.u8 values 4 s₆ == some ([3, 4, 1, 2].map byte) &&
    (Heap.swapBytes padded values (shift values 1) s₆).isNone)

example : symbolicSwap = some () := by native_decide

def framedWriter : RawPtr U8 := ⟨1, ⟨0⟩⟩
def framedWriterBlock : Block :=
  ⟨addr 256, 0, [.shared 0 (.data (byte 7))], false, true, true⟩
def framedWriterHeap : Heap :=
  ⟨fun id => if id = 0 then
      some ⟨addr 256, 0, [.borrowed], true, true, true⟩
    else if id = 1 then some framedWriterBlock else none, 2⟩

/-- A real checked write with a physically overlapping borrowed ancestor frame.
The contract retains the frame and proves read-back of the updated scalar. -/
example : HeapWP.Spec
    (Result.checkedModify (State.write Repr.u8 framedWriter (byte 9)))
    (fun _ s' =>
      SepLogic.Fragment.Matches s'
        (SepLogic.cellsHeap (addr 256) 0 0 [.borrowed]) ∧
      Heap.read Repr.u8 framedWriter s' = some (byte 9)) framedWriterHeap := by
  have hb : framedWriter.byteOffset.val + Repr.u8.size ≤ framedWriterBlock.repr.length := by
    native_decide
  have ha : Repr.u8.align.val ∣ framedWriterBlock.bptr.val + framedWriter.byteOffset.val :=
    Nat.one_dvd _
  have hs : Repr.u8.select framedWriterBlock.bytes framedWriter.byteOffset.val hb =
      (#v[Byte.data (byte 7)]).map (Cell.shared 0) := by
    apply Vector.toList_inj.mp
    rw [Repr.select_toList]
    native_decide
  have init : ∀ bytes, Repr.u8.encodes (byte 9) bytes →
      ∀ i : Fin 1, bytes[i.val] ≠ .uninit := by
    intro bytes encoded i
    change bytes = #v[Byte.data (byte 9)] at encoded
    subst bytes
    have hz : i.val = 0 := by grind
    have he : i = ⟨0, by decide⟩ := Fin.ext hz
    subst i
    change Byte.data (byte 9) ≠ Byte.uninit
    decide
  have witness : ∃ data, Repr.u8.encodes (byte 9) data ∧
      (framedWriterHeap.storeRepr framedWriter.base
        (Repr.u8.update framedWriterBlock.bytes framedWriter.byteOffset.val hb
          (data.map (Cell.shared 0))).toList).check = true :=
    ⟨#v[Byte.data (byte 9)], rfl, by rw [Repr.update_toList]; native_decide⟩
  have contract := SepLogic.write.spec Repr.u8 framedWriter framedWriterHeap framedWriterBlock
    #v[Byte.data (byte 7)] (byte 9) (by decide) hb rfl (by native_decide) ha hs init witness
  let h := SepLogic.cellsHeap (addr 256) 1 0 [.shared 0 (.data (byte 7))]
  let F := SepLogic.cellsHeap (addr 256) 0 0 [.borrowed]
  have hoff : framedWriter.byteOffset.val = 0 := by native_decide
  have hp : SepLogic.block Repr.u8 framedWriter (addr 256)
      ((#v[Byte.data (byte 7)]).map (Cell.shared 0)).toList h := by
    refine ⟨ha, ?_⟩
    rw [hoff]
    simp [h, framedWriter]
  have hd : h.Disjoint F := SepLogic.disjoint_views _ _ _ _ _ _ _ _ (by decide)
  have hm : SepLogic.Fragment.Matches framedWriterHeap (h ∪ F) := by
    apply (SepLogic.Fragment.matches_union _ _ _).mpr
    constructor
    · rw [SepLogic.matches_cellsHeap]
      intro i hi
      have he : i = 0 := by change i < 1 at hi; grind
      subst i
      exact ⟨framedWriterBlock, rfl, by native_decide, rfl, rfl⟩
    · rw [SepLogic.matches_cellsHeap]
      intro i hi
      have he : i = 0 := by change i < 1 at hi; grind
      subst i
      exact ⟨⟨addr 256, 0, [.borrowed], true, true, true⟩,
        rfl, by native_decide, rfl, rfl⟩
  have hinv : framedWriterHeap.Inv := by
    refine ⟨?_, by native_decide⟩
    intro id hi
    change 2 ≤ id at hi
    have hzero : id ≠ 0 := by grind
    have hone : id ≠ 1 := by grind
    simp [framedWriterHeap, hzero, hone]
  have run := HeapWP.TripleAt.checkedModify contract h F hp hd hm hinv
  apply HeapWP.Spec.mono run
  rintro _ s' ⟨h', _, hm', _, hp'⟩
  have parts := SepLogic.Fragment.matches_union _ _ _ |>.mp hm'
  exact ⟨parts.2, SepLogic.read_of_pointsTo (by decide) hp' parts.1⟩

#print axioms Heap.createRepr_Inv
#print axioms Heap.modify_Inv
#print axioms Heap.addresses_storeRepr
#print axioms Heap.addresses_retire
#print axioms Repr.pointer_roundTrip
#print axioms Repr.u8_write_data
#print axioms Repr.encoding_no_forgery
#print axioms Heap.compatible_writer_excludes
#print axioms SepLogic.Resource.Holds.overlapCompatible
#print axioms SepLogic.Resource.Holds.noAliases_unique
#print axioms SepLogic.write.spec
#print axioms SepLogic.endBorrow.spec
#print axioms SepLogic.createRepr.spec
#print axioms HeapWP.TripleAt.checkedModify

end Aeneas.Std.HeapTests
