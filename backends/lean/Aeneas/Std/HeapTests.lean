module

import Aeneas.Std.Heap.Provenance
import Aeneas.Std.Heap.Effects
import Aeneas.Std.Heap.Borrowing
import Aeneas.Std.Heap.EffectSpecs
import Aeneas.Std.Heap.Initialization
import Aeneas.Std.Heap.Ranges
import Aeneas.Std.Heap.RangeRestoration
import Aeneas.Std.Heap.PointerOps
import Aeneas.Std.Scalar.Core
public meta import Aeneas.Std.Heap.Model
public meta import Aeneas.Std.Scalar.Core

/-! Executable regressions for the concrete-address/provenance replacement.
Native checks are not premises of the generic, kernel-checked core laws. -/

namespace Aeneas.Std.HeapTests

/- OOM is an accepted abort, never a successful return or an excuse for UB. -/
example : WP.spec (Result.oom : Result Unit) (fun _ => False) := WP.spec_oom

example (s : Heap) : HeapWP.Spec (Result.oom : Result Unit) (fun _ _ => False) s :=
  HeapWP.Spec.oom

example : (do
    let _ ← (Result.oom : Result Unit)
    Result.fail .panic : Result Unit) = Result.oom := by
  simp [Result.oom]

example (s : Heap) (Q : Unit → Heap → Prop) :
    ¬ HeapWP.Spec (Result.fail .panic) Q s := by
  simp [HeapWP.Spec.fail]

example (s : Heap) (Q : Unit → Heap → Prop) :
    ¬ HeapWP.Spec (Result.fail .undef) Q s := by
  simp [HeapWP.Spec.fail]

example (s : Heap) (Q : Unit → Heap → Prop) :
    ¬ HeapWP.Spec Result.div Q s := HeapWP.Spec.div

example (s : Heap) :
    HeapWP.Spec (Result.allocatingModify (fun _ (_ : Unit) _ => False))
      (fun _ _ => False) s := by
  apply HeapWP.Spec.allocatingModify.mpr
  exact fun _ _ h => h.elim

example (s : Heap) (Q : Unit → Heap → Prop) :
    ¬ HeapWP.Spec (Result.checkedModify (fun _ (_ : Unit) _ => False)) Q s := by
  intro h
  obtain ⟨_, _, impossible⟩ := (HeapWP.Spec.checkedModify.mp h).1
  exact impossible

example (s : Heap) (Q : Unit → Heap → Prop) :
    ¬ HeapWP.Spec (Result.require False) Q s := by
  intro h
  obtain ⟨_, _, impossible, _⟩ := (HeapWP.Spec.checkedModify.mp h).1
  exact impossible

example (s : Heap) :
    ¬ HeapWP.Spec (Result.allocatingModify (fun start (_ : Bool) stop => stop = start))
      (fun b _ => b = true) s := by
  intro h
  have impossible := HeapWP.Spec.allocatingModify.mp h false s rfl
  cases impossible

def addr (n : Nat) : Usize := ⟨BitVec.ofNat _ n⟩
def byte (n : Nat) : U8 := ⟨BitVec.ofNat _ n⟩
def enc (values : List U8) : List (Vector Byte 1) :=
  values.map fun value => #v[Byte.data value]
def require (condition : Bool) : Option Unit := if condition then some () else none
def shift (p : RawPtr T) (offset : Nat) : RawPtr T :=
  ⟨p.provenance, addr (p.address.val + offset)⟩
def put (p : RawPtr U8) (value : U8) (s : Heap) : Option Heap :=
  Heap.write Repr.u8 p value #v[Byte.data value] rfl s

def nestedSlices : Option (List U8) := do
  let values := (List.range 8).map byte
  let (a, s₀) ← Heap.newBlock Repr.u8 (enc values) true (addr 256) none Heap.empty
  let s₁ ← Heap.borrowRange Repr.u8 a 8 s₀
  let (b, s₂) ← Heap.newBlock Repr.u8 (enc (values.drop 1 |>.take 6))
    false (addr 257) (some a.provenance) s₁
  let s₃ ← Heap.borrowRange Repr.u8 (shift b 1) 4 s₂
  let (c, s₄) ← Heap.newBlock Repr.u8 (enc (values.drop 2 |>.take 4))
    false (addr 258) (some a.provenance) s₃
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
  let (b, s₂) ← Heap.newSharedExposure Repr.u8 data (addr 256) (some a.provenance) s₁
  let s₃ ← Heap.shareRange Repr.u8 b 2 s₂
  let (c, s₄) ← Heap.newSharedExposure Repr.u8 data (addr 256) (some a.provenance) s₃
  require ((Heap.endShareRange Repr.u8 a 2 s₄).isNone &&
    (Heap.newSharedExposure Repr.u8 (enc [byte 9, byte 8])
      (addr 256) (some a.provenance) s₄).isNone &&
    Heap.ptrEq s₄ a b == some true && a.provenance != b.provenance)
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
    (addr 256) (some a.provenance) s₁
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
    target.provenance != replacement.provenance &&
    (Heap.read Repr.u8 target s₆).isNone &&
    Heap.read Repr.u8 replacement s₆ == some (byte 9))

example : pointerStorage = some () := by native_decide

def pointerUpdate : Option Unit := do
  let (a, s₀) ← Heap.newBlock Repr.u8 (enc [byte 7]) true (addr 256) none Heap.empty
  let (b, s₁) ← Heap.newBlock Repr.u8 (enc [byte 9]) true (addr 264) none s₀
  let (slot, s₂) ← Heap.newBlock (Repr.pointer U8) [Repr.pointerEncoding a]
    true (addr 512) none s₁
  let s₃ ← Heap.write (Repr.pointer U8) slot b (Repr.pointerEncoding b) rfl s₂
  let loaded ← Heap.read (Repr.pointer U8) slot s₃
  require (loaded == b && Heap.read Repr.u8 loaded s₃ == some (byte 9))
  let s₄ ← Heap.dealloc Repr.u8 a 1 s₃
  let s₅ ← Heap.write (Repr.pointer U8) slot a (Repr.pointerEncoding a) rfl s₄
  require (Heap.read (Repr.pointer U8) slot s₅ == some a &&
    (Heap.read Repr.u8 a s₅).isNone)

example : pointerUpdate = some () := by native_decide

def laneCoherence : Option Unit := do
  let (a, s₀) ← Heap.newBlock Repr.u8 (enc [byte 7]) true (addr 258) none Heap.empty
  let s₁ ← Heap.share Repr.u8 a s₀
  let (b, s₂) ← Heap.newSharedExposure Repr.u8 (enc [byte 7])
    (addr 258) (some a.provenance) s₁
  let first := Repr.pointerEncoding a
  let mixed := first.set 1 (.pointer (b.cast Unit) 1)
  let same := first.set 1 (.pointer (a.cast Unit) 1)
  require (Heap.ptrEq s₂ a b == some true &&
    (Repr.decodePointer (T := U8) mixed).isNone &&
    Repr.decodePointer (T := U8) same == some a)
  require ((List.range pointerWidth).all fun lane =>
    if h : lane < pointerWidth then
      (Repr.decodePointer (T := U8) (first.set lane .uninit h)).isNone &&
      (Repr.decodePointer (T := U8) (first.set lane (.data (byte 0)) h)).isNone &&
      (Repr.decodePointer (T := U8)
        (first.set lane (.pointer (a.cast Unit) ((lane + 1) % pointerWidth)) h)).isNone
    else false)

example : laneCoherence = some () := by native_decide

def owningReturn : Option Unit := do
  let data := enc [byte 7]
  let (a, s₀) ← Heap.newBlock Repr.u8 data true (addr 256) none Heap.empty
  let s₁ ← Heap.returnOwned Repr.u8 a 1 s₀
  require ((Heap.read Repr.u8 a s₁).isNone && a.address == addr 256 &&
    ((s₁.allocations a.provenance).map Block.alive).getD false)
  let (b, s₂) ← Heap.newBlock Repr.u8 data true (addr 256) (some a.provenance) s₁
  require (b.provenance == a.provenance + 1 && Heap.ptrEq s₂ a b == some true &&
    (Heap.read Repr.u8 a s₂).isNone)
  let s₃ ← Heap.dealloc Repr.u8 b 1 s₂
  require (!((s₃.allocations a.provenance).map Block.alive).getD true &&
    a.address == addr 256 && (Heap.read Repr.u8 b s₃).isNone)
  let (_, _) ← Heap.newBlock Repr.u8 data true (addr 256) none s₃
  some ()

example : owningReturn = some () := by native_decide

/- A foreign-root alias cannot bypass owner cleanup, even while fully borrowed. -/
def rootAndLoanGuards : Option Unit := do
  let (a, s₀) ← Heap.newBlock Repr.u8 (enc [byte 7]) true (addr 256) none Heap.empty
  let s₁ ← Heap.borrow Repr.u8 a s₀
  require ((Heap.newBlock Repr.u8 (enc [byte 7]) false (addr 256) none s₁).isNone)
  let (b, s₂) ← Heap.newBlock Repr.u8 (enc [byte 7])
    false (addr 256) (some a.provenance) s₁
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
      false (addr 256) (some a.provenance) s₁
    let s₃ ← Heap.borrow Repr.u8 ⟨1, addr 256⟩ s₂
    let s₄ ← Heap.endBorrow Repr.u8 a #v[Byte.data (byte 7)] s₃
    Heap.read Repr.u8 a s₄) = some (byte 7) := by native_decide

def padded : Repr U8 where
  size := 2
  align := ⟨2, ⟨1, rfl⟩⟩
  decode := fun bytes => bytes[0].numeric
  encode := fun value bytes =>
    bytes[0] = .data value ∧
      (bytes[1] = .uninit ∨ ∃ padding : U8, bytes[1] = .data padding)
  aligned := by decide
  encode_complete := fun value => ⟨#v[Byte.data value, Byte.uninit], rfl, Or.inl rfl⟩
  encode_decode := by
    intro value bytes h
    simp [h.1, Byte.numeric]
  decode_mono := by
    intro bytes bytes' value decoded agree
    have initialized : bytes[0] ≠ .uninit := by
      intro he
      simp [he, Byte.numeric] at decoded
    change bytes'[0].numeric = some value
    rw [agree ⟨0, by decide⟩ initialized]
    exact decoded
  encode_valid := by
    intro value bytes i h
    obtain ⟨h0, h1⟩ := h
    have hi : i.val = 0 ∨ i.val = 1 := by grind
    rcases hi with hi | hi
    · simp [hi, h0]
    · rcases h1 with h1 | ⟨padding, h1⟩
      · simp [hi, h1]
      · simp [hi, h1]

theorem padded_noPointers (value : U8) (p : RawPtr Unit) :
    ¬ padded.Carries value p := by
  rintro ⟨bytes, ⟨h0, h1⟩, i, lane, hp⟩
  have bound : i.val < 2 := i.isLt
  have hi : i.val = 0 ∨ i.val = 1 := by grind
  rcases hi with hi | hi
  · simp only [hi] at hp
    have impossible := h0.symm.trans hp
    cases impossible
  · rcases h1 with h1 | ⟨padding, h1⟩
    · simp only [hi] at hp
      have impossible := h1.symm.trans hp
      cases impossible
    · simp only [hi] at hp
      have impossible := h1.symm.trans hp
      cases impossible

example (value : U8) (replacement : Byte) :
    padded.decode #v[Byte.data value, replacement] = some value := by
  exact padded.decode_set_uninit #v[Byte.data value, Byte.uninit] value
    ⟨1, by decide⟩ replacement rfl rfl

example :
    padded.read #v[Cell.shared 0 (.data (byte 7)), Cell.borrowed] 0 = none := by native_decide

def jointChoice : Option Unit := do
  let data := [#v[Byte.data (byte 7), Byte.data (byte 0)]]
  let (a, s₀) ← Heap.newBlock padded data true (addr 256) none Heap.empty
  let s₁ ← Heap.shareRange padded a 1 s₀
  require ((Heap.newSharedExposure padded [#v[Byte.data (byte 7), Byte.data (byte 1)]]
    (addr 256) (some a.provenance) s₁).isNone)
  let (_, s₂) ← Heap.newSharedExposure padded data (addr 256) (some a.provenance) s₁
  require (s₂.check)

example : jointChoice = some () := by native_decide

example (p : RawPtr U8) (bptr : BasePtr) (old value : U8) :
    HeapWP.Triple (SepLogic.pointsTo padded p bptr old)
      (do
        let _ ← MutRawPtr.write padded p value
        RawPtr.read padded p)
      (fun result h => result = value ∧ SepLogic.pointsTo padded p bptr value 0 h) := by
  apply HeapWP.Triple.bind
    (HeapWP.write.spec padded p bptr old value (padded_noPointers value) (by decide))
  intro _
  exact HeapWP.read.spec padded p bptr value 0 (by decide)

example (slot : RawPtr (RawPtr U8)) (slotAddress : BasePtr) (old target : RawPtr U8)
    (targetAddress : BasePtr) (count : Nat) :
    HeapWP.Triple
      (SepLogic.sep (SepLogic.pointsTo (Repr.pointer U8) slot slotAddress old)
        (SepLogic.alloc Repr.u8 target targetAddress count true))
      (MutRawPtr.write (Repr.pointer U8) slot target)
      (fun _ => SepLogic.sep (SepLogic.pointsTo (Repr.pointer U8) slot slotAddress target)
        (SepLogic.alloc Repr.u8 target targetAddress count true)) :=
  HeapWP.write_supported.spec (Repr.pointer U8) slot slotAddress old target _
    (fun _ ha => SepLogic.supportsValue_pointer_alloc Repr.u8 target targetAddress
      count true ha) (by decide)

theorem initialize_padded (p : RawPtr U8) (bptr : BasePtr) (value : U8) :
    HeapWP.Triple
      (SepLogic.block padded p bptr (List.replicate padded.size (.shared 0 .uninit)))
      (do MutRawPtr.write padded p value; RawPtr.read padded p)
      (fun result h => result = value ∧ SepLogic.pointsTo padded p bptr value 0 h) := by
  apply HeapWP.Triple.bind
    (HeapWP.write_uninitialized.spec padded p bptr value (padded_noPointers value) (by decide))
  intro _
  exact HeapWP.read.spec padded p bptr value 0 (by decide)

/-- A safe update returns through its matching backward computation before
the next raw read. Ignored padding remains outside the client's obligations. -/
theorem borrow_update_read (p : RawPtr U8) (bptr : BasePtr) (initial replacement : U8) :
    HeapWP.Triple (SepLogic.pointsTo padded p bptr initial)
      (do
        let before ← RawPtr.withBorrow padded p (fun _ => replacement)
        let after ← RawPtr.read padded p
        pure (before, after))
      (fun result h => result = (initial, replacement) ∧
        SepLogic.pointsTo padded p bptr replacement 0 h) := by
  apply HeapWP.Triple.bind
    (HeapWP.withBorrow.spec padded p bptr initial (fun _ => replacement)
      (padded_noPointers replacement) (by decide))
  intro before
  apply HeapWP.Triple.pure_pre
  intro before_eq
  subst before
  apply HeapWP.Triple.bind (HeapWP.read.spec padded p bptr replacement 0 (by decide))
  intro after
  apply HeapWP.Triple.pure_pre
  intro after_eq
  subst after
  exact HeapWP.Triple.pure _ (initial, replacement)

theorem read_borrow_padded_range (p : RawPtr U8) (bptr : BasePtr)
    (values : Vector U8 2) :
    HeapWP.Triple (SepLogic.pointsToRange padded p bptr values)
      (do
        let observed ← RawPtr.readRange padded p 2
        let borrowed ← RawPtr.borrowRange padded p 2
        pure (observed, borrowed))
      (fun (observed, borrowed) h => observed = values.toList ∧ borrowed = values.toList ∧
        SepLogic.block padded p bptr (List.replicate (2 * padded.size) .borrowed) h) := by
  apply HeapWP.Triple.bind (HeapWP.readRange.spec padded p bptr values 0 (by decide) (by decide))
  intro observed
  apply HeapWP.Triple.pure_pre
  intro he
  subst observed
  apply HeapWP.Triple.bind (HeapWP.borrowRange.spec padded p bptr values (by decide) (by decide))
  intro borrowed
  apply HeapWP.Triple.pure_pre
  intro he
  subst borrowed
  apply HeapWP.Triple.conseq (fun _ hp => hp) ?_
    (HeapWP.Triple.pure _ (values.toList, values.toList))
  rintro _ _ ⟨rfl, hp⟩
  exact ⟨rfl, rfl, hp⟩

theorem nested_range_shares (p : RawPtr U8) (bptr : BasePtr) (values : Vector U8 2) :
    HeapWP.Triple (SepLogic.pointsToRange padded p bptr values 1)
      (do
        let _ ← RawPtr.shareRange padded p 2
        RawPtr.endShareRange padded p values.toList
        RawPtr.readRange padded p 2)
      (fun result h => result = values.toList ∧ SepLogic.pointsToRange padded p bptr values 1 h) := by
  apply HeapWP.Triple.bind (HeapWP.shareRange.spec padded p bptr values 1 (by decide) (by decide))
  intro _
  apply HeapWP.Triple.pure_pre
  intro _
  apply HeapWP.Triple.bind
    (HeapWP.endShareRange.spec padded p bptr values 1 (by decide) (by decide) (by decide))
  intro _
  exact HeapWP.readRange.spec padded p bptr values 1 (by decide) (by decide)

theorem framed_range_read (p : RawPtr U8) (bptr : BasePtr) (values : Vector U8 2)
    (R : SepLogic.Assertion) :
    HeapWP.Triple (SepLogic.sep (SepLogic.pointsToRange padded p bptr values) R)
      (RawPtr.readRange padded p 2)
      (fun result => SepLogic.sep
        (fun h => result = values.toList ∧ SepLogic.pointsToRange padded p bptr values 0 h) R) :=
  HeapWP.frame (HeapWP.readRange.spec padded p bptr values 0 (by decide) (by decide))

theorem swap_then_read (repr : Repr T) (p q : RawPtr T) (a b : BasePtr)
    (left right : T) (hsize : 0 < repr.size) :
    HeapWP.Triple
      (SepLogic.sep (SepLogic.pointsTo repr p a left) (SepLogic.pointsTo repr q b right))
      (do RawPtr.swap repr p q; RawPtr.read repr p)
      (fun result h => result = right ∧
        SepLogic.sep (SepLogic.pointsTo repr p a right) (SepLogic.pointsTo repr q b left) h) := by
  apply HeapWP.Triple.bind (HeapWP.swap.spec repr p q a b left right hsize)
  intro _
  exact HeapWP.Triple.conseq (fun _ hp => hp)
    (fun result h hp => (SepLogic.sep_and_left (result = right) _ _ h).mp hp)
    (HeapWP.frame (HeapWP.read.spec repr p a right 0 hsize))

theorem self_swap_then_read (p : RawPtr (RawPtr U8)) (bptr : BasePtr) (target : RawPtr U8) :
    HeapWP.Triple (SepLogic.pointsTo (Repr.pointer U8) p bptr target)
      (do RawPtr.swap (Repr.pointer U8) p p; RawPtr.read (Repr.pointer U8) p)
      (fun result h => result = target ∧
        SepLogic.pointsTo (Repr.pointer U8) p bptr target 0 h) := by
  apply HeapWP.Triple.bind (HeapWP.swap_same.spec (Repr.pointer U8) p bptr target (by decide))
  intro _
  exact HeapWP.read.spec (Repr.pointer U8) p bptr target 0 (by decide)

example (p : RawPtr U8) (bptr : BasePtr) (value : U8) (R : SepLogic.Assertion) :
    HeapWP.Triple (SepLogic.sep (SepLogic.pointsTo padded p bptr value) R)
      (do
        let _ ← RawPtr.shareRange padded p 1
        RawPtr.read padded p)
      (fun result => SepLogic.sep
        (fun h => result = value ∧ SepLogic.pointsTo padded p bptr value 1 h) R) := by
  apply HeapWP.Triple.bind (HeapWP.frame
    (HeapWP.shareRange_single.spec padded p bptr value 0 (by decide)))
  intro values
  apply HeapWP.Triple.conseq ?_ (fun _ _ hp => hp)
    (HeapWP.frame (HeapWP.read.spec padded p bptr value 1 (by decide)))
  rintro h ⟨a, b, hd, he, hq, hr⟩
  exact ⟨a, b, hd, he, hq.2, hr⟩

example (p : RawPtr U8) (bptr : BasePtr) (value : U8) :
    HeapWP.Triple (SepLogic.pointsTo padded p bptr value)
      (do
        let values ← RawPtr.readRange padded p 1
        let borrowed ← RawPtr.borrow padded p
        pure (values, borrowed))
      (fun (values, borrowed) h => values = [value] ∧ borrowed = value ∧
        SepLogic.block padded p bptr (Vector.replicate padded.size .borrowed).toList h) := by
  apply HeapWP.Triple.bind (HeapWP.readRange_single.spec padded p bptr value 0 (by decide))
  intro values
  apply HeapWP.Triple.pure_pre
  intro hvalues
  subst values
  apply HeapWP.Triple.bind (HeapWP.borrow.spec padded p bptr value (by decide))
  intro borrowed
  apply HeapWP.Triple.pure_pre
  intro hborrowed
  subst borrowed
  apply HeapWP.Triple.conseq (fun _ hp => hp) ?_ (HeapWP.Triple.pure _ ([value], value))
  rintro _ h ⟨rfl, hp⟩
  exact ⟨rfl, rfl, hp⟩

def uninitializedPadding : Option Unit := do
  let data := #v[Byte.data (byte 7), Byte.uninit]
  let (p, s₀) ← Heap.newBlock padded [data] true (addr 256) none Heap.empty
  require (Heap.read padded p s₀ == some (byte 7) &&
    (Heap.read Repr.u8 (shift p 1) s₀).isNone)
  let s₁ ← Heap.share padded p s₀
  let (reader, s₂) ← Heap.newSharedExposure padded [data] (addr 256) (some p.provenance) s₁
  require (Heap.read padded reader s₂ == some (byte 7))
  let (bad, s₃) ← Heap.newBlock padded [#v[Byte.uninit, Byte.data (byte 7)]]
    true (addr 512) none s₂
  require ((Heap.read padded bad s₃).isNone)
  let s₄ ← Heap.copyBytes reader bad 2 s₃
  require (Heap.read padded bad s₄ == some (byte 7) &&
    (Heap.read Repr.u8 (shift bad 1) s₄).isNone)
  let s₅ ← Heap.borrow padded bad s₄
  require ((Heap.read padded bad s₅).isNone)

example : uninitializedPadding = some () := by native_decide

example : padded.encode (byte 7) #v[Byte.data (byte 7), Byte.uninit] :=
  ⟨rfl, .inl rfl⟩

example : State.exposes padded Heap.empty 256 (byte 7)
    #v[Byte.data (byte 7), Byte.uninit] := by
  refine ⟨rfl, ?_⟩
  intro i
  change Fin 2 at i
  have hi : i.val = 0 ∨ i.val = 1 := by grind
  rcases hi with hi | hi
  · simp only [hi]
    trivial
  · simp only [hi]
    trivial

def alignmentAndBounds : Option Unit := do
  let (a, s₀) ← Heap.newBlock Repr.u8 (enc ([0, 1, 2, 3].map byte))
    true (addr 256) none Heap.empty
  let s₁ ← Heap.borrowRange Repr.u8 a 4 s₀
  let (b, s₂) ← Heap.newBlock Repr.u8 (enc ([1, 2, 3].map byte))
    false (addr 257) (some a.provenance) s₁
  require ((Heap.read padded (b.cast U8) s₂).isNone &&
    Heap.read padded (shift b 1) s₂ == some (byte 2) &&
    Heap.distance Repr.u8 (shift b 1) a s₂ == some 2)
  let finish ← Heap.offset Repr.u8 b 3 s₂
  require (finish.address == addr 260 &&
    (Heap.read Repr.u8 finish s₂).isNone &&
    (Heap.offset Repr.u8 finish 1 s₂).isNone &&
    (Heap.offset Repr.u8 b (-1) s₂).isNone &&
    (Heap.alloc Repr.u8 2 (addr (2 ^ UScalarTy.numBits .Usize - 2)) Heap.empty).isNone)

example : alignmentAndBounds = some () := by native_decide

/-- A formatter returns its mutable view, then re-exposes the same storage.
    Subtraction needs the surviving allocation, not permission to read the old view. -/
def retiredViewArithmetic : Option Unit := do
  let data := [#v[Byte.data (byte 49)], #v[Byte.data (byte 50)],
    #v[Byte.data (byte 51)], #v[Byte.uninit]]
  let (writer, s₀) ← Heap.newBlock Repr.u8 data false (addr 256) none Heap.empty
  let finish ← Heap.offset Repr.u8 writer 3 s₀
  let s₁ ← Heap.endExposureAt Repr.u8 writer 4 0 s₀
  let (origin, s₂) ← Heap.newSharedExposure Repr.u8 data
    (addr 256) (some writer.provenance) s₁
  require (writer.provenance != origin.provenance &&
    writer.address == origin.address &&
    Heap.distance Repr.u8 finish origin s₂ == some 3 &&
    Heap.offset Repr.u8 writer 3 s₂ == some finish &&
    (Heap.read Repr.u8 writer s₂).isNone &&
    (put writer (byte 9) s₂).isNone &&
    (Heap.distance padded (shift writer 1) origin s₂).isNone &&
    (Heap.distance Repr.u8 (shift writer 5) origin s₂).isNone &&
    (Heap.distance Repr.u8 ⟨999, writer.address⟩ origin s₂).isNone)
  let (reader, s₃) ← Heap.newSharedExposure Repr.u8 data
    (addr 256) (some writer.provenance) s₂
  let s₄ ← Heap.shareRange Repr.u8 reader 3 s₃
  require (Heap.readRange Repr.u8 reader 3 s₄ == some ([49, 50, 51].map byte) &&
    (Heap.readRange Repr.u8 reader 4 s₄).isNone)
  let s₅ ← Heap.endShareRange Repr.u8 reader 3 s₄
  let s₆ ← Heap.endSharedExposure Repr.u8 reader 4 s₅
  let s₇ ← Heap.endSharedExposure Repr.u8 origin 4 s₆
  let (adjacent, s₈) ← Heap.alloc Repr.u8 4 (addr 260) s₇
  require ((Heap.distance Repr.u8 (shift writer 4) adjacent s₈).isNone)

example : retiredViewArithmetic = some () := by native_decide

def deadAllocationArithmetic : Option Unit := do
  let (old, s₀) ← Heap.alloc Repr.u8 4 (addr 256) Heap.empty
  let s₁ ← Heap.dealloc Repr.u8 old 4 s₀
  let (fresh, s₂) ← Heap.alloc Repr.u8 4 (addr 256) s₁
  require (old.address == fresh.address &&
    (Heap.offset Repr.u8 old 1 s₂).isNone &&
    (Heap.distance Repr.u8 old old s₂).isNone &&
    (Heap.distance Repr.u8 old fresh s₂).isNone)

example : deadAllocationArithmetic = some () := by native_decide

def concreteAddressBounds : Option Unit := do
  let (p, s₀) ← Heap.newBlock Repr.u8 (enc [byte 7, byte 8])
    true (addr 256) none Heap.empty
  let before : RawPtr U8 := ⟨p.provenance, addr 255⟩
  let past : RawPtr U8 := ⟨p.provenance, addr 258⟩
  let outside : RawPtr U8 := ⟨p.provenance, addr 259⟩
  require ((Heap.read Repr.u8 before s₀).isNone &&
    (put before (byte 9) s₀).isNone &&
    (Heap.borrowRange Repr.u8 before 0 s₀).isNone &&
    (Heap.readRange Repr.u8 before 0 s₀).isNone &&
    (Heap.copyBytes before p 0 s₀).isNone &&
    (Heap.copyBytes p before 0 s₀).isNone &&
    (Heap.swapBytes Repr.u8 before p s₀).isNone &&
    (Heap.offset Repr.u8 before 1 s₀).isNone &&
    (Heap.distance Repr.u8 before p s₀).isNone &&
    (Heap.read Repr.u8 past s₀).isNone &&
    Heap.readRange Repr.u8 past 0 s₀ == some [] &&
    Heap.offset Repr.u8 past (-1) s₀ == some (shift p 1) &&
    (Heap.offset Repr.u8 past 1 s₀).isNone &&
    (Heap.offset Repr.u8 outside (-1) s₀).isNone &&
    (Heap.offset Repr.u8 p (2 ^ 64) s₀).isNone)
  let invalidView : RawPtr U8 := ⟨999, p.address⟩
  require (Heap.ptrEq s₀ p invalidView == some true &&
    (Heap.read Repr.u8 invalidView s₀).isNone &&
    Repr.u8.decode #v[Byte.pointer (invalidView.cast Unit) 0] == some (byte 0))

example : concreteAddressBounds = some () := by native_decide

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
    ((s₄.cells destination.provenance).getD []).all (fun c => c == .shared 0 .uninit))

example : copyInitializationAndAtomicity = some () := by native_decide

def pointerLoanTarget : RawPtr U8 := ⟨0, addr 258⟩
def pointerLoanSlot : Block :=
  ⟨addr 512, 1, (Repr.pointerEncoding pointerLoanTarget).toList.map (Cell.shared 1),
    true, true, true⟩
def pointerLoanHeap : Heap :=
  ⟨fun id => if id = 0 then
      some ⟨addr 258, 0, [.shared 0 (.data (byte 7))], true, true, true⟩
    else if id = 1 then some pointerLoanSlot else none, 2⟩
def pointerLoanAlias : RawPtr U8 := ⟨2, addr 512⟩
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
      change _ ∨ _
      refine .inr ?_
      exact ⟨1, pointerLoanSlot, 0, 1, rfl, by native_decide, rfl, rfl⟩
  · have hv : pointerLoanResult.check = true := by native_decide
    have ha : Repr.u8.align.val ∣ (addr 512).val := Nat.one_dvd _
    unfold Heap.newSharedExposure
    rw [ite_eq_left ha]
    unfold Heap.createRepr
    change ((Heap.commit pointerLoanResult).map (fun s => (2, s))).map
      (fun (id, s) => (⟨id, addr 512⟩, s)) = some (pointerLoanAlias, pointerLoanResult)
    rw [Heap.commit, ite_eq_left hv]
    rfl

/-- Typed scalar writes still cannot encode the pointer fragment just exposed. -/
theorem pointerLane_not_scalar : ¬ Repr.u8.encode (byte 2) pointerLoanBytes := by
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
    (Heap.borrowRange Repr.u8 ⟨1, addr 512⟩ 1 pointerMutableLoanHeap).isSome = true := by
  native_decide

example : ¬ State.mutableValues Repr.u8 ⟨1, addr 512⟩ [byte 2] pointerMutableLoanHeap := by
  rintro ⟨blk, hb, values⟩
  have he : blk = pointerMutableLoanSlot := by
    simpa [pointerMutableLoanHeap, update] using hb.symm
  subst blk
  obtain ⟨bytes, bounds, hread, encoded⟩ := values 0 (by decide)
  have hselect : Repr.u8.select pointerMutableLoanSlot.bytes
      ((⟨1, addr 512⟩ : RawPtr U8).offsetFrom pointerMutableLoanSlot.bptr +
        0 * Repr.u8.size) bounds =
      pointerLoanBytes.map (Cell.shared 0) := by
    apply Vector.toList_inj.mp
    rw [Repr.select_toList]
    native_decide
  have hr : Repr.readBytes 1
      (Repr.u8.select pointerMutableLoanSlot.bytes
        ((⟨1, addr 512⟩ : RawPtr U8).offsetFrom pointerMutableLoanSlot.bptr +
          0 * Repr.u8.size) bounds) =
        some pointerLoanBytes := by
    rw [hselect]
    exact Repr.readBytes_shared pointerLoanBytes 0
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

def framedWriter : RawPtr U8 := ⟨1, addr 256⟩
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
  have ha : Repr.u8.align.val ∣ framedWriter.address.val :=
    Nat.one_dvd _
  have contract := SepLogic.write.spec Repr.u8 framedWriter (addr 256)
    #v[Byte.data (byte 7)] (byte 9) (Repr.u8_noPointers _) (by decide)
  let h := SepLogic.cellsHeap (addr 256) 1 0 [.shared 0 (.data (byte 7))]
  let F := SepLogic.cellsHeap (addr 256) 0 0 [.borrowed]
  have hp : SepLogic.block Repr.u8 framedWriter (addr 256)
      ((#v[Byte.data (byte 7)]).map (Cell.shared 0)).toList h := by
    refine ⟨by native_decide, ha, ?_⟩
    simp [h, framedWriter, RawPtr.offsetFrom]
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
  have run := HeapWP.Triple.checkedModify contract h F framedWriterHeap hp hd hm hinv
  apply HeapWP.Spec.mono run
  rintro _ s' ⟨h', _, hm', _, hp'⟩
  have parts := SepLogic.Fragment.matches_union _ _ _ |>.mp hm'
  exact ⟨parts.2, SepLogic.read_of_pointsTo (by decide) hp' parts.1⟩

#print axioms Heap.createRepr_Inv
#print axioms Heap.modify_Inv
#print axioms Heap.validByte_storeRepr
#print axioms Heap.update_Inv
#print axioms Repr.pointer_roundTrip
#print axioms Repr.pointer_decode_iff
#print axioms Repr.decode_set_uninit
#print axioms Repr.u8_write_data
#print axioms Repr.encoding_no_forgery
#print axioms Heap.compatible_writer_excludes
#print axioms SepLogic.Resource.Holds.overlapCompatible
#print axioms initialize_padded
#print axioms HeapWP.borrowWithBack.spec
#print axioms borrow_update_read
#print axioms read_borrow_padded_range
#print axioms nested_range_shares
#print axioms framed_range_read
#print axioms swap_then_read
#print axioms self_swap_then_read
#print axioms HeapWP.endBorrowRange.spec
#print axioms SepLogic.Resource.Holds.noAliases_unique
#print axioms SepLogic.write.spec
#print axioms SepLogic.endBorrow.spec
#print axioms SepLogic.createRepr.spec
#print axioms HeapWP.TripleAt.checkedModify

/-- info: 'Aeneas.Std.Heap.Inv.same_root_of_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Heap.Inv.same_root_of_overlap

/-- info: 'Aeneas.Std.HeapWP.offset_from_reexposed.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HeapWP.offset_from_reexposed.spec

end Aeneas.Std.HeapTests
