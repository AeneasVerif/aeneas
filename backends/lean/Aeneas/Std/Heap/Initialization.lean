module

public import Aeneas.Std.Heap.EffectSpecs
import all Aeneas.Std.Core.Ptr

/-! Initialization requires writable bytes, not a pre-existing typed value. -/

@[expose] public section

namespace Aeneas.Std.HeapWP

/-- Writing does not read or require validity of the previous contents. -/
theorem write_writable.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (old : Vector Byte repr.size) (value : T)
    (noPointers : ∀ q, ¬ repr.Carries value q) (hsize : 0 < repr.size) :
    Triple (SepLogic.block repr p bptr (old.map (Cell.shared 0)).toList)
      (MutRawPtr.write repr p value) (fun _ => SepLogic.pointsTo repr p bptr value) :=
  Triple.checkedModify (SepLogic.write.spec repr p bptr old value noPointers hsize)

/-- Pointer initialization uses local provenance support, just like replacement. -/
theorem write_writable_supported.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (old : Vector Byte repr.size) (value : T) (R : SepLogic.Assertion)
    (support : ∀ h, R h → SepLogic.SupportsValue repr value h) (hsize : 0 < repr.size) :
    Triple (SepLogic.sep (SepLogic.block repr p bptr (old.map (Cell.shared 0)).toList) R)
      (MutRawPtr.write repr p value) (fun _ => SepLogic.sep (SepLogic.pointsTo repr p bptr value) R) :=
  Triple.checkedModify (SepLogic.write_supported.spec repr p bptr old value R support hsize)

/-- The first typed write initializes a wholly uninitialized footprint. -/
theorem write_uninitialized.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (value : T) (noPointers : ∀ q, ¬ repr.Carries value q) (hsize : 0 < repr.size) :
    Triple (SepLogic.block repr p bptr (List.replicate repr.size (.shared 0 .uninit)))
      (MutRawPtr.write repr p value) (fun _ => SepLogic.pointsTo repr p bptr value) := by
  simpa using write_writable.spec repr p bptr (Vector.replicate repr.size .uninit)
    value noPointers hsize

end Aeneas.Std.HeapWP
