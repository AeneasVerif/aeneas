module

public import Aeneas.Std.Heap.EffectSpecs
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Heap.Repr

/-! Initialization requires writable bytes, not a pre-existing typed value. -/

@[expose] public section

namespace Aeneas.Std.SepLogic

/-- Every chosen valid encoding initializes an arbitrary writable footprint. -/
theorem write_writable_encoding.spec (repr : Repr T) (p : RawPtr T)
    (old : Vector (Option U8) repr.size) (value : T)
    (data : Vector U8 repr.size) (decoded : repr.decode data = some value)
    (hsize : 0 < repr.size) :
    Triple (block repr p (old.map (Cell.shared 0)).toList)
      (fun s (_ : Unit) s' => Heap.write repr p value data decoded s = some s')
      (fun _ => pointsTo repr p value) := by
  apply Triple.conseq (fun _ h => h) (fun _ _ h => ⟨data, decoded, h⟩)
  apply modify.spec repr p _ (data.map (Cell.shared 0 ∘ some)) _ hsize
  intro r contents hb he
  simp [Repr.write, hsize, hb, he, Repr.writeBytes_shared]

end Aeneas.Std.SepLogic

namespace Aeneas.Std.HeapWP

/-- Writing does not read or require validity of the previous contents. -/
theorem write_writable.spec (repr : Repr T) (p : RawPtr T)
    (old : Vector (Option U8) repr.size) (value : T) (hsize : 0 < repr.size) :
    Triple (SepLogic.block repr p (old.map (Cell.shared 0)).toList)
      (MutRawPtr.write repr p value) (fun _ => SepLogic.pointsTo repr p value) := by
  unfold MutRawPtr.write
  apply Triple.bind (Triple.choose _ repr value)
  intro data
  exact Triple.checkedModify
    (SepLogic.write_writable_encoding.spec repr p old value data.val data.property hsize)

/-- The first typed write initializes a wholly uninitialized footprint. -/
theorem write_uninitialized.spec (repr : Repr T) (p : RawPtr T)
    (value : T) (hsize : 0 < repr.size) :
    Triple (SepLogic.block repr p (List.replicate repr.size (.shared 0 none)))
      (MutRawPtr.write repr p value) (fun _ => SepLogic.pointsTo repr p value) := by
  simpa using write_writable.spec repr p (Vector.replicate repr.size none) value hsize

end Aeneas.Std.HeapWP
