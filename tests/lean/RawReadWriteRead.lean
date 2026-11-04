/- Extracted by Aeneas, then adapted to explicit representations and corrected to retain reads after writes.
   The compiler is not patched. Re-extraction overwrites these corrections;
   see EXTRACTION.md. -/
-- [raw_read_write_read]
module
public import Aeneas
public import Aeneas.Std.Heap.EffectSpecs
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.internalConstructors false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048

namespace raw_read_write_read

/-- [raw_read_write_read::read_write_read]:
    Source: 'tests/src/raw_read_write_read.rs', lines 5:0-9:1
    Visibility: public -/
def read_write_read (repr : Aeneas.Std.Repr Std.U32)
    (p : MutRawPtr Std.U32) : Result (Std.U32 × Std.U32) := do
  let before ← RawPtr.read repr p
  MutRawPtr.write repr p 1#u32
  let after ← RawPtr.read repr p
  ok (before, after)

/-- [raw_read_write_read::discarded_read]:
    Source: 'tests/src/raw_read_write_read.rs', lines 13:0-17:1
    Visibility: public -/
def discarded_read (repr : Aeneas.Std.Repr Std.U32) (p : MutRawPtr Std.U32) : Result Std.U32 := do
  let _ ← RawPtr.read repr p
  MutRawPtr.write repr p 1#u32
  RawPtr.read repr p

/-- Both reads observe their own point in the effect sequence. -/
theorem read_write_read.spec (repr : Aeneas.Std.Repr U32) (p : MutRawPtr U32)
    (bptr : BasePtr) (initial : U32)
    (noPointers : ∀ q, ¬ repr.Carries 1#u32 q) (hsize : 0 < repr.size) :
    HeapWP.Triple (SepLogic.pointsTo repr p bptr initial) (read_write_read repr p)
      (fun result h => result = (initial, 1#u32) ∧ SepLogic.pointsTo repr p bptr 1#u32 0 h) := by
  unfold read_write_read
  apply HeapWP.Triple.bind (HeapWP.read.spec repr p bptr initial 0 hsize)
  intro before
  apply HeapWP.Triple.pure_pre
  intro hbefore
  subst before
  apply HeapWP.Triple.bind (HeapWP.write.spec repr p bptr initial 1#u32 noPointers hsize)
  intro _
  apply HeapWP.Triple.bind (HeapWP.read.spec repr p bptr 1#u32 0 hsize)
  intro after
  apply HeapWP.Triple.pure_pre
  intro hafter
  subst after
  exact HeapWP.Triple.pure (SepLogic.pointsTo repr p bptr 1#u32) (initial, 1#u32)

/-- A discarded read cannot be reused across a write. -/
theorem discarded_read.spec (repr : Aeneas.Std.Repr U32) (p : MutRawPtr U32)
    (bptr : BasePtr) (initial : U32)
    (noPointers : ∀ q, ¬ repr.Carries 1#u32 q) (hsize : 0 < repr.size) :
    HeapWP.Triple (SepLogic.pointsTo repr p bptr initial) (discarded_read repr p)
      (fun result h => result = 1#u32 ∧ SepLogic.pointsTo repr p bptr 1#u32 0 h) := by
  unfold discarded_read
  apply HeapWP.Triple.bind (HeapWP.read.spec repr p bptr initial 0 hsize)
  intro _
  apply HeapWP.Triple.pure_pre
  intro _
  apply HeapWP.Triple.bind (HeapWP.write.spec repr p bptr initial 1#u32 noPointers hsize)
  intro _
  exact HeapWP.read.spec repr p bptr 1#u32 0 hsize

/-- info: 'raw_read_write_read.read_write_read.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms read_write_read.spec

/-- info: 'raw_read_write_read.discarded_read.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms discarded_read.spec

end raw_read_write_read
