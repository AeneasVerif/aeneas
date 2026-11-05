module

public import RawRyuMwe.Memory

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic scalar_mwe
open scoped Aeneas.Std.HeapWP

namespace raw_ryu_mwe

def out_parameters (a b : U64) (first second : RawPtr U64) : Result Unit := do
  MutRawPtr.write u64Repr first a
  MutRawPtr.write u64Repr second b

/-- **Spec theorem for `raw_ryu_mwe::out_parameters`**
    Both out-parameters are initialized without reading their previous bytes. -/
@[step]
theorem out_parameters.spec (a b : U64) (first second : RawPtr U64)
    (firstBase secondBase : BasePtr) (oldFirst oldSecond : Vector Aeneas.Std.Byte 8) :
    ⦃ block u64Repr first firstBase (oldFirst.map (Cell.shared 0)).toList ∗
      block u64Repr second secondBase (oldSecond.map (Cell.shared 0)).toList ⦄
    out_parameters a b first second
    ⦃ _ => pointsTo u64Repr first firstBase a ∗ pointsTo u64Repr second secondBase b ⦄ := by
  unfold out_parameters
  apply HeapWP.Triple.bind (HeapWP.frame
    (HeapWP.write_writable.spec u64Repr first firstBase oldFirst a (u64_noPointers a) (by decide)))
  intro _
  exact HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ h hp => (sep_comm _ _ h).mp hp)
    (HeapWP.frame (HeapWP.write_writable.spec u64Repr second secondBase oldSecond b
      (u64_noPointers b) (by decide)))

/- The two local MaybeUninit slots are explicit resident storage parameters.
   `assume_init` reads their initialized representations; it is not an axiom.
   Stack allocation and scope retirement remain outside this raw-tail boundary. -/
def initialized_outputs (a b : U64) (first second : RawPtr U64) : Result (U64 × U64) := do
  out_parameters a b first second
  let x ← RawPtr.read u64Repr first
  let y ← RawPtr.read u64Repr second
  pure (x, y)

/-- **Spec theorem for `raw_ryu_mwe::initialized_outputs`**
    The resident-slot adaptation returns exactly the two supplied values. -/
@[step]
theorem initialized_outputs.spec (a b : U64) (first second : RawPtr U64)
    (firstBase secondBase : BasePtr) (oldFirst oldSecond : Vector Aeneas.Std.Byte 8) :
    ⦃ block u64Repr first firstBase (oldFirst.map (Cell.shared 0)).toList ∗
      block u64Repr second secondBase (oldSecond.map (Cell.shared 0)).toList ⦄
    initialized_outputs a b first second
    ⦃ (x : U64) (y : U64) => fun h =>
      x = a ∧ y = b ∧
      (pointsTo u64Repr first firstBase a ∗ pointsTo u64Repr second secondBase b) h ⦄ := by
  unfold initialized_outputs
  apply HeapWP.Triple.bind (out_parameters.spec a b first second firstBase secondBase oldFirst oldSecond)
  intro _
  apply HeapWP.Triple.bind (HeapWP.frame_value (HeapWP.read.spec u64Repr first firstBase a 0 (by decide)))
  intro x
  apply HeapWP.Triple.pure_pre
  intro hx
  subst x
  have secondRead : HeapWP.Triple
      (pointsTo u64Repr first firstBase a ∗ pointsTo u64Repr second secondBase b)
      (RawPtr.read u64Repr second)
      (fun y h => y = b ∧
        (pointsTo u64Repr first firstBase a ∗ pointsTo u64Repr second secondBase b) h) :=
    HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ h hp => ⟨hp.1, (sep_comm _ _ h).mp hp.2⟩)
    (HeapWP.frame_value (HeapWP.read.spec u64Repr second secondBase b 0 (by decide)))
  apply HeapWP.Triple.bind secondRead
  intro y
  apply HeapWP.Triple.pure_pre
  intro hy
  subst y
  apply HeapWP.Triple.conseq (fun _ hp => hp) _ (HeapWP.Triple.pure _ (a, b))
  rintro _ h ⟨rfl, hp⟩
  exact ⟨rfl, rfl, hp⟩

end raw_ryu_mwe
