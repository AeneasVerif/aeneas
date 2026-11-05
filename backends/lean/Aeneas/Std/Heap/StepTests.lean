module

import Aeneas.Std.Heap.Step
import Aeneas.Std.Heap.EffectSpecs
import Aeneas.Std.Heap.SliceExposure

open Aeneas Aeneas.Std Aeneas.Std.SepLogic
open scoped Aeneas.Std.HeapWP

namespace Aeneas.Std.HeapWP.Tests

/- The actual effect contracts are indexed directly, not copied into a second WP. -/
attribute [local step] HeapWP.read_exposed.spec HeapWP.write_readable.spec

example (repr : Repr T) (p : RawPtr T) (base : BasePtr) (old value : T)
    (positive : 0 < repr.size) (noPointers : ∀ q, ¬ repr.Carries value q) :
    ⦃ readable repr p base old ⦄
    (do let _ ← RawPtr.read repr p
        MutRawPtr.write repr p value)
    ⦃ _ => pointsTo repr p base value ⦄ := by
  step with HeapWP.read_exposed.spec repr p base old 0 positive
  step with HeapWP.write_readable.spec repr p base old value noPointers positive
  assumption

example (repr : Repr T) (p : RawPtr T) (base : BasePtr) (value : T)
    (positive : 0 < repr.size) (R : Assertion) :
    ⦃ readable repr p base value ∗ R ⦄
    RawPtr.read repr p
    ⦃ result => fun h => result = value ∧ (readable repr p base value ∗ R) h ⦄ := by
  step with HeapWP.frame (R := R)
    (HeapWP.read_exposed.spec repr p base value 0 positive) as ⟨result, h, hp⟩
  simpa only [sep_and_left] using hp

/- Pure arithmetic under a heap triple retains the original resource assertion. -/
example (P : Assertion) (x : U32) (hx : x.val + 1 ≤ U32.max) :
    ⦃ P ⦄ (do let y ← x + 1#u32; pure (y, x))
    ⦃ (y : U32) (original : U32) => fun h =>
      y.val = x.val + 1 ∧ original = x ∧ P h ⦄ := by
  step*

/- OOM short-circuits the invalid continuation, including after pure-WP lifting. -/
example (P : Assertion) :
    ⦃ P ⦄ (do let _ ← (Result.oom : Result Unit); (Result.fail .undef : Result Unit))
    ⦃ _ => empty ⦄ := by
  step with (WP.spec_oom (α := Unit) (p := fun _ => False))

/- The actual mutable callback is sequenced, not treated as an already returned slice. -/
example (repr : Repr T) (p : RawPtr T) (original : Slice T)
    (values : Vector T count) (hlen : original.length = count) (positive : 0 < repr.size) :
    ⦃ alloc repr p p.address count false ∗ readableRange repr p p.address values 0 ⦄
    (do let result ← Slice.end_as_mut_ptr repr original p; pure (result, count))
    ⦃ (result : Slice T) (length : Nat) => fun h =>
      result.val = values.toList ∧ length = count ∧ empty h ⦄ := by
  step with mutable_range_end.spec repr p original values hlen positive
  step*

end Aeneas.Std.HeapWP.Tests
