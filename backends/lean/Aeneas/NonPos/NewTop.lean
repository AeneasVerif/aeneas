module
public import Lean
public import Aeneas.NonPos.Proofs

@[expose] public section

-- TODO: this is a work-in-progress, where I'm copying things piece by piece from Top.lean.

/-
This is the top level specification of a library that implements structures that
can break positivity. It allows for example the following command:

```
nonpos_structure Measure (A : Type) : Type 1 where
  size : A → Option Nat
  larger : ∀ B, Measure B → A → B → Option Bool
```

This library is written by ai, but to maintain human verifiability this single
contains the entire exposed surface of the library.
-/

namespace Example
open NonPos

abbrev MeasureF A (Measure : Type → Type) := A ×' (Measure A → Option Nat) ×' PUnit.{1}
-- example : Shape (MeasureF A) := inferInstance

end Example

/-

-/
