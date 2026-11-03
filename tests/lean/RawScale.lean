import RawScale.Wrappers

open Aeneas Aeneas.Std Aeneas.Std.SepLogic
open scoped Aeneas.Std.HeapWP

/- Syntax checks: assertion precedence, tuple results, predicate postconditions,
   and coexistence with the original pure specification notation. -/
example (P Q R : Assertion) (c : Result Unit) :
    (⦃ P ∗ Q ∗ R ⦄ c ⦃ _ => P ⦄) =
      HeapWP.Triple (sep P (sep Q R)) c (fun _ => P) := rfl

example (P : Assertion) (c : Result (U32 × U32)) :
    (⦃ P ⦄ c ⦃ (a : U32) (b : U32) => fun h => a = b ∧ P h ⦄) =
      HeapWP.Triple P c (fun (a, b) h => a = b ∧ P h) := rfl

example (P : Assertion) (Q : U32 → Assertion) (c : Result U32) :
    (⦃ P ⦄ c ⦃ Q ⦄) = HeapWP.Triple P c Q := rfl

example (P : Assertion) (x : U32) :
    ⦃ P ⦄ Result.ok x ⦃ (result : U32) => fun h => result = x ∧ P h ⦄ :=
  HeapWP.Triple.pure P x

example (x : U32) : Result.ok x ⦃ (result : U32) => result = x ⦄ :=
  (WP.spec_ok x).mpr rfl

/-- info: 'raw_scale.scale_in_place.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_scale.scale_in_place.spec

/-- info: 'raw_scale.scale_into.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_scale.scale_into.spec

/-- info: 'raw_scale.scale_via_borrow.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_scale.scale_via_borrow.spec

/-- info: 'raw_scale.scaledRow_zero_padding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_scale.scaledRow_zero_padding

/-- info: 'raw_scale.rowRepr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_scale.rowRepr

/-- info: 'raw_scale.scale_slice.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_scale.scale_slice.spec

/-- info: 'raw_scale.scale_raw_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_scale.scale_raw_zero

/-- info: 'raw_scale.scale_raw.in_place_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_scale.scale_raw.in_place_spec

/-- info: 'raw_scale.scale_raw.disjoint_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_scale.scale_raw.disjoint_spec

/-- info: 'raw_scale.scale_raw.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_scale.scale_raw.spec

/-- info: 'raw_scale.scale_via_borrow_raw.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_scale.scale_via_borrow_raw.spec

/-- info: 'raw_scale.scaledWords_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_scale.scaledWords_values

/-- info: 'raw_scale.scaledWords_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_scale.scaledWords_zero
