import Aeneas.Std.WP

/-!
# Reflexive spec strengthening

`spec_refl` strengthens any spec's postcondition with the call identity `m = ok r`. The `refl_of%`
elaborator lifts this over the binders of a `∀`-quantified spec theorem, so a reflexive spec can be
dropped into a proof's local context where `step` picks them up.
-/

namespace Aeneas.Std.WP

/-- Strengthen any spec's postcondition with the identity `m = ok r`. -/
theorem spec_refl {α : Type u} {m : Result α} {P : Post α} (h : m ⦃ P ⦄) :
    m ⦃ fun r => P r ∧ m = Result.ok r ⦄ := by
  obtain ⟨r, h_eq, h_post⟩ := spec_imp_exists h
  exact exists_imp_spec ⟨r, h_eq, h_post, h_eq⟩

open Lean Elab Term Meta in
/-- `refl_of% e` turns a spec theorem `e` of the form `∀ xs, m xs ⦃ P xs ⦄` into its strengthening
`∀ xs, m xs ⦃ fun r => P xs r ∧ m xs = ok r ⦄`, telescoping the binders and applying `spec_refl`
under them. Any arity (including none). Errors if `e` is not, after telescoping, a spec. -/
elab "refl_of% " t:term : term => withRef t do
  let e ← elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars (← inferType e)
  forallTelescope ty fun xs body => do
    let refled ←
      try mkAppM ``spec_refl #[mkAppN e xs]
      catch _ =>
        throwError "refl_of%: expected a spec `m ⦃ P ⦄`, but the statement concludes \
          with{indentExpr body}"
    mkLambdaFVars xs refled

/-!
## Tests
-/
namespace SpecReflTests

private def add1 (x : Nat) : Result Nat := Result.ok (x + 1)
private theorem add1_spec (x : Nat) : add1 x ⦃ y => y = x + 1 ⦄ := by simp [add1, spec_ok]

-- `spec_refl` strengthens the postcondition with the call identity `m = ok r`.
example (x : Nat) : add1 x ⦃ y => y = x + 1 ∧ add1 x = Result.ok y ⦄ :=
  spec_refl (add1_spec x)

-- `refl_of%` lifts the strengthening over the `∀` binder, yielding a reusable spec.
example : ∀ x, add1 x ⦃ y => y = x + 1 ∧ add1 x = Result.ok y ⦄ :=
  refl_of% add1_spec

-- The strengthened spec can be introduced directly into a proof's local context.
example : True := by
  have _h := refl_of% add1_spec
  trivial

-- Zero-arity specs (no binders to telescope) work too.
private theorem c_spec : (Result.ok 5 : Result Nat) ⦃ y => y = 5 ⦄ := by simp [spec_ok]

example : (Result.ok 5 : Result Nat) ⦃ y => y = 5 ∧ (Result.ok 5 : Result Nat) = Result.ok y ⦄ :=
  refl_of% c_spec

-- Multiple binders telescope correctly.
private def pair (a b : Nat) : Result (Nat × Nat) := Result.ok (a, b)
private theorem pair_spec (a b : Nat) : pair a b ⦃ p => p = (a, b) ⦄ := by simp [pair, spec_ok]

example : ∀ a b, pair a b ⦃ p => p = (a, b) ∧ pair a b = Result.ok p ⦄ :=
  refl_of% pair_spec

-- `refl_of%` telescopes through hypotheses (Π-binders), not just data binders — matching real
-- specs that carry side-conditions (e.g. boundedness), which end up as binders on the result.
private theorem add1_spec' (x : Nat) (_ : x ≤ 10) : add1 x ⦃ y => y = x + 1 ⦄ := by
  simp [add1, spec_ok]

example : ∀ x, x ≤ 10 → add1 x ⦃ y => y = x + 1 ∧ add1 x = Result.ok y ⦄ :=
  refl_of% add1_spec'

/-!
### Realistic use: carrying the determinism of a hash

A deterministic function such as a hash exposes a spec that constrains only the *shape* of its
output. To prove that hashing the same input twice yields the same digest, we need the call identity
`hash data = ok r`, which `refl_of%` adds to the postcondition.
-/

variable (hash : List Nat → Result (List Nat))
  (hash_spec : ∀ data, hash data ⦃ digest => digest.length = 32 ⦄)

example (data : List Nat) :
    (do let a ← hash data; let b ← hash data; Result.ok (a, b)) ⦃ (r₁, r₂) => r₁ = r₂ ⦄ := by
  have hs := refl_of% hash_spec
  apply spec_bind (hs data); rintro a ⟨-, ha⟩
  apply spec_bind (hs data); rintro b ⟨-, hb⟩
  grind

end SpecReflTests

end Aeneas.Std.WP
