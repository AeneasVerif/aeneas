module
public import Aeneas.Tactic.Step
public section

namespace Aeneas.Tactic.Step.Tests.SpatialGhosts

open Aeneas.Std Aeneas.SepLogic

/- The most recent pure bound deliberately describes an old view. The owned
   resource, not that bound, determines the callee's ghost state. -/
example (cell : Nat → Nat → IProp) (read : Nat → Result Nat)
    (hread : ∀ p value, 0 < value →
      ⦃ cell p value ⦄ read p
      ⦃⇓ result => ⌜result = value⌝ ∗ cell p value ⦄)
    (p current old : Nat) (hcurrent : 0 < current) (_hold : 0 < old) :
    ⦃ cell p current ⦄ read p
    ⦃⇓ result => cell p current ∗ ⌜result = current⌝ ⦄ := by
  step*

example (cell : Nat → Nat → IProp) (read : Nat → Result Nat)
    (hread : ∀ p value, 0 < value →
      ⦃ cell p value ⦄ read p
      ⦃⇓ result => ⌜result = value⌝ ∗ cell p value ⦄)
    (p current old : Nat) (frame : IProp)
    (hcurrent : 0 < current) (_hold : 0 < old) :
    WP.ispec (frame ∗ cell p current)
    (do let value ← read p; pure (value + 1))
    (fun result => iprop(⌜result = current + 1⌝ ∗ cell p current ∗ frame)) := by
  step*

example (cell : Nat → Nat → IProp) (read : Nat → Result Nat)
    (hread : ∀ p value, 0 < value →
      ⦃ cell p value ⦄ read p
      ⦃⇓ result => ⌜result = value⌝ ∗ cell p value ⦄)
    (p current old : Nat) (hcurrent : 0 < current) (_hold : 0 < old) :
    WP.dispec (cell p current) (read p)
      (fun result => iprop(⌜result = current⌝ ∗ cell p current)) := by
  step*

/- A returned pointer can be propositionally equal to the pointer whose
   ownership is framed. The view still comes from that ownership. -/
example (cell : Nat → Nat → IProp) (read : Nat → Result Nat)
    (hread : ∀ p value, 0 < value →
      ⦃ cell p value ⦄ read p
      ⦃⇓ result => ⌜result = value⌝ ∗ cell p value ⦄)
    (p q current old : Nat) (hp : q = p)
    (hcurrent : 0 < current) (_hold : 0 < old) :
    WP.ispec (cell p current)
      (do let value ← read q; pure (value + 1))
      (fun result => iprop(⌜result = current + 1⌝ ∗ cell p current)) := by
  step*

/- A terminal spatial rule introduces the result tuple and its ghost view,
   frames resources, and leaves only the new mathematical postcondition. -/
example (pre frame : IProp) (cell : Nat → IProp) (P Q : Nat → Prop)
    (run : Result (Nat × Nat))
    (hrun : ⦃ pre ⦄ run
      ⦃⇓ x y => ∃ view : Nat, ⌜view = x + y ∧ P view⌝ ∗ cell view ⦄)
    (hQ : ∀ n, P n → Q n) :
    ⦃ frame ∗ pre ⦄ run
    ⦃⇓ x y => ∃ view : Nat, ⌜view = x + y ∧ Q view⌝ ∗ cell view ∗ frame ⦄ := by
  step with hrun as ⟨x, y, view, hView, hP⟩
  exact ⟨hView, hQ view hP⟩

example (pre frame : IProp) (cell : Nat → IProp) (P Q : Nat → Prop)
    (run : Result (Nat × Nat))
    (hrun : WP.dispec pre run
      (fun (x, y) => iprop(∃ view : Nat, ⌜view = x + y ∧ P view⌝ ∗ cell view)))
    (hQ : ∀ n, P n → Q n) :
    WP.dispec (frame ∗ pre) run
      (fun (x, y) => iprop(∃ view : Nat, ⌜view = x + y ∧ Q view⌝ ∗ cell view ∗ frame)) := by
  step with hrun as ⟨result, view, hView, hP⟩
  exact ⟨hView, hQ view hP⟩

/- Uninferred witnesses must not be lost at the single-goal introduction hook. -/
example (H : IProp) (run : Result Nat)
    (hrun : ⦃ H ⦄ run ⦃⇓ _ => H ⦄) :
    ⦃ H ⦄ run ⦃⇓ result => ∃ witness : Nat, ⌜witness = result⌝ ∗ H ⦄ := by
  step with hrun
  isimp only
  · exact value
  · rfl

/- The 20-component return of VCR's store_8_blocks fits the marker budget. -/
example (cell : Nat → IProp) (n : Nat) (P : Nat → Prop) (hP : Unit → P n) :
    ⦃ cell n ⦄
    Result.ok (n, n, n, n, n, n, n, n, n, n, n, n, n, n, n, n, n, n, n, n)
    ⦃⇓ first _a2 _a3 _a4 _a5 _a6 _a7 _a8 _a9 _a10
        _a11 _a12 _a13 _a14 _a15 _a16 _a17 _a18 _a19 last =>
      ∃ view : Nat, ⌜view = first ∧ P last⌝ ∗ cell view ⦄ := by
  step
  guard_target = P n
  exact hP ()

/- Larger returns need the post-introduction framing pass: the initial marker
   reduction cannot expose the existential within its fuel budget. -/
example (cell : Nat → IProp) (n : Nat) (P : Nat → Prop) (hP : Unit → P n) :
    ⦃ cell n ⦄
    Result.ok (n, n, n, n, n, n, n, n, n, n, n, n,
      n, n, n, n, n, n, n, n, n, n, n, n)
    ⦃⇓ first _a2 _a3 _a4 _a5 _a6 _a7 _a8 _a9 _a10 _a11 _a12
        _a13 _a14 _a15 _a16 _a17 _a18 _a19 _a20 _a21 _a22 _a23 last =>
      ∃ view : Nat, ⌜view = first ∧ P last⌝ ∗ cell view ⦄ := by
  step
  guard_target = P n
  exact hP ()

example (cell : Nat → IProp) (n : Nat) (P : Nat → Prop) (hP : Unit → P n) :
    ⦃ cell n ⦄
    Result.ok (n, n, n, n, n, n, n, n, n, n, n, n,
      n, n, n, n, n, n, n, n, n, n, n, n)
    ⦃⇓ first _a2 _a3 _a4 _a5 _a6 _a7 _a8 _a9 _a10 _a11 _a12
        _a13 _a14 _a15 _a16 _a17 _a18 _a19 _a20 _a21 _a22 _a23 last =>
      ∃ view : Nat, ⌜view = first ∧ P last⌝ ∗ cell view ⦄div := by
  step
  guard_target = P n
  exact hP ()

/- A returned tuple which is not a literal is still destructured by the
   postcondition, and the resource is framed. -/
example (cell : Nat → IProp) (n : Nat) (p : Nat × Nat) (P : Nat → Nat → Prop)
    (hP : Unit → P p.1 p.2) :
    ⦃ cell n ⦄ Result.ok (n, p)
    ⦃⇓ first (a, b) => ⌜first = n ∧ P a b⌝ ∗ cell first ⦄ := by
  step
  guard_target = P p.1 p.2
  exact hP ()

/- Same, when the destructured tuple is followed by more outputs. -/
example (cell : Nat → IProp) (n : Nat) (p : Nat × Nat) (P : Nat → Nat → Nat → Prop)
    (hP : Unit → P p.1 p.2 n) :
    ⦃ cell n ⦄ Result.ok (p, n)
    ⦃⇓ (a, b) last => ⌜P a b last⌝ ∗ cell last ⦄ := by
  step
  guard_target = P p.1 p.2 n
  exact hP ()

end Aeneas.Tactic.Step.Tests.SpatialGhosts
