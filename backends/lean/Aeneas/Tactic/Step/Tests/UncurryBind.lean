module
import Aeneas.Std.Slice
import Aeneas.Tactic.Step
import Aeneas.Do

open Aeneas Aeneas.Std Result

namespace Aeneas.Tactic.Step.Tests.UncurryBind

/-- A toy "indexed read with a setter" that returns a pair, mirroring
    `Array.index_mut_usize`. -/
def readPair (xs : List Nat) (i : Nat) : Result (Nat × (Nat → List Nat)) :=
  ok (xs.getD i 0, fun y => xs.set i y)

@[step]
theorem readPair_spec (xs : List Nat) (i : Nat) :
    readPair xs i ⦃ x y => x = xs.getD i 0 ∧ y = (fun y => xs.set i y) ⦄ := by
  unfold readPair; simp [WP.spec_ok, Std.WP.uncurry']

def readSingle (xs : List Nat) (i : Nat) : Result Nat :=
  ok (xs.getD i 0)

@[step]
theorem readSingle_spec (xs : List Nat) (i : Nat) :
    readSingle xs i ⦃ x => x = xs.getD i 0 ⦄ := by
  unfold readSingle; simp [WP.spec_ok]

/-- a `do` block alternating tuple-destructuring binds with single binds. -/
def prog (xs : List Nat) : Result (List Nat × Nat) := do
  let (a, setA) ← readPair xs 0
  let b ← readSingle xs 1
  let (c, setC) ← readPair (setA b) 2
  let d ← readSingle (setC c) 3
  ok (setC c, a + b + c + d)

-- `step*` should finish this proof off
example (xs : List Nat) :
    prog xs ⦃ _ => True ⦄ := by
  unfold prog
  step*

/--
info: Try this:

  [apply]     let* ⟨ a, setA, a_post, setA_post ⟩ ← readPair_spec
    let* ⟨ b, b_post ⟩ ← readSingle_spec
    let* ⟨ c, setC, c_post, setC_post ⟩ ← readPair_spec
    let* ⟨ ⟩ ← readSingle_spec
-/
#guard_msgs in
example (xs : List Nat) :
    prog xs ⦃ _ => True ⦄ := by
  unfold prog
  step*?

/-- Nested-tuple bind followed by another bind. Checks that `introOutputs`
  properly reduces a nested `Std.uncurry` chain. -/
def readNested (xs : List Nat) : Result ((Nat × Nat) × Nat) :=
  ok ((xs.getD 0 0, xs.getD 1 0), xs.getD 2 0)

@[step]
theorem readNested_spec (xs : List Nat) :
    readNested xs ⦃ r => r = ((xs.getD 0 0, xs.getD 1 0), xs.getD 2 0) ⦄ := by
  unfold readNested; step*

def progNested (xs : List Nat) : Result Nat := do
  let ((a, b), c) ← readNested xs
  let d ← readSingle xs 3
  ok (a + b + c + d)

example (xs : List Nat) :
    progNested xs ⦃ _ => True ⦄ := by
  unfold progNested
  step*

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post ⟩ ← readNested_spec
    let* ⟨ ⟩ ← readSingle_spec
-/
#guard_msgs in
example (xs : List Nat) :
    progNested xs ⦃ _ => True ⦄ := by
  unfold progNested
  step*?

/- Checking we're getting the right names in step*?-/

/--
info: Try this:

  [apply]     let* ⟨ a, setA, a_post, setA_post ⟩ ← readPair_spec
    let* ⟨ b, b_post ⟩ ← readSingle_spec
    agrind
-/
#guard_msgs in
example (xs : List Nat) :
    (do let (a, setA) ← readPair xs 0
        let b ← readSingle (setA a) 0
        ok (a + b)) ⦃ res => 0 ≤ res ⦄ := by
  step*?

def mkTriple (x : Nat) : Result ((Nat × Nat) × Nat) :=
  ok ((x, x + 1), x + 2)

/- delabing the postcondition -/

/--
error: unsolved goals
x : ℕ
⊢ mkTriple x ⦃ (a, b) c => a = x ∧ b = x + 1 ∧ c = x + 2 ⦄
-/
#guard_msgs in
example (x : Nat) :
    mkTriple x ⦃ (a, b) c => a = x ∧ b = x + 1 ∧ c = x + 2 ⦄ := by
    done

universe u v

example {α : Type u} {β : Type v} {m : Result α} {k : α → Result β}
    {P : α → Prop} {Q : β → Prop}
    (hm : WP.spec m P) (hk : ∀ x, P x → WP.spec (k x) Q) :
    WP.spec (Std.bind m k) Q :=
  WP.spec_bind hm hk

example {α : Type u} {β : Type v} {m : Result α} {k : α → Result β}
    {P : α → Prop} {Q : β → Prop}
    (hm : WP.dspec m P) (hk : ∀ x, P x → WP.dspec (k x) Q) :
    WP.dspec (Std.bind m k) Q :=
  WP.dspec_bind hm hk

/- A heterogeneous inner bind must reassociate through the ordinary outer bind,
   without a local simp registration or manual bind normalization. -/
example {α : Type u} {β γ : Type v}
    (m : Result α) (f : α → Result β) (g : β → Result γ)
    (P : α → Prop) (Q : β → Prop) (R : γ → Prop)
    (hm : m ⦃ x => P x ⦄)
    (hf : ∀ x, P x → f x ⦃ y => Q y ⦄)
    (hg : ∀ y, Q y → g y ⦃ z => R z ⦄) :
    ((do let y ← ((do let x ← m; f x) : Result β); g y) : Result γ)
    ⦃ z => R z ⦄ := by
  step with hm as ⟨x, hx⟩
  step with hf x hx as ⟨y, hy⟩
  step with hg y hy
  assumption

example {α : Type u} {β γ : Type v}
    (m : Result α) (f : α → Result β) (g : β → Result γ)
    (P : α → Prop) (Q : β → Prop) (R : γ → Prop)
    (hm : m ⦃ x => P x ⦄)
    (hf : ∀ x, P x → f x ⦃ y => Q y ⦄)
    (hg : ∀ y, Q y → g y ⦃ z => R z ⦄) :
    ((do let y ← ((do let x ← m; f x) : Result β); g y) : Result γ)
    ⦃ z => R z ⦄ := by
  let* ⟨x, hx⟩ ← hm
  let* ⟨y, hy⟩ ← hf x hx
  let* ⟨z, hz⟩ ← hg y hy
  exact hz

example {α : Type u} {β γ : Type v}
    (m : Result α) (f : α → Result β) (g : β → Result γ)
    (P : α → Prop) (Q : β → Prop) (R : γ → Prop)
    (hm : m ⦃ x => P x ⦄)
    (hf : ∀ x, P x → f x ⦃ y => Q y ⦄)
    (hg : ∀ y, Q y → g y ⦃ z => R z ⦄) :
    ((do let y ← ((do let x ← m; f x) : Result β); g y) : Result γ)
    ⦃ z => R z ⦄ := by
  step*

end Aeneas.Tactic.Step.Tests.UncurryBind
