import Aeneas

open Aeneas Aeneas.Std Result ControlFlow Error

namespace tuples

set_option Aeneas.customDoElab true

def foo : Result (Nat × Nat) :=
  ok (1, 2)

@[step]
theorem foo_spec : foo ⦃ a b => a = 1 ∧ b = 2⦄ := by unfold foo; step*

def bar : Result ((Nat × Nat) × (Nat × Nat)) :=
  ok ((3, 4), (5, 6))

@[step]
theorem bar_spec : bar ⦃ (a, b) (c,d) => a = 3 ∧ b = 4 ∧ c = 5 ∧ d = 6⦄ := by
  unfold bar; step*

def baz : Result Nat := do
  let (a, b) ← foo
  let (c, d) ← foo
  let ((a, b), (c, d)) ← bar
  let ((e, f), (g, h)) ← bar
  ok (a + f + g + d)

example : baz ⦃ res => res = 18⦄ := by
  unfold baz
  simp only [step_simps]
  let* ⟨ a, b, a_post1, a_post2 ⟩ ← foo_spec
  let* ⟨ c, d, c_post1, c_post2 ⟩ ← foo_spec
  let* ⟨ a, c, a_post ⟩ ← bar_spec
  let* ⟨ e, g, e_post ⟩ ← bar_spec
  agrind

def mkTriple (x : Nat) : Result ((Nat × Nat) × Nat) :=
  ok ((x, x+1), x+2)

@[step] theorem mkTriple_spec (x : Nat) :
   mkTriple x ⦃ (a, b) c => -- this introduces a match on the first argument while we should decompose it with `curry`
    a = x ∧ b = x + 1 ∧ c = x + 2
  ⦄ :=
  by
  simp [mkTriple]
  
#print mkTriple_spec

end tuples

