module
import Aeneas.Tactic.Step

open Aeneas Std Result Lean Elab Tactic

namespace Aeneas.Tactic.Step.Tests.ParserErrors

def f (n : Nat) : Result Nat := .ok (n + 1)

theorem f_spec (n : Nat) : f n ⦃ r => r = n + 1 ⦄ := by
  simp [f]

/- Attaching an elaborator must not register a second parser for the same syntax. -/
run_cmd do
  let letStep ← `(tactic| let* ⟨r, hr⟩ ← f_spec 0)
  unless letStep.raw.isOfKind ``Aeneas.Step.letStep do
    throwError "Expected the letStep parser, got {letStep.raw.getKind}"
  for stx in #[← `(tactic| step*), ← `(tactic| step*?),
      ← `(tactic| spec_split), ← `(tactic| spec_split as h)] do
    if stx.raw.isOfKind `choice then
      throwError "Unexpected parser choice: {stx.raw}"
  for input in #["let* ⟨r, hr⟩ ←", "step* (splits := )"] do
    match Parser.runParserCategory (← getEnv) `tactic input with
    | .error _ => pure ()
    | .ok stx => throwError "Malformed syntax was accepted: {stx}"

/- A malformed call must report its type error, not just a sorry warning. -/
/--
error: Application type mismatch: The argument
  true
has type
  Bool
but is expected to have type
  ℕ
in the application
  f_spec true
-/
#guard_msgs in
example : f 0 ⦃ r => r = 1 ⦄ := by
  let* ⟨r, hr⟩ ← f_spec true

/--
error: Application type mismatch: The argument
  true
has type
  Bool
but is expected to have type
  ℕ
in the application
  f_spec true
-/
#guard_msgs in
example : f 0 ⦃ r => r = 1 ⦄ := by
  step with f_spec true

/--
error: Application type mismatch: The argument
  true
has type
  Bool
but is expected to have type
  ℕ
in the application
  f_spec true
-/
#guard_msgs in
example : f 0 ⦃ r => r = 1 ⦄ := by
  step? with f_spec true

/- Parsing itself must throw before returning a spec containing synthetic sorry.
   The surrounding tactic still permits recovery, as it does in normal use. -/
run_cmd Command.liftTermElabM do
  let goal ← Meta.mkFreshExprSyntheticOpaqueMVar (mkConst ``True)
  discard <| Tactic.run goal.mvarId! <| withRecover true do
    let reject (label : String) (action : TacticM Unit) : TacticM Unit := do
      let rejected ← try
        action
        pure false
      catch _ => pure true
      unless rejected do throwError "{label} accepted an ill-typed argument"
    let args ← `(Aeneas.Step.stepArgs| with f_spec true)
    reject "parseStepArgs" (discard <| Aeneas.Step.parseStepArgs args)
    let stx ← `(tactic| let* ⟨r, hr⟩ ← f_spec true)
    reject "parseLetStep" (discard <| Aeneas.Step.parseLetStep ⟨stx.raw⟩)
    /- Config fields are compared by name, so they must not acquire quotation scopes. -/
    let field := mkIdent `splits
    let args ← `(Aeneas.Step.stepArgs| ($field:ident := true))
    reject "step config" (discard <| Aeneas.Step.parseStepArgs args)
    let stx ← `(tactic| let* ⟨r, hr⟩ ← [($field:ident := true)] f_spec)
    reject "let* config" (discard <| Aeneas.Step.parseLetStep ⟨stx.raw⟩)
    let args ← `(Aeneas.StepStar.«step*_args»| ($field:ident := true))
    reject "step* config" (discard <| Aeneas.StepStar.parseArgs args)

/--
error: Application type mismatch: The last
  true
argument has type
  Bool
but is expected to have type
  ℕ
in the application
  Step.Config.mk false true true false false false true true true
-/
#guard_msgs in
example : True := by
  step* (splits := true)

/- Failed alternatives must leave a real goal for the successful branch. -/
example : f 0 ⦃ r => r = 1 ⦄ := by
  first
  | let* ⟨r, hr⟩ ← f_spec true
  | let* ⟨r, hr⟩ ← f_spec 0
    exact hr

end Aeneas.Tactic.Step.Tests.ParserErrors
