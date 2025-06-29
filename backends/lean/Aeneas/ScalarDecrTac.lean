/- Some utilities to prove termination -/
import Lean
import Mathlib.Tactic.Core
import Aeneas.Utils
import Aeneas.ScalarTac

namespace Aeneas

namespace Utils

open Lean Lean.Elab Command Term Lean.Meta Tactic

/-- Attempt to clear a list of fvar ids -/
def tryClearFVarIds (fvarIds : Array FVarId) : TacticM Unit := do
  let fvarIds ← withMainContext <| sortFVarIds fvarIds
  for fvarId in fvarIds.reverse do
    try
      withMainContext do
        let mvarId ← (← getMainGoal).clear fvarId
        replaceMainGoal [mvarId]
    catch _ =>
      pure ()

/- Utility function for proofs of termination (i.e., inside `decreasing_by`).

   Clean up the local context by removing all assumptions containing occurrences
   of `invImage` (those are introduced automatically when doing proofs of
   termination). We do so because we often need to simplify the context in the
   proofs, and if we simplify those assumptions they tend to make the context
   blow up.
-/
def removeInvImageAssumptions : TacticM Unit := do
  withMainContext do
  -- Get the local declarations
  let ctx ← Lean.MonadLCtx.getLCtx
  let decls ← ctx.getDecls
  -- Retrieve the list of local declarations which contain `invertImage`
  let containsInvertImage (decl : LocalDecl) : MetaM Bool := do
    reduceVisit (
      fun _ b e =>
      pure (
        b ||
        match e with
        | .const name _ => name == ``invImage
        | _ => false)) false decl.type
  let filtDecls ← liftM (decls.filterM fun decl => do
    if ← isProp decl.type then containsInvertImage decl
    else pure false)
  let filtDecls := filtDecls.toArray.map LocalDecl.fvarId
  /- Attempt to clear those assumptions - note that it may not always succeed as
     some other assumptions might depend on them -/
  setGoals [← (← getMainGoal).tryClearMany filtDecls]

elab "remove_invImage_assumptions" : tactic =>
  removeInvImageAssumptions

-- For termination proofs
syntax "scalar_decr_tac" : tactic
macro_rules
  | `(tactic| scalar_decr_tac) =>
    `(tactic|
      simp_wf <;>
      -- Simplify the context - otherwise simp_all below will blow up
      remove_invImage_assumptions <;>
      -- Finish
      scalar_tac)

-- This simplification lemma it is useful for the proofs of termination
attribute [scalar_tac_simps, simp] Prod.lex_iff

end Utils

end Aeneas
