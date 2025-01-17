/- Some utilities to prove termination -/
import Lean
import Mathlib.Tactic.Core
import Aeneas.Utils
import Aeneas.ScalarTac

namespace Aeneas

namespace Utils

open Lean Lean.Elab Command Term Lean.Meta Tactic

-- Inspired by the `clear` tactic
def clearFvarIds (fvarIds : Array FVarId) : TacticM Unit := do
  let fvarIds ← withMainContext <| sortFVarIds fvarIds
  for fvarId in fvarIds.reverse do
    withMainContext do
      let mvarId ← (← getMainGoal).clear fvarId
      replaceMainGoal [mvarId]

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
    let expr := decl.toExpr
    reduceVisit (
      fun _ b e =>
      pure (
        b ||
        match e with
        | .const name _ => name == ``invImage
        | _ => false)) false (← inferType expr)
  let filtDecls ← liftM (decls.filterM containsInvertImage)
  -- It can happen that other variables depend on the variables we want to clear:
  -- filter them.
  let allFVarsInTypes ← decls.foldlM (fun hs d => do
    let hs ← getFVarIds (← inferType d.toExpr) hs
    -- Explore the body if it is not opaque
    match d.value? with
    | none => pure hs
    | some e => getFVarIds e hs
    ) Std.HashSet.empty
  let fvarIds := filtDecls.map fun d => d.fvarId
  let fvarIds := fvarIds.filter (fun id => ¬ allFVarsInTypes.contains id)
  -- Clear them
  clearFvarIds fvarIds.toArray

elab "remove_invImage_assumptions" : tactic =>
  removeInvImageAssumptions

-- Auxiliary function
def scalarDecrTac_apply_lemmas : TacticM Unit := do
  withMainContext do
  let goal ← getMainGoal
  let rec applyFirst (names : List Name) : TacticM (List MVarId) :=
    match names with
    | [] => pure [goal]
    | name :: names =>
      -- Should use try ... catch or Lean.observing?
      -- Generally speaking we should use Lean.observing? to restore the state,
      -- but with tactics the try ... catch variant seems to work
      try do
        let th ← mkConstWithFreshMVarLevels name
        goal.apply th
      catch _ => do applyFirst names
  let ngoals ← applyFirst [``ScalarTac.to_int_to_nat_lt, ``ScalarTac.to_int_sub_to_nat_lt]
  setGoals ngoals

elab "scalar_decr_tac_apply_lemmas" : tactic =>
  scalarDecrTac_apply_lemmas

-- For termination proofs
syntax "scalar_decr_tac" : tactic
macro_rules
  | `(tactic| scalar_decr_tac) =>
    `(tactic|
      simp_wf <;>
      -- Simplify the context - otherwise simp_all below will blow up
      remove_invImage_assumptions <;>
      -- Transform the goal a bit to get rid of `Int.toNat` if there is
      -- (note that this is actually not necessary anymore).
      scalar_decr_tac_apply_lemmas <;>
      -- Finish
      simp_all (config := {maxDischargeDepth := 1}) <;> scalar_tac)

-- We always activate this simplification lemma because it is useful for the proofs of termination
attribute [simp] Prod.lex_iff

end Utils

end Aeneas
