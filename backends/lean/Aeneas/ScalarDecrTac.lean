/- Some utilities to prove termination -/
import Lean
import Mathlib.Tactic.Core
import AeneasMeta.Utils
import Aeneas.ScalarTac

namespace Aeneas

namespace Utils

open Lean Lean.Elab Command Term Lean.Meta Tactic

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


def clearUnusedDeclsOnePass : TacticM Unit := do
  withMainContext do
  let lctx ← getLCtx
  let decls ← lctx.getDecls
  let decls ← decls.filterM (fun d => do pure (¬ (← isProp d.type)))
  let allFVarIds : Std.HashSet FVarId := Std.HashSet.ofList (decls.map LocalDecl.fvarId)
  let usedFVarIds ← decls.foldlM (fun used d => do
    let used ← Utils.getFVarIds d.type used
    match d.value? with
    | none => pure used
    | some value => getFVarIds value used) Std.HashSet.emptyWithCapacity
  let toClear := allFVarIds.filter (fun id => ¬ usedFVarIds.contains id)
  setGoals [← (← getMainGoal).tryClearMany toClear.toArray]

elab "clear_unused_decls_one_pass" : tactic =>
  clearUnusedDeclsOnePass

/- We clear from the end to the beginning -/
def clearRedundantHyps : TacticM Unit := do
  withTraceNode `ScalarTac (fun _ => pure m!"clearRedundantHyps") do
  withMainContext do
  let lctx ← getLCtx
  let decls ← lctx.getAssumptions
  let decls := decls.reverse
  let mut assums := Std.HashSet.emptyWithCapacity
  let mut toClear := #[]
  for decl in decls do
    trace[ScalarTac] "Exploring: {Expr.fvar decl.fvarId}"
    if isExists decl.type then
      toClear := toClear.push decl.fvarId
      trace[ScalarTac] "Clearing because existential"
      continue
    let conjs := splitConjs decl.type
    trace[ScalarTac] "conjs:\n{conjs}"
    if conjs.all fun x => assums.contains x then
      toClear := toClear.push decl.fvarId
      trace[ScalarTac] "Clearing because assumptions are already in the context"
      continue
    trace[ScalarTac] "Not clearing"
    assums := assums.insertMany conjs
  setGoals [← (← getMainGoal).tryClearMany toClear]

elab "clear_redundant_hyps" : tactic =>
  clearRedundantHyps

/--
info: example :
  True
  := by sorry
-/
#guard_msgs in
example (x y : Nat) (_ : x < 3 ∧ y < 4) (_ : x < 3) (_ : y < 4) : True := by
  clear_redundant_hyps
  extract_goal1
  simp only

-- For termination proofs
syntax "scalar_decr_tac_preprocess" : tactic
macro_rules
  | `(tactic| scalar_decr_tac_preprocess) =>
    `(tactic|
      simp_wf <;> -- TODO: simp_wf is not necessary anymore?
      -- Simplify the context - otherwise simp_all below will blow up
      remove_invImage_assumptions <;>
      --
      clear_unused_decls_one_pass <;>
      --
      clear_redundant_hyps)

/-- This tactic is a variant of `scalar_tac` specialized for `decreasing_by` proofs.

It does a slightly different preprocessing step to remove useless assumptions introduced
automatically by Lean when doing termination proofs and which tend to slow down `scalar_tac`
considerably.
-/
syntax "scalar_decr_tac" : tactic
macro_rules
  | `(tactic| scalar_decr_tac) =>
    `(tactic| scalar_decr_tac_preprocess <;> scalar_tac)

-- This simplification lemma it is useful for the proofs of termination
attribute [scalar_tac_simps, simp] Prod.lex_iff

end Utils

end Aeneas
