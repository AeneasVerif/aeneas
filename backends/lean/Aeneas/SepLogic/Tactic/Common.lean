module
public import Aeneas.SepLogic.Tactic.Normalize
public meta import Aeneas.SepLogic.Tactic.Normalize
public meta import Lean
public meta import AeneasMeta.Simp

/-! Helpers shared by the separation-logic tactics, on top of `Normalize`: exposing entailments
hidden behind definitions, matching atoms, and pulling facts into the context. -/

public meta section

namespace Aeneas.SepLogic

open Lean Lean.Elab Lean.Meta Lean.Elab.Tactic Normalize

namespace Common

partial def exposeEntailment? (e : Expr) : MetaM (Option Expr) := do
  let e := (← instantiateMVars e).consumeMData
  if e.isAppOfArity ``Entails 2 then return some e
  match ← unfoldDefinition? e with
  | some e' => exposeEntailment? e'
  | none => return none

def mkEntailmentLike (target source destination newSource : Expr) : MetaM Expr := do
  let (fn, targetArgs) :=
    target.consumeMData.withApp fun fn args => (fn, args)
  let newSourceType ← inferType newSource
  for h : i in [:targetArgs.size] do
    let argType ← inferType targetArgs[i]
    if ← isDefEq argType newSourceType then
      let candidate := mkAppN fn (targetArgs.set! i newSource)
      if let some exposed ← exposeEntailment? candidate then
        let args := exposed.getAppArgs
        if ← isDefEq args[0]! newSource then
          if ← isDefEq args[1]! destination then
            return candidate
  let replacement := target.replace fun e =>
    if e == source then some newSource else none
  if let some exposed ← exposeEntailment? replacement then
    let args := exposed.getAppArgs
    if ← isDefEq args[0]! newSource then
      if ← isDefEq args[1]! destination then
        return replacement
  mkAppM ``Entails #[newSource, destination]

/-- Match each `required` atom with a distinct `available` atom, by unification. Atoms without
metavariables go first, so that a flexible atom `P ?w` cannot take the match a rigid atom needs.
Returns the matched and the unmatched required atoms, and the unused available atoms. -/
def matchAtoms (available required : Array Expr) :
    MetaM (Array Expr × Array Expr × Array Expr) := do
  let mut rigid := #[]
  let mut flexible := #[]
  for atom in required do
    if (← instantiateMVars atom).hasExprMVar then flexible := flexible.push atom
    else rigid := rigid.push atom
  let mut remaining := available
  let mut matched := #[]
  let mut unmatched := #[]
  for expected in rigid ++ flexible do
    let mut found := none
    for h : i in [:remaining.size] do
      if ← isDefEq expected remaining[i] then
        found := some i
        break
    match found with
    | some i =>
      matched := matched.push expected
      remaining := remaining.eraseIdx! i
    | none => unmatched := unmatched.push expected
  return (matched, unmatched, remaining)

def removeMatches (available required : Array Expr) :
    MetaM (Option (Array Expr)) := commitWhenSome? do
  let (_, unmatched, remaining) ← matchAtoms available required
  return if unmatched.isEmpty then some remaining else none

/-- `pullLeft`, then rewrite the goal with the facts this introduced (if `useFacts`); `none` if
that closed the goal. -/
def pullAndRewrite (goal : MVarId) (useFacts := true) : TacticM (Option MVarId) := do
  let before ← goal.withContext do
    return (← getLCtx).foldl (init := (∅ : Std.HashSet FVarId))
      fun ids decl => ids.insert decl.fvarId
  let goal ← pullLeft goal
  let facts ← goal.withContext do
    return (← (← getLCtx).getAssumptions).filterMap fun decl =>
      if before.contains decl.fvarId then none else some decl.fvarId
  if !useFacts || facts.isEmpty then return some goal
  goal.withContext <| simpGoal goal true { hypsToUse := facts.toArray }

end Common

end Aeneas.SepLogic
