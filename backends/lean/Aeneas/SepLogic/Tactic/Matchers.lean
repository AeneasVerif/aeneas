module
public import Aeneas.SepLogic.Tactic.Normalize
public meta import Aeneas.SepLogic.Tactic.Normalize
public meta import Lean

/-! Matching the atoms of separation-logic assertions by unification, and cancellation of the
matched atoms, on top of `Normalize`. -/

public meta section

namespace Aeneas.SepLogic

open Lean Lean.Meta Normalize

namespace Matchers

/-- The indices of `atoms`, those with the head symbol of `atom` first: they are the likely
matches, and failing unifications across different heads may unfold a lot. -/
private def candidates (atoms : Array Expr) (atom : Expr) : Array Nat :=
  let key := atom.consumeMData.toHeadIndex
  let (same, other) := (Array.range atoms.size).partition
    (atoms[·]!.consumeMData.toHeadIndex == key)
  same ++ other

/-- Atoms without metavariables first, so that a flexible atom `P ?w` cannot take the match a
rigid atom needs. -/
private def rigidFirst (atoms : Array Expr) : MetaM (Array Expr) := do
  let mut rigid := #[]
  let mut flexible := #[]
  for atom in atoms do
    if (← instantiateMVars atom).hasExprMVar then flexible := flexible.push atom
    else rigid := rigid.push atom
  return rigid ++ flexible

/-- Greedily match each `required` atom with a distinct `available` atom, by unification. With
`unique`, a flexible atom is only matched when exactly one atom unifies with it, so that its
metavariables are not committed to an arbitrary choice. Returns the matched pairs
`(required, available)`, the unmatched required atoms, and the unused available atoms. -/
def matchAtoms (available required : Array Expr) (unique := false) :
    MetaM (Array (Expr × Expr) × Array Expr × Array Expr) := do
  let mut remaining := available
  let mut matched := #[]
  let mut unmatched := #[]
  for expected in ← rigidFirst required do
    let tries := candidates remaining expected
    let found ←
      if unique && (← instantiateMVars expected).hasExprMVar then
        let unifiers ← tries.filterM fun i =>
          withoutModifyingState <| isDefEq expected remaining[i]!
        match unifiers with
        | #[i] => pure (if ← isDefEq expected remaining[i]! then some i else none)
        | _ => pure none
      else tries.findM? fun i => isDefEq expected remaining[i]!
    match found with
    | some i =>
      matched := matched.push (expected, remaining[i]!)
      remaining := remaining.eraseIdx! i
    | none => unmatched := unmatched.push expected
  return (matched, unmatched, remaining)

/-- Match every `required` atom with a distinct `available` atom, backtracking over the choices
for atoms with metavariables. Returns the matched pairs `(required, available)` and the unused
available atoms; on failure, no metavariable is assigned. -/
def matchAll (available required : Array Expr) :
    MetaM (Option (Array (Expr × Expr) × Array Expr)) := do
  go available (← rigidFirst required).toList
where
  go (available : Array Expr) : List Expr → MetaM (Option (Array (Expr × Expr) × Array Expr))
    | [] => return some (#[], available)
    | expected :: required => do
      -- ponytail: a rigid atom commits to its first match; backtrack over those too if two
      -- defeq-but-distinct copies of an atom ever need to go to different flexible atoms.
      let flexible := (← instantiateMVars expected).hasExprMVar
      for i in candidates available expected do
        let saved ← saveState
        if ← isDefEq expected available[i]! then
          if let some (matched, rest) ← go (available.eraseIdx! i) required then
            return some (#[(expected, available[i]!)] ++ matched, rest)
          saved.restore
          unless flexible do return none
      return none

/-- Frame away the atoms of the destination that unify with atoms of the source (see
`matchAtoms`, and `unique`). Returns the residual goal `left ⊢ right` over the other atoms, or
`goal` itself if nothing matched. -/
def cancelGoal (goal : MVarId) (unique := false) : MetaM MVarId := goal.withContext do
  let some (source, destination) ← entailment? goal | return goal
  let source ← reducePostApplication source
  let destination ← reducePostApplication destination
  let (matched, unmatched, remaining) ←
    matchAtoms (← flatten source) (← flatten destination) unique
  if matched.isEmpty then return goal
  let frame := mkStar (matched.map (·.1))
  let left := mkStar remaining
  let right := mkStar unmatched
  let residual ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Entails) left right)
  let leftEq ← proveEqAC source (mkApp2 (mkConst ``sep) frame left) matched
  let rightEq ← proveEqAC (mkApp2 (mkConst ``sep) frame right) destination
  let framed ← mkAppM ``sep_mono #[← mkAppM ``entails_refl #[frame], residual]
  let finish ← mkAppM ``entails_trans #[framed, ← mkAppM ``entails_of_eq #[rightEq]]
  goal.assign (← mkAppM ``entails_trans #[← mkAppM ``entails_of_eq #[leftEq], finish])
  return residual.mvarId!

end Matchers

end Aeneas.SepLogic
