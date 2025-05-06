import Aeneas.Utils
import Mathlib.Tactic.DefEqTransformations

namespace Aeneas.GLet

open Lean Elab Term Meta Tactic

def opaque_refold (h x : Name) (e : Expr) : TacticM Unit :=
  withMainContext do
  /- Retrieve the list of propositions in the context -/
  let ctx ← getLCtx
  let props ← (← ctx.getDecls).filterM fun x => do pure (← inferType x.type).isProp
  /- Generalize -/
  let goal ← getMainGoal
  let (_, _, ngoal) ← goal.generalizeHyp #[{expr := e, xName? := x, hName? := h}] (props.map LocalDecl.fvarId).toArray
  setGoals [ngoal]
  withMainContext do
  /- Revert the equality.
  This is slightly annoying: `generalizeHyp` doesn't directly give us the introduced equality, we have to look it up.
  -/
  let eq ← getLocalDeclFromUserName h
  let th ← mkAppM ``Eq.symm #[eq.toExpr]
  Utils.addDeclTac h th (← inferType th) (asLet := false) fun _ => do
  setGoals [← (← getMainGoal).clear eq.fvarId]

elab "glet" h:ident " : " x:ident " := " e:term : tactic =>
  withMainContext do
  opaque_refold h.getId x.getId (← Tactic.elabTerm e none)

elab "glet" h:ident " : " "(" x:ident " : " ty:term ")" " := " e:term : tactic =>
  withMainContext do
  let ty  ← Tactic.elabTerm ty none
  opaque_refold h.getId x.getId (← Tactic.elabTerm e (expectedType? := ty))

/--
info: example
  (x : Nat)
  (h : x = 1 + 1) :
  x = 2
  := by sorry
-/
#guard_msgs in
set_option linter.unusedTactic false in
example : 1 + 1 = 2 := by
  glet h: x := 1 + 1
  extract_goal1
  omega

example (x y z : Nat) (h0 : x + y = z) (h1 : x + y = 3) (_ : z ≤ 4) : x + y + z = 3 + z := by
  glet ha: a := x + y
  glet hb: b := a + z
  omega

example (x y z : Nat) (h0 : x + y = z) (h1 : x + y = 3) (_ : z ≤ 4) : x + y + z = 3 + z := by
  glet ha: (a : Nat) := x + y
  glet hb: (b : Nat) := a + z
  omega

def transparent_refold (x : Name) (e : Expr) : TacticM Unit :=
  withMainContext do
  /- Retrieve the list of propositions in the context -/
  let ctx ← getLCtx
  let props ← (← ctx.getDecls).filterM fun x => do pure (← inferType x.type).isProp
  /- List the assumptions which contain the declaration that we want to refold -/
  let mut toRevert := #[]
  for decl in props.reverse do
    trace[Utils] "Trying to rewrite decl: {Expr.fvar decl.fvarId}"
    let ty' ← kabstract decl.type e
    if ¬ ty' == decl.type then
      toRevert := toRevert.push decl.fvarId
  trace[Utils] "To revert: {toRevert.map Expr.fvar}"
  /- Revert those assumptions -/
  let (reverted, mvarId) ← (← getMainGoal).revert toRevert
  setGoals [mvarId]
  trace[Utils] "Goal after reverting: {← getMainGoal}"
  /- Introduce the let binding -/
  Utils.addDeclTac x e (← inferType e) true fun x => do
  /- This is taken from `refold_let` -/
  Mathlib.Tactic.runDefEqTactic (Mathlib.Tactic.refoldFVars  #[x.fvarId!]) none "transparentRefold"
  /- Reintroduce the assumptions -/
  let (_, mvarId) ← (← getMainGoal).introNP reverted.size
  setGoals [mvarId]
  pure ()

elab "glet" x:ident " := " e:term : tactic =>
  withMainContext do
  transparent_refold x.getId (← Tactic.elabTerm e none)

elab "glet" x:ident ":" ty:term " := " e:term : tactic =>
  withMainContext do
  let ty ← Tactic.elabTerm ty none
  transparent_refold x.getId (← Tactic.elabTerm e (expectedType? := ty))

example (x y z : Nat) (h0 : x + y = z) (h1 : x + y = 3) (_ : z ≤ 4) : x + y + z = 3 + z := by
  glet a := x + y
  omega

example (x y z : Nat) (h0 : x + y = z) (h1 : x + y = 3) (_ : z ≤ 4) : x + y + z = 3 + z := by
  glet a := x + y
  glet b := a + z
  omega

example (x y z : Nat) (h0 : x + y = z) (h1 : x + y = 3) (_ : z ≤ 4) : x + y + z = 3 + z := by
  glet a : Nat := x + y
  glet b : Nat := a + z
  omega

end Aeneas.GLet
