import Lean
import Aeneas.Std.Primitives

/-! # Shared delaboration helpers for uncurry chains

These helpers are used by both the `⦃ ⦄` postcondition delaborator (`WP.lean`)
and the `do`-notation delaborator (`Do/Delab.lean`) to walk `Std.uncurry` chains
and produce binder patterns. -/

open Lean PrettyPrinter Delaborator SubExpr

namespace Aeneas.Std.Delab

/-- A binder entry collected while traversing lambda/uncurry layers:
- `FVarId` — the fvar introduced by the lambda
- `Name` — the binder name
- `Pos` — the SubExpr position of the enclosing lambda (for hover annotation) -/
abbrev BinderEntry := FVarId × Name × Pos

/-- Enter leading `fun` binders, collecting a `BinderEntry` for each.
Descends through the `SubExpr` reader via `withBindingBody'`.

Example: on `fun a b => body`, collects `[a, b]` and leaves the reader at `body`. -/
partial def enterLams (acc : Array BinderEntry)
    (k : Array BinderEntry → DelabM α) : DelabM α := do
  match (← getExpr) with
  | .lam n _ _ _ =>
    let pos ← getPos
    withBindingBody' n pure fun fv =>
      enterLams (acc.push (fv.fvarId!, n, pos)) k
  | _ => k acc

/-- Enter `fun` binders and chained `Std.uncurry`s, flattening all leaves.

Example: on `uncurry (fun a => uncurry (fun b c => body))`, collects `[a, b, c]`
and leaves the reader at `body`. -/
partial def enterUncurryChain (acc : Array BinderEntry)
    (k : Array BinderEntry → DelabM α) : DelabM α :=
  enterLams acc fun acc' => do
    if (← getExpr).isAppOfArity ``_root_.Aeneas.Std.uncurry 4 then
      withAppArg <| enterUncurryChain acc' k
    else
      k acc'

/-- Build tuple syntax `(p₀, p₁, ...)` from an array of pattern terms. -/
def buildTupleTerm (pats : Array Term) : DelabM Term := do
  let head := pats[0]!
  let tail := pats.extract 1 pats.size
  `(($head, $tail,*))

/-- Build a pattern for each binder, folding any immediate destructuring of
    `fv` (tuple via `Std.uncurry`, or ctor via `T.casesOn`) into a nested
    pattern. `k` runs on the resulting body. -/
partial def delabBinders (binders : List BinderEntry) (k : DelabM α) :
    DelabM (Array Term × α) := do
  match binders with
  | [] => return (#[], ← k)
  | (fv, name, binderPos) :: rest =>
    if let some r ← tupleBind? fv binderPos rest then return r
    if let some r ← ctorBind? fv rest then return r
    leafBind fv name binderPos rest
where
  splitRec (inner : Array BinderEntry) (rest : List BinderEntry) :
      DelabM (Array Term × Array Term × α) := do
    let (all, a) ← delabBinders (inner.toList ++ rest) k
    let n := inner.size
    return (all.extract 0 n, all.extract n all.size, a)
  /-- Tuple destructuring via `Std.uncurry`. -/
  tupleBind? (fv : FVarId) (tuplePos : Pos) (rest : List BinderEntry) :
      DelabM (Option (Array Term × α)) := do
    let e ← getExpr
    unless e.isAppOfArity ``_root_.Aeneas.Std.uncurry 5 do return none
    let val := e.appArg!
    unless val.isFVar ∧ val.fvarId! == fv do return none
    withAppFn <| withAppArg <| enterUncurryChain #[] fun inner => do
      let (innerPats, restPats, a) ← splitRec inner rest
      let fvPat : Term := annotatePos tuplePos (← buildTupleTerm innerPats)
      addTermInfo tuplePos fvPat.raw (.fvar fv) (isBinder := true)
      return some (#[fvPat] ++ restPats, a)
  /-- Ctor destructuring via single-ctor `T.casesOn` (excluding `Prod`). -/
  ctorBind? (fv : FVarId) (rest : List BinderEntry) :
      DelabM (Option (Array Term × α)) := do
    let e ← getExpr
    let .const (.str typeName "casesOn") _ := e.getAppFn | return none
    if typeName == ``Prod then return none
    let some (.inductInfo { ctors := [_], numParams, .. }) := (← getEnv).find? typeName
      | return none
    let args := e.getAppArgs
    unless args.size == numParams + 3 do return none
    let discr := args[numParams + 1]!
    unless discr.isFVar ∧ discr.fvarId! == fv do return none
    unless args[numParams + 2]!.isLambda do return none
    withNaryArg (numParams + 2) <| enterLams #[] fun ctorBinders => do
      let (ctorPats, restPats, a) ← splitRec ctorBinders rest
      let fvPat ← `(⟨$ctorPats,*⟩)
      return some (#[fvPat] ++ restPats, a)
  /-- No destructuring, bind `name` directly. -/
  leafBind (fv : FVarId) (name : Name) (binderPos : Pos) (rest : List BinderEntry) :
      DelabM (Array Term × α) := do
    let stx : Term := annotatePos binderPos ⟨Lean.mkIdent name⟩
    addTermInfo binderPos stx.raw (.fvar fv) (isBinder := true)
    let (restPats, a) ← delabBinders rest k
    return (#[stx] ++ restPats, a)

/-- Enter an `uncurry` chain, collect binder patterns via `delabBinders`,
and wrap them in a single tuple term. Returns `(tupleTerm, k_result)`.

Expects the reader to be positioned at the function argument of `uncurry`
(i.e., after `withAppArg`).

Example: on `fun a => uncurry (fun b c => body)`, produces `((a, b, c), bodyTerm)`. -/
def delabUncurryAsTuple (k : DelabM α) : DelabM (Term × α) :=
  enterUncurryChain #[] fun binders => do
    let (pats, a) ← delabBinders binders.toList k
    return (← buildTupleTerm pats, a)

end Aeneas.Std.Delab
