import Lean
import Aeneas.Do.Elab

/-! # Delaborator for new `do` pattern matching logic -/

open Lean PrettyPrinter Delaborator SubExpr 

namespace Aeneas
namespace Do
namespace Delab

/-- Enter leading `fun` binders, collecting `(fvarId, name)` for each. -/
partial def enterLams (acc : Array (FVarId × Name))
    (k : Array (FVarId × Name) → DelabM α) : DelabM α := do
  match (← getExpr) with
  | .lam n _ _ _ =>
    withBindingBody' n pure fun fv =>
      enterLams (acc.push (fv.fvarId!, n)) k
  | _ => k acc

/-- Enter outer `fun` binders and chained `Function.uncurry`s for flat tuples. -/
partial def enterUncurryChain (acc : Array (FVarId × Name))
    (k : Array (FVarId × Name) → DelabM α) : DelabM α :=
  enterLams acc fun acc' => do
    if (← getExpr).isAppOfArity ``Function.uncurry 4 then
      withAppArg <| enterUncurryChain acc' k
    else
      k acc'

def buildTupleTerm (pats : Array Term) : DelabM Term := do
  let head := pats[0]!
  let tail := pats.extract 1 pats.size
  `(($head, $tail,*))

/-- Build a pattern for each binder, folding any immediate destructuring of
    `fv` (tuple via `Function.uncurry`, or ctor via `T.casesOn`) into a nested
    pattern. `k` runs on the resulting body. -/
partial def delabBinders (binders : List (FVarId × Name)) (k : DelabM α) :
    DelabM (Array Term × α) := do
  match binders with
  | [] => return (#[], ← k)
  | (fv, name) :: rest =>
    if let some r ← tupleBind? fv rest then return r
    if let some r ← ctorBind? fv rest then return r
    leafBind name rest
where
  splitRec (inner : Array (FVarId × Name)) (rest : List (FVarId × Name)) :
      DelabM (Array Term × Array Term × α) := do
    let (all, a) ← delabBinders (inner.toList ++ rest) k
    let n := inner.size
    return (all.extract 0 n, all.extract n all.size, a)
  /-- Tuple destructuring via `Function.uncurry`. -/
  tupleBind? (fv : FVarId) (rest : List (FVarId × Name)) :
      DelabM (Option (Array Term × α)) := do
    let e ← getExpr
    unless e.isAppOfArity ``Function.uncurry 5 do return none
    let val := e.appArg!
    unless val.isFVar ∧ val.fvarId! == fv do return none
    withAppFn <| withAppArg <| enterUncurryChain #[] fun inner => do
      let (innerPats, restPats, a) ← splitRec inner rest
      let fvPat ← buildTupleTerm innerPats
      return some (#[fvPat] ++ restPats, a)
  /-- Ctor destructuring via single-ctor `T.casesOn` (excluding `Prod`). -/
  ctorBind? (fv : FVarId) (rest : List (FVarId × Name)) :
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
  leafBind (name : Name) (rest : List (FVarId × Name)) : DelabM (Array Term × α) := do
    let leafPat : TSyntax `term := ⟨Lean.mkIdent name⟩
    let (restPats, a) ← delabBinders rest k
    return (#[leafPat] ++ restPats, a)

/-- `Function.uncurry (fun x₁ … xₙ => body) val` → `let (x₁, …, xₙ) := val; body` -/
@[delab app.Function.uncurry]
def delabUncurryLet : Delab := do
  unless Aeneas.customDoElab.get (← getOptions) do failure
  let valStx ← withAppArg delab
  let (pats, bodyStx) ← withAppFn <| withAppArg <|
    enterUncurryChain #[] fun outerBinders => do
      delabBinders outerBinders.toList delab
  let tupleStx ← buildTupleTerm pats
  `(let $tupleStx:term := $valStx
    $bodyStx)

/-- `T.casesOn val (fun f₁ … fₙ => body)` → `let ⟨f₁, …, fₙ⟩ := val; body` -/
@[delab app]
def delabSingleCtorCasesOn : Delab := do
  unless Aeneas.customDoElab.get (← getOptions) do failure
  let e ← getExpr
  let .const (.str typeName "casesOn") _ := e.getAppFn | failure
  let some (.inductInfo { ctors := [_], numParams, .. }) := (← getEnv).find? typeName | failure
  let discrStx ← withNaryArg (numParams + 1) delab
  let (binders, bodyStx) ← withNaryArg (numParams + 2) <|
    enterLams #[] fun bs => do return (bs.map fun (_, b) => (Lean.mkIdent b), ← delab)
  `(let ⟨$binders,*⟩ := $discrStx
    $bodyStx)

private structure CtorBindShape where
  xName : Name
  numParams : Nat

/-- Recognise `fun _x => T.casesOn _x …` for single-ctor `T ≠ Prod`. -/
private def parseCtorBind? (arg : Expr) : DelabM CtorBindShape := do
  let .lam xName _ body _ := arg | failure
  let .const (.str typeName "casesOn") _ := body.getAppFn | failure
  let some (.inductInfo { ctors := [_], numParams, .. }) := (← getEnv).find? typeName
    | failure
  return { xName, numParams }

/-- Walk a `Bind.bind` chain into `doElem`s, recognising tuple and ctor
    destructuring continuations in addition to plain binds and lets. -/
partial def aeneasDelabDoElems : DelabM (List DoElem) := do
  let e ← getExpr
  if e.isAppOfArity ``Bind.bind 6 then
    let α := e.getAppArgs[2]!
    let ma ← withAppFn <| withAppArg delab
    let arg := e.appArg!
    if arg.isAppOfArity ``Function.uncurry 4 then
      tupleBind ma
    else 
      try 
        let ctor ← parseCtorBind? arg 
        ctorBind ctor ma
      catch _ =>
        plainBind α ma
  else if e.isLet then
    letBind
  else
    return [← `(doElem| $(← delab):term)]
where
  /-- `let (x₁, …, xₙ) ← e` -/
  tupleBind (ma : Term) : DelabM (List DoElem) := do
    let (pats, rest) ← withAppArg <|
      enterUncurryChain #[] fun outerBinders =>
        delabBinders outerBinders.toList aeneasDelabDoElems
    let tupleStx ← buildTupleTerm pats
    return (← `(doElem| let $tupleStx:term ← $ma:term)) :: rest
  /-- `let ⟨f₁, …, fₙ⟩ ← e` -/
  ctorBind (ctor : CtorBindShape) (ma : Term) : DelabM (List DoElem) := do
    let (pats, rest) ← withAppArg <| withBindingBody ctor.xName <|
      withNaryArg (ctor.numParams + 2) <|
        enterLams #[] fun ctorBinders =>
          delabBinders ctorBinders.toList aeneasDelabDoElems
    return (← `(doElem| let ⟨$pats,*⟩ ← $ma:term)) :: rest
  /-- `let n ← e` (or bare `e` when the result is unused/`Unit`) -/
  plainBind (α : Expr) (ma : Term) : DelabM (List DoElem) :=
    withAppArg do
      let .lam _ _ body _ ← getExpr | failure
      withBindingBodyUnusedName fun n => do
        let rest ← aeneasDelabDoElems
        let nStx : Term := ⟨n⟩
        let item ←
          if body.hasLooseBVars then `(doElem| let $nStx:term ← $ma:term)
          else if α.isConstOf ``Unit ∨ α.isConstOf ``PUnit then `(doElem| $ma:term)
          else `(doElem| let _ ← $ma:term)
        return item :: rest
  /-- `let n : T := v` / `have n : T := v` -/
  letBind : DelabM (List DoElem) := do
    let .letE n t v b nondep ← getExpr | failure
    let n ← getUnusedName n b
    let stxT ← descend t 0 delab
    let stxV ← descend v 1 delab
    Meta.withLetDecl n t v (nondep := nondep) fun fvar =>
      descend (b.instantiate1 fvar) 2 do
        let rest ← aeneasDelabDoElems
        let item ←
          if nondep then `(doElem| have $(mkIdent n) : $stxT := $stxV)
          else `(doElem| let $(mkIdent n) : $stxT := $stxV)
        return item :: rest

open Parser Term

/-- Top-level `do`-block delab, restricted to the `Std.Result` monad. -/
@[delab app.Bind.bind]
def aeneasDelabDo : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  unless Aeneas.customDoElab.get (← getOptions) do failure
  let e ← getExpr
  -- only use the new `do` delaborator for `Result _` do blocks
  unless e.isAppOfArity ``Bind.bind 6 do failure
  unless e.getAppArgs[0]!.isConstOf ``Aeneas.Std.Result do failure
  let elems ← aeneasDelabDoElems
  let items ← elems.toArray.mapM (`(doSeqItem|$(·):doElem))
  `(do $items:doSeqItem*)

end Delab
end Do
end Aeneas
