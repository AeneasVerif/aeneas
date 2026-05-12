import Lean
import Aeneas.Do.Elab
import Aeneas.Std.Delab

/-! # Delaborator for new `do` pattern matching logic -/

open Lean PrettyPrinter Delaborator SubExpr
open Aeneas.Std.Delab (enterLams enterUncurryChain delabBinders buildTupleTerm delabUncurryAsTuple)

namespace Aeneas
namespace Do
namespace Delab

/-- `Std.uncurry (fun x₁ … xₙ => body) val` → `let (x₁, …, xₙ) := val; body`. -/
@[delab app.Aeneas.Std.uncurry]
def delabUncurryLet : Delab := do
  unless Aeneas.customDoElab.get (← getOptions) do failure
  -- only fire when fully applied
  unless (← getExpr).isAppOfArity ``_root_.Aeneas.Std.uncurry 5 do failure
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
    enterLams #[] fun bs => do return (bs.map fun (_, b, _) => (Lean.mkIdent b), ← delab)
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
    if arg.isAppOfArity ``_root_.Aeneas.Std.uncurry 4 then
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
    let (tupleStx, rest) ← withAppArg <| delabUncurryAsTuple aeneasDelabDoElems
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
