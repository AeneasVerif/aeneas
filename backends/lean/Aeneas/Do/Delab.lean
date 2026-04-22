import Lean
import Aeneas.Do.Elab

/-! # Delaborator for new `do` pattern matching logic -/

open Lean PrettyPrinter Delaborator SubExpr 

namespace Aeneas
namespace Do

/-- Partially applied `Function.uncurry (fun a b => body)` → `fun (a, b) => body`. -/
@[app_unexpander Function.uncurry]
def unexpUncurry : Unexpander
  | `($_ fun $a:ident $b:ident => $body) => `(fun ($a, $b) => $body)
  | _ => throw ()

/-- Extract binder names from a chain of `fun n₁ … nₖ => body`. -/
private def extractLamBinders : Expr → List Name
  | .lam n _ b _ => n :: extractLamBinders b
  | _ => []

/-- Enter `names.size` consecutive `fun` binders via `withBindingBody'`,
    collecting the corresponding `(fvarId, name)` pairs, then invoke `k`. -/
private partial def enterLamsAux (names : List Name)
    (acc : Array (FVarId × Name))
    (k : Array (FVarId × Name) → DelabM α) : DelabM α := do
  match names with
  | [] => k acc
  | n :: rest =>
    withBindingBody' n pure fun fv =>
      enterLamsAux rest (acc.push (fv.fvarId!, n)) k

/-- Walk past outer `fun` binders and chained 4-arg `Function.uncurry`s (the
    encoding emitted for flat `N`-tuples by `mkUncurries`), collecting each
    lambda binder as `(fvarId, name)`. Leaves SubExpr at the innermost body. -/
private partial def enterUncurryChain (acc : Array (FVarId × Name))
    (k : Array (FVarId × Name) → DelabM α) : DelabM α := do
  let e ← getExpr
  match e with
  | .lam n _ _ _ =>
    withBindingBody' n pure fun fv =>
      enterUncurryChain (acc.push (fv.fvarId!, n)) k
  | _ =>
    if e.isAppOfArity ``Function.uncurry 4 then
      withAppArg <| enterUncurryChain acc k
    else
      k acc

/-- Build a tuple term `(p₀, p₁, …, pₙ)` from `pats`. Requires `pats.size ≥ 2`. -/
private def buildTupleTerm (pats : Array (TSyntax `term)) : DelabM (TSyntax `term) := do
  guard (pats.size >= 2)
  let head := pats[0]!
  let tail : Array (TSyntax `term) := pats.extract 1 pats.size
  `(($head, $tail,*))

/-- Given a list of outer binders `(fv, name)`, build a `TSyntax \`term` pattern
    for each. At each step, check whether the current body starts with a
    destructuring of `fv` (either a `Function.uncurry … fv` chain or a
    `T.casesOn fv …`); if so, enter the destructuring, recurse on inner
    binders, and build a nested `(…, …, …)` or `⟨…⟩` pattern. Otherwise treat
    it as a leaf named `name`. After all binders are handled, `k` runs at the
    fully-advanced body and its result comes back alongside the patterns.

    Polymorphic over the body-action's return type so it serves both the
    monadic (`aeneasDelabDoElems` returning `doElem`s) and non-monadic
    (`delabUncurryLet` returning a term) callers. -/
partial def delabBinders (binders : List (FVarId × Name)) (k : DelabM α)
    : DelabM (Array (TSyntax `term) × α) := do
  match binders with
  | [] =>
    let a ← k
    return (#[], a)
  | (fv, name) :: rest =>
    let e ← getExpr
    -- Tuple destructuring: `Function.uncurry … fv` (possibly a nested chain).
    if e.isAppOfArity ``Function.uncurry 5 then
      let val := e.appArg!
      if val.isFVar ∧ val.fvarId! == fv then
        return ← withAppFn <| withAppArg <|
          enterUncurryChain #[] fun innerBinders => do
            guard (innerBinders.size >= 2)
            let (allPats, a) ← delabBinders (innerBinders.toList ++ rest) k
            let innerCount := innerBinders.size
            let innerPats := allPats.extract 0 innerCount
            let restPats := allPats.extract innerCount allPats.size
            let fvPat ← buildTupleTerm innerPats
            return (#[fvPat] ++ restPats, a)
    -- Ctor destructuring: `T.casesOn fv (fun f₁ … fₙ => …)`
    if let .const fnName _ := e.getAppFn then
      if let .str typeName "casesOn" := fnName then
        if typeName != ``Prod then
          if let some (.inductInfo indInfo) := (← getEnv).find? typeName then
            if indInfo.ctors.length == 1 then
              let args := e.getAppArgs
              let numParams := indInfo.numParams
              if args.size == numParams + 3 then
                let discr := args[numParams + 1]!
                if discr.isFVar ∧ discr.fvarId! == fv then
                  let names := extractLamBinders args[numParams + 2]!
                  if !names.isEmpty then
                    return ← withNaryArg (numParams + 2) <|
                      enterLamsAux names #[] fun ctorBinders => do
                        let (allPats, a) ← delabBinders (ctorBinders.toList ++ rest) k
                        let ctorCount := ctorBinders.size
                        let ctorPats := allPats.extract 0 ctorCount
                        let restPats := allPats.extract ctorCount allPats.size
                        let fvPat ← `(⟨$ctorPats,*⟩)
                        return (#[fvPat] ++ restPats, a)
    -- Leaf
    let leafPat : TSyntax `term := ⟨Lean.mkIdent name⟩
    let (restPats, a) ← delabBinders rest k
    return (#[leafPat] ++ restPats, a)

/-- `Function.uncurry (fun x₁ … xₙ => body) val` → `let (x₁, …, xₙ) := val; body`,
    including nested chain encodings of `N`-tuples (`N ≥ 2`). -/
@[delab app.Function.uncurry]
def delabUncurryLet : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 5)
  let valStx ← withAppArg delab
  let (pats, bodyStx) ← withAppFn <| withAppArg <|
    enterUncurryChain #[] fun outerBinders => do
      guard (outerBinders.size >= 2)
      delabBinders outerBinders.toList delab
  let tupleStx ← buildTupleTerm pats
  `(let $tupleStx:term := $valStx
    $bodyStx)

/-- `T.casesOn val (fun f₁ … fₙ => body)` → `let ⟨f₁, …, fₙ⟩ := val; body`
    for any single-constructor inductive `T` (other than `Prod`). -/
@[delab app]
def delabSingleCtorCasesOn : Delab := do
  let e ← getExpr
  let .const fnName _ := e.getAppFn | failure
  let .str typeName "casesOn" := fnName | failure
  guard (typeName != ``Prod)
  let some (.inductInfo indInfo) := (← getEnv).find? typeName | failure
  guard (indInfo.ctors.length == 1)
  let args := e.getAppArgs
  let numParams := indInfo.numParams
  guard (args.size == numParams + 3)
  let names := extractLamBinders args[numParams + 2]!
  guard (!names.isEmpty)
  let discrStx ← withNaryArg (numParams + 1) delab
  let bodyStx ← withNaryArg (numParams + 2) <|
    names.foldr (fun n d => withBindingBody n d) delab
  let binders := names.toArray.map Lean.mkIdent
  `(let ⟨$binders,*⟩ := $discrStx
    $bodyStx)

/-- Walk a `Bind.bind` chain collecting `doElem`s. Extends Lean's builtin
    `delabDoElems` with two continuation shapes emitted by our elaborator:
    `Function.uncurry (fun a b => body)` → `let (a, b) ← e`, and
    `fun _x => T.casesOn _x (fun f₁ … fₙ => body)` → `let ⟨f₁, …, fₙ⟩ ← e`.
    Nested destructurings of the bound values are folded into nested patterns
    via `delabBinders`. -/
partial def aeneasDelabDoElems : DelabM (List (TSyntax `doElem)) := do
  let e ← getExpr
  if e.isAppOfArity ``Bind.bind 6 then
    let α := e.getAppArgs[2]!
    let ma ← withAppFn <| withAppArg delab
    let arg := e.appArg!
    -- Tuple pattern: `Function.uncurry …` (possibly a chain for flat N-tuples).
    if arg.isAppOfArity ``Function.uncurry 4 then
      let (pats, rest) ← withAppArg <|
        enterUncurryChain #[] fun outerBinders => do
          guard (outerBinders.size >= 2)
          delabBinders outerBinders.toList aeneasDelabDoElems
      let tupleStx ← buildTupleTerm pats
      return (← `(doElem| let $tupleStx:term ← $ma:term)) :: rest
    -- Ctor pattern: `fun _x => T.casesOn _x (fun f₁ … fₙ => body)`
    if let .lam xName _ xBody _ := arg then
      if let .const fnName _ := xBody.getAppFn then
        if let .str typeName "casesOn" := fnName then
          if typeName != ``Prod then
            if let some (.inductInfo indInfo) := (← getEnv).find? typeName then
              if indInfo.ctors.length == 1 then
                let xArgs := xBody.getAppArgs
                let numParams := indInfo.numParams
                if xArgs.size == numParams + 3 ∧ xArgs[numParams + 1]! == .bvar 0 then
                  let names := extractLamBinders xArgs[numParams + 2]!
                  if !names.isEmpty then
                    let (pats, rest) ← withAppArg <| withBindingBody xName <|
                      withNaryArg (numParams + 2) <|
                        enterLamsAux names #[] fun ctorBinders =>
                          delabBinders ctorBinders.toList aeneasDelabDoElems
                    let elem ← `(doElem| let ⟨$pats,*⟩ ← $ma:term)
                    return elem :: rest
    -- Regular bind: fun n => body (mirrors Lean's delabDoElems)
    withAppArg do
      match (← getExpr) with
      | .lam _ _ body _ =>
        withBindingBodyUnusedName fun n => do
          let nStx : TSyntax `term := ⟨n⟩
          let rest ← aeneasDelabDoElems
          if body.hasLooseBVars then
            return (← `(doElem| let $nStx:term ← $ma:term)) :: rest
          else if α.isConstOf ``Unit ∨ α.isConstOf ``PUnit then
            return (← `(doElem| $ma:term)) :: rest
          else
            return (← `(doElem| let _ ← $ma:term)) :: rest
      | _ => failure
  else if e.isLet then
    let .letE n t v b nondep ← getExpr | unreachable!
    let n ← getUnusedName n b
    let stxT ← descend t 0 delab
    let stxV ← descend v 1 delab
    Meta.withLetDecl n t v (nondep := nondep) fun fvar =>
      let b := b.instantiate1 fvar
      descend b 2 do
        let rest ← aeneasDelabDoElems
        if nondep then
          return (← `(doElem| have $(mkIdent n) : $stxT := $stxV)) :: rest
        else
          return (← `(doElem| let $(mkIdent n) : $stxT := $stxV)) :: rest
  else
    let stx ← delab
    return [← `(doElem| $stx:term)]

open Parser Term

/-- Top-level `do`-block delab. Walks a `Bind.bind` chain with
    `aeneasDelabDoElems`, which understands tuple/ctor pattern continuations
    and so doesn't bail on them the way Lean's builtin `delabDo` does. -/
@[delab app.Bind.bind]
def aeneasDelabDo : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  guard <| (← getExpr).isAppOfArity ``Bind.bind 6
  let elems ← aeneasDelabDoElems
  let items ← elems.toArray.mapM (`(doSeqItem|$(·):doElem))
  `(do $items:doSeqItem*)

end Do
end Aeneas
