module
public import Aeneas.SepLogic.IProp
@[expose] public section

namespace Aeneas.SepLogic

open Lean PrettyPrinter Delaborator SubExpr

@[app_delab ipure]
meta def delabIpure : Delab := do
  guard ((← getExpr).isAppOfArity ``ipure 1)
  let proposition ← withAppArg delab
  `(⌜$proposition⌝)

@[app_delab iand]
meta def delabIand : Delab := do
  guard ((← getExpr).isAppOfArity ``iand 2)
  let lhs ← withNaryArg 0 delab
  let rhs ← withNaryArg 1 delab
  `(iprop($lhs ∧ $rhs))

@[app_delab Entails]
meta def delabEntails : Delab := do
  guard ((← getExpr).isAppOfArity ``Entails 2)
  let lhs ← withNaryArg 0 delab
  let rhs ← withNaryArg 1 delab
  `($lhs ⊢ $rhs)

/-- Is `e` the quantifier `quant` (`iexists`/`iforall`) applied to a lambda? -/
private meta def isQuantLam (quant : Name) (e : Expr) : Bool :=
  e.isAppOfArity quant 2 && e.appArg!.isLambda

/-- At `quant fun x => …`: the binders of the nested `quant` lambdas, merged, and the body. -/
private meta partial def delabQuantBinders (quant : Name) : DelabM (Array Ident × Term) :=
  withAppArg <| withBindingBodyUnusedName fun x => do
    if isQuantLam quant (← getExpr) then
      let (binders, body) ← delabQuantBinders quant
      return (#[⟨x⟩] ++ binders, body)
    else
      return (#[⟨x⟩], ← delab)

/-- `iexists fun a => iexists fun b => H` as `iprop(∃ a b, H)`; an eta-reduced `iexists J` is
left as is. -/
@[app_delab iexists]
meta def delabIexists : Delab := do
  guard (isQuantLam ``iexists (← getExpr))
  let (binders, body) ← delabQuantBinders ``iexists
  let binders ← binders.mapM fun x => `(binderIdent| $x:ident)
  `(iprop(∃ $binders:binderIdent*, $body))

/-- `iforall fun a => iforall fun b => H` as `iprop(∀ a b, H)`; an eta-reduced `iforall J` is
left as is. -/
@[app_delab iforall]
meta def delabIforall : Delab := do
  guard (isQuantLam ``iforall (← getExpr))
  let (binders, body) ← delabQuantBinders ``iforall
  let binders : TSyntaxArray
      [`ident, ``Lean.Parser.Term.hole, ``Lean.Parser.Term.bracketedBinder] :=
    binders.map (⟨·.raw⟩)
  `(iprop(∀ $binders*, $body))

end Aeneas.SepLogic
