module
public import Aeneas.SepLogic.Basic
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
  let lhs ← withNaryArg 0 delab
  let rhs ← withNaryArg 1 delab
  `(iprop($lhs ∧ $rhs))

@[app_delab Entails]
meta def delabEntails : Delab := do
  guard ((← getExpr).isAppOfArity ``Entails 2)
  let lhs ← withNaryArg 0 delab
  let rhs ← withNaryArg 1 delab
  `($lhs ⊢ $rhs)

end Aeneas.SepLogic
