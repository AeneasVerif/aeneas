module
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Tactic.Congr
public section

open Lean Meta Parser Elab Tactic

namespace FCongr

syntax (name := fcongr) "fcongr" (ppSpace num)? : tactic

@[tactic fcongr]
meta def evalFCongr : Tactic
| `(tactic| fcongr $[$n?]?) => withMainContext do
  let hugeDepth := 1000000
  let depth := n?.map (·.getNat) |>.getD hugeDepth
  withTransparency .reducible do
    liftMetaTactic fun mvarId => mvarId.congrN depth
| _ => throwUnsupportedSyntax

end FCongr
