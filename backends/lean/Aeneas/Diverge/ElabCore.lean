import Lean
import Aeneas.Utils
import Aeneas.Std.Primitives
import Aeneas.Extensions

namespace Aeneas

namespace Diverge

open Lean Elab Term Meta
open Utils Extensions

-- We can't define and use trace classes in the same file
initialize registerTraceClass `Diverge
initialize registerTraceClass `Diverge.elab
initialize registerTraceClass `Diverge.def
initialize registerTraceClass `Diverge.def.sigmas
initialize registerTraceClass `Diverge.def.prods
initialize registerTraceClass `Diverge.def.genBody
initialize registerTraceClass `Diverge.def.genBody.visit
initialize registerTraceClass `Diverge.def.valid
initialize registerTraceClass `Diverge.def.unfold

-- For the attribute (for higher-order functions)
initialize registerTraceClass `Diverge.attr

-- Attribute

-- divspec attribute
structure DivSpecAttr where
  attr : AttributeImpl
  ext  : DiscrTreeExtension Name
  deriving Inhabited

/- The persistent map from expressions to divspec theorems. -/
initialize divspecAttr : DivSpecAttr ← do
  let ext ← mkDiscrTreeExtension `divspecMap
  let attrImpl : AttributeImpl := {
    name := `divspec
    descr := "Marks theorems to use with the `divergent` encoding"
    add := fun thName stx attrKind => do
      Attribute.Builtin.ensureNoArgs stx
      -- TODO: use the attribute kind
      unless attrKind == AttributeKind.global do
        throwError "invalid attribute divspec, must be global"
      -- Lookup the theorem
      let env ← getEnv
      let thDecl := env.constants.find! thName
      let fKey : Array (DiscrTree.Key) ← MetaM.run' (do
        /- The theorem should have the shape:
           `∀ ..., is_valid_p k (λ k => ...)`

           Dive into the ∀:
         -/
        let (_, _, fExpr) ← forallMetaTelescope thDecl.type.consumeMData
        /- Dive into the argument of `is_valid_p`: -/
        fExpr.consumeMData.withApp fun _ args => do
        if args.size ≠ 7 then throwError "Invalid number of arguments to is_valid_p"
        let fExpr := args.get! 6
        /- Dive into the lambda: -/
        let (_, _, fExpr) ← lambdaMetaTelescope fExpr.consumeMData
        trace[Diverge] "Registering divspec theorem for {fExpr}"
        -- Convert the function expression to a discrimination tree key
        DiscrTree.mkPath fExpr)
      let env := ext.addEntry env (fKey, thName)
      setEnv env
      trace[Diverge] "Saved the environment"
      pure ()
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl, ext := ext }

def DivSpecAttr.find? (s : DivSpecAttr) (e : Expr) : MetaM (Array Name) := do
  (s.ext.getState (← getEnv)).getMatch e

def DivSpecAttr.getState (s : DivSpecAttr) : MetaM (DiscrTree Name) := do
  pure (s.ext.getState (← getEnv))

def showStoredDivSpec : MetaM Unit := do
  let st ← divspecAttr.getState
  -- TODO: how can we iterate over (at least) the values stored in the tree?
  --let s := st.toList.foldl (fun s (f, th) => f!"{s}\n{f} → {th}") f!""
  let s := f!"{st}"
  IO.println s

end Diverge

end Aeneas
