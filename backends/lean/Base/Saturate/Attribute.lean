import Lean
import Base.Utils
import Base.Extensions

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Tactic
open Utils Extensions

namespace Saturate

initialize registerTraceClass `Saturate
initialize registerTraceClass `Saturate.attribute

namespace Attribute

/-- The saturation attribute is a map from rule set name to set of rules.

    We store the forward saturation rules as a discrimination tree which maps to
    pairs of a matching expression and the lemma to apply if the expression matches.

    Note that the matching expression uses lambdas for all the quantifiers used in
    the theorem.

    For instance, we might want to have the following rule:
    ```
    ∀ {α} (l : List α) f, (l.map f).length = l.length
    ```
    while using the pattern:
    ```
    l.map f
    ```
    If so, the pattern we save below is actually:
    ```
    λ {α} (l : List α), l.map f
    ```
    This way, if we introduce meta-variables for all the quantified variables and
    successfully match the pattern with an expression, we know exactly how to instantiate
    the lemma above.

    Also note that we store the number of binders.
 -/
structure SaturateAttribute where
  attr : AttributeImpl
  ext : MapDiscrTreeExtension (Nat × Expr × Name)
  deriving Inhabited

-- The ident is the name of the saturation set, the term is the pattern.
syntax (name := aeneas_saturate) "aeneas_saturate" " (" &"set" " := " ident ")" " (" &"pattern" " := " term ")" : attr

def elabSaturateAttribute (stx : Syntax) : MetaM (Name × Syntax) :=
  withRef stx do
    match stx with
    | `(attr| aeneas_saturate (set := $set) (pattern := $pat)) => do
      pure (set.getId, pat)
    | _ => throwUnsupportedSyntax

initialize saturateAttr : SaturateAttribute ← do
  let ext ← Extensions.mkMapDiscrTreeExtension `aeneas_saturate_map
  let attrImpl : AttributeImpl := {
    name := `aeneas_saturate
    descr := "Saturation attribute"
    add := fun thName stx attrKind => do
      trace[Saturate.attribute] "Theorem: {thName}"
      -- TODO: use the attribute kind
      unless attrKind == AttributeKind.global do
        throwError "invalid attribute {attrKind}: must be global"
      -- Ignore some auxiliary definitions (see the comments for attrIgnoreMutRec)
      attrIgnoreAuxDef thName (pure ()) do
        -- Lookup the theorem
        let env ← getEnv
        let thDecl := env.constants.find! thName
        MetaM.run' do
        -- Analyze the theorem
        let v ← MetaM.run' do
          let ty := thDecl.type
          -- Strip the quantifiers
          forallTelescope ty.consumeMData fun fvars _ => do
          let numFVars := fvars.size
          -- Elaborate the pattern
          trace[Saturate.attribute] "Syntax: {stx}"
          let (setName, pat) ← elabSaturateAttribute stx
          trace[Saturate.attribute] "Syntax: setName: {setName}, pat: {pat}"
          let pat ← instantiateMVars (← Elab.Term.elabTerm pat none |>.run')
          trace[Saturate.attribute] "Pattern: {pat}"
          -- Check that the pattern contains all the quantified variables
          let allFVars ← fvars.foldlM (fun hs arg => getFVarIds arg hs) HashSet.empty
          let patFVars ← getFVarIds pat (← getFVarIds (← inferType pat))
          trace[Saturate.attribute] "allFVars: {← allFVars.toList.mapM FVarId.getUserName}"
          trace[Saturate.attribute] "patFVars: {← patFVars.toList.mapM FVarId.getUserName}"
          let remFVars := patFVars.toList.foldl (fun hs fvar => hs.erase fvar) allFVars
          unless remFVars.isEmpty do
            let remFVars ← remFVars.toList.mapM FVarId.getUserName
            throwError "The pattern does not contain all the variables quantified in the theorem; those are not included in the pattern: {remFVars}"
          -- Create the pattern
          let patExpr ← mkLambdaFVars fvars pat
          trace[Saturate.attribute] "Pattern expression: {patExpr}"
          -- Create the discrimination tree key - we use the default configuration
          let (_, _, patWithMetas) ← lambdaMetaTelescope patExpr
          trace[Saturate.attribute] "patWithMetas: {patWithMetas}"
          let config : WhnfCoreConfig := {}
          let key ← DiscrTree.mkPath patWithMetas config
          trace[Saturate.attribute] "key: {key}"
          --
          pure (setName, key, numFVars, patExpr, thName)
        -- Store
        let env := ext.addEntry env v
        setEnv env
    -- TODO: local attribute
    -- erase := fun ...
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl, ext := ext }

def SaturateAttribute.find? (s : SaturateAttribute) (setName : Name) (e : Expr) :
  MetaM (Array (Nat × Expr × Name)) := do
  match (s.ext.getState (← getEnv)).find? setName with
  | none => pure #[]
  | some dTree =>
    -- We use the default configuration
    let config : WhnfCoreConfig := {}
    dTree.getMatch e config

def SaturateAttribute.getState (s : SaturateAttribute) : MetaM (NameMap (DiscrTree (Nat × Expr × Name))) := do
  pure (s.ext.getState (← getEnv))

def showStoredSaturateAttribute : MetaM Unit := do
  let st ← saturateAttr.getState
  let s := f!"{st.toList}"
  IO.println s

end Attribute

end Saturate
