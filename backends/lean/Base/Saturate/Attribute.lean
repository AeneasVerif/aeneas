import Lean
import Base.Utils
import Base.Extensions

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Tactic
open Utils Extensions

namespace Saturate

initialize registerTraceClass `Saturate
initialize registerTraceClass `Saturate.attribute

namespace Attribute

structure Key where
  setName : Name
  discrTreeKey : DiscrTreeKey
  deriving Inhabited

instance : ToFormat Key where
  format k := f!"({k.setName}, {k.discrTreeKey})"

instance : ToMessageData Key where
  toMessageData k := m!"({k.setName}, {k.discrTreeKey})"

structure Rule where
  numBinders : Nat
  pattern : Expr
  thName : Name
  deriving Inhabited, BEq

instance : ToFormat Rule where
  format x := f!"({x.numBinders}, {x.pattern}, {x.thName})"

instance : ToMessageData Rule where
  toMessageData x := m!"({x.numBinders}, {x.pattern}, {x.thName})"

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

    # Erasing attributes (`attribute [- ...] foo`)
    We also need to store a map from the names of the theorems we registered as rules to matching
    patterns.

    When erasing attributes, Lean instructs us to remove the attribute from a declaration
    by giving us the *name* of the declaration (and that's it). In particular, we don't have the
    pattern anymore under our hand, which is what we need to remove the rule form the set
    above. A second issue is also that we can't remove keys from discrimination trees.

    Our solution is to save a map from the names of the theorems to the rule which is
    currently registered for it.

    Whenever we do a forward saturation and a rule matches, we check if the rule is still
    applicable for this rule (by checking if the name of the theorem still maps to this rule).

    Remark: those design choices constrain us to have at most one rule per theorem (which should be fine).
-/
structure Rules where
  nameToRule : NameMap Rule
  rules : NameMap (DiscrTree Rule)
  deriving Inhabited

def Rules.empty : Rules := ⟨ RBMap.empty, RBMap.empty ⟩

abbrev Extension :=
  SimpleScopedEnvExtension (Key × Rule) Rules

private def Rules.insert (s : Rules) (kv : Key × Rule) : Rules :=
  let ⟨ nameToRule, rules ⟩ := s
  let ⟨ k, v ⟩ := kv
  let nameToRule := nameToRule.insert v.thName v
  -- Update the discrimination tree
  let dtree :=
    match rules.find? k.setName with
    | none => DiscrTree.empty
    | some dtree => dtree
  let dtree := dtree.insertCore k.discrTreeKey v
  let rules := rules.insert k.setName dtree
  --
  { nameToRule, rules }

private def Rules.erase (s : Rules) (thName : Name) : Rules :=
  let ⟨ nameToRule, rules ⟩ := s
  let nameToRule := nameToRule.erase thName
  ⟨ nameToRule, rules ⟩

def mkExtension (name : Name := by exact decl_name%) :
  IO Extension :=
  registerSimpleScopedEnvExtension {
    name          := name,
    initial       := Rules.empty,
    addEntry      := Rules.insert,
  }

/-- The saturation attribute. -/
structure SaturateAttribute where
  -- The attribute
  attr : AttributeImpl
  -- The rule sets
  ext : Extension
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
  let ext ← mkExtension `aeneas_saturate_map
  let attrImpl : AttributeImpl := {
    name := `aeneas_saturate
    descr := "Saturation attribute"
    add := fun thName stx attrKind => do
      trace[Saturate.attribute] "Theorem: {thName}"
      -- Check that the rule is not already registered
      let s := ext.getState (← getEnv)
      if let some rule := s.nameToRule.find? thName then
        throwError "A rule is already registered for {thName} with pattern {rule.pattern}: we can only register one rule per pattern"
      -- Ignore some auxiliary definitions (see the comments for attrIgnoreMutRec)
      attrIgnoreAuxDef thName (pure ()) do
        -- Lookup the theorem
        let env ← getEnv
        let thDecl := env.constants.find! thName
        MetaM.run' do
        -- Analyze the theorem
        let (key, rule) ← MetaM.run' do
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
          let key : Key := ⟨ setName, key ⟩
          let rule : Rule := ⟨ numFVars, patExpr, thName ⟩
          pure (key, rule)
        -- Store
        ScopedEnvExtension.add ext (key, rule) attrKind
    erase := fun thName => do
      let s := ext.getState (← getEnv)
      let s := s.erase thName
      modifyEnv fun env => ext.modifyState env fun _ => s
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl, ext := ext }

def SaturateAttribute.find? (s : SaturateAttribute) (setName : Name) (e : Expr) :
  MetaM (Array Rule) := do
  let s := s.ext.getState (← getEnv)
  match s.rules.find? setName with
  | none => pure #[]
  | some dTree =>
    -- We use the default configuration
    let config : WhnfCoreConfig := {}
    let rules ← dTree.getMatch e config
    -- Filter the rules which have been deactivated
    pure (rules.filter fun r => s.nameToRule.contains r.thName)

def SaturateAttribute.getState (s : SaturateAttribute) : MetaM Rules := do
  pure (s.ext.getState (← getEnv))

def showStoredSaturateAttribute : MetaM Unit := do
  let st ← saturateAttr.getState
  IO.println f!"nameToRule: {st.nameToRule.toList}"
  IO.println f!""
  IO.println f!"rules: {st.rules.toList}"

end Attribute

end Saturate
