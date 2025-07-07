import Lean
import AeneasMeta.Utils
import AeneasMeta.Extensions

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Tactic

namespace Aeneas

open Utils Extensions

namespace Saturate

initialize registerTraceClass `Saturate
initialize registerTraceClass `Saturate.insertPartialMatch
initialize registerTraceClass `Saturate.explore
initialize registerTraceClass `Saturate.attribute
initialize registerTraceClass `Saturate.diagnostics

namespace Attribute

structure Key where
  discrTreeKey : DiscrTreeKey
  deriving Inhabited

instance : ToFormat Key where
  format k := f!"({k.discrTreeKey})"

instance : ToMessageData Key where
  toMessageData k := m!"({k.discrTreeKey})"

structure Pattern where
  pattern : Expr
  /- The variables bound in the theorem and that are used in the pattern -/
  boundVars : Array Nat
  /- If the pattern is for the type of a precondition, this contains the identifier
     of the free variable identifying this precondition (e.g., the pattern is
     `inBounds l q` while there is an assumption `h : inBounds l q`) -/
  instVar : Option Nat
deriving Inhabited, BEq

structure Rule where
  -- The source info allows to uniquely identify where the rule was introduced
  src : SourceInfo
  numBinders : Nat
  /- There can be several patterns. -/
  patterns : Array Pattern
  thName : Name
  deriving Inhabited, BEq

instance : ToFormat Pattern where
  format x := f!"{x.pattern}"

instance : ToMessageData Pattern where
  toMessageData x := m!"{x.pattern}"

instance : ToFormat Rule where
  format x := f!"({x.numBinders}, {x.patterns}, {x.thName})"

instance : ToMessageData Rule where
  toMessageData x := m!"({x.numBinders}, {x.patterns}, {x.thName})"

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
    When erasing attributes, Lean instructs us to remove the attribute from a declaration
    by giving us the *name* of the declaration (and that's it). In particular, we don't have the
    pattern anymore under our hand, which is what we need to remove the rule form the set
    above. A second issue is also that we can't remove keys from discrimination trees.
    Our solution is to save a set of the names of the deactivated theorems. We also
    save the set of all rules which were created, to make sure we do not create
    two rules for the same theorem (otherwise deactivating the theorem would deactivate
    the two rules, which may cause an unexpected behavior for the user).

    TODO: allow using several patterns.
-/
structure Rules where
  /- The set of rules.

     We actually save a *map* rather than a set: it is convenient useful
     to print error messages (if we detect that the user is trying to
     add the same theorem again, we can display the already existing rule).
   -/
  nameToRules : Std.HashMap Name Rule
  deactivatedRules : Std.HashSet Name
  rules : DiscrTree Rule
deriving Inhabited

def Rules.empty : Rules := {
  nameToRules := Std.HashMap.emptyWithCapacity,
  deactivatedRules := Std.HashSet.emptyWithCapacity
  rules := DiscrTree.empty
}

abbrev Extension :=
  SimpleScopedEnvExtension (Key × Rule) Rules

private def Rules.insert (s : Rules) (kv : Key × Rule) : Rules :=
  let { nameToRules, deactivatedRules, rules } := s
  let ⟨ k, v ⟩ := kv
  let nameToRules := nameToRules.insert v.thName v
  -- Update the discrimination tree
  let rules := rules.insertCore k.discrTreeKey v
  --
  { nameToRules, deactivatedRules, rules }

private def Rules.erase (s : Rules) (thName : Name) : Rules :=
  let { nameToRules, deactivatedRules, rules } := s
  /- Note that we can't remove a key from a discrimination tree, so we
     add the theorem name to the `deactivatedRules` set instead: when instantiating rules
     we check that their corresponding theorems are still active (i.e., they are still in
     `deactivatedRules`) -/
  let deactivatedRules := deactivatedRules.insert thName
  { nameToRules, deactivatedRules, rules }

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

def makeAttribute (mapName attributeName : Name) (elabAttribute : Syntax → MetaM (Option Syntax)) :
  IO SaturateAttribute := do
  let ext ← mkExtension mapName
  let attrImpl : AttributeImpl := {
    name := attributeName
    descr := "Saturation attribute to automatically introduce lemmas in the context"
    add := fun thName stx attrKind => do
      trace[Saturate.attribute] "Theorem: {thName}"
      -- Check that the rule is not already registered
      let s := ext.getState (← getEnv)
      if let some rule := s.nameToRules.get? thName then
        throwError "A rule is already registered for {thName} with pattern {rule.patterns}: we can only register one rule per pattern"
      -- Retrieve the source information
      let src ← do
        match stx with
        | .missing => throwError "Unexpected error: missing source information in the syntax tree"
        | .node info _ _
        | .atom info _
        | .ident info _ _ _ => pure info
      -- Ignore some auxiliary definitions (see the comments for attrIgnoreMutRec)
      attrIgnoreAuxDef thName (pure ()) do
        -- Lookup the theorem
        let env ← getEnv
        let some thDecl := env.findAsync? thName
          | throwError "Could not find theorem {thName}"
        -- Analyze the theorem
        let (key, rule) ← MetaM.run' do
          let sig := thDecl.sig.get
          let ty := sig.type
          /- Strip the quantifiers.

             We do this before elaborating the pattern because we need the universally quantified variables
             to be in the context.
          -/
          forallTelescope ty.consumeMData fun fvars _ => do
          let fvarsMap : Std.HashMap FVarId Nat := Std.HashMap.ofList (fvars.mapIdx (fun i fv => (fv.fvarId!, i))).toList
          let idToFVarMap : Std.HashMap Nat Expr := Std.HashMap.ofList (fvars.mapIdx (fun i fv => (i, fv))).toList
          let numFVars := fvars.size
          -- Elaborate the pattern
          trace[Saturate.attribute] "Syntax: {stx}"
          let pat ← elabAttribute stx
          trace[Saturate.attribute] "Syntpat: {pat}"
          /- Elaborate the user-provided pattern, if there is one.
             We also collect the set of free variables covered by this pattern.
             We then go through the remaining free variables in reverse order (the reason
             being that the type of some later variables often refers to some earlier
             variables) and use the free variables which have not been covered yet and
             which are assumptions (the type of their type is `Prop`) to introduce more
             patterns.

             Also note that we compute a list of pairs: (pattern, Option (free variable id)).
             We need the free variable id to know which variable to instantiate when we
             match a pattern corresponding to a precondition.

             # Ex.:
             ```
             @[aeneas_saturate (pattern := l[i]!)]
             theorem th {q} (h0 : inBounds l q) (h1 : i < l.length) : l[i]! < q`
             ```
             The pattern is `l[i]!` which covers variables `l` and `i` (but not `q`, `h0`, `h1`).
             We then look at the last variable which has not been covered so far (that is `h1`)
             and add the pattern `i < l.length`. When doing so we need to remember that the
             pattern `i < l.length` is for `h1`, so that we can instantiate the theorem when matching
             (i.e., if we find an assumption `h : i < l.length`, we need to instantiate `th` with it).
             We then look at the next one (`h0`) and add the pattern `in Bounds l q`. All the variables
             are now covered.
           -/
          let (first, patterns, patFVars) ← do
            match pat with
            | none =>
              trace[Saturate.attribute] "No pattern provided"
              pure (true, #[], Std.HashSet.emptyWithCapacity)
            | some pat =>
              let pat ← instantiateMVars (← Elab.Term.elabTerm pat none |>.run')
              trace[Saturate.attribute] "Pattern: {pat}"
              let patTy ← inferType pat
              let patFVars ← getFVarIds pat (← getFVarIds patTy)
              trace[Saturate.attribute] "patFVars: {← patFVars.toList.mapM FVarId.getUserName}"
              let boundVars := Array.range numFVars
              pure (false, #[(pat, boundVars, none)], patFVars)

          /- Go through the free variables from the last to the first to introduce additional patterns.
             Note that we only add patterns for variables whose type type is `Prop`. For instance, we
             would add a pattern for `h : x < y` but not for `x : ℕ` (in which case we throw an exception). -/
          let patterns ← do
            let mut first := first
            let mut patFVars := patFVars
            let mut patterns := patterns
            let ifvars := (fvars.mapIdx (fun i fv => (i, fv))).reverse
            trace[Saturate.attribute] "About to explore fvars: {ifvars}"
            for (i, fv) in ifvars do
              if patFVars.contains fv.fvarId! then continue
              else
                -- Create a pattern
                let pat ← inferType fv
                unless ← isProp pat do
                  throwError "Found a free variable not bound in the (optional) user provided pattern or in a precondition: {fv}"
                let curPatFVars ← getFVarIds pat (Std.HashSet.emptyWithCapacity)
                patFVars := patFVars.union (curPatFVars.insert fv.fvarId!)
                let boundVars :=
                  if first then Array.range numFVars
                  else
                    curPatFVars.toArray.map fun fvid => Std.HashMap.get! fvarsMap fvid
                trace[Saturate.attribute] "Adding pattern for var {i}: {pat}"
                patterns := patterns.push (pat, boundVars, some i)
            -- Sanity check: all the bound variables have been covered
            trace[Saturate.attribute] "patFVars: {patFVars.toList.map Expr.fvar}"
            let remFVars := patFVars.toList.foldl (fun hs fvar => hs.erase fvar) patFVars
            trace[Saturate.attribute] "remFVars: {remFVars.toList.map Expr.fvar}"
            unless remFVars.isEmpty do
              throwError "Not all the free variables in the theorem are covered by patterns: please report a bug"
            --
            pure patterns

          /- Process the patterns.
             We need to introduce lambdas to bind the variables present in the patterns, to create closed terms.
             This later allows us to introduce meta-variables when generating keys for the discrimination tree.
           -/
          let patterns : Array Pattern ← patterns.mapM fun (pat, boundVars, patVar) => do
            let fvars := boundVars.map fun i => idToFVarMap.get! i
            let patExpr ← mkLambdaFVars fvars pat
            pure { pattern := patExpr, boundVars, instVar := patVar }

          -- Create the rule and the key
          if patterns.size > 0 then
            let pattern := patterns[0]!
            let (_, _, patWithMetas) ← lambdaMetaTelescope pattern.pattern (some numFVars)
            trace[Saturate.attribute] "patWithMetas: {patWithMetas}"
            let key ← DiscrTree.mkPath patWithMetas
            trace[Saturate.attribute] "key: {key}"
            --
            let key : Key := ⟨ key ⟩
            let rule : Rule := ⟨ src, numFVars, patterns, thName ⟩
            pure (key, rule)
          else throwError "Unreachable: there should be at least one pattern"

        -- Store
        ScopedEnvExtension.add ext (key, rule) attrKind
    erase := fun thName => do
      let s := ext.getState (← getEnv)
      let s := s.erase thName
      modifyEnv fun env => ext.modifyState env fun _ => s
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl, ext := ext }


-- The ident is the name of the saturation set, the term is the pattern.
-- If `allow_loose` is specified, we allow not instantiating all the variables.
syntax (name := aeneas_saturate) "aeneas_saturate" (term)? : attr

def elabSaturateAttribute (stx : Syntax) : MetaM (Option Syntax) :=
  withRef stx do
    match stx with
    | `(attr| aeneas_saturate $[$pat]?) => do pure pat
    | _ => throwUnsupportedSyntax

initialize saturateAttr : SaturateAttribute ← do
  makeAttribute `aeneas_saturate_map `aeneas_saturate elabSaturateAttribute

def SaturateAttribute.find? (s : SaturateAttribute) (e : Expr) :
  MetaM (Array Rule) := do
  let s := s.ext.getState (← getEnv)
  let rules ← s.rules.getMatch e
  /- Only keep the rules (remove the partial matches - note that there shouldn't be any actually)
      and filter the rules which have been deactivated -/
  pure (rules.filter fun r => ¬ s.deactivatedRules.contains r.thName)

def SaturateAttribute.getState (s : SaturateAttribute) : MetaM Rules := do
  pure (s.ext.getState (← getEnv))

def SaturateAttribute.showStored (s : SaturateAttribute) : MetaM Unit := do
  let st ← s.getState
  IO.println f!"rules:\n{st.rules}"
  IO.println f!"deactivated rules:\n{st.deactivatedRules.toArray}"

end Attribute

end Saturate

end Aeneas
