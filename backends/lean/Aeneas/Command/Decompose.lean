/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

namespace Aeneas.Command.Decompose

open Lean Elab Term Meta Command

-- ============================================================================
-- Pattern representation
-- ============================================================================

/-- Pattern describing which sub-expression to extract from a function body. -/
inductive DecomposePattern where
  | letRange (start count : Nat)
  | letAt (index : Nat) (inner : DecomposePattern)
  | full
  | branch (index : Nat) (inner : DecomposePattern)
  | lam (count : Nat) (inner : DecomposePattern)
  | appFun (inner : DecomposePattern)
  | argArg (index : Nat) (inner : DecomposePattern)
  deriving Repr, Inhabited

-- ============================================================================
-- Syntax
-- ============================================================================

declare_syntax_cat decompose_pat

syntax "letRange " num num : decompose_pat
syntax "letAt " num " (" decompose_pat ")" : decompose_pat
syntax "full" : decompose_pat
syntax "branch " num " (" decompose_pat ")" : decompose_pat
syntax "branch " num " full" : decompose_pat
syntax "lam " num " (" decompose_pat ")" : decompose_pat
syntax "lam " num " full" : decompose_pat
syntax "appFun " "(" decompose_pat ")" : decompose_pat
syntax "appFun " "full" : decompose_pat
syntax "argArg " num " (" decompose_pat ")" : decompose_pat
syntax "argArg " num " full" : decompose_pat

partial def elabDecomposePat : Syntax → Except String DecomposePattern
  | `(decompose_pat| letRange $start $count) =>
    return .letRange start.getNat count.getNat
  | `(decompose_pat| letAt $idx ($inner)) => do
    return .letAt idx.getNat (← elabDecomposePat inner)
  | `(decompose_pat| full) =>
    return .full
  | `(decompose_pat| branch $idx ($inner)) => do
    return .branch idx.getNat (← elabDecomposePat inner)
  | `(decompose_pat| branch $idx full) =>
    return .branch idx.getNat .full
  | `(decompose_pat| lam $n ($inner)) => do
    return .lam n.getNat (← elabDecomposePat inner)
  | `(decompose_pat| lam $n full) =>
    return .lam n.getNat .full
  | `(decompose_pat| appFun ($inner)) => do
    return .appFun (← elabDecomposePat inner)
  | `(decompose_pat| appFun full) =>
    return .appFun .full
  | `(decompose_pat| argArg $idx ($inner)) => do
    return .argArg idx.getNat (← elabDecomposePat inner)
  | `(decompose_pat| argArg $idx full) =>
    return .argArg idx.getNat .full
  | stx => throw s!"Unknown decompose pattern: {stx}"

syntax decompose_clause := decompose_pat " => " ident

syntax (name := decomposeCmd) "#decompose " ident ident (ppLine decompose_clause)* : command

-- ============================================================================
-- Binding representation
-- ============================================================================

/-- A single let-binding (pure or monadic) in a flattened binding sequence. -/
structure BindingEntry where
  name : Name
  type : Expr
  value : Expr       -- pure: the value; monadic: the computation
  fvar : Expr
  isMonadic : Bool
  monadExpr : Option Expr := none  -- the monad `m` (for monadic bindings)
  deriving Inhabited

-- ============================================================================
-- Bind / ite / dite matching
-- ============================================================================

/-- Match `Bind.bind` or `bind` applied to 6 args.
    Returns `(m, inst, α, β, computation, continuation)`. -/
def matchBind? (e : Expr) : Option (Expr × Expr × Expr × Expr × Expr × Expr) := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  guard ((fn.isConstOf ``Bind.bind || fn.isConstOf ``bind) && args.size == 6)
  return (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, args[5]!)

def matchIte? (e : Expr) : Option (Expr × Expr × Expr × Expr × Expr) := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  guard (fn.isConstOf ``ite && args.size == 5)
  return (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)

def matchDite? (e : Expr) : Option (Expr × Expr × Expr × Expr × Expr) := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  guard (fn.isConstOf ``dite && args.size == 5)
  return (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)

-- ============================================================================
-- Parsing: expression → flat binding sequence + terminal
-- ============================================================================

/-- CPS-style parser: opens all pure/monadic let-binders, introduces fvars,
    then calls `k` with the accumulated entries and the terminal expression. -/
partial def withParsedBindings (e : Expr) (acc : Array BindingEntry)
    (k : Array BindingEntry → Expr → MetaM α) : MetaM α := do
  -- Pure let
  match e with
  | .letE name type value body _nonDep =>
    withLetDecl name type value fun fvar => do
      let body' := body.instantiate1 fvar
      withParsedBindings body' (acc.push ⟨name, type, value, fvar, false, none⟩) k
  | _ =>
    -- Monadic bind
    match matchBind? e with
    | some (m, _inst, _α, _β, computation, continuation) =>
      match continuation with
      | .lam lname ltype lbody lbinfo =>
        withLocalDecl lname lbinfo ltype fun fvar => do
          let lbody' := lbody.instantiate1 fvar
          withParsedBindings lbody' (acc.push ⟨lname, ltype, computation, fvar, true, some m⟩) k
      | _ => k acc e
    | none => k acc e

-- ============================================================================
-- Reconstruction: binding entries → Expr
-- ============================================================================

/-- Rebuild an expression from `bindings[startIdx .. endIdx-1]` followed by `terminal`.
    Abstracts fvars bottom-up using `mkLambdaFVars` / `mkLetFVars`. -/
def rebuildBindings (bindings : Array BindingEntry) (terminal : Expr)
    (startIdx endIdx : Nat) : MetaM Expr := do
  let mut result := terminal
  let mut i := endIdx
  while i > startIdx do
    i := i - 1
    let entry := bindings[i]!
    if entry.isMonadic then
      let cont ← mkLambdaFVars #[entry.fvar] result
      result ← mkAppM ``Bind.bind #[entry.value, cont]
    else
      result ← mkLetFVars #[entry.fvar] result
  return result

-- ============================================================================
-- Tuple helpers
-- ============================================================================

/-- Nested product type `T₁ × T₂ × ⋯ × Tₖ` (right-associated). -/
def mkProdType (types : Array Expr) : MetaM Expr := do
  if types.size == 0 then throwError "mkProdType: empty"
  if types.size == 1 then return types[0]!
  let mut r := types.back!
  for i in (List.range (types.size - 1)).reverse do
    r ← mkAppM ``Prod #[types[i]!, r]
  return r

/-- Nested tuple `(v₁, (v₂, (…, vₖ)))`. -/
def mkTuple (values : Array Expr) : MetaM Expr := do
  if values.size == 0 then throwError "mkTuple: empty"
  if values.size == 1 then return values[0]!
  let mut r := values.back!
  for i in (List.range (values.size - 1)).reverse do
    r ← mkAppM ``Prod.mk #[values[i]!, r]
  return r

/-- Project element `idx` from a nested tuple of `totalSize` components. -/
partial def mkProjection (tuple : Expr) (totalSize idx : Nat) : MetaM Expr := do
  if totalSize ≤ 1 then return tuple
  if idx == 0 then mkAppM ``Prod.fst #[tuple]
  else do
    let snd ← mkAppM ``Prod.snd #[tuple]
    mkProjection snd (totalSize - 1) (idx - 1)

-- ============================================================================
-- Free-variable filtering
-- ============================================================================

/-- Which of `available` appear free in `e`? Preserves order. -/
def filterRelevantFVars (e : Expr) (available : Array Expr) : MetaM (Array Expr) :=
  available.filterM fun fv => pure (e.containsFVar fv.fvarId!)

/-- Collect all non-implementation-detail fvars from the local context that appear
    free in `e`, in context order. This captures fvars from function parameters,
    binding fvars opened by navigation patterns (`letAt`, `branch`, `lam`), etc. -/
def collectFreeLocalFVars (e : Expr) : MetaM (Array Expr) := do
  let lctx ← getLCtx
  let mut result : Array Expr := #[]
  for decl in lctx do
    if !decl.isImplementationDetail && e.containsFVar decl.fvarId then
      result := result.push (mkFVar decl.fvarId)
  return result

/-- Abstract over `fvars`, always creating lambda binders (even for let-decl fvars).
    Standard `mkLambdaFVars` creates let-bindings for let-decl fvars, which is wrong
    when building extracted function definitions that should take parameters. -/
private def mkLamAbstract (fvars : Array Expr) (body : Expr) : MetaM Expr := do
  let mut result := body
  for fv in fvars.reverse do
    let decl ← fv.fvarId!.getDecl
    result := .lam decl.userName decl.type (result.abstract #[fv]) decl.binderInfo
  return result

/-- Abstract over `fvars`, always creating forall binders (even for let-decl fvars).
    Standard `mkForallFVars` creates let-types for let-decl fvars, which is wrong
    when building extracted function type signatures. -/
private def mkForallAbstract (fvars : Array Expr) (body : Expr) : MetaM Expr := do
  let mut result := body
  for fv in fvars.reverse do
    let decl ← fv.fvarId!.getDecl
    result := .forallE decl.userName decl.type (result.abstract #[fv]) decl.binderInfo
  return result

-- ============================================================================
-- Helpers: adding definitions (with noncomputable fallback)
-- ============================================================================

/-- Check if an expression transitively references any noncomputable or opaque constant. -/
private def hasNoncomputableDep (env : Environment) (e : Expr) : Bool :=
  e.foldConsts false fun n acc =>
    acc || isNoncomputable env n ||
    match env.find? n with
    | some (.opaqueInfo _) => true
    | _ => false

/-- Add a definition. Uses `addAndCompile` + realizations when possible (for simp
    unfolding). Falls back to `addDecl` + noncomputable tag when the value depends
    on noncomputable or opaque constants (which cause deferred IR errors). -/
private def addDefinition (name : Name) (levelParams : List Name)
    (type value : Expr) (srcIsNoncomputable : Bool) : MetaM Unit := do
  let decl : DefinitionVal := {
    name, levelParams, type, value,
    hints := .abbrev, safety := .safe, all := [name]
  }
  let env ← getEnv
  let isNC := srcIsNoncomputable || hasNoncomputableDep env value
  if isNC then
    addDecl (.defnDecl decl)
    Lean.enableRealizationsForConst name
    modifyEnv fun env' => noncomputableExt.tag env' name
  else
    addAndCompile (.defnDecl decl)
    Lean.enableRealizationsForConst name

-- ============================================================================
-- Core extraction: `full`
-- ============================================================================

/-- Extract the whole expression as a new definition.
    Returns the call expression that replaces it. -/
def extractFull (body : Expr) (newName : Name)
    (levelParams : List Name) (srcIsNoncomputable : Bool) : MetaM Expr := do
  let relevantFVars ← collectFreeLocalFVars body
  let fnValue ← mkLamAbstract relevantFVars body
  let fnType  ← mkForallAbstract relevantFVars (← inferType body)
  addDefinition newName levelParams fnType fnValue srcIsNoncomputable
  return mkAppN (mkConst newName (levelParams.map Level.param)) relevantFVars

-- ============================================================================
-- Core extraction: `letRange`
-- ============================================================================

/-- Extract `count` consecutive bindings starting at `start`.
    Returns the **full** modified body (wrapping bindings before the range too). -/
def extractLetRange (bindings : Array BindingEntry) (terminal : Expr)
    (start count : Nat) (newName : Name)
    (levelParams : List Name) (srcIsNoncomputable : Bool) : MetaM Expr := do
  let n := bindings.size            -- number of actual bindings
  let totalPositions := n + 1       -- bindings + terminal
  let endPos := start + count
  if endPos > totalPositions || count == 0 then
    throwError "letRange {start} {count}: out of range (total positions = {totalPositions})"

  let includesTerminal := (endPos == totalPositions)

  -- Determine if the range is monadic (has any monadic binding)
  let rangeBindings := bindings[start : endPos].toArray
  let hasMonadic := rangeBindings.any (·.isMonadic)

  -- Get monad expression from the first monadic binding
  let getMonadExpr : MetaM (Option Expr) := do
    for entry in rangeBindings do
      if let some m := entry.monadExpr then return some m
    return none

  -- Helper: add the definition and build the call expression.
  -- Uses `collectFreeLocalFVars` to capture all relevant fvars from the local
  -- context (function params, navigation fvars from letAt/branch/lam, etc.).
  let addDef (fnValue : Expr) : MetaM Expr := do
    let relevantFVars ← collectFreeLocalFVars fnValue
    let fnValueClosed ← mkLamAbstract relevantFVars fnValue
    let fnTypeClosed  ← mkForallAbstract relevantFVars (← inferType fnValue)
    addDefinition newName levelParams fnTypeClosed fnValueClosed srcIsNoncomputable
    return mkAppN (mkConst newName (levelParams.map Level.param)) relevantFVars

  if includesTerminal then
    -- ── Case A: range goes to the end ──────────────────────────────────
    let extractedBody ← rebuildBindings bindings terminal start n
    let callExpr ← addDef extractedBody
    rebuildBindings bindings callExpr 0 start

  else
    -- ── Case B: range does NOT include terminal ────────────────────────
    let contExpr ← rebuildBindings bindings terminal endPos n
    let extractedFVars := rangeBindings.map (·.fvar)
    let neededFVars ← filterRelevantFVars contExpr extractedFVars
    let lastEntry := bindings[start + count - 1]!

    if neededFVars.size == 1 && neededFVars[0]!.fvarId! == lastEntry.fvar.fvarId! then
      -- ── Optimized: only the last variable is needed ──────────────────
      -- Build the extracted body: all bindings in [start, endPos-1], with
      -- the last binding's value as the terminal. If the last binding is
      -- pure but the range has monadic bindings, wrap in `pure`.
      let termVal := lastEntry.value
      let needsWrap := hasMonadic && !lastEntry.isMonadic
      let extractedTerminal ← if needsWrap then do
        let some monadExpr ← getMonadExpr | throwError "letRange: no monad found for pure"
        mkAppOptM ``Pure.pure #[some monadExpr, none, none, some termVal]
      else pure termVal
      let extractedBody ← rebuildBindings bindings extractedTerminal start (endPos - 1)
      let callExpr ← addDef extractedBody
      if hasMonadic then
        -- Use mkLamAbstract to create a proper lambda even if lastEntry.fvar
        -- is a let-decl (from a pure binding in a mixed-mode range)
        let cont ← mkLamAbstract #[lastEntry.fvar] contExpr
        let replacement ← mkAppM ``Bind.bind #[callExpr, cont]
        rebuildBindings bindings replacement 0 start
      else
        -- Pure: use a let-binding for the replacement
        withLetDecl lastEntry.name (← inferType lastEntry.fvar) callExpr fun newFvar => do
          let contExprSubst := contExpr.replaceFVar lastEntry.fvar newFvar
          let replacement ← mkLetFVars #[newFvar] contExprSubst
          rebuildBindings bindings replacement 0 start

    else if neededFVars.size == 0 then
      -- ── No variables needed (side-effect only range) ─────────────────
      -- Build the extracted body from all range bindings. The terminal is
      -- the last binding's value (for a single monadic binding) or we
      -- need to rebuild the full range with `pure ()` as terminal.
      if hasMonadic then
        -- Rebuild ALL range bindings with `pure ()` as terminal
        let some monadExpr ← getMonadExpr | throwError "letRange: no monad found for pure"
        let pureUnit ← mkAppOptM ``Pure.pure #[some monadExpr, none, none, some (mkConst ``Unit.unit)]
        let extractedBody ← rebuildBindings bindings pureUnit start endPos
        let callExpr ← addDef extractedBody
        -- The extracted function returns `m Unit`. Create a fresh Unit-typed
        -- fvar for the continuation (not lastEntry.fvar which has the wrong type).
        withLocalDeclD `_ (mkConst ``Unit) fun unitFvar => do
          let cont ← mkLambdaFVars #[unitFvar] contExpr
          let replacement ← mkAppM ``Bind.bind #[callExpr, cont]
          rebuildBindings bindings replacement 0 start
      else
        let extractedBody ← rebuildBindings bindings lastEntry.value start (endPos - 1)
        let _callExpr ← addDef extractedBody
        rebuildBindings bindings contExpr 0 start

    else
      -- ── General: multiple variables needed → tuple return ────────────
      let neededTypes ← neededFVars.mapM (inferType ·)
      let tupleVal ← mkTuple neededFVars
      let returnExpr ← if hasMonadic then do
        -- Build: pure (v1, v2, ..., vk) using the monad from bindings
        let some monadExpr ← getMonadExpr | throwError "letRange: no monad found for pure"
        mkAppOptM ``Pure.pure #[some monadExpr, none, none, some tupleVal]
      else
        pure tupleVal
      let extractedBody ← rebuildBindings bindings returnExpr start endPos
      let callExpr ← addDef extractedBody

      -- Build the destructuring replacement
      let tupleType ← mkProdType neededTypes

      -- Helper: create let-bindings for tuple projections
      --   let v1 := _tup.1; let v2 := _tup.2; ...; contExpr
      let mkTupleDestructBindings (tupFVar : Expr) (body : Expr) : MetaM Expr := do
        let mut result := body
        for i in (List.range neededFVars.size).reverse do
          let fv := neededFVars[i]!
          let proj ← mkProjection tupFVar neededFVars.size i
          let fvType ← inferType fv
          let fvName ← fv.fvarId!.getUserName
          -- Abstract fv out of result: use Expr.abstract directly to avoid
          -- mkLambdaFVars creating let-bindings for let-decl fvars
          result := .letE fvName fvType proj (result.abstract #[fv]) false
        return result

      if hasMonadic then do
        withLocalDeclD `_tup tupleType fun tupFVar => do
          let innerBody ← mkTupleDestructBindings tupFVar contExpr
          let innerCont ← mkLambdaFVars #[tupFVar] innerBody
          let replacement ← mkAppM ``Bind.bind #[callExpr, innerCont]
          rebuildBindings bindings replacement 0 start
      else do
        -- Pure tuple destructuring
        withLocalDeclD `_tup tupleType fun tupFVar => do
          let innerBody ← mkTupleDestructBindings tupFVar contExpr
          let contBody ← mkLambdaFVars #[tupFVar] innerBody
          let replacement := (Expr.app contBody callExpr).headBeta
          rebuildBindings bindings replacement 0 start

-- ============================================================================
-- Navigation helpers (for composite patterns)
-- ============================================================================

/-- Modify branch `idx` of an ite/dite/match expression.
    Calls `action` on the branch body; returns the reconstructed expression. -/
def modifyBranch (e : Expr) (idx : Nat) (action : Expr → MetaM Expr) : MetaM Expr := do
  -- Try ite
  if let some (α, inst, cond, thenB, elseB) := matchIte? e then
    if idx == 0 then
      let thenB' ← action thenB
      return mkApp5 (mkConst ``ite e.getAppFn.constLevels!) α inst cond thenB' elseB
    else if idx == 1 then
      let elseB' ← action elseB
      return mkApp5 (mkConst ``ite e.getAppFn.constLevels!) α inst cond thenB elseB'
    else throwError "branch {idx}: ite has only branches 0 (then) and 1 (else)"
  -- Try dite
  if let some (α, inst, cond, thenB, elseB) := matchDite? e then
    if idx == 0 then
      -- thenB is a lambda: fun h : cond => body
      let thenB' ← modifyLambdaBody thenB action
      return mkApp5 (mkConst ``dite e.getAppFn.constLevels!) α inst cond thenB' elseB
    else if idx == 1 then
      let elseB' ← modifyLambdaBody elseB action
      return mkApp5 (mkConst ``dite e.getAppFn.constLevels!) α inst cond thenB elseB'
    else throwError "branch {idx}: dite has only branches 0 (then) and 1 (else)"
  -- Try match (casesOn): branches are the last arguments
  -- For now, treat as a generic app and modify the appropriate arg
  -- The user can use `argArg` for fine-grained control
  throwError "branch {idx}: expression is not an ite or dite; use argArg for match"
where
  modifyLambdaBody (e : Expr) (action : Expr → MetaM Expr) : MetaM Expr := do
    match e with
    | .lam name type body binfo =>
      withLocalDecl name binfo type fun fvar => do
        let body' := body.instantiate1 fvar
        let modifiedBody ← action body'
        mkLambdaFVars #[fvar] modifiedBody
    | _ => action e

/-- Open `n` lambda binders, apply `action` to the inner body, close back. -/
partial def modifyUnderLambdas (e : Expr) (n : Nat) (action : Expr → MetaM Expr) : MetaM Expr := do
  if n == 0 then action e
  else match e with
  | .lam name type body binfo =>
    withLocalDecl name binfo type fun fvar => do
      let body' := body.instantiate1 fvar
      let modifiedBody ← modifyUnderLambdas body' (n - 1) action
      mkLambdaFVars #[fvar] modifiedBody
  | _ => throwError "lam {n}: expected lambda, got {← ppExpr e}"

/-- Modify the function part of an application. -/
def modifyAppFun (e : Expr) (action : Expr → MetaM Expr) : MetaM Expr := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  if args.size == 0 then throwError "appFun: expression is not an application"
  let fn' ← action fn
  return mkAppN fn' args

/-- Modify argument `idx` of an application (0-indexed, explicit args). -/
def modifyAppArg (e : Expr) (idx : Nat) (action : Expr → MetaM Expr) : MetaM Expr := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  if idx >= args.size then
    throwError "argArg {idx}: application has only {args.size} arguments"
  let args' ← args.mapIdxM fun i arg => if i == idx then action arg else pure arg
  return mkAppN fn args'

-- ============================================================================
-- Navigate to the i-th binding's VALUE and modify it
-- ============================================================================

/-- Navigate to the value of the `idx`-th binding and apply `action` to it.
    Returns the modified full expression. -/
partial def modifyBindingValue (e : Expr) (idx : Nat)
    (action : Expr → MetaM Expr) : MetaM Expr := do
  if idx == 0 then
    -- Modify the current binding's value
    match e with
    | .letE name type value body nonDep =>
      let value' ← action value
      return .letE name type value' body nonDep
    | _ =>
      match matchBind? e with
      | some (m, inst, α, β, computation, continuation) =>
        let computation' ← action computation
        return mkApp6 (mkConst ``Bind.bind (e.getAppFn.constLevels!)) m inst α β computation' continuation
      | none => throwError "letAt 0: not a let or bind"
  else
    -- Navigate past this binding
    match e with
    | .letE name type value body _nonDep =>
      withLetDecl name type value fun fvar => do
        let body' := body.instantiate1 fvar
        let modifiedBody ← modifyBindingValue body' (idx - 1) action
        mkLetFVars #[fvar] modifiedBody
    | _ =>
      match matchBind? e with
      | some (m, inst, α, β, computation, continuation) =>
        match continuation with
        | .lam lname ltype lbody lbinfo =>
          withLocalDecl lname lbinfo ltype fun fvar => do
            let lbody' := lbody.instantiate1 fvar
            let modifiedBody ← modifyBindingValue lbody' (idx - 1) action
            let newCont ← mkLambdaFVars #[fvar] modifiedBody
            return mkApp6 (mkConst ``Bind.bind (e.getAppFn.constLevels!)) m inst α β computation newCont
        | _ => throwError "letAt: bind continuation is not a lambda"
      | none => throwError "letAt {idx}: reached terminal before binding"

-- ============================================================================
-- Apply a single clause (pattern + name) to the current body
-- ============================================================================

/-- Apply one decompose clause: navigate with the pattern, extract, replace.
    Returns the modified function body. -/
partial def applyClause (body : Expr) (pat : DecomposePattern) (newName : Name)
    (levelParams : List Name)
    (srcIsNoncomputable : Bool) : MetaM Expr := do
  match pat with
  | .full =>
    extractFull body newName levelParams srcIsNoncomputable

  | .letRange start count =>
    withParsedBindings body #[] fun bindings terminal => do
      extractLetRange bindings terminal start count newName levelParams srcIsNoncomputable

  | .letAt idx inner =>
    modifyBindingValue body idx fun value => do
      applyClause value inner newName levelParams srcIsNoncomputable

  | .branch idx inner =>
    modifyBranch body idx fun branchBody => do
      applyClause branchBody inner newName levelParams srcIsNoncomputable

  | .lam n inner =>
    modifyUnderLambdas body n fun innerBody => do
      applyClause innerBody inner newName levelParams srcIsNoncomputable

  | .appFun inner =>
    modifyAppFun body fun fn => do
      applyClause fn inner newName levelParams srcIsNoncomputable

  | .argArg idx inner =>
    modifyAppArg body idx fun arg => do
      applyClause arg inner newName levelParams srcIsNoncomputable

-- ============================================================================
-- Proof generation
-- ============================================================================

/-- Look up a lemma name in the environment, trying multiple candidates. -/
private def findLemma (candidates : Array Name) : MetaM (Option Name) := do
  let env ← getEnv
  for candidate in candidates do
    if env.contains candidate then return some candidate
  return none

/-- Prove a single step: `∀ params, body_before = body_after`.
    Uses `rfl`, then `simp only [newFnName, bind_assoc_eq]`, then
    `simp [newFnName, bind_assoc_eq]` (with global @[simp] set).
    Raises an error if the proof fails. -/
def proveStep (goalType : Expr) (newFnName : Name) : TermElabM Expr := do
  let mvar ← mkFreshExprMVar goalType
  let mvarId := mvar.mvarId!
  let (_, mvarId) ← mvarId.intros
  -- Try rfl
  try
    mvarId.refl
    return ← instantiateMVars mvar
  catch _ => pure ()
  -- Build simp lemma names
  let mut simpNames : Array Name := #[newFnName]
  if let some baEq ← findLemma #[`Aeneas.Std.bind_assoc_eq, `bind_assoc_eq] then
    simpNames := simpNames.push baEq
  if let some pb ← findLemma #[`LawfulMonad.pure_bind, `pure_bind] then
    simpNames := simpNames.push pb
  -- Strategy 1: simp only [f_i, bind_assoc_eq, pure_bind]
  try
    let remaining ← Lean.Elab.Tactic.run mvarId do
      let lemmas ← simpNames.mapM fun n =>
        `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)
      Lean.Elab.Tactic.evalTactic (← `(tactic| simp only [$[$lemmas],*]))
    if remaining.isEmpty then
      return ← instantiateMVars mvar
  catch _ => pure ()
  -- Strategy 2: unfold + simp (for noncomputable defs where simp only fails)
  try
    let remaining ← Lean.Elab.Tactic.run mvarId do
      Lean.Elab.Tactic.evalTactic
        (← `(tactic| unfold $(mkIdent newFnName)))
      let lemmas ← simpNames.filterMapM fun n => do
        if n != newFnName then
          some <$> `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)
        else pure none
      if lemmas.isEmpty then
        Lean.Elab.Tactic.evalTactic (← `(tactic| rfl))
      else
        Lean.Elab.Tactic.evalTactic (← `(tactic| simp only [$[$lemmas],*]))
    if remaining.isEmpty then
      return ← instantiateMVars mvar
  catch _ => pure ()
  throwError "#decompose: could not prove decomposition step for '{newFnName}' \
    with simp only [{simpNames.toList}]"

-- ============================================================================
-- Main command elaboration
-- ============================================================================

@[command_elab decomposeCmd]
def elabDecompose : CommandElab := fun stx => do
  match stx with
  | `(command| #decompose $fnId $eqId $[$clauses]*) => do
    liftTermElabM do
      -- Resolve the function name
      let some fnConst ← Term.resolveId? fnId | throwError "Unknown: {fnId}"
      let fnName := fnConst.constName!
      let env ← getEnv
      let some info := env.find? fnName | throwError "No declaration: {fnName}"
      let fnValue ← match info with
        | .defnInfo val => pure val.value
        | _ => throwError "{fnName} is not a definition"
      let _fnType := info.type
      let levelParams := info.levelParams
      let srcIsNoncomputable := isNoncomputable env fnName

      -- Parse all clauses
      let mut parsedClauses : Array (DecomposePattern × Name) := #[]
      for clauseStx in clauses do
        match clauseStx with
        | `(decompose_clause| $pat => $name) => do
          let p ← match elabDecomposePat pat with
            | .ok p => pure p
            | .error msg => throwError msg
          -- Resolve the new name in the current namespace
          let ns ← getCurrNamespace
          let fullName := if ns.isAnonymous then name.getId else ns ++ name.getId
          parsedClauses := parsedClauses.push (p, fullName)
        | _ => throwError "Invalid decompose clause syntax"

      -- Open the function parameters
      lambdaTelescope fnValue fun params body => do
        let mut currentBody := body
        let mut stepProofs : Array Expr := #[]  -- closed proof terms (∀ params, ...)

        -- Apply each clause sequentially; prove each step
        for (pat, newName) in parsedClauses do
          let prevBody := currentBody
          currentBody ← applyClause currentBody pat newName levelParams srcIsNoncomputable

          -- Prove: ∀ params, prevBody = currentBody
          let stepEqType ← mkForallFVars params (← mkEq prevBody currentBody)
          let stepProof ← proveStep stepEqType newName
          stepProofs := stepProofs.push stepProof

        -- Compose step proofs into the final theorem: ∀ params, f params = currentBody
        -- Since f params ≡ body (definitionally), and step_0 proves body = body_1,
        -- we can chain: step_0.trans step_1.trans ... step_n
        let composedProof ←
          if stepProofs.isEmpty then
            -- No clauses: f params = body by rfl
            let rflProof ← mkAppM ``Eq.refl #[mkAppN (mkConst fnName (levelParams.map Level.param)) params]
            mkLambdaFVars params rflProof
          else
            -- Apply each step proof to params, then chain with Eq.trans
            let mut proof := mkAppN stepProofs[0]! params
            for i in List.range (stepProofs.size - 1) do
              let nextStep := mkAppN stepProofs[i + 1]! params
              proof ← mkAppM ``Eq.trans #[proof, nextStep]
            mkLambdaFVars params proof

        let lhs := mkAppN (mkConst fnName (levelParams.map Level.param)) params
        let eqType ← mkEq lhs currentBody
        let eqTypeForall ← mkForallFVars params eqType

        let eqName ← do
          let ns ← getCurrNamespace
          let rawName := eqId.getId
          pure (if ns.isAnonymous then rawName else ns ++ rawName)

        -- Add the theorem
        addDecl (.thmDecl {
          name        := eqName
          levelParams := levelParams
          type        := eqTypeForall
          value       := composedProof
        })

        logInfo m!"#decompose: created {parsedClauses.size} definition(s) and theorem '{eqName}'"
  | _ => throwError "Invalid #decompose syntax"

end Aeneas.Command.Decompose
