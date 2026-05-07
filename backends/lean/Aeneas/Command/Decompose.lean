/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Aeneas.Std.Primitives
import AeneasMeta.Simp.Simp
import AeneasMeta.Utils

/-!
# The `#decompose` command

`#decompose` extracts sub-expressions from a function body into auxiliary definitions,
producing a correctness theorem that rewrites the original function in terms of the
new helpers. This is useful for breaking large monadic functions into smaller pieces
that can be verified independently.

## Basic usage

```
#decompose originalFn eqThm
  pattern₁ => auxName₁
  pattern₂ => auxName₂
  ...
```

This creates auxiliary definitions `auxName₁`, `auxName₂`, ... and a theorem `eqThm`
proving `originalFn args = <body rewritten using the auxiliaries>`. The clauses are
applied sequentially: each clause sees the body as modified by previous clauses.

## Patterns

### `letRange start count`
Extract `count` consecutive let-bindings starting at index `start` (0-indexed).
Works for both pure (`let x := ...`) and monadic (`let x ← ...`) bindings.
When the continuation needs multiple variables from the range, the auxiliary
function returns a tuple.

```
def f (x : U32) : Result U32 := do
  let a ← x + 1#u32       -- binding 0
  let b ← a + 1#u32       -- binding 1
  let c ← b + 1#u32       -- binding 2
  c + 10#u32               -- terminal (position 3)

#decompose f f_eq
  letRange 0 3 => f_prefix  -- extracts bindings 0,1,2
-- f_prefix : U32 → Result U32
-- f_eq : f x = f_prefix x >>= fun c => c + 10#u32
```

### `full`
Extract the entire expression at the current position as a new definition.

```
#decompose f f_eq
  full => f_body
-- f_body x = <entire body of f>
-- f_eq : f x = f_body x
```

### `branch idx inner`
Navigate into branch `idx` of an `if-then-else`, `dite`, or `match`, then apply `inner`.
Branch 0 is `then`/first alternative, branch 1 is `else`/second alternative, etc.
For matches, automatically opens the pattern-variable lambdas.

```
def g (b : Bool) (x : U32) : Result U32 := do
  if b then
    let a ← x + 1#u32
    a + 2#u32
  else
    x + 10#u32

#decompose g g_eq
  branch 0 (letRange 0 2) => g_then  -- extract from the then-branch
```

### `letAt idx inner`
Navigate to the value of the `idx`-th binding, then apply `inner` to it.

### `lam n inner`
Open `n` lambda binders, then apply `inner` to the body.

### `appFun inner` / `argArg idx inner`
Navigate into the function or the `idx`-th argument of an application.

## Name reuse

When the same name appears in multiple clauses, `#decompose` checks whether the
new extraction is definitionally equal to the existing definition (at reducible
transparency). If equal, the existing definition is reused — no new definition
is created.

This is useful when the same operation appears at multiple positions:

```
def f (x y : U32) : Result U32 := do
  let x1 ← x + 1#u32
  let x2 ← x1 + 1#u32
  let x3 ← x2 + 1#u32
  let y1 ← y + 1#u32
  let y2 ← y1 + 1#u32
  let y3 ← y2 + 1#u32
  x3 + y3

#decompose f f_eq
  letRange 0 3 => add3    -- creates `add3`
  letRange 1 3 => add3    -- reuses `add3` (same body)
-- f_eq : f x y = do
--   let x3 ← add3 x
--   let y3 ← add3 y
--   x3 + y3
```

If the bodies differ, an error is raised with a detailed message showing both bodies.

A warning is emitted when two clauses produce identical definitions under different
names, suggesting to reuse the same name instead.

## Using existing definitions

Name reuse also works with definitions that already exist in the environment (e.g.,
from a previous `#decompose` call or manually written). If the name resolves to an
existing definition whose value matches the extraction, it is reused.

## Options

- `set_option Aeneas.Decompose.checkDuplicate false` — disable the warning when two
  clauses in the same `#decompose` call produce definitionally equal definitions
  under different names. Enabled by default.

- `set_option Aeneas.Decompose.useExisting false` — disable reuse of definitions
  that already exist in the environment. When false, only definitions introduced
  by the *current* `#decompose` call can be reused (by repeating the same name).
  Enabled by default.

## Tracing

Enable `set_option trace.Decompose true` to see a summary of created definitions.
-/

namespace Aeneas.Command.Decompose

open Lean Elab Term Meta Command
open Aeneas.Simp (mkSimpCtx SimpArgs)

initialize registerTraceClass `Decompose

/-- If true (default), warn when two clauses in the same `#decompose` call produce
    definitionally equal definitions under different names. -/
register_option Aeneas.Decompose.checkDuplicate : Bool := {
  defValue := true
  descr := "Warn when two decomposition clauses produce identical definitions with different names"
}

/-- If true (default), when a clause uses a name that already exists in the environment,
    check that the existing definition is definitionally equal and reuse it.
    If false, only look at definitions introduced by the current `#decompose` call. -/
register_option Aeneas.Decompose.useExisting : Bool := {
  defValue := true
  descr := "Allow reusing definitions that already exist in the environment"
}

/-- State for the decompose command: tracks definitions introduced so far. -/
structure DecomposeState where
  introduced : Array (Name × Expr) := #[]

/-- Monad for the decompose command: `MetaM` with additional state tracking
    which definitions have been introduced in the current `#decompose` sequence. -/
abbrev DecomposeM := StateRefT DecomposeState MetaM

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

/-- A single let-binding (pure or monadic) in a flattened binding sequence.
    For simple binds, `fvars` has one element. For tuple-destructuring binds
    (`let (a, b, c) ← comp`), `fvars` has one element per component. -/
structure BindingEntry where
  name : Name
  type : Expr
  value : Expr       -- pure: the value; monadic: the computation
  fvars : Array Expr -- bound variables (1 for simple, N for tuple destructuring)
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

/-- Match `@ite α cond inst thenBranch elseBranch`. -/
def matchIte? (e : Expr) : Option (Expr × Expr × Expr × Expr × Expr) := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  guard (fn.isConstOf ``ite && args.size == 5)
  return (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)

/-- Match `@dite α cond inst thenBranch elseBranch`. -/
def matchDite? (e : Expr) : Option (Expr × Expr × Expr × Expr × Expr) := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  guard (fn.isConstOf ``dite && args.size == 5)
  return (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)

-- ============================================================================
-- Parsing: expression → flat binding sequence + terminal
-- ============================================================================

/-- CPS-style parser: opens all pure/monadic let-binders, introduces fvars,
    then calls `k` with the accumulated entries and the terminal expression.
    Handles `Function.uncurry` continuations from tuple-destructuring binds. -/
partial def withParsedBindings (e : Expr) (acc : Array BindingEntry)
    (k : Array BindingEntry → Expr → DecomposeM α) : DecomposeM α := do
  -- Pure let
  match e with
  | .letE name type value body _nonDep =>
    withLetDecl name type value fun fvar => do
      let body' := body.instantiate1 fvar
      withParsedBindings body' (acc.push ⟨name, type, value, #[fvar], false, none⟩) k
  | _ =>
    -- Monadic bind
    match matchBind? e with
    | some (m, _inst, _α, _β, computation, continuation) =>
      -- Open the continuation, handling Function.uncurry for tuple binds
      openBindContinuation m computation continuation acc k
    | none => k acc e
where
  /-- Unwrap nested `Function.uncurry` applications, collecting the lambda binders.
      Returns the flattened array of (name, type, binderInfo) and the innermost body. -/
  openUncurryLambdas (cont : Expr) (binders : Array (Name × Expr × BinderInfo)) :
      MetaM (Array (Name × Expr × BinderInfo) × Expr) := do
    -- Check for Function.uncurry: @Function.uncurry α β γ f
    if cont.isAppOfArity ``Function.uncurry 4 then
      let f := cont.getAppArgs[3]!
      match f with
      | .lam lname ltype _lbody lbinfo =>
        let binders := binders.push (lname, ltype, lbinfo)
        -- The body may contain another uncurry or be the innermost lambda
        -- We need to enter the lambda first to see the body
        withLocalDecl lname lbinfo ltype fun _fvar => do
          let lbody := _lbody.instantiate1 _fvar
          openUncurryLambdas lbody binders
      | _ => return (binders, cont)
    else
      -- Not an uncurry — check if it's a final lambda (innermost of the chain)
      match cont with
      | .lam lname ltype _lbody lbinfo =>
        return (binders.push (lname, ltype, lbinfo), cont)
      | _ => return (binders, cont)
  /-- Open a bind continuation. Detects `Function.uncurry` chains for tuple
      destructuring and creates a single BindingEntry with all component fvars. -/
  openBindContinuation (m computation : Expr) (cont : Expr)
      (acc : Array BindingEntry) (k : Array BindingEntry → Expr → DecomposeM α) :
      DecomposeM α := do
    -- First, probe the structure to see if it's an uncurry chain
    let (binders, _) ← openUncurryLambdas cont #[]
    if binders.size > 1 then
      -- Tuple bind: open all binders, record a single entry with extraFVars
      openUncurryFVars m computation cont #[] acc k
    else
      -- Simple bind: single lambda
      match cont with
      | .lam lname ltype lbody lbinfo =>
        withLocalDecl lname lbinfo ltype fun fvar => do
          let lbody' := lbody.instantiate1 fvar
          withParsedBindings lbody' (acc.push ⟨lname, ltype, computation, #[fvar], true, some m⟩) k
      | _ => k acc e
  /-- Recursively open uncurry+lambda chains, collecting fvars into an array.
      When all binders are opened, creates a single BindingEntry and continues parsing. -/
  openUncurryFVars (m computation : Expr) (cont : Expr) (fvars : Array Expr)
      (acc : Array BindingEntry) (k : Array BindingEntry → Expr → DecomposeM α) :
      DecomposeM α := do
    if cont.isAppOfArity ``Function.uncurry 4 then
      let f := cont.getAppArgs[3]!
      match f with
      | .lam lname ltype lbody lbinfo =>
        withLocalDecl lname lbinfo ltype fun fvar => do
          let lbody' := lbody.instantiate1 fvar
          openUncurryFVars m computation lbody' (fvars.push fvar) acc k
      | _ => k acc e
    else
      -- Innermost part: should be a lambda
      match cont with
      | .lam lname ltype lbody lbinfo =>
        withLocalDecl lname lbinfo ltype fun fvar => do
          let lbody' := lbody.instantiate1 fvar
          let allFVars := fvars.push fvar
          let mainName := (← allFVars[0]!.fvarId!.getDecl).userName
          let mainType ← inferType allFVars[0]!
          let entry : BindingEntry := ⟨mainName, mainType, computation, allFVars, true, some m⟩
          withParsedBindings lbody' (acc.push entry) k
      | _ => k acc e

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
-- Reconstruction: binding entries → Expr
-- ============================================================================

/-- Build `Function.uncurry (fun x => body)` for a single pair layer.
    Always creates a lambda (not a let-binding), even for let-decl fvars. -/
private def mkUncurry (fvar : Expr) (body : Expr) : MetaM Expr := do
  let fn ← mkLamAbstract #[fvar] body
  mkAppM ``Function.uncurry #[fn]

/-- Rebuild an expression from `bindings[startIdx .. endIdx-1]` followed by `terminal`.
    Abstracts fvars bottom-up using `mkLambdaFVars` / `mkLetFVars`.
    Handles tuple-destructuring binds by reconstructing `Function.uncurry` chains. -/
def rebuildBindings (bindings : Array BindingEntry) (terminal : Expr)
    (startIdx endIdx : Nat) : MetaM Expr := do
  let mut result := terminal
  let mut i := endIdx
  while i > startIdx do
    i := i - 1
    let entry := bindings[i]!
    if entry.isMonadic then
      if entry.fvars.size > 1 then
        -- Tuple bind: rebuild Function.uncurry chain
        -- Build from inside out: last fvar first
        let mut cont ← mkLambdaFVars #[entry.fvars.back!] result
        -- Wrap each remaining fvar with uncurry (from second-to-last back to first)
        for j in (List.range (entry.fvars.size - 1)).reverse do
          cont ← mkUncurry entry.fvars[j]! cont
        result ← mkAppM ``Bind.bind #[entry.value, cont]
      else
        let cont ← mkLambdaFVars #[entry.fvars[0]!] result
        result ← mkAppM ``Bind.bind #[entry.value, cont]
    else
      result ← mkLetFVars #[entry.fvars[0]!] result
  return result

-- ============================================================================
-- Tuple helpers
-- ============================================================================

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
    free in `e` or in the types of collected fvars (dependency closure).
    This ensures extracted definitions include all necessary type parameters.
    Returns fvars in context order. -/
def collectFreeLocalFVars (e : Expr) : MetaM (Array Expr) := do
  let lctx ← getLCtx
  -- Collect fvar IDs that we need (iteratively, until fixpoint)
  let mut needed : Std.HashSet FVarId := {}
  -- Seed: fvars directly appearing in the expression
  for decl in lctx do
    if !decl.isImplementationDetail && e.containsFVar decl.fvarId then
      needed := needed.insert decl.fvarId
  -- Closure: also include fvars appearing in the types of needed fvars
  let mut changed := true
  while changed do
    changed := false
    for decl in lctx do
      if !decl.isImplementationDetail && !needed.contains decl.fvarId then
        -- Check if any already-needed fvar has a type referencing this one
        let isDepOf := needed.any fun neededId =>
          match lctx.find? neededId with
          | some neededDecl => neededDecl.type.containsFVar decl.fvarId
          | none => false
        if isDepOf then
          needed := needed.insert decl.fvarId
          changed := true
  -- Return in context order
  let mut result : Array Expr := #[]
  for decl in lctx do
    if needed.contains decl.fvarId then
      result := result.push (mkFVar decl.fvarId)
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

/-- Add a definition, or reuse an existing one if the name already exists.

    Behavior depends on options:
    - `Aeneas.Decompose.useExisting` (default: true): when the name already exists
      in the environment, check definitional equality and reuse if equal.
      When false, only definitions introduced by the current `#decompose` call
      can be reused via name matching.
    - `Aeneas.Decompose.checkDuplicate` (default: true): after adding a new definition,
      warn if a previously introduced definition (in the same call) has the same body.

    Uses `addAndCompile` + realizations when possible (for simp unfolding).
    Falls back to `addDecl` + noncomputable tag when the value depends on
    noncomputable or opaque constants (which cause deferred IR errors).
    `clauseDesc` is used in error messages to identify which decomposition clause
    triggered the conflict. -/
private def addDefinition (name : Name) (levelParams : List Name)
    (type value : Expr) (srcIsNoncomputable : Bool)
    (clauseDesc : MessageData := "decomposition clause") : DecomposeM Unit := do
  let env ← getEnv
  let useExisting := Aeneas.Decompose.useExisting.get (← getOptions)
  let checkDuplicate := Aeneas.Decompose.checkDuplicate.get (← getOptions)
  -- Check if a definition with this name was already introduced in this sequence
  let introduced := (← get).introduced
  for (prevName, prevValue) in introduced do
    if prevName == name then
      let isEq ← withReducible do isDefEq value prevValue
      if isEq then
        return  -- Reuse definition from this sequence
      else
        throwError "#decompose: cannot apply {clauseDesc}: definition '{name}' already \
          exists with body{indentExpr prevValue}\nbut the new extraction \
          produced{indentExpr value}\nwhich is not definitionally equal (at reducible transparency)"
  -- Check if the name already exists in the environment
  if let some existingInfo := env.find? name then
    if useExisting then
      match existingInfo with
      | .defnInfo existingVal =>
        let isEq ← withReducible do isDefEq value existingVal.value
        if isEq then
          -- Track it so we can detect duplicates against it too
          modify fun s => { s with introduced := s.introduced.push (name, value) }
          return  -- Reuse existing definition
        else
          throwError "#decompose: cannot apply {clauseDesc}: definition '{name}' already \
            exists with body{indentExpr existingVal.value}\nbut the new extraction \
            produced{indentExpr value}\nwhich is not definitionally equal (at reducible transparency)"
      | _ =>
        throwError "#decompose: cannot apply {clauseDesc}: '{name}' already exists \
          but is not a definition"
    else
      throwError "#decompose: cannot apply {clauseDesc}: '{name}' already exists in the \
        environment (set `Aeneas.Decompose.useExisting` to true to allow reuse)"
  -- Add new definition
  let decl : DefinitionVal := {
    name, levelParams, type, value,
    hints := .abbrev, safety := .safe, all := [name]
  }
  let isNC := srcIsNoncomputable || hasNoncomputableDep env value
  if isNC then
    addDecl (.defnDecl decl)
    Lean.enableRealizationsForConst name
    modifyEnv fun env' => noncomputableExt.tag env' name
  else
    addAndCompile (.defnDecl decl)
    Lean.enableRealizationsForConst name
  -- Check for duplicate values among previously introduced definitions
  if checkDuplicate then
    for (prevName, prevValue) in introduced do
      let isDup ← withReducible do isDefEq value prevValue
      if isDup then
        logWarning m!"#decompose: '{name}' has the same definition as '{prevName}' \
          (consider reusing the same name)"
        break
  modify fun s => { s with introduced := s.introduced.push (name, value) }

-- ============================================================================
-- Core extraction: `full`
-- ============================================================================

/-- Extract the whole expression as a new definition.
    Returns the call expression that replaces it. -/
def extractFull (body : Expr) (newName : Name)
    (levelParams : List Name) (srcIsNoncomputable : Bool)
    (clauseDesc : MessageData) : DecomposeM Expr := do
  let relevantFVars ← collectFreeLocalFVars body
  let fnValue ← mkLamAbstract relevantFVars body
  let fnType  ← mkForallAbstract relevantFVars (← inferType body)
  addDefinition newName levelParams fnType fnValue srcIsNoncomputable clauseDesc
  return mkAppN (mkConst newName (levelParams.map Level.param)) relevantFVars

-- ============================================================================
-- Core extraction: `letRange`
-- ============================================================================

/-- Extract `count` consecutive bindings starting at `start`.
    Returns the **full** modified body (wrapping bindings before the range too). -/
def extractLetRange (bindings : Array BindingEntry) (terminal : Expr)
    (start count : Nat) (newName : Name)
    (levelParams : List Name) (srcIsNoncomputable : Bool)
    (clauseDesc : MessageData) : DecomposeM Expr := do
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
  let addDef (fnValue : Expr) : DecomposeM Expr := do
    let relevantFVars ← collectFreeLocalFVars fnValue
    let fnValueClosed ← mkLamAbstract relevantFVars fnValue
    let fnTypeClosed  ← mkForallAbstract relevantFVars (← inferType fnValue)
    addDefinition newName levelParams fnTypeClosed fnValueClosed srcIsNoncomputable clauseDesc
    return mkAppN (mkConst newName (levelParams.map Level.param)) relevantFVars

  if includesTerminal then
    -- ── Case A: range goes to the end ──────────────────────────────────
    let extractedBody ← rebuildBindings bindings terminal start n
    let callExpr ← addDef extractedBody
    rebuildBindings bindings callExpr 0 start

  else
    -- ── Case B: range does NOT include terminal ────────────────────────
    let contExpr ← rebuildBindings bindings terminal endPos n
    let extractedFVars := rangeBindings.foldl (fun acc e => acc ++ e.fvars) #[]
    let neededFVars ← filterRelevantFVars contExpr extractedFVars
    let lastEntry := bindings[start + count - 1]!

    if neededFVars.size == 1 && neededFVars[0]!.fvarId! == lastEntry.fvars[0]!.fvarId! then
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
        -- Use mkLamAbstract to create a proper lambda even if the fvar
        -- is a let-decl (from a pure binding in a mixed-mode range)
        let cont ← mkLamAbstract #[lastEntry.fvars[0]!] contExpr
        let replacement ← mkAppM ``Bind.bind #[callExpr, cont]
        rebuildBindings bindings replacement 0 start
      else
        -- Pure: use a let-binding for the replacement
        withLetDecl lastEntry.name (← inferType lastEntry.fvars[0]!) callExpr fun newFvar => do
          let contExprSubst := contExpr.replaceFVar lastEntry.fvars[0]! newFvar
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
        -- fvar for the continuation (not lastEntry's fvar which has the wrong type).
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
      let tupleVal ← Utils.mkProdsVal neededFVars.toList
      let returnExpr ← if hasMonadic then do
        -- Build: pure (v1, v2, ..., vk) using the monad from bindings
        let some monadExpr ← getMonadExpr | throwError "letRange: no monad found for pure"
        mkAppOptM ``Pure.pure #[some monadExpr, none, none, some tupleVal]
      else
        pure tupleVal
      let extractedBody ← rebuildBindings bindings returnExpr start endPos
      let callExpr ← addDef extractedBody

      -- Build the destructuring continuation using Function.uncurry
      if hasMonadic then do
        -- Build: callExpr >>= Function.uncurry (fun v1 => Function.uncurry (fun v2 v3 => contExpr))
        -- Start from the innermost lambda (last fvar), then wrap with uncurry from inside out
        let mut cont ← mkLamAbstract #[neededFVars.back!] contExpr
        for j in (List.range (neededFVars.size - 1)).reverse do
          cont ← mkUncurry neededFVars[j]! cont
        let replacement ← mkAppM ``Bind.bind #[callExpr, cont]
        rebuildBindings bindings replacement 0 start
      else do
        -- Pure tuple destructuring: use let-bindings with projections
        let tupleType ← Utils.mkProdsType neededFVars.toList
        let mkTupleDestructBindings (tupFVar : Expr) (body : Expr) : MetaM Expr := do
          let mut result := body
          for i in (List.range neededFVars.size).reverse do
            let fv := neededFVars[i]!
            let proj ← mkProjection tupFVar neededFVars.size i
            let fvType ← inferType fv
            let fvName ← fv.fvarId!.getUserName
            result := .letE fvName fvType proj (result.abstract #[fv]) false
          return result
        withLocalDeclD `_tup tupleType fun tupFVar => do
          let innerBody ← mkTupleDestructBindings tupFVar contExpr
          let contBody ← mkLambdaFVars #[tupFVar] innerBody
          let replacement := (Expr.app contBody callExpr).headBeta
          rebuildBindings bindings replacement 0 start

-- ============================================================================
-- Navigation helpers (for composite patterns)
-- ============================================================================

/-- Open `n` nested lambda binders, apply `action` to the innermost body, close them back.
    If `strict`, throws an error when fewer than `n` lambdas are found.
    If not strict, applies `action` to whatever expression remains. -/
private def modifyUnderLambdasCore (strict : Bool) (e : Expr) (n : Nat)
    (action : Expr → DecomposeM Expr) : DecomposeM Expr := do
  match n with
  | 0 => action e
  | n + 1 =>
    match e with
    | .lam name type body binfo =>
      withLocalDecl name binfo type fun fvar => do
        let body' := body.instantiate1 fvar
        let modifiedBody ← modifyUnderLambdasCore strict body' n action
        mkLambdaFVars #[fvar] modifiedBody
    | _ =>
      if strict then
        throwError "lam: expected {n + 1} more lambda binder(s), got {← ppExpr e}"
      else
        action e

/-- Open up to `n` lambda binders (permissive: applies action even if fewer lambdas exist).
    Used for match/dite branches where Lean may compile away some binders. -/
private def modifyUnderLambdasPermissive (e : Expr) (n : Nat)
    (action : Expr → DecomposeM Expr) : DecomposeM Expr :=
  modifyUnderLambdasCore (strict := false) e n action

/-- Open exactly `n` lambda binders (strict: throws if fewer exist).
    Used for the `lam` navigation pattern. -/
def modifyUnderLambdas (e : Expr) (n : Nat)
    (action : Expr → DecomposeM Expr) : DecomposeM Expr :=
  modifyUnderLambdasCore (strict := true) e n action

/-- Modify branch `idx` of an ite/dite/match expression.
    Calls `action` on the branch body (under all pattern-variable lambdas);
    returns the reconstructed expression. -/
def modifyBranch (e : Expr) (idx : Nat) (action : Expr → DecomposeM Expr) : DecomposeM Expr := do
  -- Try ite
  if let some (α, cond, inst, thenB, elseB) := matchIte? e then
    if idx == 0 then
      let thenB' ← action thenB
      return mkApp5 (mkConst ``ite e.getAppFn.constLevels!) α cond inst thenB' elseB
    else if idx == 1 then
      let elseB' ← action elseB
      return mkApp5 (mkConst ``ite e.getAppFn.constLevels!) α cond inst thenB elseB'
    else throwError "branch {idx}: ite has only branches 0 (then) and 1 (else)"
  -- Try dite
  if let some (α, cond, inst, thenB, elseB) := matchDite? e then
    if idx == 0 then
      let thenB' ← modifyUnderLambdasPermissive thenB 1 action
      return mkApp5 (mkConst ``dite e.getAppFn.constLevels!) α cond inst thenB' elseB
    else if idx == 1 then
      let elseB' ← modifyUnderLambdasPermissive elseB 1 action
      return mkApp5 (mkConst ``dite e.getAppFn.constLevels!) α cond inst thenB elseB'
    else throwError "branch {idx}: dite has only branches 0 (then) and 1 (else)"
  -- Try match (detected via matchMatcherApp?)
  if let some mApp ← matchMatcherApp? e then
    if h : idx < mApp.alts.size then
      let some info ← getMatcherInfo? mApp.matcherName
        | throwError "branch {idx}: could not get matcher info for '{mApp.matcherName}'"
      let numLambdas := info.altNumParams[idx]?.getD 0
      let alt := mApp.alts[idx]
      let alt' ← modifyUnderLambdasPermissive alt numLambdas action
      let mApp' := { mApp with alts := mApp.alts.set idx alt' }
      return mApp'.toExpr
    else
      throwError "branch {idx}: match has only {mApp.alts.size} alternative(s) (0-indexed)"
  throwError "branch {idx}: expression is not an ite, dite, or match"

/-- Modify the function part of an application. -/
def modifyAppFun (e : Expr) (action : Expr → DecomposeM Expr) : DecomposeM Expr := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  if args.size == 0 then throwError "appFun: expression is not an application"
  let fn' ← action fn
  return mkAppN fn' args

/-- Modify argument `idx` of an application (0-indexed, explicit args). -/
def modifyAppArg (e : Expr) (idx : Nat) (action : Expr → DecomposeM Expr) : DecomposeM Expr := do
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
    (action : Expr → DecomposeM Expr) : DecomposeM Expr := do
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

/-- Format a decompose clause for error messages. -/
private def formatClause (pat : DecomposePattern) (name : Name) : MessageData :=
  let rec go : DecomposePattern → String
    | .letRange s c => s!"letRange {s} {c}"
    | .letAt i inner => s!"letAt {i} ({go inner})"
    | .full => "full"
    | .branch i inner => s!"branch {i} ({go inner})"
    | .lam n inner => s!"lam {n} ({go inner})"
    | .appFun inner => s!"appFun ({go inner})"
    | .argArg i inner => s!"argArg {i} ({go inner})"
  m!"{go pat} => {name}"

/-- Apply one decompose clause: navigate with the pattern, extract, replace.
    Returns the modified function body. -/
partial def applyClause (body : Expr) (pat : DecomposePattern) (newName : Name)
    (levelParams : List Name)
    (srcIsNoncomputable : Bool) : DecomposeM Expr := do
  let clauseDesc := formatClause pat newName
  match pat with
  | .full =>
    extractFull body newName levelParams srcIsNoncomputable clauseDesc

  | .letRange start count =>
    withParsedBindings body #[] fun bindings terminal => do
      extractLetRange bindings terminal start count newName levelParams srcIsNoncomputable clauseDesc

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

/-- Run `simp only` with the given theorems on the goal's target. Returns `none`
    if the goal was closed, `some mvarId` otherwise. -/
private def simpOnlyTarget (mvarId : MVarId) (declsToUnfold : Array Name)
    (addSimpThms : Array Name) : MetaM (Option MVarId) := do
  let args : SimpArgs := { declsToUnfold, addSimpThms }
  let (ctx, simprocs) ← mkSimpCtx (simpOnly := true) { singlePass := true, maxSteps := 100000 } .simp args
  -- Increase maxRecDepth for large decompositions
  withTheReader Core.Context (fun ctx => { ctx with maxRecDepth := 2048 }) do
    let (result?, _) ← Meta.simpGoal mvarId ctx (simprocs := simprocs)
    match result? with
    | none => return none
    | some (_, mvarId') => return some mvarId'

/-- Prove the decomposition equality: `∀ params, body_original = body_decomposed`.
    `defNames` are the names of all auxiliary definitions introduced.
    Strategy 1: `rfl`.
    Strategy 2: `simp only [defNames..., bind_assoc_eq, pure_bind]`.
    Strategy 3: `unfold defNames; simp only [bind_assoc_eq, pure_bind]`
                (for noncomputable defs where simp can't unfold directly).
    Raises an error if all strategies fail. -/
def proveStep (goalType : Expr) (defNames : Array Name) : TermElabM Expr := do
  let simpThms := #[``Aeneas.Std.bind_assoc_eq, ``LawfulMonad.pure_bind]
  -- Strategy 1: rfl
  if let some proof ← observing? do
    let mvar ← mkFreshExprMVar goalType
    let (_, mvarId) ← mvar.mvarId!.intros
    mvarId.refl
    instantiateMVars mvar
  then return proof
  -- Strategy 2: simp only [defNames..., bind_assoc_eq, pure_bind]
  if let some proof ← observing? do
    let mvar ← mkFreshExprMVar goalType
    let (_, mvarId) ← mvar.mvarId!.intros
    if (← simpOnlyTarget mvarId defNames simpThms).isNone then
      return ← instantiateMVars mvar
    throwError "simp did not close the goal"
  then return proof
  -- Strategy 3: unfold defNames, then simp only [bind_assoc_eq, pure_bind]
  if let some proof ← observing? do
    let mvar ← mkFreshExprMVar goalType
    let (_, mvarId) ← mvar.mvarId!.intros
    let mvarId' ← mvarId.deltaTarget (defNames.contains ·)
    match ← simpOnlyTarget mvarId' #[] simpThms with
    | none => return ← instantiateMVars mvar
    | some mvarId'' =>
      mvarId''.refl
      return ← instantiateMVars mvar
  then return proof
  throwError "#decompose: could not prove decomposition equality"

-- ============================================================================
-- Main command elaboration
-- ============================================================================

@[command_elab decomposeCmd]
def elabDecompose : CommandElab := fun stx => do
  match stx with
  | `(command| #decompose $fnId $eqId $[$clauses]*) => do
    liftTermElabM do
      -- Resolve the function name
      let fnName ← match ← Term.resolveId? fnId with
        | some (.const name _) => pure name
        | some e => throwError "{fnId} resolved to non-constant expression: {e}"
        | none => throwError "Unknown: {fnId}"
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
        -- Apply each clause sequentially (in DecomposeM to track introduced defs)
        -- Collect the names of all definitions introduced
        let ((currentBody, introNames), _) ←
          (do
            let mut currentBody := body
            let mut introNames : Array Name := #[]
            for (pat, newName) in parsedClauses do
              currentBody ← applyClause currentBody pat newName levelParams srcIsNoncomputable
              if !introNames.contains newName then
                introNames := introNames.push newName
            return (currentBody, introNames) : DecomposeM _).run {}

        -- Prove the single equality: ∀ params, body = currentBody
        -- using simp with all introduced definition names + bind_assoc_eq
        let eqType ← mkForallFVars params (← mkEq body currentBody)
        let proof ← proveStep eqType introNames

        -- Build the theorem type: ∀ params, f params = currentBody
        let lhs := mkAppN (mkConst fnName (levelParams.map Level.param)) params
        let thmTypeForall ← mkForallFVars params (← mkEq lhs currentBody)

        let eqName ← do
          let ns ← getCurrNamespace
          let rawName := eqId.getId
          pure (if ns.isAnonymous then rawName else ns ++ rawName)

        -- Add the theorem
        addDecl (.thmDecl {
          name        := eqName
          levelParams := levelParams
          type        := thmTypeForall
          value       := proof
        })

        trace[Decompose] "#decompose: created {parsedClauses.size} definition(s) and theorem '{eqName}'"
  | _ => throwError "Invalid #decompose syntax"

end Aeneas.Command.Decompose
