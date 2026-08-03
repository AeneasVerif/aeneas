import Lean
import Aeneas.Tactic.Elab.TraitInst.ParserSetup

/-!
# `@[trait_inst]` — Pretty-Printed Trait Instance Names

## Motivation

Aeneas generates extremely precise (long) names for Lean models of Rust trait
implementations to avoid collisions. For example:
`alloc.vec.Vec.Insts.CoreCloneClone`. These are hard to read and write.

This module provides a bidirectional pretty-printing system that allows users to
write `{core.clone.Clone for alloc.vec.Vec<T>}` instead.

## Usage

```lean
-- Register a trait instance with a pretty name. Identifiers which match a
-- ∀-binder of the definition (like `T` below) are *pattern variables*; the
-- other names are resolved in the current scope.
@[trait_inst {core.clone.Clone for alloc.vec.Vec<T>}]
def alloc.vec.Vec.Insts.CoreCloneClone (T : Type) (cloneInst : core.clone.Clone T) :
  core.clone.Clone (alloc.vec.Vec T) := ...

-- Use the pretty name to refer to it
#check {core.clone.Clone for alloc.vec.Vec<_>}
-- ^ elaborates to `alloc.vec.Vec.Insts.CoreCloneClone`
```

Definitions carrying the `@[rust_trait_impl]` attribute are registered
automatically (see `Aeneas.Extract`), by reflection on their type.
-/

namespace Aeneas.TraitInst

open Lean Elab Meta Command

/-! ## Core Types -/

/-- Simplified type identifier for trait instance matching.

- `name n args`: a named type (e.g., `alloc.vec.Vec` with args `[U8]`)
- `pvar n`: a named pattern variable, bound to a ∀-binder of the registered
  definition (only appears in *registered* patterns, never in usage queries)
- `hole`: a wildcard type `_`
- `tuple tys`: a tuple type `(A, B, C)`
- `slice elem`: `Slice<T>`
- `array elem size`: `Array<T, N>` (the size is a `lit`, `hole`, `pvar` or `name`)
- `lit n`: a const-generic literal argument (e.g. the `32` in `Trait<32>`) -/
inductive TypeId where
  | name (n : Name) (args : List TypeId)
  | pvar (n : Name)
  | hole
  | tuple (tys : List TypeId)
  | slice (elem : TypeId)
  | array (elem : TypeId) (size : TypeId)
  | lit (n : Int)
  deriving BEq, Hashable, Repr, Inhabited

/-- A trait instance identifier: trait name + self type + optional trait type arguments.

For registered patterns, the trait arguments mirror the parameters of the Lean
structure modeling the trait, minus the leading `Self` (so they include lifted
associated types and const generics, in order). In usage queries the argument
list may be omitted, which is equivalent to filling it with holes. -/
structure TraitInstanceId where
  traitId : Name
  selfType : TypeId
  traitArgs : List TypeId := []
  deriving BEq, Hashable, Repr, Inhabited

/-! ## Pretty-printing helpers -/

partial def TypeId.toString : TypeId → String
  | .name n [] => n.toString
  | .name n args =>
    let argsStr := ", ".intercalate (args.map TypeId.toString)
    s!"{n}<{argsStr}>"
  | .pvar n => n.toString
  | .hole => "_"
  | .tuple tys =>
    let tysStr := ", ".intercalate (tys.map TypeId.toString)
    s!"({tysStr})"
  | .slice elem => s!"Slice<{TypeId.toString elem}>"
  | .array elem size => s!"Array<{TypeId.toString elem}, {TypeId.toString size}>"
  | .lit n => s!"{n}"

instance : ToString TypeId := ⟨TypeId.toString⟩

def TraitInstanceId.toString : TraitInstanceId → String
  | { traitId, selfType, traitArgs := [] } =>
    s!"\{{traitId} for {selfType}}"
  | { traitId, selfType, traitArgs } =>
    let argsStr := ", ".intercalate (traitArgs.map TypeId.toString)
    s!"\{{traitId}<{argsStr}> for {selfType}}"

instance : ToString TraitInstanceId := ⟨TraitInstanceId.toString⟩

instance : ToMessageData TypeId := ⟨fun t => .ofFormat (format t.toString)⟩
instance : ToMessageData TraitInstanceId := ⟨fun t => .ofFormat (format t.toString)⟩

/-! ## Head keys — the registry index -/

/-- The head constructor of a self type, used to index the registry. -/
inductive HeadKey where
  | const (n : Name)
  | tuple
  | slice
  | array
  | lit
  /-- The self type is a pattern variable or a hole (e.g. a blanket impl) -/
  | wildcard
  deriving BEq, Hashable, Repr, Inhabited

def TypeId.headKey : TypeId → HeadKey
  | .name n _ => .const n
  | .pvar _ | .hole => .wildcard
  | .tuple _ => .tuple
  | .slice _ => .slice
  | .array _ _ => .array
  | .lit _ => .lit

/-- Registry index key: trait + head of the self type. -/
structure TraitInstKey where
  traitId : Name
  selfHead : HeadKey
  deriving BEq, Hashable, Repr, Inhabited

/-! ## Pattern matching -/

/-- Bindings accumulated while matching a pattern: pattern variable → sub-query. -/
abbrev PatBindings := List (Name × TypeId)

mutual

/-- Match a query `TypeId` against a pattern `TypeId`.

- `hole` in the pattern matches anything (no binding).
- `hole` in the *query* also matches anything (underspecified query).
- `pvar` in the pattern binds the query sub-term; repeated occurrences must
  agree (a binding to `hole` can be refined by a later concrete binding). -/
partial def TypeId.matchPat (pat query : TypeId) (bound : PatBindings) :
    Option PatBindings :=
  match pat, query with
  | .hole, _ => some bound
  | _, .hole => some bound
  | .pvar n, q =>
    match bound.find? (·.1 == n) with
    | some (_, q') =>
      if q' == q then some bound
      else if q' == .hole then some ((n, q) :: bound.filter (·.1 != n))
      else none
    | none => some ((n, q) :: bound)
  | .name n1 args1, .name n2 args2 =>
    if n1 == n2 then TypeId.matchPatList args1 args2 bound else none
  | .tuple t1, .tuple t2 => TypeId.matchPatList t1 t2 bound
  | .slice e1, .slice e2 => TypeId.matchPat e1 e2 bound
  | .array e1 s1, .array e2 s2 => do
    TypeId.matchPat s1 s2 (← TypeId.matchPat e1 e2 bound)
  | .lit n1, .lit n2 => if n1 == n2 then some bound else none
  | _, _ => none

partial def TypeId.matchPatList (pats queries : List TypeId) (bound : PatBindings) :
    Option PatBindings :=
  match pats, queries with
  | [], [] => some bound
  | p :: ps, q :: qs => do TypeId.matchPatList ps qs (← TypeId.matchPat p q bound)
  | _, _ => none

end

/-- Match a query against a registered pattern. An empty query argument list is
    treated as "all holes" when the pattern has arguments. -/
def TraitInstanceId.matchPat (pat query : TraitInstanceId) : Option PatBindings := do
  guard (pat.traitId == query.traitId)
  let bound ← TypeId.matchPat pat.selfType query.selfType []
  let qArgs :=
    if query.traitArgs.isEmpty && !pat.traitArgs.isEmpty then
      pat.traitArgs.map (fun _ => TypeId.hole)
    else query.traitArgs
  TypeId.matchPatList pat.traitArgs qArgs bound

/-- Lenient structural compatibility: `hole` is compatible with anything.
    Used for consistency checks between a user-provided pattern and the pattern
    derived from a definition's type (mismatches only produce warnings). -/
partial def TypeId.compatible : TypeId → TypeId → Bool
  | .hole, _ | _, .hole => true
  | .pvar a, .pvar b => a == b
  | .pvar _, _ | _, .pvar _ => true
  | .name n1 args1, .name n2 args2 =>
    n1 == n2 && args1.length == args2.length
      && (List.zip args1 args2).all (fun (a, b) => TypeId.compatible a b)
  | .tuple t1, .tuple t2 =>
    t1.length == t2.length && (List.zip t1 t2).all (fun (a, b) => TypeId.compatible a b)
  | .slice e1, .slice e2 => TypeId.compatible e1 e2
  | .array e1 s1, .array e2 s2 => TypeId.compatible e1 e2 && TypeId.compatible s1 s2
  | .lit n1, .lit n2 => n1 == n2
  | _, _ => false

def TraitInstanceId.compatible (a b : TraitInstanceId) : Bool :=
  a.traitId == b.traitId && TypeId.compatible a.selfType b.selfType
    && a.traitArgs.length == b.traitArgs.length
    && (List.zip a.traitArgs b.traitArgs).all (fun (x, y) => TypeId.compatible x y)

/-- Rename the pattern variables to positional names (`«%0»`, `«%1»`, ...), so
    that patterns which only differ in the names of their pattern variables
    compare equal. Used to detect duplicate registrations. -/
partial def TypeId.alphaNormalize (tid : TypeId) (subst : PatBindings) :
    TypeId × PatBindings :=
  match tid with
  | .pvar n =>
    match subst.find? (·.1 == n) with
    | some (_, t) => (t, subst)
    | none =>
      let fresh := TypeId.pvar (Name.mkSimple s!"%{subst.length}")
      (fresh, (n, fresh) :: subst)
  | .name n args =>
    let (args, subst) := goList args subst
    (.name n args, subst)
  | .tuple tys =>
    let (tys, subst) := goList tys subst
    (.tuple tys, subst)
  | .slice elem =>
    let (elem, subst) := TypeId.alphaNormalize elem subst
    (.slice elem, subst)
  | .array elem size =>
    let (elem, subst) := TypeId.alphaNormalize elem subst
    let (size, subst) := TypeId.alphaNormalize size subst
    (.array elem size, subst)
  | .hole | .lit _ => (tid, subst)
where
  goList (tys : List TypeId) (subst : PatBindings) : List TypeId × PatBindings :=
    match tys with
    | [] => ([], subst)
    | t :: ts =>
      let (t, subst) := TypeId.alphaNormalize t subst
      let (ts, subst) := goList ts subst
      (t :: ts, subst)

def TraitInstanceId.alphaNormalize (tid : TraitInstanceId) : TraitInstanceId :=
  let (selfType, subst) := TypeId.alphaNormalize tid.selfType []
  let (traitArgs, _) := TypeId.alphaNormalize.goList tid.traitArgs subst
  { tid with selfType, traitArgs }

/-! ## Persistent State -/

/-- An entry in the trait instance registry. -/
structure TraitInstEntry where
  declName : Name
  instId : TraitInstanceId
  deriving Inhabited

/-- State of the trait instance registry.

- `byHead`: registered patterns, indexed by trait name + head of the self type.
  Blanket impls (self type is a pattern variable) live in the `wildcard` bucket
  of their trait.
- `rev`: definition name → registered pattern (used by the delaborator). -/
structure TraitInstState where
  byHead : Std.HashMap TraitInstKey (Array TraitInstEntry) := {}
  rev : Std.HashMap Name TraitInstanceId := {}
  deriving Inhabited

def TraitInstEntry.key (e : TraitInstEntry) : TraitInstKey :=
  ⟨e.instId.traitId, e.instId.selfType.headKey⟩

/-- Add an entry. If the definition was already registered (e.g. an explicit
    `@[trait_inst]` overriding an automatic registration), the old entry is
    replaced. -/
def TraitInstState.addEntry (s : TraitInstState) (e : TraitInstEntry) : TraitInstState :=
  let s :=
    match s.rev[e.declName]? with
    | some oldId =>
      let oldKey : TraitInstKey := ⟨oldId.traitId, oldId.selfType.headKey⟩
      let oldBucket :=
        (s.byHead.getD oldKey #[]).filter (fun (e' : TraitInstEntry) => e'.declName != e.declName)
      { s with byHead := s.byHead.insert oldKey oldBucket }
    | none => s
  { byHead := s.byHead.insert e.key ((s.byHead.getD e.key #[]).push e)
    rev := s.rev.insert e.declName e.instId }

/-- Persistent environment extension storing the trait instance registry. -/
initialize traitInstExt : SimplePersistentEnvExtension TraitInstEntry TraitInstState ←
  registerSimplePersistentEnvExtension {
    addEntryFn := TraitInstState.addEntry
    addImportedFn := fun arrs =>
      arrs.flatten.foldl TraitInstState.addEntry {}
  }

/-- Find the registered entries whose pattern matches the given query, together
    with the pattern-variable bindings of the match. -/
def findEntriesMatching (env : Environment) (query : TraitInstanceId) :
    Array (TraitInstEntry × PatBindings) :=
  let s := traitInstExt.getState env
  let buckets :=
    let key : TraitInstKey := ⟨query.traitId, query.selfType.headKey⟩
    let base := s.byHead.getD key #[]
    if query.selfType.headKey == .wildcard then base
    else base ++ s.byHead.getD ⟨query.traitId, .wildcard⟩ #[]
  let found := buckets.filterMap fun e =>
    (e.instId.matchPat query).map fun bound => (e, bound)
  -- Specific instances shadow blanket instances: if some candidates have a
  -- concrete self-type head, drop the ones whose self type is a pattern
  -- variable (e.g. the `Clone` instance of `Box<T>`, which is the identity
  -- after `Box` gets erased by the extraction)
  let specific := found.filter fun (e, _) =>
    e.instId.selfType.headKey != .wildcard
  if specific.isEmpty then found else specific

/-- Find a registration structurally equal (up to pattern-variable renaming) to
    the given pattern. -/
def findDeclByInstId (env : Environment) (instId : TraitInstanceId) : Option Name :=
  let s := traitInstExt.getState env
  let norm := instId.alphaNormalize
  let key : TraitInstKey := ⟨instId.traitId, instId.selfType.headKey⟩
  ((s.byHead.getD key #[]).find? fun e => e.instId.alphaNormalize == norm).map (·.declName)

def findInstIdByDecl (env : Environment) (declName : Name) : Option TraitInstanceId :=
  (traitInstExt.getState env).rev[declName]?

def registerTraitInstEntry (env : Environment) (declName : Name)
    (instId : TraitInstanceId) : Environment :=
  traitInstExt.addEntry env { declName, instId }

/-! ## Trace class -/

initialize registerTraceClass `Aeneas.traitInst

/-! ## Syntax -/

/-- Syntax category for dotted names like `core.clone.Clone`. -/
declare_syntax_cat traitInstName
syntax (name := tinIdent) ident : traitInstName
syntax (name := tinDotted) ident "." traitInstName : traitInstName

/-- Syntax category for types within trait instance notation. -/
declare_syntax_cat traitInstType
syntax (name := tiName) traitInstName : traitInstType
syntax (name := tiNameArgs) traitInstName "<" traitInstType,* Aeneas.TraitInst.closingAngle : traitInstType
syntax (name := tiHole) "_" : traitInstType
syntax (name := tiNum) num : traitInstType
syntax (name := tiNegNum) "-" num : traitInstType
syntax (name := tiTuple) "(" traitInstType "," ppSpace traitInstType,* ")" : traitInstType

/-- Syntax category for a trait instance identifier `{Trait for Type}`. -/
declare_syntax_cat traitInstId
syntax (name := tidBasic) "{" traitInstName ppSpace "for" ppSpace traitInstType "}" : traitInstId
syntax (name := tidArgs) "{" traitInstName "<" traitInstType,* Aeneas.TraitInst.closingAngle ppSpace "for" ppSpace traitInstType "}" : traitInstId

/-! ## Syntax → Core Type Conversion -/

/-- Prepend a string at the root of a hierarchical `Name`. -/
private def prependStr (s : String) (n : Name) : Name :=
  match n with
  | .anonymous => .str .anonymous s
  | .str parent s' => .str (prependStr s parent) s'
  | .num parent n' => .num (prependStr s parent) n'

/-- Convert a `traitInstName` syntax to a `Name`. -/
partial def elabTraitInstName (stx : Syntax) : Name :=
  if stx.isOfKind ``tinDotted then
    let s := stx[0].getId.eraseMacroScopes.getString!
    let rest := elabTraitInstName stx[2]
    prependStr s rest
  else if stx.isOfKind ``tinIdent then
    stx[0].getId.eraseMacroScopes
  else
    .anonymous

/-- Convert a `traitInstType` syntax to a `TypeId`. -/
partial def elabTraitInstType (stx : Syntax) : Except String TypeId := do
  if stx.isOfKind ``tiName then
    let name := elabTraitInstName stx[0]
    return .name name []
  else if stx.isOfKind ``tiNameArgs then
    let name := elabTraitInstName stx[0]
    let argStxs := stx[2].getSepArgs
    -- Special-case Slice<T>
    if name == `Slice then
      if argStxs.size != 1 then
        .error "Slice expects exactly 1 type argument"
      else
        let elem ← elabTraitInstType argStxs[0]!
        return .slice elem
    -- Special-case Array<T, N>
    else if name == `Array then
      if argStxs.size != 2 then
        .error "Array expects exactly 2 arguments (element type and size)"
      else
        let elem ← elabTraitInstType argStxs[0]!
        let size ← elabTraitInstType argStxs[1]!
        checkSizeArg size
        return .array elem size
    else
      let args ← argStxs.toList.mapM elabTraitInstType
      return .name name args
  else if stx.isOfKind ``tiHole then
    return .hole
  else if stx.isOfKind ``tiNum then
    return .lit stx[0].toNat
  else if stx.isOfKind ``tiNegNum then
    return .lit (- (stx[1].toNat : Int))
  else if stx.isOfKind ``tiTuple then
    -- "(" traitInstType "," traitInstType,* ")"
    let first ← elabTraitInstType stx[1]
    let restStxs := stx[3].getSepArgs
    let rest ← restStxs.toList.mapM elabTraitInstType
    return .tuple (first :: rest)
  else
    .error s!"Unknown traitInstType syntax: {stx}"
where
  /-- An Array size argument must be a literal, a hole, or a variable. -/
  checkSizeArg (size : TypeId) : Except String Unit :=
    match size with
    | .lit _ | .hole | .name _ [] => .ok ()
    | _ => .error s!"Array size must be a number literal, _, or a variable, got: {size}"

/-- Convert a `traitInstId` syntax to a `TraitInstanceId`. -/
def elabTraitInstId (stx : Syntax) : Except String TraitInstanceId := do
  if stx.isOfKind ``tidBasic then
    -- "{" traitInstName "for" traitInstType "}"
    let traitName := elabTraitInstName stx[1]
    let selfType ← elabTraitInstType stx[3]
    return { traitId := traitName, selfType := selfType }
  else if stx.isOfKind ``tidArgs then
    -- "{" traitInstName "<" traitInstType,* ">" "for" traitInstType "}"
    let traitName := elabTraitInstName stx[1]
    let argStxs := stx[3].getSepArgs
    let args ← argStxs.toList.mapM elabTraitInstType
    let selfType ← elabTraitInstType stx[6]
    return { traitId := traitName, selfType := selfType, traitArgs := args }
  else
    .error s!"Unknown traitInstId syntax: {stx}"

/-! ## Name resolution and canonicalization -/

/-- The canonical names of the special type constructors. We use raw literals
    (not checked names) so that this file does not depend on `Aeneas.Std`. -/
private def stdSliceName : Name := `Aeneas.Std.Slice
private def stdArrayName : Name := `Aeneas.Std.Array

/-- After name resolution, fold `Aeneas.Std.Slice`/`Aeneas.Std.Array`
    applications into the dedicated `TypeId` constructors, so that all the ways
    of writing them (`Slice<T>`, `Std.Slice<T>`, reflection on `Expr`s) produce
    the same canonical form. -/
private def canonicalizeName (n : Name) (args : List TypeId) : TypeId :=
  if n == stdSliceName && args.length == 1 then .slice args[0]!
  else if n == stdArrayName && args.length == 2 then .array args[0]! args[1]!
  else .name n args

/-- Try to resolve a raw name against the environment (respecting open namespaces).
    Only full matches count: matches with leftover field projections are discarded. -/
private def tryResolveName {m : Type → Type} [Monad m] [MonadResolveName m]
    [MonadEnv m] [MonadOptions m] (rawName : Name) : m Name := do
  let res := ResolveName.resolveGlobalName (← getEnv) (← getOptions)
    (← getCurrNamespace) (← getOpenDecls) rawName
  match res.filter (·.2.isEmpty) with
  | (resolved, _) :: _ => return resolved
  | [] => return rawName

/-- Resolve the names in a `TypeId` against the current environment, and
    canonicalize the special type constructors. -/
partial def resolveTypeId {m : Type → Type} [Monad m] [MonadResolveName m]
    [MonadEnv m] [MonadOptions m] (tid : TypeId) : m TypeId := do
  match tid with
  | .name n args =>
    let n' ← tryResolveName n
    let args' ← args.mapM resolveTypeId
    return canonicalizeName n' args'
  | .pvar _ | .hole | .lit _ => return tid
  | .tuple tys => return .tuple (← tys.mapM resolveTypeId)
  | .slice elem => return .slice (← resolveTypeId elem)
  | .array elem size => return .array (← resolveTypeId elem) (← resolveTypeId size)

/-- Resolve the names in a `TraitInstanceId` against the current environment. -/
def resolveTraitInstId {m : Type → Type} [Monad m] [MonadResolveName m]
    [MonadEnv m] [MonadOptions m] (tid : TraitInstanceId) : m TraitInstanceId := do
  return {
    traitId := ← tryResolveName tid.traitId
    selfType := ← resolveTypeId tid.selfType
    traitArgs := ← tid.traitArgs.mapM resolveTypeId
  }

/-! ## Pattern variables -/

/-- The names of the ∀-binders of a declaration's type. -/
def getBinderNames (declName : Name) : MetaM (Array Name) := do
  let some ci := (← getEnv).find? declName | return #[]
  forallTelescope ci.type fun xs _ =>
    xs.mapM fun x => do
      return (← x.fvarId!.getUserName).eraseMacroScopes

/-- Replace the atomic names which match a ∀-binder of the registered
    definition with pattern variables. This must run *before* name
    resolution. -/
partial def TypeId.toPatternVars (binders : Array Name) : TypeId → TypeId
  | .name n [] => if n.isAtomic && binders.contains n then .pvar n else .name n []
  | .name n args => .name n (args.map (TypeId.toPatternVars binders))
  | .pvar n => .pvar n
  | .hole => .hole
  | .lit n => .lit n
  | .tuple tys => .tuple (tys.map (TypeId.toPatternVars binders))
  | .slice elem => .slice (TypeId.toPatternVars binders elem)
  | .array elem size =>
    .array (TypeId.toPatternVars binders elem) (TypeId.toPatternVars binders size)

def TraitInstanceId.toPatternVars (binders : Array Name) (tid : TraitInstanceId) :
    TraitInstanceId :=
  { tid with
    selfType := tid.selfType.toPatternVars binders
    traitArgs := tid.traitArgs.map (TypeId.toPatternVars binders) }

/-! ## Reflection: `Expr` → `TypeId` -/

/-- Try to interpret an expression as a const-generic literal (e.g. `32#usize`,
    which is `Usize.ofNat 32 (by ...)`, or a raw `Nat`/`Int` literal). -/
private def litOfExpr (e : Expr) : Option Int :=
  match e.int? with
  | some n => some n
  | none =>
    -- Scalar literals: an application of an `ofNat`/`ofInt`-like function with
    -- a literal argument (e.g. `Usize.ofNat 32 h`, `UScalar.ofNat 32 h`, ...)
    let fn := e.getAppFn
    match fn with
    | .const declName _ =>
      let last := declName.componentsRev.head?
      let isOfLit :=
        match last with
        | some (.str _ s) => s == "ofNat" || s == "ofNatCore" || s == "ofInt" || s == "ofIntCore"
        | _ => false
      if isOfLit then e.getAppArgs.findSome? (·.int?)
      else none
    | _ => none

/-- Reflect an expression into a `TypeId`. `pvars` maps the free variables which
    should become pattern variables (the ∀-binders of a definition) to their
    user names. If `fvarsByName` is true, the other free variables are
    represented by their (unresolved) user name - this is used when reflecting
    the types appearing in a local context. Returns `none` if the expression is
    not representable (arrow types, raw pointers, unnamed types, ...). -/
partial def typeIdOfExpr (pvars : Std.HashMap FVarId Name) (e : Expr)
    (fvarsByName : Bool := false) : MetaM (Option TypeId) := do
  let e := e.consumeMData
  match e with
  | .fvar id =>
    match pvars[id]? with
    | some n => return some (.pvar n)
    | none =>
      if fvarsByName then
        let n := (← id.getUserName).eraseMacroScopes
        if n.isAnonymous then return none else return some (.name n [])
      else return none
  | _ =>
    if let some n := litOfExpr e then
      return some (.lit n)
    else
    match e.getAppFn with
    | .const declName _ =>
      let args := e.getAppArgs
      -- Tuples: flatten right-nested products
      if declName == ``Prod && args.size == 2 then
        let some fst ← typeIdOfExpr pvars args[0]! fvarsByName | return none
        let some rest ← typeIdOfExpr pvars args[1]! fvarsByName | return none
        match rest with
        | .tuple tys => return some (.tuple (fst :: tys))
        | t => return some (.tuple [fst, t])
      else if declName == stdSliceName && args.size == 1 then
        let some elem ← typeIdOfExpr pvars args[0]! fvarsByName | return none
        return some (.slice elem)
      else if declName == stdArrayName && args.size == 2 then
        let some elem ← typeIdOfExpr pvars args[0]! fvarsByName | return none
        let size ← do
          match litOfExpr args[1]! with
          | some n => pure (TypeId.lit n)
          | none =>
            match args[1]!.consumeMData with
            | .fvar id =>
              match pvars[id]? with
              | some n => pure (TypeId.pvar n)
              | none =>
                if fvarsByName then
                  let n := (← id.getUserName).eraseMacroScopes
                  if n.isAnonymous then return none
                  else pure (TypeId.name n [])
                else return none
            | _ => return none
        return some (.array elem size)
      else
        let mut targs := #[]
        for a in args do
          let some t ← typeIdOfExpr pvars a fvarsByName | return none
          targs := targs.push t
        return some (.name declName targs.toList)
    | _ => return none

/-- Derive the trait instance pattern of a definition by reflection on its type:
    the ∀-binders become pattern variables, and the conclusion must be an
    application of a structure (the trait) to a self type and trait arguments.
    Returns `none` if the definition does not have the right shape or mentions
    unrepresentable types. -/
def deriveTraitInstId (declName : Name) : MetaM (Option TraitInstanceId) := do
  let env ← getEnv
  let some ci := env.find? declName | return none
  try
    forallTelescope ci.type fun xs resTy => do
      let resTy ← whnfR resTy
      let .const traitName _ := resTy.getAppFn | return none
      unless isStructure env traitName do return none
      let args := resTy.getAppArgs
      unless args.size ≥ 1 do return none
      let mut pvars : Std.HashMap FVarId Name := {}
      for x in xs do
        pvars := pvars.insert x.fvarId! ((← x.fvarId!.getUserName).eraseMacroScopes)
      let some self ← typeIdOfExpr pvars args[0]! | return none
      let mut targs := []
      for a in args[1:] do
        let some t ← typeIdOfExpr pvars a | return none
        targs := targs ++ [t]
      return some { traitId := traitName, selfType := self, traitArgs := targs }
  catch _ => return none

/-- Register a definition in the trait instance registry, unless an equivalent
    pattern is already registered to a *different* definition (first wins, with
    a warning: this can legitimately happen when a crate and one of its
    dependencies are extracted separately). -/
def registerChecked (declName : Name) (instId : TraitInstanceId)
    (warnOnDup : Bool := true) : MetaM Unit := do
  match findDeclByInstId (← getEnv) instId with
  | some existingName =>
    if existingName != declName then
      let msg := m!"trait_inst: {instId} is already registered to `{existingName}`; keeping the existing registration"
      if warnOnDup then logWarning msg
      else trace[Aeneas.traitInst] msg
    else
      modifyEnv fun env => registerTraitInstEntry env declName instId
  | none =>
    trace[Aeneas.traitInst] "Registering {declName} as {instId}"
    modifyEnv fun env => registerTraitInstEntry env declName instId

/-- Automatic registration by reflection on the type of `declName` (used for
    the definitions carrying the `@[rust_trait_impl]` attribute). Does nothing
    if the definition is already registered (an explicit `@[trait_inst]` wins),
    or if its type cannot be reflected. -/
def autoRegister (declName : Name) : MetaM Unit := do
  if (findInstIdByDecl (← getEnv) declName).isSome then return
  match ← deriveTraitInstId declName with
  | some instId =>
    -- Do not auto-register patterns whose self type is a bare pattern
    -- variable: they are usually artifacts of type erasure (e.g. the `Clone`
    -- instance of `Box<T>` has type `Clone T → Clone T` after `Box` gets
    -- erased) and would match *any* self type. Genuine blanket impls can
    -- still be registered with an explicit `@[trait_inst]` attribute.
    unless instId.selfType.headKey == .wildcard do
      registerChecked declName instId (warnOnDup := false)
  | none => pure ()

/-! ## Trait declaration marker: `@[trait_decl]`

The local-context instance search below needs to know which structures model
Rust *traits* (as opposed to data structures): the search treats hypotheses of
a trait type as instances, and walks their parent-clause fields (which are
precisely their fields of trait type). We cannot recognize trait structures
purely structurally — a data structure may well have a field of trait type —
so we mark them:
- the extraction generates `@[trait_decl]` on the structures it emits for
  Rust traits;
- the structures of the hand-written Std modeling Rust traits are marked
  automatically via their `@[rust_trait]` attribute (see `Aeneas.Extract`). -/

initialize traitDeclExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s n => s.insert n
    addImportedFn := fun arrs =>
      arrs.flatten.foldl (fun s n => s.insert n) {}
  }

def registerTraitDecl (env : Environment) (declName : Name) : Environment :=
  traitDeclExt.addEntry env declName

def isTraitDecl (env : Environment) (declName : Name) : Bool :=
  (traitDeclExt.getState env).contains declName

syntax (name := traitDeclAttr) "trait_decl" : attr

initialize registerBuiltinAttribute {
  name := `traitDeclAttr
  descr := "Mark a structure as modeling a Rust trait declaration"
  applicationTime := .afterTypeChecking
  add := fun declName _stx _attrKind => do
    unless isStructure (← getEnv) declName do
      throwError "trait_decl: `{declName}` is not a structure"
    modifyEnv fun env => registerTraitDecl env declName
}

/-! ## Attribute: `@[trait_inst {Trait for Type}]` -/

syntax (name := traitInstAttr) "trait_inst " traitInstId : attr

initialize registerBuiltinAttribute {
  name := `traitInstAttr
  descr := "Register a definition as a trait instance with a pretty-printed identifier"
  applicationTime := .afterTypeChecking
  add := fun declName stx _attrKind => do
    -- stx = `(attr| trait_inst $tid:traitInstId)
    let tidStx := stx[1]
    match elabTraitInstId tidStx with
    | .ok rawInstId => MetaM.run' do
      -- Convert the binder names to pattern variables, then resolve the
      -- remaining names against the current environment
      let binders ← getBinderNames declName
      let instId := rawInstId.toPatternVars binders
      let instId ← resolveTraitInstId instId
      -- Check the pattern against the shape derived from the definition's type
      (do
        match ← deriveTraitInstId declName with
        | some derived =>
          unless instId.compatible derived do
            logWarning m!"trait_inst: the pattern {instId} does not match the shape derived from the type of `{declName}`: {derived}"
        | none => pure ())
      registerChecked declName instId
    | .error msg =>
      throwError "trait_inst: {msg}"
}

/-! ## Building expressions from `TypeId`s -/

/-- Resolve a `TypeId` for *usage* (as opposed to registration): atomic names
    which match a variable of the local context are kept as is (they later get
    elaborated to the corresponding free variable), the other names are
    resolved against the environment. -/
partial def resolveTypeIdUsage (tid : TypeId) : MetaM TypeId := do
  match tid with
  | .name n args =>
    if args.isEmpty && n.isAtomic && ((← getLCtx).findFromUserName? n).isSome then
      return .name n []
    else
      let n' ← tryResolveName n
      let args' ← args.mapM resolveTypeIdUsage
      return canonicalizeName n' args'
  | .pvar _ | .hole | .lit _ => return tid
  | .tuple tys => return .tuple (← tys.mapM resolveTypeIdUsage)
  | .slice elem => return .slice (← resolveTypeIdUsage elem)
  | .array elem size =>
    return .array (← resolveTypeIdUsage elem) (← resolveTypeIdUsage size)

def resolveTraitInstIdUsage (tid : TraitInstanceId) : MetaM TraitInstanceId := do
  return {
    traitId := ← tryResolveName tid.traitId
    selfType := ← resolveTypeIdUsage tid.selfType
    traitArgs := ← tid.traitArgs.mapM resolveTypeIdUsage
  }

/-- Does this identifier contain holes? -/
partial def TypeId.hasHole : TypeId → Bool
  | .hole => true
  | .pvar _ | .lit _ => false
  | .name _ args => args.any TypeId.hasHole
  | .tuple tys => tys.any TypeId.hasHole
  | .slice elem => elem.hasHole
  | .array elem size => elem.hasHole || size.hasHole

def TraitInstanceId.hasHole (tid : TraitInstanceId) : Bool :=
  tid.selfType.hasHole || tid.traitArgs.any TypeId.hasHole

/-- Does this identifier determine the instance completely (no pattern
    variables and no holes)? -/
partial def TypeId.isConcrete : TypeId → Bool
  | .name _ args => args.all TypeId.isConcrete
  | .pvar _ | .hole => false
  | .tuple tys => tys.all TypeId.isConcrete
  | .slice elem => elem.isConcrete
  | .array elem size => elem.isConcrete && size.isConcrete
  | .lit _ => true

def TraitInstanceId.isConcrete (tid : TraitInstanceId) : Bool :=
  tid.selfType.isConcrete && tid.traitArgs.all TypeId.isConcrete

/-- Build the expression of a const-generic literal against an expected type
    (`Nat`, `Int`, or an Aeneas scalar type like `Std.Usize`). -/
def literalForType (expectedTy : Expr) (n : Int) : MetaM Expr := do
  let ty ← whnfD expectedTy
  let throwUnsupported {α} : MetaM α :=
    throwError "trait_inst: cannot elaborate the literal {n} against the expected type {expectedTy}"
  let .const c _ := ty.getAppFn | throwUnsupported
  if c == ``Nat then
    if n < 0 then throwUnsupported
    else return mkNatLit n.toNat
  else if c == ``Int then
    return toExpr n
  else if c == `Aeneas.Std.UScalar then
    if n < 0 then throwUnsupported
    let tyArg := ty.appArg!
    let x := mkNatLit n.toNat
    let cMax := mkApp (mkConst `Aeneas.Std.UScalar.cMax) tyArg
    let prop ← mkAppM ``LE.le #[x, cMax]
    let h ← mkDecideProof prop
    return mkAppN (mkConst `Aeneas.Std.UScalar.ofNat) #[tyArg, x, h]
  else if c == `Aeneas.Std.IScalar then
    let tyArg := ty.appArg!
    let x := toExpr n
    let cMin := mkApp (mkConst `Aeneas.Std.IScalar.cMin) tyArg
    let cMax := mkApp (mkConst `Aeneas.Std.IScalar.cMax) tyArg
    let prop ← mkAppM ``And
      #[← mkAppM ``LE.le #[cMin, x], ← mkAppM ``LE.le #[x, cMax]]
    let h ← mkDecideProof prop
    return mkAppN (mkConst `Aeneas.Std.IScalar.ofInt) #[tyArg, x, h]
  else throwUnsupported

/-- Resolve an atomic name to a local fvar, or a name to a global constant. -/
def resolveConstOrLocal (n : Name) : MetaM Expr := do
  if n.isAtomic then
    if let some decl := (← getLCtx).findFromUserName? n then
      return decl.toExpr
  if (← getEnv).contains n then
    mkConstWithFreshMVarLevels n
  else
    throwError "trait_inst: unknown type `{n}`"

/-- Resolve a Std type constructor, trying the fully qualified name first and
    the short name (which may refer to a local definition in tests) second. -/
def resolveStdConst (fullName shortName : Name) : MetaM Expr := do
  let env ← getEnv
  if env.contains fullName then mkConstWithFreshMVarLevels fullName
  else
    let resolved ← tryResolveName shortName
    if env.contains resolved then mkConstWithFreshMVarLevels resolved
    else throwError "trait_inst: unknown type `{fullName}`"

mutual

/-- Build the expression of a (usage) `TypeId`. -/
partial def typeIdToExpr (tid : TypeId) : MetaM Expr := do
  match tid with
  | .hole => mkFreshExprMVar none
  | .pvar n =>
    throwError "trait_inst: unexpected pattern variable `{n}` in a usage query"
  | .lit _ =>
    throwError "trait_inst: literal in a position where no expected type is known"
  | .name n args => typeIdApplyArgs (← resolveConstOrLocal n) args
  | .tuple tys =>
    match tys with
    | [] => throwError "trait_inst: empty tuple"
    | [t] => typeIdToExpr t
    | t :: ts => do
      let a ← typeIdToExpr t
      let b ← typeIdToExpr (.tuple ts)
      mkAppM ``Prod #[a, b]
  | .slice elem =>
    typeIdApplyArgs (← resolveStdConst `Aeneas.Std.Slice `Slice) [elem]
  | .array elem size =>
    typeIdApplyArgs (← resolveStdConst `Aeneas.Std.Array `Array) [elem, size]

/-- Apply a head (a type constructor) to `TypeId` arguments, using the
    constructor's signature to give expected types to literal arguments. -/
partial def typeIdApplyArgs (f : Expr) (args : List TypeId) : MetaM Expr := do
  if args.isEmpty then return f
  let fTy ← inferType f
  let (mvars, _, _) ← forallMetaTelescopeReducing fTy (some args.length)
  unless mvars.size == args.length do
    throwError "trait_inst: too many arguments applied to {f}"
  for m in mvars, a in args.toArray do
    match a with
    | .hole => pure ()
    | .lit n =>
      let e ← literalForType (← inferType m) n
      unless ← isDefEq m e do
        throwError "trait_inst: cannot use the literal {n} here"
    | _ =>
      let e ← typeIdToExpr a
      unless ← isDefEq m e do
        throwError "trait_inst: type mismatch when elaborating {a}"
  instantiateMVars (mkAppN f mvars)

end

/-! ## Local context search -/

/-- Reflect the type of a hypothesis as a trait instance identifier: the type
    must be an application of a structure marked with `@[trait_decl]`. -/
def reflectInstTypeId? (ty : Expr) : MetaM (Option TraitInstanceId) := do
  let ty ← instantiateMVars ty
  let ty ← whnfR ty
  let .const traitName _ := ty.getAppFn | return none
  unless isTraitDecl (← getEnv) traitName do return none
  let args := ty.getAppArgs
  unless args.size ≥ 1 do return none
  let some self ← typeIdOfExpr {} args[0]! (fvarsByName := true) | return none
  let mut targs := []
  for a in args[1:] do
    let some t ← typeIdOfExpr {} a (fvarsByName := true) | return none
    targs := targs ++ [t]
  return some { traitId := traitName, selfType := self, traitArgs := targs }

/-- Search the local context for an instance matching the query:
    - the hypotheses whose type is (an application of) a `@[trait_decl]`
      structure;
    - then, transitively, their parent-clause fields — i.e. their fields of
      trait type (breadth-first, so that an instance found at a shallower
      depth shadows the deeper ones).

    Returns all the (syntactically distinct) instances found at the shallowest
    depth at which there is a match. -/
def localSearch (query : TraitInstanceId) (maxDepth : Nat := 4) :
    MetaM (Array Expr) := do
  let env ← getEnv
  let mut current : Array (Expr × TraitInstanceId) := #[]
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    let some tid ← reflectInstTypeId? decl.type | continue
    current := current.push (decl.toExpr, tid)
  for _ in [0:maxDepth] do
    let hits := current.filterMap fun (e, tid) =>
      (tid.matchPat query).map fun _ => e
    unless hits.isEmpty do return hits
    let mut next : Array (Expr × TraitInstanceId) := #[]
    for (e, tid) in current do
      for f in getStructureFields env tid.traitId do
        let fe ← mkProjection e f
        if let some ftid ← reflectInstTypeId? (← inferType fe) then
          next := next.push (fe, ftid)
    current := next
  return #[]

/-! ## The resolver -/

/-- The result of resolving a trait-instance query. -/
inductive Resolution where
  | localInst (e : Expr)
  | registered (entry : TraitInstEntry) (implExpr : Expr)

mutual

/-- Resolve a trait-instance query: search the local context first (a clause
    which is in scope shadows the global instances), then the registry.

    For a registry match: if the query is fully concrete, the implementation
    is instantiated (the type arguments are elaborated and the clause
    parameters are recursively resolved); otherwise the resolution returns the
    bare constant, and the arguments are supplied by the surrounding
    application. -/
partial def resolveQuery (query : TraitInstanceId) (fuel : Nat := 8) :
    MetaM Resolution := do
  if fuel == 0 then
    throwError "trait_inst: maximum instance resolution depth exceeded"
  -- Local context first
  let hits ← localSearch query
  if !hits.isEmpty then
    let mut distinct : Array Expr := #[]
    for h in hits do
      let mut dup := false
      for d in distinct do
        if ← isDefEq h d then
          dup := true
          break
      unless dup do distinct := distinct.push h
    if distinct.size == 1 then
      return .localInst distinct[0]!
    else
      throwError "trait_inst: ambiguous: several instances of {query} are in scope: {distinct}"
  -- Then the registry
  let env ← getEnv
  match findEntriesMatching env query with
  | #[] => throwError "trait_inst: no instance found for {query}"
  | #[(entry, bindings)] =>
    trace[Aeneas.traitInst] "Resolved {query} to `{entry.declName}`"
    let implExpr ←
      if query.hasHole || !query.isConcrete then
        -- Underspecified query: return the bare constant (the arguments are
        -- supplied positionally by the surrounding application)
        mkConstWithFreshMVarLevels entry.declName
      else
        instantiateImpl entry bindings fuel
    return .registered entry implExpr
  | entries =>
    let names := entries.map fun (e, _) => e.declName
    throwError "trait_inst: ambiguous: {query} matches several registered instances: {names}"

/-- Instantiate a registered implementation with the bindings of a pattern
    match: create metavariables for its parameters, assign the bound pattern
    variables, and recursively resolve the remaining parameters of trait type
    (the clause parameters). -/
partial def instantiateImpl (entry : TraitInstEntry) (bindings : PatBindings)
    (fuel : Nat) : MetaM Expr := do
  let implC ← mkConstWithFreshMVarLevels entry.declName
  let implTy ← inferType implC
  let (mvars, _, _) ← forallMetaTelescopeReducing implTy
  let binderNames ← forallTelescopeReducing implTy fun xs _ =>
    xs.mapM fun x => do pure ((← x.fvarId!.getUserName).eraseMacroScopes)
  -- Assign the bound pattern variables
  for m in mvars, n in binderNames do
    match bindings.find? (·.1 == n) with
    | some (_, tid) =>
      match tid with
      | .hole => pure ()
      | .lit k =>
        let e ← literalForType (← inferType m) k
        unless ← isDefEq m e do
          throwError "trait_inst: cannot instantiate the parameter `{n}` of `{entry.declName}` with {tid}"
      | _ =>
        let e ← typeIdToExpr tid
        unless ← isDefEq m e do
          throwError "trait_inst: cannot instantiate the parameter `{n}` of `{entry.declName}` with {tid}"
    | none => pure ()
  -- Recursively resolve the unassigned parameters of trait type
  for m in mvars do
    let m' ← instantiateMVars m
    if m'.isMVar then
      let mTy ← instantiateMVars (← inferType m')
      if let some subQuery ← reflectInstTypeId? mTy then
        unless subQuery.hasHole do
          let r ← resolveQuery subQuery (fuel - 1)
          let e := match r with
            | .localInst e => e
            | .registered _ e => e
          unless ← isDefEq m' e do
            throwError "trait_inst: failed to instantiate a clause of `{entry.declName}` with {subQuery}"
  instantiateMVars (mkAppN implC mvars)

end

/-! ## Term Elaboration: `{Trait for Type}` and `{Trait for Type}.method` -/

/-- Walk the syntax tree of a `traitInstId` and register `TermInfo` for each
    `traitInstName` node, enabling hover and go-to-definition in the IDE.
    Only annotates the outermost name node (not inner suffixes of dotted names). -/
private partial def annotateTraitInstSyntax (stx : Syntax) : Term.TermElabM Unit := do
  if stx.isOfKind ``tinIdent || stx.isOfKind ``tinDotted then
    let name := elabTraitInstName stx
    let resolved ← tryResolveName name
    let env ← getEnv
    if env.contains resolved then
      let lctx ← getLCtx
      Elab.pushInfoLeaf (.ofTermInfo {
        elaborator := `Aeneas.TraitInst
        stx := stx
        lctx := lctx
        expectedType? := none
        expr := mkConst resolved
      })
    return
  for child in stx.getArgs do
    annotateTraitInstSyntax child

/-- The notation term: a trait instance identifier, possibly followed by a
    member access `.f`. The member access is handled by this elaborator (and
    not the generic field projection) so that, when the trait instance
    resolves to a top-level implementation `C` and a method definition `C.f`
    exists, we can elaborate directly to `C.f` applied to the implementation's
    arguments: this produces exactly the same term as the direct call the
    extraction generates today (which the `progress` spec theorems are
    registered against), instead of a record projection. -/
syntax:max (name := traitInstTerm) traitInstId ("." noWs ident)? : term

open Term in
@[term_elab traitInstTerm] def elabTraitInstTerm : TermElab := fun stx _expectedType? => do
  let tidStx := stx[0]
  -- The optional `.f`: a null node with children `[".", ident]`
  let projPart := stx[1]
  let fieldName? : Option Name :=
    match projPart.getArgs.find? (·.isIdent) with
    | some id => some id.getId.eraseMacroScopes
    | none => none
  match elabTraitInstId tidStx with
  | .error msg => throwError "trait_inst: {msg}"
  | .ok rawQuery =>
    let query ← resolveTraitInstIdUsage rawQuery
    let res ← resolveQuery query
    let result ← do
      match res with
      | .localInst e =>
        match fieldName? with
        | none => pure e
        | some f => mkProjection e f
      | .registered entry implExpr =>
        match fieldName? with
        | none => pure implExpr
        | some f =>
          let mName := entry.declName ++ f
          let joined? ← do
            if (← getEnv).contains mName then
              -- Name-join: rebuild the method definition application from the
              -- implementation's arguments (the method definition takes the
              -- implementation's parameters as its first parameters)
              let implArgs := implExpr.getAppArgs
              let mC ← mkConstWithFreshMVarLevels mName
              let (mMvars, _, _) ←
                forallMetaTelescopeReducing (← inferType mC) (some implArgs.size)
              if mMvars.size == implArgs.size then
                let mut ok := true
                for mm in mMvars, ia in implArgs do
                  unless ← isDefEq mm ia do
                    ok := false
                    break
                if ok then
                  pure (some (← instantiateMVars (mkAppN mC mMvars)))
                else pure none
              else pure none
            else pure none
          match joined? with
          | some e => pure e
          | none => mkProjection implExpr f
    -- Annotate the whole expression (parent TermInfo)
    discard <| Term.addTermInfo tidStx result
    -- Annotate inner names AFTER the outer info — as sibling leaves with
    -- smaller ranges, they win over the outer node in `smallestInfo?`
    annotateTraitInstSyntax tidStx
    return result

/-! ## TypeId → Syntax Conversion (for delaboration) -/

/-- Build a `TSepArray` by interleaving elements with a separator atom. -/
private def mkTSepArray (elems : Array (TSyntax k)) (sep : String := ",") :
    Syntax.TSepArray k sep :=
  if _h : elems.isEmpty then ⟨#[]⟩
  else
    let first : Array Syntax := #[elems[0]!.raw]
    let rest := elems.toList.drop 1
    let arr := rest.foldl (fun acc e => acc.push (mkAtom sep) |>.push e.raw) first
    ⟨arr⟩

/-- Strip a namespace prefix from a name. Returns the suffix if `n` starts with
    `prefix_`, otherwise returns `n` unchanged. -/
private def stripPrefix (prefix_ : Name) (n : Name) : Name :=
  if n == prefix_ then .anonymous
  else if prefix_ == .anonymous then n
  else
    match n with
    | .str parent s =>
      let parent' := stripPrefix prefix_ parent
      if parent' == parent then n  -- prefix not found
      else .str parent' s
    | .num parent k =>
      let parent' := stripPrefix prefix_ parent
      if parent' == parent then n
      else .num parent' k
    | .anonymous => n

/-- Make a `traitInstName` syntax from a `Name`, stripping the given namespace prefix.
    Uses a single `ident` token so Lean prints `Foo.Bar` without spaces. -/
private def mkTraitInstNameSyntaxShort (prefix_ : Name) (n : Name) :
    CoreM (TSyntax `traitInstName) := do
  let shortName := stripPrefix prefix_ n
  `(traitInstName| $(mkIdent shortName):ident)

partial def typeIdToSyntax (prefix_ : Name) (tid : TypeId) :
    CoreM (TSyntax `traitInstType) := do
  match tid with
  | .hole => `(traitInstType| _)
  | .pvar n => do
    let nameStx ← mkTraitInstNameSyntaxShort .anonymous n
    `(traitInstType| $nameStx:traitInstName)
  | .lit n =>
    if n < 0 then
      let nLit := Syntax.mkNumLit (ToString.toString (-n))
      `(traitInstType| -$nLit:num)
    else
      let nLit := Syntax.mkNumLit (ToString.toString n)
      `(traitInstType| $nLit:num)
  | .name n [] => do
    let nameStx ← mkTraitInstNameSyntaxShort prefix_ n
    `(traitInstType| $nameStx:traitInstName)
  | .name n args => do
    let nameStx ← mkTraitInstNameSyntaxShort prefix_ n
    let argStxs ← args.mapM (typeIdToSyntax prefix_)
    let argArr := mkTSepArray argStxs.toArray
    `(traitInstType| $nameStx:traitInstName < $argArr,* >)
  | .tuple tys => do
    match tys with
    | [] => `(traitInstType| _)
    | first :: rest => do
      let firstStx ← typeIdToSyntax prefix_ first
      let restStxs ← rest.mapM (typeIdToSyntax prefix_)
      let restArr := mkTSepArray restStxs.toArray
      `(traitInstType| ( $firstStx:traitInstType , $restArr,* ))
  | .slice elem => do
    let elemStx ← typeIdToSyntax prefix_ elem
    let nameStx ← mkTraitInstNameSyntaxShort prefix_ `Slice
    let argArr := mkTSepArray #[elemStx]
    `(traitInstType| $nameStx:traitInstName < $argArr,* >)
  | .array elem size => do
    let elemStx ← typeIdToSyntax prefix_ elem
    let sizeStx ← typeIdToSyntax prefix_ size
    let nameStx ← mkTraitInstNameSyntaxShort prefix_ `Array
    let argArr := mkTSepArray #[elemStx, sizeStx]
    `(traitInstType| $nameStx:traitInstName < $argArr,* >)

def traitInstIdToSyntax (prefix_ : Name) (tid : TraitInstanceId) :
    CoreM (TSyntax `traitInstId) := do
  let nameStx ← mkTraitInstNameSyntaxShort prefix_ tid.traitId
  let selfStx ← typeIdToSyntax prefix_ tid.selfType
  match tid.traitArgs with
  | [] =>
    `(traitInstId| { $nameStx:traitInstName for $selfStx:traitInstType })
  | args => do
    let argStxs ← args.mapM (typeIdToSyntax prefix_)
    let argArr := mkTSepArray argStxs.toArray
    `(traitInstId| { $nameStx:traitInstName < $argArr,* > for $selfStx:traitInstType })

/-! ## Delaboration -/

open PrettyPrinter.Delaborator in
/-- Make a `traitInstName` syntax from a `Name`. Global names are shortened to
    the shortest form which still resolves to them (respecting the open
    namespaces); the other names have the given namespace prefix stripped.
    The ident is annotated so the Infoview renders it as interactive
    (hover/go-to-def). -/
private def mkAnnotatedTraitInstNameSyntax (prefix_ : Name) (n : Name) :
    Delab := do
  let env ← getEnv
  let ident ← if env.contains n then
    mkAnnotatedIdent (← unresolveNameGlobal n) (mkConst n)
  else
    pure (mkIdent (stripPrefix prefix_ n))
  pure ⟨(← `(traitInstName| $ident:ident)).raw⟩

open PrettyPrinter.Delaborator in
partial def typeIdToDelabSyntax (prefix_ : Name) (tid : TypeId) :
    Delab := do
  let r ← go prefix_ tid
  -- Cast from TSyntax `traitInstType to TSyntax `term
  pure ⟨r.raw⟩
where
  castName (stx : TSyntax `term) : TSyntax `traitInstName := ⟨stx.raw⟩
  go (prefix_ : Name) (tid : TypeId) : DelabM (TSyntax `traitInstType) := do
    match tid with
    | .hole => `(traitInstType| _)
    | .pvar n => do
      let nameStx : TSyntax `traitInstName := ⟨(← `(traitInstName| $(mkIdent n):ident)).raw⟩
      `(traitInstType| $nameStx:traitInstName)
    | .lit n =>
      if n < 0 then
        let nLit := Syntax.mkNumLit (ToString.toString (-n))
        `(traitInstType| -$nLit:num)
      else
        let nLit := Syntax.mkNumLit (ToString.toString n)
        `(traitInstType| $nLit:num)
    | .name n [] => do
      let nameStx ← mkAnnotatedTraitInstNameSyntax prefix_ n
      `(traitInstType| $(castName nameStx):traitInstName)
    | .name n args => do
      let nameStx ← mkAnnotatedTraitInstNameSyntax prefix_ n
      let argStxs ← args.mapM (go prefix_)
      let argArr := mkTSepArray argStxs.toArray
      `(traitInstType| $(castName nameStx):traitInstName < $argArr,* >)
    | .tuple tys => do
      match tys with
      | [] => `(traitInstType| _)
      | first :: rest => do
        let firstStx ← go prefix_ first
        let restStxs ← rest.mapM (go prefix_)
        let restArr := mkTSepArray restStxs.toArray
        `(traitInstType| ( $firstStx:traitInstType , $restArr,* ))
    | .slice elem => do
      let elemStx ← go prefix_ elem
      let nameStx ← mkAnnotatedTraitInstNameSyntax prefix_ `Slice
      let argArr := mkTSepArray #[elemStx]
      `(traitInstType| $(castName nameStx):traitInstName < $argArr,* >)
    | .array elem size => do
      let elemStx ← go prefix_ elem
      let sizeStx ← go prefix_ size
      let nameStx ← mkAnnotatedTraitInstNameSyntax prefix_ `Array
      let argArr := mkTSepArray #[elemStx, sizeStx]
      `(traitInstType| $(castName nameStx):traitInstName < $argArr,* >)

open PrettyPrinter.Delaborator in
def traitInstIdToDelabSyntax (prefix_ : Name) (tid : TraitInstanceId) :
    Delab := do
  let nameStx : TSyntax `traitInstName ← do
    let r ← mkAnnotatedTraitInstNameSyntax prefix_ tid.traitId
    pure ⟨r.raw⟩
  let selfStx : TSyntax `traitInstType ← do
    let r ← typeIdToDelabSyntax prefix_ tid.selfType
    pure ⟨r.raw⟩
  let r ← match tid.traitArgs with
  | [] =>
    `(traitInstId| { $nameStx:traitInstName for $selfStx:traitInstType })
  | args => do
    let argStxs ← args.mapM (typeIdToDelabSyntax prefix_)
    let argArr : Syntax.TSepArray `traitInstType "," := mkTSepArray (argStxs.toArray.map (⟨·.raw⟩))
    `(traitInstId| { $nameStx:traitInstName < $argArr,* > for $selfStx:traitInstType })
  pure ⟨r.raw⟩

register_option pp.aeneas.traitInst : Bool := {
  defValue := true
  descr := "(pretty-printing) print registered trait instances with the `{Trait for Type}` notation"
}

register_option pp.aeneas.traitInstCheck : Bool := {
  defValue := true
  descr := "(pretty-printing) check that the `{Trait for Type}` notation would elaborate back to the printed term (disable only for performance)"
}

/-- Substitute the pattern variables of an identifier. -/
partial def TypeId.substPvars (bindings : PatBindings) : TypeId → TypeId
  | .pvar n =>
    match bindings.find? (·.1 == n) with
    | some (_, t) => t
    | none => .pvar n
  | .name n args => .name n (args.map (TypeId.substPvars bindings))
  | .hole => .hole
  | .lit n => .lit n
  | .tuple tys => .tuple (tys.map (TypeId.substPvars bindings))
  | .slice elem => .slice (elem.substPvars bindings)
  | .array elem size => .array (elem.substPvars bindings) (size.substPvars bindings)

def TraitInstanceId.substPvars (tid : TraitInstanceId) (bindings : PatBindings) :
    TraitInstanceId :=
  { tid with
    selfType := tid.selfType.substPvars bindings
    traitArgs := tid.traitArgs.map (TypeId.substPvars bindings) }

/-- The number of ∀-binders of a constant's type. -/
def constArity (declName : Name) : MetaM Nat := do
  let some ci := (← getEnv).find? declName | return 0
  forallTelescopeReducing ci.type fun xs _ => return xs.size

/-- The names of the first `k` ∀-binders of a constant's type. -/
def constBinderNames (declName : Name) : MetaM (Array Name) := do
  let some ci := (← getEnv).find? declName | return #[]
  forallTelescopeReducing ci.type fun xs _ =>
    xs.mapM fun x => do pure ((← x.fvarId!.getUserName).eraseMacroScopes)

/-- Would the query elaborate back to `e` in the current context? Used by the
    delaborator to guarantee that printing the notation does not change the
    meaning of the term (e.g. when a local clause would shadow the global
    instance we want to print). -/
def roundTrips (query : TraitInstanceId) (e : Expr) : MetaM Bool := do
  unless pp.aeneas.traitInstCheck.get (← getOptions) do return true
  try
    withNewMCtxDepth do
      let r ← resolveQuery query
      let e' := match r with
        | .localInst x => x
        | .registered _ x => x
      isDefEq e' e
  catch _ => return false

/-- Compute the instantiated identifier to print for an application of a
    registered implementation `c` to (at least) its `binderNames.size`
    arguments: reflect the arguments bound to pattern variables and substitute
    them in the registered pattern. -/
def instantiatedInstId? (instId : TraitInstanceId) (binderNames : Array Name)
    (args : Array Expr) : MetaM (Option TraitInstanceId) := do
  let mut bindings : PatBindings := []
  for n in binderNames, a in args do
    match ← typeIdOfExpr {} a (fvarsByName := true) with
    | some t => bindings := (n, t) :: bindings
    | none => pure ()
  let printed := instId.substPvars bindings
  if printed.isConcrete then return some printed else return none

open PrettyPrinter.Delaborator in
/-- Build the syntax of the notation term, with an optional `.f` member
    access. -/
def mkTraitInstTermSyntax (tid : Term) (field? : Option Name) :
    Term :=
  let proj := match field? with
    | some f => mkNullNode #[mkAtom ".", mkIdent f]
    | none => mkNullNode
  ⟨Syntax.node .none ``traitInstTerm #[tid.raw, proj]⟩

open PrettyPrinter.Delaborator in
/-- Delaborator that pretty-prints the applications of registered trait
    instance definitions (and of their method definitions) with the
    `{Trait for Type}` notation, instantiating the pattern variables with the
    arguments of the application. Identifiers inside the `{...}` are annotated
    for hover/go-to-def in the Infoview.

    A candidate is only printed when re-elaborating it in the current context
    would produce the same term (see `roundTrips`). -/
@[delab app]
def delabTraitInstApp : Delab := do
  guard (pp.aeneas.traitInst.get (← getOptions))
  let e ← SubExpr.getExpr
  let .const name _ := e.getAppFn | failure
  let env ← getEnv
  match findInstIdByDecl env name with
  | some instId =>
    if e.isConst then
      -- Bare constant: print the registered pattern if elaborating it back
      -- yields the same constant (e.g. `{Clone for Vec<_>}` resolves to the
      -- bare constant, but a pattern whose variables would capture something
      -- in the current context does not round-trip and is printed raw)
      guard (← roundTrips instId e)
      let currNs ← getCurrNamespace
      let tidStx ← traitInstIdToDelabSyntax currNs instId
      return mkTraitInstTermSyntax tidStx none
    else
      -- Fully applied implementation: print the instantiated pattern
      let k ← constArity name
      guard (k > 0 && e.getAppNumArgs ≥ k)
      withOverApp k do
        let e ← SubExpr.getExpr
        let some printed ←
          instantiatedInstId? instId (← constBinderNames name) e.getAppArgs
          | failure
        guard (← roundTrips printed e)
        let currNs ← getCurrNamespace
        let tidStx ← traitInstIdToDelabSyntax currNs printed
        return mkTraitInstTermSyntax tidStx none
  | none =>
    -- A method definition `C.f` of a registered implementation `C`
    let .str parent f := name | failure
    let some instId := findInstIdByDecl env parent | failure
    let k ← constArity parent
    guard (e.getAppNumArgs ≥ k)
    -- Delaborate the prefix `C.f impl-args…` as a unit (the method arguments
    -- are appended by `withOverApp`)
    withOverApp k do
      let e ← SubExpr.getExpr
      let args := e.getAppArgs
      let some printed ←
        instantiatedInstId? instId (← constBinderNames parent) args
        | failure
      -- Check that the notation would resolve back to this implementation
      -- (with these arguments) in the current context
      let implE ← mkAppOptM parent (args.map some)
      guard (← roundTrips printed implE)
      let currNs ← getCurrNamespace
      let tidStx ← traitInstIdToDelabSyntax currNs printed
      return mkTraitInstTermSyntax tidStx (some (Name.mkSimple f))

end Aeneas.TraitInst
