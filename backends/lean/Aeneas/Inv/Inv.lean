import Aeneas.Std.Primitives
import AeneasMeta.Extensions

namespace Aeneas.Inv

open Lean Elab Meta
open Extensions

/-!
# Extensions
-/

/-- Helper for the extensions. -/
structure ExtBase (α : Type) where
  rules : DiscrTree (Name × α)
  /- We can't remove keys from a discrimination tree, so to support
     local rules we keep a set of deactivated rules (rules which have
     come out of scope) on the side -/
  deactivated : Std.HashSet Name
deriving Inhabited

def ExtBase.empty {α} : ExtBase α := ⟨ DiscrTree.empty, Std.HashSet.emptyWithCapacity ⟩

def ExtBase.insert {α} [BEq α] (e : ExtBase α) (kv : Array DiscrTree.Key × Name × α) : ExtBase α :=
  { rules := e.rules.insertCore kv.fst kv.snd,
    deactivated := e.deactivated.erase kv.snd.fst }

def ExtBase.erase {α} (r : ExtBase α) (k : Name) : ExtBase α :=
  { r with deactivated := r.deactivated.insert k }

initialize arrayGetterExt : SimpExtension ←
  registerSimpAttr `inv_array_getter "\
    Registers an array get expression, so that the invariant inferencer is aware of it."

structure ArrayAttr (α : Type) where
  attr : AttributeImpl
  ext  : SimpleScopedEnvExtension (DiscrTreeKey × Name × α) (ExtBase α)
deriving Inhabited

def initializeArrayAttrExt {α : Type} [BEq α] (name : Name)
  (add : SimpleScopedEnvExtension (Array DiscrTree.Key × Name × α) (ExtBase α) →
         Name → Syntax → AttributeKind → AttrM Unit) : IO (ArrayAttr α) := do
  let ext ← registerSimpleScopedEnvExtension {
      name := name,
      initial := ExtBase.empty,
      addEntry := ExtBase.insert,
  }
  let attrImpl : AttributeImpl := {
    name := `progress
    descr := "Adds theorems to the `progress` database"
    add := add ext
    erase := fun thName => do
      let s := ext.getState (← getEnv)
      let s := s.erase thName
      modifyEnv fun env => ext.modifyState env fun _ => s
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl, ext := ext }

/-- Find at which positions the expressions in `toFind` appear in `args` -/
def findPositions (toFind : Array Expr) (args : Array Expr) : MetaM (Array Nat) := do
  let mut map : Std.HashMap Expr Nat := Std.HashMap.emptyWithCapacity
  let toFindSet := Std.HashSet.ofArray toFind
  for h: i in [0:args.size] do
    let arg := args[i]
    if toFindSet.contains arg then
      map := map.insert arg i
  -- Sanity check:
  for e in toFind do
    if ¬ map.contains e then
      throwError m!"Could not find argument: {e}"
  pure (toFind.map (Std.HashMap.get! map))

/-!
# Attribute: `inv_array_getter`
-/

structure Getter where
  -- The array/slice/etc.
  array : Nat
  /- The arguments which stand for the indices.

     We use an array of indices to support cases like multidimentional
     arrays and matrices.
   -/
  indices : Array Nat
deriving Inhabited, BEq

syntax (name := arrayGetter) "inv_array_getter" term "at" term,* : attr

def parseArrayGetterArgs
: Syntax -> MetaM (Expr × Array Expr)
| `(attr| inv_array_getter $array at $indices,* ) => do
  let elabExpr e := do instantiateMVars (← Elab.Term.elabTerm e none |>.run')
  let array ← elabExpr array
  let indices : Array (TSyntax `term):= indices.getElems
  let indices ← Array.mapM elabExpr indices
  return (array, indices)
| _ => throwUnsupportedSyntax

initialize arrayGetterAttr : ArrayAttr Getter ← do
  initializeArrayAttrExt `arrayGetterAttr
    fun ext defName stx attrKind => do
    -- Lookup the definition
    let env ← getEnv
    let some decl := env.findAsync? defName
      | throwError "Could not find definition {defName}"
    let sig := decl.sig.get
    let ty := sig.type
    -- Find where the position of the arguments
    let getter : Getter ← MetaM.run' do
      /- Strip the quantifiers.

          We do this before elaborating the pattern because we need the universally
          quantified variables to be in the context.
      -/
      forallTelescope ty.consumeMData fun fvars _ => do
      let (array, indices) ← parseArrayGetterArgs stx
      /- Find the position of every fvar id -/
      let positions ← findPositions (indices ++ #[array]) fvars
      pure { array := positions.back!, indices := positions.pop }
    -- Generate the key for the discrimination tree
    let key ← MetaM.run' do
      let (mvars, _) ← forallMetaTelescope ty.consumeMData
      DiscrTree.mkPath (← mkAppOptM defName (mvars.map Option.some))
    -- Store
    ScopedEnvExtension.add ext (key, defName, getter) attrKind

/-!
# Attribute: `inv_array_setter`
-/

structure Setter where
  -- The array/slice/etc.
  array : Nat
  /- The arguments which stand for the indices.

     We use an array of indices to support cases like multidimentional
     arrays and matrices. -/
  indices : Array Nat
  -- The new
  value : Nat
deriving Inhabited, BEq

syntax (name := arraySetter) "inv_array_setter" term "at" term,* "to" term : attr

def parseArraySetterArgs
: Syntax -> MetaM (Expr × Array Expr × Expr)
| `(attr| inv_array_setter $array at $indices,* to $value ) => do
  let elabExpr e := do instantiateMVars (← Elab.Term.elabTerm e none |>.run')
  let array ← elabExpr array
  let indices : Array (TSyntax `term):= indices.getElems
  let indices ← Array.mapM elabExpr indices
  let value ← elabExpr value
  return (array, indices, value)
| _ => throwUnsupportedSyntax

initialize arraySetterAttr : ArrayAttr Setter ← do
  initializeArrayAttrExt `arraySetterAttr
    fun ext defName stx attrKind => do
    -- Lookup the definition
    let env ← getEnv
    let some decl := env.findAsync? defName
      | throwError "Could not find definition {defName}"
    let sig := decl.sig.get
    let ty := sig.type
    -- Find where the position of the arguments
    let setter : Setter ← MetaM.run' do
      /- Strip the quantifiers.

          We do this before elaborating the pattern because we need the universally
          quantified variables to be in the context.
      -/
      forallTelescope ty.consumeMData fun fvars _ => do
      let (array, indices, value) ← parseArraySetterArgs stx
      /- Find the position of every fvar id -/
      let positions ← findPositions (indices ++ #[array, value]) fvars
      let value := positions.back!
      let positions := positions.pop
      let array := positions.back!
      let indices := positions.pop
      pure { array, indices, value }
    -- Generate the key for the discrimination tree
    let key ← MetaM.run' do
      let (mvars, _) ← forallMetaTelescope ty.consumeMData
      DiscrTree.mkPath (← mkAppOptM defName (mvars.map Option.some))
    -- Store
    ScopedEnvExtension.add ext (key, defName, setter) attrKind

/-!
# Attribute: `inv_array_val`
-/

/-- This is used to minimize array expressions.

    For instance, if `x : Array α`, then in the expression `x.toList`
    we consider that `x` is the minimal array expression.
 -/
structure ArrayVal where
  -- The array/slice/etc.
  array : Nat
deriving Inhabited, BEq

syntax (name := arrayVal) "inv_array_val" term : attr

def parseArrayValArgs
: Syntax -> MetaM Expr
| `(attr| inv_array_val $array ) => do
  let elabExpr e := do instantiateMVars (← Elab.Term.elabTerm e none |>.run')
  elabExpr array
| _ => throwUnsupportedSyntax

initialize arrayValAttr : ArrayAttr ArrayVal ← do
  initializeArrayAttrExt `arrayValAttr
    fun ext defName stx attrKind => do
    -- Lookup the definition
    let env ← getEnv
    let some decl := env.findAsync? defName
      | throwError "Could not find definition {defName}"
    let sig := decl.sig.get
    let ty := sig.type
    -- Find where the position of the arguments
    let array : ArrayVal ← MetaM.run' do
      /- Strip the quantifiers.

          We do this before elaborating the pattern because we need the universally
          quantified variables to be in the context.
      -/
      forallTelescope ty.consumeMData fun fvars _ => do
      let array ← parseArrayValArgs stx
      /- Find the position of every fvar id -/
      let positions ← findPositions (#[array]) fvars
      pure { array := positions[0]! }
    -- Generate the key for the discrimination tree
    let key ← MetaM.run' do
      let (mvars, _) ← forallMetaTelescope ty.consumeMData
      DiscrTree.mkPath (← mkAppOptM defName (mvars.map Option.some))
    -- Store
    ScopedEnvExtension.add ext (key, defName, array) attrKind

/-!
# Footprints
-/

inductive ArithBinop where
  | add
  | sub
  | mul
  | div
  | mod
  | pow
deriving Inhabited, BEq

inductive ArithExpr where
  | input (fvarId : FVarId) -- An input of the loop
  | lit (n : Nat)
  /- A constant natural number.

     We store a general expression rather than, e.g., a constant name, because
     it might be an expression of the shape: `n config`, where `config`
     remains constant inside the loop (and typically within the function).
  -/
  | const (e : Expr)
  | binop (op : ArithBinop) (a b : ArithExpr)
  | unknown
deriving BEq

instance : Inhabited ArithExpr := { default := .unknown }

/-- An expression which we register in the footprint.

    This is typically an expression which reads or writes to an array.
-/
inductive FootprintExpr where
  | input (v : FVarId) -- An input of the loop
  | get (array : FootprintExpr) (indices : Array ArithExpr)
  | set (array : FootprintExpr) (indices : Array ArithExpr)
  | arith (e : ArithExpr)
  | unknown
deriving BEq

instance : Inhabited FootprintExpr := { default := .unknown }

structure Footprint where
  /- Inputs of the loop.

     Ex.: when exploring `loop (fun (x, y) => ...)`, the inputs of the loop
     are `x` and `y`.
   -/
  inputs : Std.HashSet FVarId := {}
  /- The expressions a loop body evaluates to.

    Ex.: when exploring `foldl (fun x => if x % 2 = 0 then x + 1 else x + 2)`, `x` is a loop input,
    while `x + 1` and `x + 2` are loop outputs.
  -/
  outputs : Array FootprintExpr := #[]
  /- The provenance of a variable, if we could compute one.

     For now, we only track array like operations (get and set).
   -/
  provenance : Std.HashMap FVarId FootprintExpr := {}
  /- The footprint expressions we have encountered so far.

     When a variable goes out of scope, we remove it from `provenance`
     and insert its provenance here.
   -/
  footprint : Array FootprintExpr := #[]
deriving Inhabited

structure State extends Footprint where
  /- Destruct a monadic result (ex.: `pure x`) -/
  destResult : Expr → MetaM (Option Expr)
  /- Destruct a monadic bind into: the bound expression, the bound variable, the inner expression -/
  destBind : Expr → MetaM (Option (Expr × FVarId × Expr))
deriving Inhabited

abbrev FootprintM := ReaderT Context $ StateRefT State MetaM

-- Make the compiler generate specialized `pure`/`bind` so we do not have to optimize through the
-- whole monad stack at every use site. May eventually be covered by `deriving`.
@[always_inline]
instance : Monad FootprintM := let i := inferInstanceAs (Monad FootprintM); { pure := i.pure, bind := i.bind }

instance : Inhabited (FootprintM α) where
  default := fun _ _ => default

instance : MonadLCtx FootprintM where
  getLCtx := return (← read).lctx

/-instance : MonadEnv FootprintM where
  getEnv      := return (← getThe Core.State).env
  modifyEnv f := do modifyThe Core.State fun s => { s with env := f s.env, cache := {} }; modify fun s => { s with cache := {} }-/

instance : AddMessageContext FootprintM where
  addMessageContext := addMessageContextFull

@[inline] def FootprintM.run (x : FootprintM α) (ctx : Context := {}) (s : State) : MetaM (α × State) :=
  x ctx |>.run s

@[inline] def FootprintM.run' (x : FootprintM α) (ctx : Context := {}) (s : State) : MetaM α :=
  Prod.fst <$> x.run ctx s

@[inline] def FootprintM.toIO (x : FootprintM α) (ctxCore : Core.Context) (sCore : Core.State) (ctx : Context := {}) (s : State) :
  IO (α × Core.State × Meta.State × State) := do
  let ((a, s), (sCore, mState)) ← (x.run ctx s).toIO ctxCore sCore
  pure (a, sCore, mState, s)

@[inline] def liftMetaM [MonadLiftT FootprinM m] (x : FootprinM α) : m α :=
  liftM x

/-- To be used when a variable goes out of scope: remove it from `provenance` and adds it to `footprint` -/
def popFVar (fvar : FVarId) : FootprintM Unit := do
  let s ← get
  match s.provenance.get? fvar with
  | none => pure ()
  | some p =>
    set ({ s with provenance := s.provenance.erase fvar, footprint := s.footprint ++ #[p] })

def popFVars (fvars : Array FVarId) : FootprintM Unit := do
  for fvar in fvars do popFVar fvar

def withFVar (fvar : FVarId) (e : FootprintExpr) (k : FootprintM α) : FootprintM α := do
  -- TODO: this is probably not the proper way of scoping things
  let s ← get
  set ({s with provenance := s.provenance.insert fvar e})
  let x ← k
  popFVar fvar
  pure x

def withFVars (fvars : Array (FVarId × FootprintExpr)) (k : FootprintM α) : FootprintM α := do
  -- TODO: this is probably not the proper way of scoping things
  let s ← get
  set ({s with provenance := s.provenance.insertMany fvars})
  let x ← k
  popFVars (fvars.map Prod.fst)
  pure x

def pushOutput (p : FootprintExpr) : FootprintM Unit := do
  let s ← get
  set ({ s with outputs := s.outputs ++ #[p] })

def pushOptOutput (push : Bool) (p : FootprintExpr) : FootprintM Unit := do
  if push then pushOutput p

def lambdaTelescope (e : Expr) (k : Array Expr → Expr → FootprintM α) : FootprintM α :=
  Meta.lambdaTelescope e fun fvars e => do
    let x ← k fvars e
    -- Pop the variables from the provenance and insert them in the footprint
    popFVars (fvars.map Expr.fvarId!)
    -- Continue
    pure x

def lambdaLetTelescope (e : Expr) (k : Array Expr → Expr → FootprintM α) : FootprintM α :=
  Meta.lambdaLetTelescope e fun fvars e => do
    let x ← k fvars e
    -- Pop the variables from the provenance and insert them in the footprint
    popFVars (fvars.map Expr.fvarId!)
    -- Continue
    pure x

def FootprintExpr.toArithExpr (e : FootprintExpr) : ArithExpr :=
  match e with
  | .input v => .input v
  | .get _ _ | .set _ _ => .unknown
  | .arith e => e
  | .unknown => .unknown

def minimizeArrayVal (e : Expr) : FootprintM Expr := do
  let env ← getEnv
  let arrayValState := arrayValAttr.ext.getState env
  let rec minimize (e : Expr) : FootprintM Expr := do
    let rules ← arrayValState.rules.getMatch e
    -- Just try the first rule - there should be no more than one
    if rules.size > 0 then
      let (_, rule) := rules[0]!
      let args := e.getAppArgs
      pure args[rule.array]!
    else pure e
  minimize e

mutual

/-- Compute the footprint of an expression.

  `terminal` is true if we are exploring an expression which evaluates to
  the result of a loop. For instance, in `loop do let x ← e1; e2`, `e2` is terminal
  while `e1` is not.

  Remark: this function attempts to be robust, so we try not too fail as much as possible,
  even when encountering unexpected situations.
 -/
partial def footprint.expr (terminal : Bool) (e : Expr) : FootprintM FootprintExpr := do
  let p ← footprint.exprAux terminal e
  /- If this is terminal expression, we need to register this as an output -/
  pushOptOutput terminal p
  pure p

partial def footprint.exprAux (terminal : Bool) (e : Expr) : FootprintM FootprintExpr := do
  match e with
  | .bvar _ =>
    -- This is unexpected, but we can gracefully stop the exploration
    pure .unknown
  | .fvar fvarId =>
    match (← get).provenance.get? fvarId with
    | none => pure .unknown
    | some p => pure p
  | .mvar _ | .sort _ => pure .unknown
  | .const _ _ =>
    -- Check if this is a natural number
    let ty ← inferType e
    let p ←
      match ty with
      | .const ``Nat [] => pure (.arith (.const e))
      | _ => pure .unknown
    pushOptOutput terminal p
    pure p
  | .lit l =>
    match l with
    | .natVal n => pure (.arith (.lit n))
    | .strVal _ => pure .unknown
  | .app _ _ =>
    /- There are several cases:
       - it might be a monadic let, in which case we need to destruct it
       - it might be a get/set expression
    -/
    -- Check if this is a monadic let-binding
    if let some (bound, fvarId, inner) ← (← get).destBind e then
      -- Explore the bound expression
      let bound ← footprint.expr false bound
      return ← do
        withFVar fvarId bound do
        -- Continue exploring the inner expression
        footprint.expr false inner
    -- Check if this is a get/set expression
    if let some e ← footprint.arrayExpr terminal e then
      return e
    -- Don't know
    pure .unknown
  | .lam _ _ _ _ =>
    -- Typically happens when diving into a match or a let-binding
    lambdaTelescope e fun _ body => do
    footprint.expr terminal body
  | .letE _ _ _ _ _ =>
    -- How do we destruct exactly *one* let?
    lambdaLetTelescope e fun bound inner => do
    -- Explore the bound expressions
    for fvar in bound do
      -- Retrieve the declaration
      if let some decl := (← getLCtx).fvarIdToDecl.find? fvar.fvarId! then do
        if let some value := decl.value? then
          let _ ← footprint.expr false value
    -- Explore the inner body
    footprint.expr terminal inner
  | .mdata _ e => footprint.expr terminal e
  | .proj _ _ struct =>
    let _ ← footprint.expr false struct
    pure .unknown
  | .forallE _ _ _ _ =>
    /- If we find a forall it's probably because we're exploring a type:
       we can just stop -/
    pure .unknown

partial def footprint.arrayExpr (terminal : Bool) (e : Expr) : FootprintM (Option FootprintExpr) := do
  let env ← getEnv
  /- Attempt to deconstruct a getter -/
  let getterState := arrayGetterAttr.ext.getState env
  let rules ← getterState.rules.getMatch e
  -- Just try the first rule - there should be no more than one
  if rules.size > 0 then
    let (_, rule) := rules[0]!
    let args := e.getAppArgs
    let array := args[rule.array]!
    let array ← footprint.expr false array
    let indices := rule.indices.map fun id => args[id]!
    let indices ← indices.mapM (footprint.expr false)
    let indices := indices.map FootprintExpr.toArithExpr
    return (FootprintExpr.get array indices)

  /- Attempt to deconstruct a setter -/
  let setterState := arraySetterAttr.ext.getState env
  let rules ← setterState.rules.getMatch e
  -- Just try the first rule - there should be no more than one
  if rules.size > 0 then
    let (_, rule) := rules[0]!
    let args := e.getAppArgs
    let array := args[rule.array]!
    let array ← footprint.expr false array
    let indices := rule.indices.map fun id => args[id]!
    let indices ← indices.mapM (footprint.expr false)
    let indices := indices.map FootprintExpr.toArithExpr
    return (FootprintExpr.set array indices)

  /- Attempt to deconstruct an array value -/
  footprint.expr terminal (← minimizeArrayVal e)

end

end Aeneas.Inv
