import Aeneas.Std.Primitives
import AeneasMeta.Extensions

namespace Aeneas.Inv

open Lean Elab Meta
open Extensions

initialize registerTraceClass `Inv

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

def initializeArrayAttrExt {α : Type} [BEq α] (extName attrName : Name)
  (add : SimpleScopedEnvExtension (Array DiscrTree.Key × Name × α) (ExtBase α) →
         Name → Syntax → AttributeKind → AttrM Unit) : IO (ArrayAttr α) := do
  let ext ← registerSimpleScopedEnvExtension {
      name := extName,
      initial := ExtBase.empty,
      addEntry := ExtBase.insert,
  }
  let attrImpl : AttributeImpl := {
    name := attrName
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
  initializeArrayAttrExt `arrayGetterAttr `arrayGetter
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
  initializeArrayAttrExt `arraySetterAttr `arraySetter
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
  initializeArrayAttrExt `arrayValAttr `arrayVal
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

instance : ToString ArithBinop where
  toString x :=
    match x with
    | .add => "+"
    | .sub => "-"
    | .mul => "*"
    | .div => "/"
    | .mod => "%"
    | .pow => "^"

instance : ToFormat ArithBinop where
  format x := f!"{toString x}"

instance : ToMessageData ArithBinop where
  toMessageData x := m!"{toString x}"

inductive ArithExpr where
  | input (v : FVarId) -- An input of the loop
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

def ArithExpr.format (e : ArithExpr) : Format :=
  match e with
  | .input fv => f!"{Expr.fvar fv}"
  | .lit n => f!"{n}"
  | .const e => f!"const({e})"
  | .binop op a b => f!"{format a} {op} {format b}"
  | .unknown => f!"?"

instance : ToFormat ArithExpr where
  format := ArithExpr.format

def ArithExpr.toMessageData (e : ArithExpr) : MessageData :=
  match e with
  | .input fv => m!"{Expr.fvar fv}"
  | .lit n => m!"{n}"
  | .const e => m!"const({e})"
  | .binop op a b => m!"{a.toMessageData} {op} {b.toMessageData}"
  | .unknown => m!"?"

instance : ToMessageData ArithExpr where
  toMessageData := ArithExpr.toMessageData

/-- An expression which we register in the footprint.

    This is typically an expression which reads or writes to an array.
-/
inductive FootprintExpr where
  | input (v : FVarId) -- An input of the loop
  | get (array : FootprintExpr) (indices : Array ArithExpr)
  | set (array : FootprintExpr) (indices : Array ArithExpr) (value : FootprintExpr)
  | arith (e : ArithExpr)
  /- Handling projectors properly is particularly useful because we often need to
     decompose loop inputs (which are usually a tuple) -/
  | proj (typename : Name) (field : Nat) (e : FootprintExpr)
  /- Useful for the outputs -/
  | tuple (x y : FootprintExpr)
  | unknown
deriving BEq

instance : Inhabited FootprintExpr := { default := .unknown }

def FootprintExpr.format (e : FootprintExpr) : Format :=
  match e with
  | .input fv => f!"input({Expr.fvar fv})"
  | .get a ids => f!"{a.format}[{ids.map ArithExpr.format}]"
  | .set a ids v => f!"{a.format}[{ids.map ArithExpr.format}] := {v.format}"
  | .arith x => f!"{x.format}"
  | .proj _ f x => f!"{x.format}.{f}"
  | .tuple x y => f!"({x.format}, {y.format})"
  | .unknown => f!"?"

instance : ToFormat FootprintExpr where
  format := FootprintExpr.format

def FootprintExpr.toMessageData (e : FootprintExpr) : MessageData :=
  match e with
  | .input fv => m!"input({Expr.fvar fv})"
  | .get a ids => m!"{a.toMessageData}[{ids.map ArithExpr.toMessageData}]"
  | .set a ids v => m!"{a.toMessageData}[{ids.map ArithExpr.toMessageData}] := {v.toMessageData}"
  | .arith x => m!"{x.toMessageData}"
  | .proj _ f x => m!"{x.toMessageData}.{f}"
  | .tuple x y => m!"({x.toMessageData}, {y.toMessageData})"
  | .unknown => m!"?"

instance : ToMessageData FootprintExpr where
  toMessageData := FootprintExpr.toMessageData

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

def Footprint.format (e : Footprint) : Format :=
  f!"- inputs := {e.inputs.toArray.map Expr.fvar}
  - outputs := {e.outputs}
  - provenance := {e.provenance.toArray.map fun (x, y) => (Expr.fvar x, y)}
  - footprint := {e.footprint}"

instance : ToFormat Footprint where
  format := Footprint.format

def Footprint.toMessageData (e : Footprint) : MessageData :=
  m!"- inputs := {e.inputs.toArray.map Expr.fvar}
  - outputs := {e.outputs}
  - provenance := {e.provenance.toArray.map fun (x, y) => (Expr.fvar x, y)}
  - footprint := {e.footprint}"

instance : ToMessageData Footprint where
  toMessageData := Footprint.toMessageData

structure State extends Footprint where
deriving Inhabited

instance : ToFormat State where
  format s := s.toFootprint.format

instance : ToMessageData State where
  toMessageData s := s.toFootprint.toMessageData

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
  set ({ s with outputs := s.outputs ++ #[p], footprint := s.footprint ++ #[p] })

def pushOptOutput (push : Bool) (p : FootprintExpr) : FootprintM Unit := do
  if push then pushOutput p

def lambdaTelescope (e : Expr) (k : Array Expr → Expr → FootprintM α) : FootprintM α :=
  Meta.lambdaTelescope e fun fvars e => do
    let x ← k fvars e
    -- Pop the variables from the provenance and insert them in the footprint
    popFVars (fvars.map Expr.fvarId!)
    -- Continue
    pure x

def lambdaBoundedTelescope (e : Expr) (maxFVars : Nat) (k : Array Expr → Expr → FootprintM α) : FootprintM α :=
  Meta.lambdaBoundedTelescope e maxFVars fun fvars e => do
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
  | .get _ _ | .set _ _ _ | .proj _ _ _ => .unknown
  | .arith e => e
  | .tuple _ _ | .unknown => .unknown

def minimizeArrayVal (e : Expr) : FootprintM Expr := do
  let env ← getEnv
  let arrayValState := arrayValAttr.ext.getState env
  let rec minimize (e : Expr) : FootprintM Expr := do
    let e := e.consumeMData
    let rules ← arrayValState.rules.getMatch e
    -- Just try the first rule - there should be no more than one
    if rules.size > 0 then
      let (_, rule) := rules[0]!
      let args := e.getAppArgs
      pure args[rule.array]!
    else pure e
  minimize e

def destBind (e : Expr) (k : Expr → FVarId → Expr → FootprintM α) : FootprintM (Option α) := do
  let (f, args) := e.consumeMData.withApp (fun f args => (f, args))
  let f := f.consumeMData
  if ¬ f.isConst then return none
  if f.constName! = ``Bind.bind ∧ args.size = 6 ∧ args[5]!.isLambda then
    let .lam xName xTy body binderInfo := args[5]!
      | throwError "Unreachable"
    withLocalDecl xName binderInfo xTy fun fvar => do
    let body := body.instantiate #[fvar]
    let bound := args[4]!
    k bound fvar.fvarId! body
  else pure none

partial def destTuple (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``Prod.mk 4 ∨ e.isAppOfArity ``MProd.mk 4 then
    let args := e.getAppArgs
    let x := args[2]!
    let y := args[3]!
    some (x, y)
  else none

mutual

/-- Compute the footprint of an expression.

  `terminal` is true if we are exploring an expression which evaluates to
  the result of a loop. For instance, in `loop do let x ← e1; e2`, `e2` is terminal
  while `e1` is not.

  Remark: this function attempts to be robust, so we try not too fail as much as possible,
  even when encountering unexpected situations.
 -/
partial def footprint.expr (terminal : Bool) (e : Expr) : FootprintM FootprintExpr := do
  withTraceNode `Inv (fun _ => pure m!"footprint.expr") do
  trace[Inv] "e: {e}"
  trace[Inv] "terminal: {terminal}"
  let e := e.consumeMData
  let e ← footprint.exprAux terminal e
  /- If this is terminal expression, we need to register this as an output -/
  pushOptOutput terminal e
  pure e

partial def footprint.exprAux (terminal : Bool) (e : Expr) : FootprintM FootprintExpr := do
  match e with
  | .bvar _ =>
    -- This is unexpected, but we can gracefully stop the exploration
    pure .unknown
  | .fvar fvarId =>
    trace[Inv] ".fvar"
    let s ← get
    if let some p := s.provenance.get? fvarId then
      trace[Inv] "known provenance: {p}"
      return p
    if s.inputs.contains fvarId then
      trace[Inv] "input"
      return (.input fvarId)
    trace[Inv] "unknown provenance"
    pure .unknown
  | .mvar _ | .sort _ => pure .unknown
  | .const _ _ =>
    trace[Inv] ".const"
    -- Check if this is a natural number
    let ty ← inferType e
    let p ←
      match ty with
      | .const ``Nat [] => pure (.arith (.const e))
      | _ => pure .unknown
    pushOptOutput terminal p
    pure p
  | .lit l =>
    trace[Inv] ".lit"
    match l with
    | .natVal n => pure (.arith (.lit n))
    | .strVal _ => pure .unknown
  | .app _ _ =>
    trace[Inv] ".app"
    footprint.app terminal e
  | .lam _ _ _ _ =>
    trace[Inv] ".lam"
    -- Typically happens when diving into a match or a let-binding
    lambdaTelescope e fun _ body => do
    footprint.expr terminal body
  | .letE _ _ _ _ _ =>
    trace[Inv] ".letE"
    -- How do we destruct exactly *one* let?
    lambdaLetTelescope e fun boundFVars inner => do
    -- Explore the bound expressions
    let boundExprs ← boundFVars.filterMapM fun fvar => do
      let fvarId := fvar.fvarId!
      if let some decl := (← getLCtx).fvarIdToDecl.find? fvarId then do
        if let some value := decl.value? then
          pure (some (fvarId, ← footprint.expr false value))
        else pure none
      else pure none
    withFVars boundExprs do
    -- Explore the inner body
    footprint.expr terminal inner
  | .mdata _ e => footprint.expr terminal e
  | .proj typename idx struct =>
    trace[Inv] ".proj"
    let struct ← footprint.expr false struct
    pure (.proj typename idx struct)
  | .forallE _ _ _ _ =>
    trace[Inv] ".forallE"
    /- If we find a forall it's probably because we're exploring a type:
       we can just stop -/
    pure .unknown

-- Subcase: the expression is a function application
partial def footprint.app (terminal : Bool) (e : Expr) : FootprintM FootprintExpr := do
  withTraceNode `Inv (fun _ => pure m!"footprint.app") do
  /- There are several cases:
      - it might be a constant
      - it might be a tuple (`Prod` or `MProd`)
      - it might be a match
      - it might be a monadic let, in which case we need to destruct it
      - it might be a get/set expression
  -/
  let f := e.getAppFn

  -- Check if this is a constant
  if e.isAppOfArity ``OfNat.ofNat 3 then
    trace[Inv] "is OfNat.ofNat"
    let args := e.getAppArgs
    return (← footprint.expr terminal args[1]!)

  -- Check if this is a. tuple
  if let some (x, y) := destTuple e then
    trace[Inv] "is a tuple"
    let x ← footprint.expr false x
    let y ← footprint.expr false y
    return (.tuple x y)

  /- Check if this is a matcher (a call to an auxiliary definition
      which implements a match) -/
  if let some me := ← matchMatcherApp? e then
    /-  We want to work on the more primitive `casesOn` expressions,
        to check if the match is, for instance, a match deconstructing.

        Note that for instance, when writing:
        ```
        match xyz with
        | (x, y, z) => ...
        ```
        Lean actually introduces the following auxiliary definition:
        ```
        def match_1 :=
          fun motive xyz h_1 => Prod.casesOn xyz fun fst snd => Prod.casesOn snd fun fst_1 snd => h_1 fst fst_1 snd
        ```
        and the match becomes a call to `match_1`.

        In order to properly analyze it the simplest is to unfold it to reveal the nested calls to `Prod.casesOn`.
      -/
    trace[Inv] "is a match"
    trace[Inv]
      "matcherApp:
      - params: {me.params}
      - motive: {me.motive}
      - discrs: {me.discrs}
      - altNumParams: {me.altNumParams}
      - alts: {me.alts}
      - remaining: {me.remaining}"

    /- Unfold the match definition: we need to unfold the definition, then beta-reduce
       it to get rid of the lambdas -/
    let e ← deltaExpand e (fun name => name = me.matcherName)
    let e ← Core.betaReduce e
    trace[Inv] "unfolded and reduced match: {e}"
    -- Small sanity check: we managed to unfold the match
    if e.getAppFn == f then return .unknown
    -- Otherwise, explore the unfolded expression
    return (← footprint.expr terminal e)

  -- Check if this is a casesOn expression (a "primitive" match)
  if let .const fname _ := f then
    if isCasesOnRecursor (← getEnv) fname then
      trace[Inv] "is a casesOn"
      return (← footprint.casesOn e)

  -- Check if this is a monadic let-binding
  if let some e ← destBind e
    fun bound fvarId inner => do
      -- Explore the bound expression
      let bound ← footprint.expr false bound
      return ← do
        withFVar fvarId bound do
        -- Continue exploring the inner expression
        footprint.expr false inner
    then
      trace[Inv] "is moandic bind"
      return e
  -- Check if this is a get/set expression
  if let some e ← footprint.arrayExpr terminal e then
    trace[Inv] "is an array expression"
    return e
  -- Don't know: explore the arguments
  let args := e.getAppArgs
  let _ ← Array.mapM (footprint.expr false) args
  -- TODO: tuple case
  pure .unknown

partial def footprint.casesOn (e : Expr) : FootprintM FootprintExpr := do
  withTraceNode `Inv (fun _ => pure m!"footprint.casesOn") do
  let f := e.getAppFn
  let fname := f.constName!
  let args := e.getAppArgs

  /-  There are two cases:
      - either this is a known match, such as a match over a `Prod` or `MProd`:
        we have special treatment for these cases.
      - or this is an unknown match, in which case we deconstruct the match and continue -/

  if (fname = ``Prod.casesOn ∨ fname = ``MProd.casesOn) ∧ args.size = 5 then
    trace[Inv] "is a Prod.casesOn or an MProd.casesOn"
    let scrut := args[3]!
    let branch := args[4]!
    trace[Inv] "scrut: {scrut}"
    trace[Inv] "branch: {branch}"

    -- Explore the scrutinee
    let scrut ← footprint.expr false scrut

    -- Explore the branch, which should have exactly two inputs (for the fields of the pair)
    lambdaBoundedTelescope branch 2 fun fvars branch => do
    if fvars.size ≠ 2 then
      -- This is unexpected: simply explore the branches
      trace[Inv] "Expected two inputs, got {fvars}"
      let _ ← footprint.expr false branch
      return .unknown

    -- Register the branch inputs as being projections of the scrutinee
    let typeName := if fname = ``Prod.casesOn then ``Prod else ``MProd
    withFVar fvars[0]!.fvarId! (.proj typeName 0 scrut) do
    withFVar fvars[1]!.fvarId! (.proj typeName 1 scrut) do
    -- Explore the branch expression
    footprint.expr false branch

  else
    /- The casesOn definition is always of the following shape:
        - input parameters (implicit parameters)
        - motive (implicit), -- the motive gives the return type of the match
        - scrutinee (explicit)
        - branches (explicit).
        In particular, we notice that the scrutinee is the first *explicit*
        parameter - this is how we spot it.
      -/
    -- Find the first explicit parameter: this is the scrutinee
    let scrutIdx ← do
      forallTelescope (← inferType f) fun xs _ => do
      let rec findFirstExplicit (i : Nat) : MetaM Nat := do
        if i ≥ xs.size then throwError "Unexpected: could not find an explicit parameter"
        else
          let x := xs[i]!
          let xFVarId := x.fvarId!
          let localDecl ← xFVarId.getDecl
          match localDecl.binderInfo with
          | .default => pure i
          | _ => findFirstExplicit (i + 1)
      findFirstExplicit 0
    -- Split the arguments
    let scrut := args[scrutIdx]!
    let branches := args.extract (scrutIdx + 1) args.size

    -- Explore the scrutinee and the branches
    let _ ← footprint.expr false scrut
    let _ ← branches.mapM (footprint.expr false)
    pure .unknown


partial def footprint.arrayExpr (_terminal : Bool) (e : Expr) : FootprintM (Option FootprintExpr) := do
  withTraceNode `Inv (fun _ => pure m!"footprint.arrayExpr") do
  trace[Inv] "e: {e}"
  let env ← getEnv
  /- Attempt to deconstruct a getter -/
  let getterState := arrayGetterAttr.ext.getState env
  let rules ← getterState.rules.getMatch e
  -- Just try the first rule - there should be no more than one
  if rules.size > 0 then
    trace[Inv] "is a getter"
    let (_, rule) := rules[0]!
    let args := e.getAppArgs
    let array := args[rule.array]!
    let array ← footprint.expr false (← minimizeArrayVal array)
    let indices := rule.indices.map fun id => args[id]!
    let indices ← indices.mapM (footprint.expr false)
    let indices := indices.map FootprintExpr.toArithExpr
    let e := FootprintExpr.get array indices
    return e

  /- Attempt to deconstruct a setter -/
  let setterState := arraySetterAttr.ext.getState env
  let rules ← setterState.rules.getMatch e
  -- Just try the first rule - there should be no more than one
  if rules.size > 0 then
    trace[Inv] "is a setter"
    let (_, rule) := rules[0]!
    let args := e.getAppArgs
    let array ← footprint.expr false (← minimizeArrayVal args[rule.array]!)
    let indices := rule.indices.map fun id => args[id]!
    let indices ← indices.mapM (footprint.expr false)
    let indices := indices.map FootprintExpr.toArithExpr
    let value ← footprint.expr false args[rule.value]!
    let e := FootprintExpr.set array indices value
    return e

  /- Don't know -/
  pure .none

end

end Aeneas.Inv
