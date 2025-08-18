import Aeneas.Std.Primitives
import AeneasMeta.Extensions

namespace Aeneas.Inv

open Lean Elab Meta
open Extensions

initialize registerTraceClass `Inv

/-!
# Helpers
-/

def arrayToTupleFormat (format : α → Format) (x : Array α) : Format := Id.run do
  let mut s := f!"("
  for h: i in [0:x.size-1] do
    have h' : i < x.size := by simp [Membership.mem] at h; omega
    s := s ++ f!"{format x[i]}, "
  if h: x.size > 0 then s := s ++ f!"{format x[x.size-1]}"
  pure (s ++ f!")")

def arrayToTupleMessageData (toMessageData : α → MessageData) (x : Array α) :
  MessageData := Id.run do
  let mut s := m!"("
  for h: i in [0:x.size-1] do
    have h' : i < x.size := by simp [Membership.mem] at h; omega
    s := s ++ m!"{toMessageData x[i]}, "
  if h: x.size > 0 then s := s ++ m!"{toMessageData x[x.size-1]}"
  pure (s ++ m!")")

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

def exprToNat (e : Expr) : Option Nat :=
  if e.isAppOfArity ``OfNat.ofNat 3 then
    let args := e.getAppArgs
    match args[1]! with
    | .lit (.natVal n) => some n
    | _ => none
  else none

/-- Find at which positions the expressions in `toFind` appear in `args`, with the exception that
    if an expression is a number then we should directly use this number as an index, rather than
    look for the expression inside of `args`. -/
def findPositionsOfIndexOrExpr (toFind : Array Expr) (args : Array Expr) :
  MetaM (Array Nat) := do
  let mut map : Std.HashMap Expr Nat := Std.HashMap.emptyWithCapacity
  let toFindSet := Std.HashSet.ofArray toFind
  for h: i in [0:args.size] do
    let arg := args[i]
    if toFindSet.contains arg then
      map := map.insert arg i
  -- Find every argument's index
  let indices ← do
    toFind.mapM fun e => do
      -- Is the expression an index?
      match exprToNat e with
      | some i =>
        -- Yes: use this index
        -- Sanity check
        if i ≥ args.size then throwError m!"Invalid index: {i}"
        pure i
      | none =>
        -- No: look up where the expression appears in the arguments
        if let some i := Std.HashMap.get? map e then pure i
        else throwError m!"Could not find argument: {e}"
  pure indices

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
      let positions ← findPositionsOfIndexOrExpr (indices ++ #[array]) fvars
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
      let positions ← findPositionsOfIndexOrExpr (indices ++ #[array, value]) fvars
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
# Attribute: `inv_val`
-/

/-- This is used to minimize values such as array and index expressions.

    For instance, if `x : Array α`, then in the expression `x.toList`
    we consider that `x` is the minimal array expression. Similarly,
    if `x : Fin 32`, then in the expression `x.val` we consider that `x`
    is the minimal index expression. Also, in `Fin.mk 32 ...`, we
    consider the minimal expression to be `32`. This allows to make
    the provenance and bound analyzes more flexible.
 -/
structure Val where
  -- The index of the minimized value in the list of arguments
  val : Nat
deriving Inhabited, BEq

syntax (name := invVal) "inv_val" term : attr

def parseValArgs
: Syntax -> MetaM Expr
| `(attr| inv_val $array ) => do
  let elabExpr e := do instantiateMVars (← Elab.Term.elabTerm e none |>.run')
  elabExpr array
| _ => throwUnsupportedSyntax

initialize valAttr : ArrayAttr Val ← do
  initializeArrayAttrExt `invValAttr `invVal
    fun ext defName stx attrKind => do
    -- Lookup the definition
    let env ← getEnv
    let some decl := env.findAsync? defName
      | throwError "Could not find definition {defName}"
    let sig := decl.sig.get
    let ty := sig.type
    -- Find where the position of the arguments
    let array : Val ← MetaM.run' do
      /- Strip the quantifiers.

          We do this before elaborating the pattern because we need the universally
          quantified variables to be in the context.
      -/
      forallTelescope ty.consumeMData fun fvars _ => do
      let val ← parseValArgs stx
      /- Find the position of every fvar id -/
      let positions ← findPositionsOfIndexOrExpr (#[val]) fvars
      pure { val := positions[0]! }
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

/-- Kind of range iterator.

    We hardcode them for now.
-/
inductive RangeKind where
  | add -- add a constant at every step
  | sub -- subtract a constant at every step
  | mul -- multiply by a constant at every step
  | div -- divide by a constant at every step
deriving BEq

def RangeKind.toString (k : RangeKind) : String :=
  match k with
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"

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
  /-- An index in a range (such as `[0:256]`).

      For now we hardcode the different ranges we support.
      The `stop` value is exclusive.
   -/
  | range (start stop step : ArithExpr) (kind : RangeKind)
  | unknown
deriving BEq

instance : Inhabited ArithExpr := { default := .unknown }

def ArithExpr.format (e : ArithExpr) : Format :=
  match e with
  | .input fv => f!"{Expr.fvar fv}"
  | .lit n => f!"{n}"
  | .const e => f!"{e}"
  | .binop op a b => f!"{format a} {op} {format b}"
  | .range start stop step kind =>
    f!"[{start.format}:{stop.format}:{kind.toString}={step.format}]"
  | .unknown => f!"?"

instance : ToFormat ArithExpr where
  format := ArithExpr.format

def ArithExpr.toMessageData (e : ArithExpr) : MessageData :=
  match e with
  | .input fv => m!"{Expr.fvar fv}"
  | .lit n => m!"{n}"
  | .const e => m!"{e}"
  | .binop op a b => m!"{a.toMessageData} {op} {b.toMessageData}"
  | .range start stop step kind =>
    m!"[{start.toMessageData}:{stop.toMessageData}:{kind.toString}={step.toMessageData}]"
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
  /- Handling projectors properly is particularly useful because we often need to
     decompose loop inputs (which are usually a tuple) -/
  | proj (typename : Name) (field : Nat) (e : FootprintExpr)
  /- Useful for the outputs -/
  | struct (typename : Name) (fields : Array FootprintExpr)
  | lit (n : Nat)
  /- A constant natural number.

     We store a general expression rather than, e.g., a constant name, because
     it might be an expression of the shape: `n config`, where `config`
     remains constant inside the loop (and typically within the function).
  -/
  | const (e : Expr)
  | binop (op : ArithBinop) (a b : FootprintExpr)
  --
  | range (start stop step : ArithExpr) (kind : RangeKind)
  --
  | unknown
deriving BEq

instance : Inhabited FootprintExpr := { default := .unknown }

partial def FootprintExpr.format (e : FootprintExpr) : Format :=
  match e with
  | .input fv => f!"{Expr.fvar fv}"
  | .get a ids => f!"{a.format}{ids.map ArithExpr.format}"
  | .set a ids v => f!"({a.format}{ids.map ArithExpr.format} := {v.format})"
  | .proj _ f x => f!"{x.format}.{f}"
  | .struct _ fields => f!"({arrayToTupleFormat format fields})"
  | .lit n => f!"{n}"
  | .const e => f!"{e}"
  | .binop op x y => f!"({x.format} {op} {y.format})"
  | .range start stop step kind =>
    f!"[{start.format}:{stop.format}:{kind.toString}={step.format}]"
  | .unknown => f!"?"

instance : ToFormat FootprintExpr where
  format := FootprintExpr.format

partial def FootprintExpr.toMessageData (e : FootprintExpr) : MessageData :=
  match e with
  | .input fv => m!"{Expr.fvar fv}"
  | .get a ids => m!"{a.toMessageData}[{ids.map ArithExpr.toMessageData}]"
  | .set a ids v => m!"({a.toMessageData}{ids.map ArithExpr.toMessageData} := {v.toMessageData})"
  | .proj _ f x => m!"{x.toMessageData}.{f}"
  | .struct _ fields => m!"({arrayToTupleMessageData toMessageData fields})"
  | .lit n => m!"{n}"
  | .const e => m!"{e}"
  | .binop op x y => m!"({x.toMessageData} {op} {y.toMessageData})"
  | .range start stop step kind =>
    m!"[{start.toMessageData}:{stop.toMessageData}:{kind.toString}={step.toMessageData}]"
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

abbrev FootprintM := StateRefT State MetaM

-- Make the compiler generate specialized `pure`/`bind` so we do not have to optimize through the
-- whole monad stack at every use site. May eventually be covered by `deriving`.
@[always_inline]
instance : Monad FootprintM := let i := inferInstanceAs (Monad FootprintM); { pure := i.pure, bind := i.bind }

instance : MonadLCtx FootprintM where
  getLCtx := do pure (← read).lctx

instance : AddMessageContext FootprintM where
  addMessageContext := addMessageContextFull

@[inline] def FootprintM.run (x : FootprintM α) (s : State) : MetaM (α × State) := do
  StateRefT'.run x s

@[inline] def FootprintM.run' (x : FootprintM α) (s : State) : MetaM α :=
  Prod.fst <$> x.run s

@[inline] def FootprintM.toIO (x : FootprintM α) (ctxCore : Core.Context) (sCore : Core.State) (s : State) :
  IO (α × Core.State × Meta.State × State) := do
  let ((a, s), (sCore, mState)) ← (x.run s).toIO ctxCore sCore
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

def withFVar {α} (fvar : FVarId) (e : FootprintExpr) (k : FootprintM α) : FootprintM α := do
  -- TODO: this is probably not the proper way of scoping things
  let s ← get
  set ({s with provenance := s.provenance.insert fvar e})
  let x ← k
  popFVar fvar
  pure x

def withFVars {α} (fvars : Array (FVarId × FootprintExpr)) (k : FootprintM α) : FootprintM α := do
  -- TODO: this is probably not the proper way of scoping things
  let s ← get
  set ({s with provenance := s.provenance.insertMany fvars})
  let x ← k
  popFVars (fvars.map Prod.fst)
  pure x

def pushOutput (p : FootprintExpr) : FootprintM Unit := do
  trace[Inv] "Pushing output: {p}"
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
  | .lit n => .lit n
  | .const c => .const c
  | .binop op x y => .binop op x.toArithExpr y.toArithExpr
  | .range start stop step kind => .range start stop step kind
  | .struct _ _ | .unknown => .unknown

/-- Minimize a value.

    Return `some` if the value was minimized, `none` if it was left unchnaged.
-/
partial def minimizeVal (e : Expr) : FootprintM (Option Expr) := do
  withTraceNode `Inv (fun _ => pure m!"minimizeVal") do
  let env ← getEnv
  let inValState := valAttr.ext.getState env
  let rec minimize (e : Expr) : FootprintM (Option Expr) := do
    let e := e.consumeMData
    let rules ← inValState.rules.getMatch e
    -- Just try the first rule - there should be no more than one
    if rules.size > 0 then
      let (_, rule) := rules[0]!
      let args := e.getAppArgs
      let arg := args[rule.val]!
      -- Minimize again
      if let some arg' ← minimizeVal arg then pure arg' else pure arg
    else pure none
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

/-- Homogeneous binops -/
def arithBinops : Std.HashMap Name ArithBinop := Std.HashMap.ofList [
  (``Add.add, .add),
  (``Sub.sub, .sub),
  (``Mul.mul, .mul),
  (``Mod.mod, .mod),
  (``Div.div, .div),
  (``Pow.pow, .pow),
]

/-- Heterogeneous biniops -/
def arithHBinops : Std.HashMap Name ArithBinop := Std.HashMap.ofList [
  (``HAdd.hAdd, .add),
  (``HSub.hSub, .sub),
  (``HMul.hMul, .mul),
  (``HMod.hMod, .mod),
  (``HDiv.hDiv, .div),
  (``HPow.hPow, .pow),
]

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
  /- We always minimize the expressions -/
  let e ← do
    if let some e' ← minimizeVal e then
      trace[Inv] "Value was minimized: {e'}"
      pure e'
    else pure e
  /- Explore -/
  let e ← footprint.exprAux terminal e
  /- If this is a terminal expression, we need to register this as an output -/
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
      | .const ``Nat [] => pure (.const e)
      | _ => pure .unknown
    pushOptOutput terminal p
    pure p
  | .lit l =>
    trace[Inv] ".lit"
    match l with
    | .natVal n => pure (.lit n)
    | .strVal _ => pure .unknown
  | .app _ _ =>
    trace[Inv] ".app"
    footprint.app terminal e
  | .lam _ _ _ _ =>
    trace[Inv] ".lam"
    -- Typically happens when diving into a match or a let-binding
    lambdaTelescope e fun _ body => do
    footprint.expr terminal body
  | .letE declName type value body _ =>
    trace[Inv] ".letE"
    -- Explore the bound value
    let value ← footprint.expr false value
    -- Explore the body
    withLocalDecl declName .default type fun fvar => do
    let body := body.instantiate #[fvar]
    withFVar fvar.fvarId! value do
    footprint.expr false body
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
      - constant
      - tuple (`Prod` or `MProd`)
      - tuple projector
      - match
      - monadic let, in which case we need to destruct it
      - get/set expression
      - binary operation
  -/
  let f := e.getAppFn
  let args := e.getAppArgs
  let env ← getEnv

  -- Check if this is a constant
  if e.isAppOfArity ``OfNat.ofNat 3 then
    trace[Inv] "is OfNat.ofNat"
    let args := e.getAppArgs
    return (← footprint.expr terminal args[1]!)

  -- Check if this is a structure constructor
  let ty ← inferType e
  let fty := ty.getAppFn
  if let .const fName _ := f then
    if let Expr.const tyName _ := fty then
      if isStructureLike env tyName then
        let info := getStructureCtor env tyName
        if info.name = fName then
          trace[Inv] "is a structure constructor"
          let fields := args.extract (args.size - info.numFields)
          let fields ← fields.mapM (footprint.expr false)
          return (.struct tyName fields)

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
    if isCasesOnRecursor env fname then
      trace[Inv] "is a casesOn"
      return (← footprint.casesOn e)

  -- Check if this is a monadic let-binding
  if let some e ← destBind e
    fun bound fvarId inner => do
      trace[Inv] "is monadic bind"
      -- Explore the bound expression
      let bound ← footprint.expr false bound
      withFVar fvarId bound do
      -- Continue exploring the inner expression
      footprint.expr false inner
    then
      trace[Inv] "monadic bind result: {e}"
      return e

  -- Homogeneous binary operations
  if f.isConst ∧ args.size = 3 then
    let fname := f.constName!
    if let some op := arithBinops.get? fname then
      trace[Inv] "homogeneous binop"
      let x ← footprint.expr false args[1]!
      let y ← footprint.expr false args[2]!
      return (.binop op x y)

  -- Heterogeneous binary operations
  if f.isConst ∧ args.size = 6 then
    let fname := f.constName!
    if let some op := arithHBinops.get? fname then
      trace[Inv] "heterogeneous binop"
      let x ← footprint.expr false args[4]!
      let y ← footprint.expr false args[5]!
      return (.binop op x y)

  -- Check if this is a get/set expression
  if let some e ← footprint.arrayExpr terminal e then
    trace[Inv] "is an array expression"
    return e

  /- Check if this is a projector

     We have to do this *after* checking whether an expression is a getter because
     some getter functions (like `getElem!`) are considered as projectors.
   -/
  if let .const fName _ := f then
    if let some info ← getProjectionFnInfo? fName then
      trace[Inv] "projector"
      trace[Inv] "numParams: {info.numParams}"
      trace[Inv] "i: {info.i}"
      trace[Inv] "args: {e.getAppArgs}"
      let x := e.getAppArgs[info.numParams]!
      let x ← footprint.expr false x
      let idx := info.i
      let structName := (Environment.getProjectionStructureName? env fName).get!
      return (.proj structName idx x)

  -- Don't know: explore the arguments
  let args := e.getAppArgs
  let _ ← Array.mapM (footprint.expr false) args
  -- TODO: tuple case
  pure .unknown

partial def footprint.casesOn (e : Expr) : FootprintM FootprintExpr := do
  withTraceNode `Inv (fun _ => pure m!"footprint.casesOn") do
  let f := e.getAppFn
  let args := e.getAppArgs

  /-  The casesOn definition is always of the following shape:
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
  trace[Inv] "scrut: {scrut}"
  trace[Inv] "branches: {branches}"

  /-  If this is a cases over a structure, then we know that the variables bound
      in the branch should refer exactly to the fields of the structure: we use this
      fact. -/

  -- Check if this is a cases on over a *structure* and retrieve the number of fields
  let scrutTy ← inferType scrut
  let scrutfty := scrutTy.getAppFn
  let structNumFields ← do
    if let .const fname _ := scrutfty then
      if isStructureLike (← getEnv) fname then
        pure (some (getStructureLikeNumFields (← getEnv) fname))
      else pure none
    else pure none

  -- If we're matching over a structure, there should be exactly one branch
  if structNumFields.isSome ∧ branches.size = 1 then
    trace[Inv] "is a casesOn over a structure"
    -- Retrieve this structure's information
    let numFields := structNumFields.get!
    let branch := branches[0]!

    -- Explore the scrutinee
    let scrut ← footprint.expr false scrut

    -- Explore the branch, which should have exactly `numFields` inputs
    lambdaBoundedTelescope branch numFields fun fvars branch => do
    if fvars.size ≠ numFields then
      -- This is unexpected: simply explore the branches
      trace[Inv] "Expected {numFields} inputs, got {fvars}"
      let _ ← footprint.expr false branch
      return .unknown

    -- Register the branch inputs as being projections of the scrutinee
    let .const typeName _ := scrutfty
      | throwError "Unreachable"
    let fvars := fvars.mapIdx (fun i fv => (fv.fvarId!, .proj typeName i scrut))
    withFVars fvars do
    -- Explore the branch expression
    footprint.expr false branch

  else
    -- Explore the scrutinee and the branches
    let _ ← footprint.expr false scrut
    let _ ← branches.mapM (footprint.expr false)
    pure .unknown


partial def footprint.arrayExpr (_terminal : Bool) (e : Expr) :
  FootprintM (Option FootprintExpr) := do
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
    trace[Inv] "array value: {array}"
    let array ← footprint.expr false array
    let indices := rule.indices.map fun id => args[id]!
    trace[Inv] "indices: {indices}"
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
    let array := args[rule.array]!
    trace[Inv] "array value: {array}"
    let array ← footprint.expr false array
    let indices := rule.indices.map fun id => args[id]!
    trace[Inv] "indices: {indices}"
    let indices ← indices.mapM (footprint.expr false)
    let indices := indices.map FootprintExpr.toArithExpr
    let value := args[rule.value]!
    trace[Inv] "value: {value}"
    let value ← footprint.expr false value
    let e := FootprintExpr.set array indices value
    return e

  /- Don't know -/
  pure .none

end

end Aeneas.Inv
