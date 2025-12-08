import Aeneas.Std.Primitives
import AeneasMeta.Extensions
import Mathlib.Data.Nat.Log

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
def findPositionsOfIndexOrExpr {n} (toFind : Vector Expr n) (args : Array Expr) :
  MetaM (Vector Nat n) := do
  let mut map : Std.HashMap Expr Nat := Std.HashMap.emptyWithCapacity
  let toFindSet := Std.HashSet.ofArray toFind.toArray
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

structure ArrayAttr (α : Type) where
  attr : AttributeImpl
  ext  : SimpleScopedEnvExtension (DiscrTreeKey × Name × α) (ExtBase α)
deriving Inhabited

def initializeArrayExt {α : Type} [BEq α] (extName : Name) :
  IO (SimpleScopedEnvExtension (Array DiscrTree.Key × Name × α) (ExtBase α)) := do
  registerSimpleScopedEnvExtension {
      name := extName,
      initial := ExtBase.empty,
      addEntry := ExtBase.insert,
  }

def initializeArrayAttr {α : Type} [BEq α] (attrName : Name)
  (ext : SimpleScopedEnvExtension (Array DiscrTree.Key × Name × α) (ExtBase α))
  (add : SimpleScopedEnvExtension (Array DiscrTree.Key × Name × α) (ExtBase α) →
         Name → Syntax → AttributeKind → AttrM Unit) : IO (ArrayAttr α) := do
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

def initializeArrayAttrExtAndAttr {α : Type} [BEq α] (extName attrName : Name)
  (add : SimpleScopedEnvExtension (Array DiscrTree.Key × Name × α) (ExtBase α) →
         Name → Syntax → AttributeKind → AttrM Unit) : IO (ArrayAttr α) := do
  let ext ← initializeArrayExt extName
  initializeArrayAttr attrName ext add

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
  initializeArrayAttrExtAndAttr `arrayGetterExt `arrayGetter
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
      let positions ← findPositionsOfIndexOrExpr (Vector.mk (indices ++ #[array]) (by simp; rfl)) fvars
      let positions := positions.toArray
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
  initializeArrayAttrExtAndAttr `arraySetterExt `arraySetter
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
      let positions ← findPositionsOfIndexOrExpr (Vector.mk (indices ++ #[array, value]) (by simp; rfl)) fvars
      let positions := positions.toArray
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
  initializeArrayAttrExtAndAttr `invValExt `invVal
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
      let positions ← findPositionsOfIndexOrExpr (Vector.mk #[val] (by simp; rfl)) fvars
      pure { val := positions[0] }
    -- Generate the key for the discrimination tree
    let key ← MetaM.run' do
      let (mvars, _) ← forallMetaTelescope ty.consumeMData
      DiscrTree.mkPath (← mkAppOptM defName (mvars.map Option.some))
    -- Store
    ScopedEnvExtension.add ext (key, defName, array) attrKind

/-!
# Footprints
-/

abbrev VarId := Nat

structure Var where
  id : VarId
  name : Option String
deriving Inhabited, BEq, Ord, Hashable

instance : ToFormat Var where
  format v :=
    match v.name with
    | some name => f!"{name}@{v.id}"
    | none => f!"@{v.id}"

instance : ToMessageData Var where
  toMessageData v :=
    match v.name with
    | some name => m!"{name}@{v.id}"
    | none => m!"@{v.id}"


/-- Kind of range iterator.

    We hardcode them for now.
-/
inductive RangeKind where
  | add -- add a constant at every step
  | sub -- subtract a constant at every step
  | mul -- multiply by a constant at every step
  | div -- divide by a constant at every step
deriving Inhabited, BEq, Ord, Hashable

def RangeKind.toString (k : RangeKind) : String :=
  match k with
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"

inductive ArithBinop where
  | add
  | sub
  | mul
  | div
  | mod
  | pow
deriving Inhabited, BEq, Ord, Hashable

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

/-- Characterizes a variable introduced by a loop -/
inductive LoopVarKind where
/-- The variable binding the state in a loop iteration.

    Ex.: `x` in the expression `loopIter (fun i x => ...)`
-/
| input
/-- The variable binding the iteration index in a loop iteration.

    Ex.: `i` in the expression `loopIter (fun i s => ...)`
-/
| index
/-- The output of a loop.

    Ex.: `x` in the expression `let x ← loopIter ...; ...`
 -/
| output
deriving Inhabited, BEq, Ord, Hashable

instance : ToMessageData LoopVarKind where
  toMessageData k :=
    match k with
    | .input => "input" | .index => "index" | .output => "output"

abbrev LoopId := Nat

/-- An expression which we register in the footprint.

    This is typically an expression which reads or writes to an array.
-/
inductive FootprintExpr where
  | var (v : Var) -- A variable
  | get (array : FootprintExpr) (indices : Array FootprintExpr)
  | set (array : FootprintExpr) (indices : Array FootprintExpr) (value : FootprintExpr)
  /- Handling projectors properly is particularly useful because we often need to
     decompose loop inputs (which are usually a tuple) -/
  | proj (field : Nat) (e : FootprintExpr)
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
  | range (start stop step : FootprintExpr) (kind : RangeKind)
  --
  | unknown
deriving Inhabited, BEq, Hashable

instance : Inhabited FootprintExpr := { default := .unknown }

partial def FootprintExpr.toMessageData (e : FootprintExpr) : MessageData :=
  match e with
  | .var v => m!"{v}"
  | .get a ids => m!"{a.toMessageData}[{ids.map toMessageData}]"
  | .set a ids v => m!"({a.toMessageData}{ids.map toMessageData} := {v.toMessageData})"
  | .proj f x => m!"{x.toMessageData}.{f}"
  | .struct _ fields => m!"({arrayToTupleMessageData toMessageData fields})"
  | .lit n => m!"{n}"
  | .const e => m!"{e}"
  | .binop op x y => m!"({x.toMessageData} {op} {y.toMessageData})"
  | .range start stop step kind =>
    m!"[{start.toMessageData}:{stop.toMessageData}:{kind.toString}={step.toMessageData}]"
  | .unknown => m!"?"

instance : ToMessageData FootprintExpr where
  toMessageData := FootprintExpr.toMessageData

/-- Projection over a variable -/
structure VarProj where
  var : Var
  projs : List Nat
deriving Inhabited, BEq, Hashable, Ord

instance : ToMessageData VarProj where
  toMessageData x :=
    let rec go (m : MessageData) (projs : List Nat) :=
      match projs with
      | [] => m
      | p :: projs =>
        go m!"{m}.{p}" projs
    go m!"{x.var}" x.projs

inductive VarProjOrLit where
| var (v : VarProj)
| lit (n : Nat)
deriving Inhabited, BEq, Hashable, Ord

instance : ToMessageData VarProjOrLit where
  toMessageData x :=
    match x with
    | .var v => m!"{v}"
    | .lit n => m!"{n}"

structure Range where
  start : FootprintExpr
  stop : FootprintExpr
  step : FootprintExpr
  kind : RangeKind
deriving Inhabited, BEq, Hashable

instance : ToMessageData Range where
  toMessageData r :=
    let { start, stop, step, kind } := r
    m!"[{start.toMessageData}:{stop.toMessageData}:{kind.toString}={step.toMessageData}]"

/-- A loop which iterates over an index.

    The definition should have the signature:
    ```
    loop (body : Idx → α → m α) (range : ...) (input : α) : m α
    ```
    where the arguments may be reordered (`input` placed before `range`, etc.).
 -/
structure LoopIterDesc where
  body : Nat
  /- The arguments which stands for the index range. -/
  start : VarProjOrLit
  stop : VarProjOrLit
  step : VarProjOrLit
  rangeKind : RangeKind
  --
  input : Nat
deriving Inhabited, BEq

structure LoopIter where
  range : Range
  input : FootprintExpr
deriving Inhabited, BEq

instance : ToMessageData LoopIter where
  toMessageData x := m!"{'{'}range := {x.range}, input := {x.input}{'}'}"

structure Footprint where
  /-- Var id counter: we increment it whenever we find a new var id -/
  varId : VarId := 0
  /- Inputs of the loop.

     Ex.: when exploring `loop (fun (x, y) => ...)`, the inputs of the loop
     are `x` and `y`.
   -/
  inputs : Std.HashMap FVarId Var := {}
  /- The expressions a loop body evaluates to.

    Ex.: when exploring `foldl (fun x => if x % 2 = 0 then x + 1 else x + 2)`, `x` is a loop input,
    while `x + 1` and `x + 2` are loop outputs.
  -/
  outputs : Std.HashMap LoopId (Array FootprintExpr) := {}
  /-- Loop id counter: we increment it whenever we find a loop -/
  loopId : LoopId := 0
  /-- The loops found so far -/
  loopIters : Std.HashMap LoopId LoopIter := {}
  /-- Partial map from variable to the loop which introduced it, together with the
      kind of the variable. See `LoopVarKind`.
   -/
  varToLoop : Std.HashMap Var (LoopId × LoopVarKind) := {}
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

def Footprint.toMessageData (e : Footprint) : MessageData :=
  m!"- inputs := {e.inputs.toArray.map (fun (fid, v) => (Expr.fvar fid, v))}
  - outputs := {e.outputs.toArray}
  - loopIters := {e.loopIters.toArray}
  - varToLoop := {e.varToLoop.toArray}
  - provenance := {e.provenance.toArray.map fun (x, y) => (Expr.fvar x, y)}
  - footprint := {e.footprint}"

instance : ToMessageData Footprint where
  toMessageData := Footprint.toMessageData

structure State extends Footprint where
deriving Inhabited

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
    set { s with provenance := s.provenance.erase fvar, footprint := s.footprint ++ #[p] }

def popFVars (fvars : Array FVarId) : FootprintM Unit := do
  for fvar in fvars do popFVar fvar

def freshLoopId : FootprintM LoopId := do
  let s ← get
  let id := s.loopId
  set { s with loopId := id + 1 }
  pure id

def freshVarId : FootprintM VarId := do
  let s ← get
  let id := s.varId
  set { s with varId := id + 1 }
  pure id

def freshLoopVar (loopId : LoopId) (name : Option String) (kind : LoopVarKind) :
  FootprintM Var := do
  let id ← freshVarId
  let s ← get
  let v : Var := { id, name }
  set { s with varToLoop := s.varToLoop.insert v (loopId, kind) }
  pure v

def pushLoop (loopId : LoopId) (loop : LoopIter) : FootprintM Unit := do
  let s ← get
  set {s with loopIters := s.loopIters.insert loopId loop }

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

def pushOutput (lpId : LoopId) (p : FootprintExpr) : FootprintM Unit := do
  trace[Inv] "Pushing output: {p}"
  let s ← get
  let outputs :=
    s.outputs.alter lpId (fun outputs =>
      match outputs with | none => #[p] | some outputs => outputs ++ #[p])
  set ({ s with outputs := outputs, footprint := s.footprint ++ #[p] })

def pushOptOutput (push : Option LoopId) (p : FootprintExpr) : FootprintM Unit := do
  match push with
  | none => pure ()
  | some lpId => pushOutput lpId p

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

def mkReducedProj (field : Nat) (e : FootprintExpr) : FootprintExpr :=
  match e with
  | .struct _ fields =>
    -- Sanity check
    if h: field < fields.size then
      fields[field]
    else
      .proj field e
  | _ => .proj field e

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
    if h: rules.size > 0 then
      let (_, rule) := rules[0]
      let args := e.getAppArgs
      if h: rule.val < args.size then
        let arg := args[rule.val]
        -- Minimize again
        if let some arg' ← minimizeVal arg then pure arg' else pure arg
      else pure none
    else pure none
  minimize e

def destBind (e : Expr) (k : Expr → FVarId → Expr → FootprintM α) : FootprintM (Option α) := do
  let (f, args) := e.consumeMData.withApp (fun f args => (f, args))
  let f := f.consumeMData
  if ¬ f.isConst then return none
  if h: f.constName! = ``Bind.bind ∧ args.size = 6 then
    if args[5].isLambda then
      let .lam xName xTy body binderInfo := args[5]
        | throwError "Unreachable"
      withLocalDecl xName binderInfo xTy fun fvar => do
      let body := body.instantiate #[fvar]
      let bound := args[4]
      k bound fvar.fvarId! body
    else pure none
  else pure none

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

/-!
# Extension: `inv_loop_iter`
We have to separate the extension from the attribute because:
- `footprint.expr` needs to access the extension
- the attribute `inv_loop_iter` needs `footprint.expr` to parse some of is arguments
-/

syntax (name := loopIter) "inv_loop_iter" "{" term "}"
  "[" term ":" term ":" ("+=" <|> "-=" <|> "*=" <|> "/=") term "]" term : attr

def parseLoopIterArgs
: Syntax -> MetaM (Expr × Expr × Expr × Expr × RangeKind × Expr)
| `(attr| inv_loop_iter { $body } [ $start : $stop : $kind $step ] $input ) => do
  let elabExpr e := do instantiateMVars (← Elab.Term.elabTerm e none |>.run')
  let body ← elabExpr body
  let start ← elabExpr start
  let stop ← elabExpr stop
  let step ← elabExpr step
  let input ← elabExpr input
  trace[Inv] "kind.getKind: {kind.raw.getKind}"
  let kind ← do
    match kind.raw.getKind with
    | `token.«+=»  => pure RangeKind.add
    | `token.«-=» => pure .sub
    | `token.«*=» => pure .mul
    | `token.«/=» => pure .div
    | _ => throwUnsupportedSyntax
  return (body, start, stop, step, kind, input)
| _ => throwUnsupportedSyntax

initialize loopIterExt :
  SimpleScopedEnvExtension (Array DiscrTree.Key × Name × LoopIterDesc) (ExtBase LoopIterDesc) ← do
  initializeArrayExt `loopIterExt

/-- -/
def asNatLit? (e : Expr) : Option Nat :=
  if e.isAppOfArity ``OfNat.ofNat 3 then
    if let .lit (.natVal n) := e.getAppArgs[1]! then pure n
    else none
  else none

/-- Return the type name and the fields -/
def asStructureConstructor? (e : Expr) : MetaM (Option (Name × Array Expr)) := do
  let ty ← inferType e
  let fty := ty.getAppFn
  let f := e.getAppFn
  let args := e.getAppArgs
  let env ← getEnv
  if let .const fName _ := f then
    if let Expr.const tyName _ := fty then
      if isStructureLike env tyName then
        let info := getStructureCtor env tyName
        if info.name = fName then
          trace[Inv] "is a structure constructor"
          let fields := args.extract (args.size - info.numFields)
          return (some (tyName, fields))
  pure none

/-- Check if this is a matcher application, if yes unfold and reduce the map to
    reveal the casesOn.

    We want to work on the more primitive `casesOn` expressions,
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
def asMatcherApp? (e : Expr) : MetaM (Option Expr) := do
  if let some me := ← matchMatcherApp? e then
    trace[Inv] "is a match"
    trace[Inv]
      "matcherApp:
      - params: {me.params}
      - motive: {me.motive}
      - discrs: {me.discrs}
      - altNumParams: {me.altNumParams}
      - alts: {me.alts}
      - remaining: {me.remaining}"
    let f := e.getAppFn

    /- Unfold the match definition: we need to unfold the definition, then beta-reduce
       it to get rid of the lambdas -/
    let e ← deltaExpand e (fun name => name = me.matcherName)
    let e ← Core.betaReduce e
    trace[Inv] "unfolded and reduced match: {e}"
    -- Small sanity check: we managed to unfold the match
    if e.getAppFn == f then pure none
    else pure e
  else pure none

def asBinop? (e : Expr) : Option (ArithBinop × Expr × Expr) :=
  let f := e.getAppFn
  let args := e.getAppArgs
  if h: f.isConst ∧ args.size = 3 then
    let fname := f.constName!
    if let some op := arithBinops.get? fname then
      pure (op, args[1], args[2])
    else none
  else none

def asHBinop? (e : Expr) : Option (ArithBinop × Expr × Expr) :=
  let f := e.getAppFn
  let args := e.getAppArgs
  if h: f.isConst ∧ args.size = 6 then
    let fname := f.constName!
    if let some op := arithHBinops.get? fname then
      return (op, args[4], args[5])
    else none
  else none

def asProjector? (e : Expr) : MetaM (Option (Nat × Expr)) := do
  let f := e.getAppFn
  if let .const fName _ := f then
    if let some info ← getProjectionFnInfo? fName then
      let args := e.getAppArgs
      if h: info.numParams < args.size then
        trace[Inv] "projector"
        trace[Inv] "numParams: {info.numParams}"
        trace[Inv] "i: {info.i}"
        trace[Inv] "args: {e.getAppArgs}"
        let x := e.getAppArgs[info.numParams]
        let idx := info.i
        return (some (idx, x))
  pure none

/-- Return the list/array expression and the indices -/
def asGetter? (e : Expr) : MetaM (Option (Expr × Array Expr)) := do
  let env ← getEnv
  let getterState := arrayGetterAttr.ext.getState env
  let rules ← getterState.rules.getMatch e

  -- Just try the first rule - there should be no more than one
  if h: rules.size > 0 then
    let args := e.getAppArgs
    let getArg (i : Nat) : MetaM Expr :=
      if h: i < args.size then pure args[i]
      else throwError ""
    let (_, rule) := rules[0]

    try
      let array ← getArg rule.array
      let indices ← rule.indices.mapM getArg
      pure (some (array, indices))
    catch _ => pure none
  else pure none

/-- Return the list/array expression, the indices and the value -/
def asSetter? (e : Expr) : MetaM (Option (Expr × Array Expr × Expr)) := do
  let env ← getEnv
  let setterState := arraySetterAttr.ext.getState env
  let rules ← setterState.rules.getMatch e
  -- Just try the first rule - there should be no more than one
  if h: rules.size > 0 then
    let args := e.getAppArgs
    let getArg (i : Nat) : MetaM Expr :=
      if h: i < args.size then pure args[i]
      else throwError ""
    let (_, rule) := rules[0]

    try
      let array ← getArg rule.array
      let indices ← rule.indices.mapM getArg
      let value ← getArg rule.value
      pure (some (array, indices, value))
    catch _ => pure none
  else pure none

mutual

/-- Compute the footprint of an expression.

  `terminal` is `some lpId` if we are exploring an expression which evaluates to
  the result of a loop, given by `lpId`. For instance, in `loop do let x ← e1; e2`, `e2`
  is terminal while `e1` is not.

  Remark: this function attempts to be robust, so we try not too fail as much as possible,
  even when encountering unexpected situations.
 -/
partial def footprint.expr (terminal : Option LoopId) (e : Expr) : FootprintM FootprintExpr := do
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

partial def footprint.exprAux (terminal : Option LoopId) (e : Expr) : FootprintM FootprintExpr := do
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
    if let some v := s.inputs.get? fvarId then
      trace[Inv] "var"
      return (.var v)
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
    let value ← footprint.expr none value
    -- Explore the body
    withLocalDecl declName .default type fun fvar => do
    let body := body.instantiate #[fvar]
    withFVar fvar.fvarId! value do
    footprint.expr none body
  | .mdata _ e => footprint.expr terminal e
  | .proj _typename idx struct =>
    trace[Inv] ".proj"
    let struct ← footprint.expr none struct
    pure (mkReducedProj idx struct)
  | .forallE _ _ _ _ =>
    trace[Inv] ".forallE"
    /- If we find a forall it's probably because we're exploring a type:
       we can just stop -/
    pure .unknown

-- Subcase: the expression is a function application
partial def footprint.app (terminal : Option LoopId) (e : Expr) : FootprintM FootprintExpr := do
  withTraceNode `Inv (fun _ => pure m!"footprint.app") do
  /- There are several cases:
      - constant
      - tuple (`Prod` or `MProd`)
      - tuple projector
      - match
      - monadic let, in which case we need to destruct it
      - get/set expression
      - loop
      - binary operation
  -/
  let f := e.getAppFn
  let env ← getEnv

  -- Check if this is a constant
  if let some n := asNatLit? e then
    trace[Inv] "is OfNat.ofNat"
    return (.lit n)

  -- Check if this is a structure constructor
  if let some (tyName, fields) ← asStructureConstructor? e then
    let fields ← fields.mapM (footprint.expr none)
    return (.struct tyName fields)

  /- Check if this is a matcher (a call to an auxiliary definition
      which implements a match) -/
  if let some me := ← asMatcherApp? e then
    -- Explore the unfolded expression
    return (← footprint.expr terminal me)

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
      let bound ← footprint.expr none bound
      withFVar fvarId bound do
      -- Continue exploring the inner expression
      footprint.expr none inner
    then
      trace[Inv] "monadic bind result: {e}"
      return e

  -- Homogeneous binary operations
  if let some (op, x, y) := asBinop? e then
    let x ← footprint.expr none x
    let y ← footprint.expr none y
    return (.binop op x y)

  -- Heterogeneous binary operations
  if let some (op, x, y) := asHBinop? e then
    let x ← footprint.expr none x
    let y ← footprint.expr none y
    return (.binop op x y)

  -- Check if this is a get/set expression
  if let some e ← footprint.arrayExpr terminal e then
    trace[Inv] "is an array expression"
    return e

  /- Check if this is a projector

     We have to do this *after* checking whether an expression is a getter because
     some getter functions (like `getElem!`) are considered as projectors.
   -/
  if let some (idx, x) ← asProjector? e then
    trace[Inv] "projector"
    let x ← footprint.expr none x
    return (mkReducedProj idx x)

  -- Check if this is a loop
  if let some e ← footprint.loop terminal e then
    trace[Inv] "is an array expression"
    return e

  -- Don't know: explore the arguments
  let args := e.getAppArgs
  let _ ← Array.mapM (footprint.expr none) args
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
      if h: i ≥ xs.size then throwError "Unexpected: could not find an explicit parameter"
      else
        let x := xs[i]
        let xFVarId := x.fvarId!
        let localDecl ← xFVarId.getDecl
        match localDecl.binderInfo with
        | .default => pure i
        | _ => findFirstExplicit (i + 1)
    findFirstExplicit 0

  -- Split the arguments
  let scrut ← if h: scrutIdx< args.size then pure args[scrutIdx] else throwError "Unreachable"
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
  if h: structNumFields.isSome ∧ branches.size = 1 then
    trace[Inv] "is a casesOn over a structure"
    -- Retrieve this structure's information
    let numFields := structNumFields.get!
    let branch := branches[0]

    -- Explore the scrutinee
    let scrut ← footprint.expr none scrut

    -- Explore the branch, which should have exactly `numFields` inputs
    lambdaBoundedTelescope branch numFields fun fvars branch => do
    if fvars.size ≠ numFields then
      -- This is unexpected: simply explore the branches
      trace[Inv] "Expected {numFields} inputs, got {fvars}"
      let _ ← footprint.expr none branch
      return .unknown

    -- Register the branch inputs as being projections of the scrutinee
    let .const _typeName _ := scrutfty
      | throwError "Unreachable"
    let fvars ← fvars.mapIdxM (fun i fv => do pure (fv.fvarId!, mkReducedProj i scrut))
    withFVars fvars do
    -- Explore the branch expression
    footprint.expr none branch

  else
    -- Explore the scrutinee and the branches
    let _ ← footprint.expr none scrut
    let _ ← branches.mapM (footprint.expr none)
    pure .unknown


partial def footprint.arrayExpr (_terminal : Option LoopId) (e : Expr) :
  FootprintM (Option FootprintExpr) := do
  withTraceNode `Inv (fun _ => pure m!"footprint.arrayExpr") do
  trace[Inv] "e: {e}"

  /- Attempt to deconstruct a getter -/
  if let some (array, indices) ← asGetter? e then
    trace[Inv] "is a getter"
    let array ← footprint.expr none array
    let indices ← indices.mapM (footprint.expr none)
    return FootprintExpr.get array indices

  /- Attempt to deconstruct a setter -/
  if let some (array, indices, value) ← asSetter? e then
    trace[Inv] "is a setter"

    let array ← footprint.expr none array
    let indices ← indices.mapM (footprint.expr none)
    let value ← footprint.expr none value
    return FootprintExpr.set array indices value

  /- Not a getter or setter -/
  pure .none

partial def footprint.loop (_terminal : Option LoopId) (e : Expr) :
  FootprintM (Option FootprintExpr) := do
  withTraceNode `Inv (fun _ => pure m!"footprint.arrayExpr") do
  trace[Inv] "e: {e}"
  let env ← getEnv

  /- Attempt to deconstruct a getter -/
  let loopState := loopIterExt.getState env
  let rules ← loopState.rules.getMatch e
  -- Just try the first rule - there should be no more than one
  if h: rules.size > 0 then
    trace[Inv] "is a loop iter"
    let (_, rule) := rules[0]
    let args := e.getAppArgs
    let loopId ← freshLoopId

    let body ← if h: rule.body < args.size then pure args[rule.body] else throwError "Unexpected"
    let rec addProjs (e : FootprintExpr) (projs : List Nat) : FootprintExpr :=
      match projs with
      | [] => e
      | p :: projs => addProjs (.proj p e) projs
    let rangeIndexToExpr (v : VarProjOrLit) : FootprintM FootprintExpr := do
      match v with
      | .var v =>
        let e ← do
          if h: v.var.id < args.size then
            footprint.expr none args[v.var.id]
          else pure .unknown
        pure (addProjs e v.projs)
      | .lit n => pure (.lit n)
    let start ← rangeIndexToExpr rule.start
    let stop ← rangeIndexToExpr rule.stop
    let step ← rangeIndexToExpr rule.step

    let input ← do
      if h: rule.input < args.size then footprint.expr none args[rule.input]
      else pure .unknown

    /- Explore the body.

       We need to push fresh variables for the bound inputs.
    -/
    let _ ← do
      lambdaBoundedTelescope body 2 fun fvars body => do
      if h: fvars.size ≠ 2 then
        trace[Inv] "Expected 2 inputs, got {fvars}"
        return .unknown -- Abort
      else
        let addVar (fvarId : FVarId) (kind : LoopVarKind) : FootprintM FootprintExpr := do
          let decl ← fvarId.getDecl
          let name := decl.userName.toString
          let var ← freshLoopVar loopId (some name) kind
          pure (.var var)

        let idx := fvars[0].fvarId!
        let idxe ← addVar idx .index
        let input := fvars[1].fvarId!
        let inpute ← addVar input .input
        withFVars #[(idx, idxe), (input, inpute)] do
        footprint.expr (some loopId) body

    /- Register the loop -/
    pushLoop loopId { range := {start, stop, step, kind := rule.rangeKind}, input }

    -- Push a fresh var for the output
    let outputVar ← freshLoopVar loopId none .output
    return (FootprintExpr.var outputVar)

  /- Not a loop -/
  pure .none

end

/-- A normalized linear arithmetic expression (of the shape: `a + ∑ a(i) * f(i)`,
    where `a(i)` is a constant, and `f(i)` is a free variable).
  -/
structure LinArithExpr where
  -- TODO: don't use a HashMap
  coefs : Std.HashMap VarProj Int
  const : Int

instance : BEq LinArithExpr where -- TODO: I don't like that
  beq a1 a2 := Id.run do
    for (v, n) in a1.coefs do
      if a2.coefs.get? v ≠ some n then return false
    for (v, n) in a2.coefs do
      if a1.coefs.get? v ≠ some n then return false
    if a1.const ≠ a2.const then pure false else pure true

def LinArithExpr.toMessageData (e : LinArithExpr) : MessageData := Id.run do
  let coefs := e.coefs.toArray.map fun (v, coef) =>
    let coef :=
      if coef = 1 then m!"{v}" else m!"{coef} * {v}"
    m!"{coef}"
  let const := if e.const = 0 then [] else [m!"{e.const}"]
  let coefs := coefs ++ const
  if h: coefs.size = 0 then m!"0"
  else
    let mut s := coefs[0]
    for h: i in [1:coefs.size] do
      s := s ++ m!" + {coefs[i]}"
    pure s

instance : ToMessageData LinArithExpr where
  toMessageData := LinArithExpr.toMessageData

partial def FootprintExpr.getVars (e : FootprintExpr) : Std.HashSet Var :=
  -- Using a state monad to store the set of fvar ids
  let m := StateT (Std.HashSet Var) Id
  let add (v : Var) : m Unit := do
    StateT.set ((← StateT.get).insert v)
  -- The visitor
  let rec go (e : FootprintExpr) : m Unit := do
    match e with
    | .var v => add v
    | .lit _ | .const _ | .unknown => pure ()
    | .binop _ a b => go a; go b
    | .range start stop step _ => go start; go stop; go step
    | .struct _ fields => fields.forM go
    | .proj _ e => go e
    | .get a ids => go a; ids.forM go
    | .set a ids v => go a; ids.forM go; go v
  (Id.run (StateT.run (go e) Std.HashSet.emptyWithCapacity)).snd

def FootprintExpr.toVarProj (e : FootprintExpr) : Option VarProj := do
  match e with
  | .var v => pure { var := v, projs := [] }
  | .proj field e =>
    let p ← e.toVarProj
    pure { p with projs := field :: p.projs}
  | _ => none

def FootprintExpr.toVarProjOrLit (e : FootprintExpr) : Option VarProjOrLit := do
  match e with
  | .lit n => pure (.lit n)
  | _ => pure (.var (← e.toVarProj))

/-- Normalize an arithmetic expression, if possible -/
def FootprintExpr.normalize (e : FootprintExpr) : Option LinArithExpr := do
  match e with
  | .var _ | .proj _ _ =>
    let v ← e.toVarProj
    pure { coefs := Std.HashMap.ofList [(v, 1)], const := 0 }
  | .lit n => pure { coefs := Std.HashMap.emptyWithCapacity, const := n }
  | .binop op a b =>
    let { coefs := acoefs, const := aconst } ← normalize a
    let { coefs := bcoefs, const := bconst } ← normalize b
    /- Combine the maps, if the result is non-linear we abort. -/
    match op with
    | .add =>
      let const := aconst + bconst
      let mut coefs := acoefs
      for (fid, n) in bcoefs do
        coefs := coefs.alter fid (fun n' =>
          match n' with
          | none => some n
          | some n' => some (n + n'))
      pure { const, coefs }
    | .mul =>
      let const := aconst * bconst
      let coefs ← do
        match acoefs.toList, bcoefs.toList with
        | [], [] => pure []
        | [(fid, n)], [] => pure [(fid, n * bconst)]
        | [], [(fid, n)] => pure [(fid, n * aconst)]
        | _, _ => none
      pure { const, coefs := Std.HashMap.ofList coefs }
    | _ => none
  | .const _ | .unknown | .struct _ _ | .get _ _ | .set _ _ _ | .range _ _ _ _ => none

inductive Input where
| var (v : Var)
| proj (field : Nat) (e : Input)
deriving BEq

inductive Output where
| input (v : Input)
| arith (a : LinArithExpr)
| array (a : Input) (writeIndices : Array LinArithExpr) -- TODO: add write values
| struct (typename : Name) (fields : Array Output)

def Input.toMessageData (e : Input) : MessageData := Id.run do
  match e with
  | .var v => m!"{v}"
  | .proj field e => m!"{e.toMessageData}.{field}"

instance : ToMessageData Input where
  toMessageData := Input.toMessageData

partial def Output.toMessageData (e : Output) : MessageData := Id.run do
  match e with
  | .input v => m!"{v}"
  | .arith e => e.toMessageData
  | .array a indices => m!"{a}{indices} ← *"
  | .struct _ fields => m!"{arrayToTupleMessageData Output.toMessageData fields}"

instance : ToMessageData Output where
  toMessageData := Output.toMessageData

structure LinRange where
  start : LinArithExpr
  stop : LinArithExpr
  step : LinArithExpr
  kind : RangeKind

instance : ToMessageData LinRange where
  toMessageData r :=
    let { start, stop, step, kind } := r
    m!"[{start}:{stop}:{kind.toString}={step}]"

def LinArithExpr.add (e0 e1 : LinArithExpr) : LinArithExpr := Id.run do
  let { coefs := coefs0, const := const0 } := e0
  let { coefs := coefs1, const := const1 } := e1
  let mut coefs := coefs0
  for (var, coef) in coefs1 do
    coefs := coefs.alter var (fun coef' =>
      match coef' with
      | none => some coef
      | some coef' => coef + coef')
  pure { coefs, const := const0 + const1 }

instance : HAdd LinArithExpr LinArithExpr LinArithExpr where
  hAdd e0 e1 := e0.add e1

def LinArithExpr.sub (e0 e1 : LinArithExpr) : LinArithExpr := Id.run do
  let { coefs := coefs0, const := const0 } := e0
  let { coefs := coefs1, const := const1 } := e1
  let mut coefs := coefs0
  for (var1, coef1) in coefs1 do
    coefs := coefs.alter var1 (fun coef0 =>
      match coef0 with
      | none => pure (-coef1)
      | some coef0 => pure (coef0 - coef1))
  pure { coefs, const := const0 + const1 }

instance : HSub LinArithExpr LinArithExpr LinArithExpr where
  hSub e0 e1 := e0.sub e1

def LinArithExpr.toPos (e0 : LinArithExpr) : LinArithExpr := Id.run do
  let { coefs, const } := e0
  let const := max const 0
  let coefs := coefs.filterMap fun _ c => if c > 0 then some c else none
  { coefs, const }

def LinArithExpr.addConst (e : LinArithExpr) (n : Int) : LinArithExpr :=
  { e with const := e.const + n }

instance : HAdd LinArithExpr Int LinArithExpr where
  hAdd e0 n := e0.addConst n

def LinArithExpr.mulConst (e : LinArithExpr) (n : Int) : LinArithExpr :=
  if n = 0 then { coefs := {}, const := 0 }
  else { coefs := e.coefs.map fun _ n' => n * n', const := e.const * n }

instance : HMul LinArithExpr Int LinArithExpr where
  hMul e0 n := e0.mulConst n

def LinArithExpr.divConst (e : LinArithExpr) (n : Int) : LinArithExpr :=
  if n = 0 then { coefs := {}, const := 0 }
  else
    let updtCoef _ n' :=
      let d := n' / n
      if d = 0 then none
      else some d
    { coefs := e.coefs.filterMap updtCoef, const := e.const / n }

def LinArithExpr.ofConst (const : Int) : LinArithExpr := { coefs := {}, const }
def LinArithExpr.ofCoef (var : VarProj) (coef : Int) : LinArithExpr :=
  { coefs := Std.HashMap.ofList [(var, coef)], const := 0 }
def LinArithExpr.zero := LinArithExpr.ofConst 0

def LinArithExpr.toConst (e : LinArithExpr) : Option Int :=
  if e.coefs.size = 0 then pure e.const else none

def LinArithExpr.toCoef (e : LinArithExpr) : Option (VarProj × Int) :=
  if e.const = 0 then
    match e.coefs.toList with
    | [(var, n)] => pure (var, n)
    | _ => none
  else none

/-- Only handles a subset of cases. -/
def LinArithExpr.div (e0 e1 : LinArithExpr) : Option LinArithExpr := do
  match e1.coefs.toList with
  | [] => -- Division by a constant
    e0.divConst e1.const
  | [(var1, coef1)] =>
    if let [(var0, coef0)] := e0.coefs.toList then
      if ¬ var0 == var1 then failure
      if e0.const ≠ 0 then failure
      if e1.const ≠ 0 then failure
      let d := coef0 / coef1
      if d = 0 then pure .zero
      else pure { coefs := Std.HashMap.ofList [(var0, d)], const := 0 }
    else failure
  | _ => none -- not supported yet

instance : HDiv LinArithExpr LinArithExpr (Option LinArithExpr) where
  hDiv e0 e1 := e0.div e1

def LinArithExpr.isZero (e : LinArithExpr) : Bool :=
  e.const = 0 ∧ e.coefs.toList.all fun (_, coef) => coef = 0

/-- Only succeeds if the result is a linarith expression -/
def LinArithExpr.mul (e0 e1 : LinArithExpr) : Option LinArithExpr := do
  if e0.isZero ∨ e1.isZero then some LinArithExpr.zero
  else
    match e0.coefs.toList, e1.coefs.toList with
    | [], _ => e1.mulConst e0.const
    | _, [] => e0.mulConst e1.const
    | _, _ => none

instance : HMul LinArithExpr LinArithExpr (Option LinArithExpr) where
  hMul e0 e1 := e0.mul e1

-- For now we only support cases where the number of steps is known to be a constant
def LinRange.toNumSteps (r : LinRange) : MetaM LinArithExpr := do
  match r.kind with
  | .add =>
    match (r.stop - r.start) / r.step with
    | none => throwError "Could not compute: ({r.stop} - {r.start}) / {r.step}"
    | some res => pure res.toPos
  | .sub =>
    match (r.start - r.stop) / r.step with
    | none => throwError "Could not compute: ({r.stop} - {r.start}) / {r.step}"
    | some res => pure res.toPos
  | .mul =>
    if let some d := r.stop / r.start then
      if let some d := d.toConst then
        if let some step := r.step.toConst then
          pure (LinArithExpr.ofConst (Nat.log step.toNat d.toNat)).toPos
        else throwError "Could not compute: log ({r.step}) ({r.stop} / {r.start})"
      else throwError "Could not compute: log ({r.step}) ({r.stop} / {r.start})"
    else throwError "Could not compute: log ({r.step}) ({r.stop} / {r.start})"
  | .div =>
    if let some d := r.start / r.stop then
      if let some d := d.toConst then
        if let some step := r.step.toConst then
          pure (LinArithExpr.ofConst (Nat.log step.toNat d.toNat)).toPos
        else throwError "Could not compute: log ({r.step}) ({r.start} / {r.stop})"
      else throwError "Could not compute: log ({r.step}) ({r.start} / {r.stop})"
    else throwError "Could not compute: log ({r.step}) ({r.start} / {r.stop})"

def Input.mk (projs : List Nat) (v : Var) : Input :=
  match projs with
  | [] => .var v
  | p :: projs => .proj p (.mk projs v)

def Input.addProjs (projs : List Nat) (e : Input) : Input :=
  match projs with
  | [] => e
  | p :: projs => .proj p (.addProjs projs e)

def applyProjsToOutput (projs : List Nat) (output : Output) : MetaM Output := do
  match projs with
  | [] => pure output
  | p :: projs' =>
    match output with
    | .input v => pure (.input (Input.addProjs projs v))
    | .struct typename fields =>
      if h: p < fields.size then
        let field := fields[p]
        applyProjsToOutput projs' field
      else throwError "Out of bound projection {p} applied to structure {output}"
    | .arith _ | .array _ _ => throwError "Unexpected projection over output: {output}"

-- TODO: add more things in there, such as the loop outputs
structure NormalizeState where
  -- Mapping from index variable to its range
  varToRange : Std.HashMap Var LinRange := {}

abbrev NormalizeM := StateRefT NormalizeState MetaM

def NormalizeState.empty : NormalizeState := {}

/-- Normalized footprint -/
structure NormFootprint where
  -- Mapping from index variable to its range
  varToRange : Std.HashMap Var LinRange
  -- Mapping from loops to their outputs
  loopOutputs : Std.HashMap LoopId (Option Output)

partial def normalizeLoop
  (fp : Footprint)
  (indices : Std.HashSet Var)
  (loopOutputs : Std.HashMap LoopId (Option Output))
  (loopId : LoopId)
  (range : Range)
  (input : FootprintExpr)
  (outputs : Array FootprintExpr) : NormalizeM Output := do
  withTraceNode `Inv (fun _ => pure m!"normalizeLoop") do
  try
    /- Normalize the outputs.

      We are only interested in the provenance (i.e., which subfield of an input value
      it comes from) and the indices at which they are update. -/
    let outputs ← outputs.mapM (normalizeOutput [])

    /- Merge the outputs together -/
    let output ← do
      match outputs.toList with
      | [] => throwError "No output"
      | output :: outputs =>
        let mut res := output
        for output in outputs do
          res ← mergeOutputs (res, output)
        pure res

    /- TODO: remove
      Check that the relation between the inputs and the outputs is consistent, that is if
      we receive a tuple as input, we do not change the order of the elements of the tuple
      (but might update them). Typically, this is ok:
      ```
        fun i state =>
        let (a, b) := state
        (a, b.set i a[i])
      ```
      but this is not (we swap `a` and `b`):
      ```
        fun i state =>
        let (a, b) := state
        (b, a)
      ```
    -/
    --checkOutput [] output


    /- Apply the transformation to the inputs of the loop.

      For instance, if we have: `loopIter 0 256 (n, a) (fun i (n', a') => (n' + 1, a'.set! i 0))`
      The output is: `(loop@0.input.0 + 1, loop@0.input.0.set! loop@0.index 0)`
      The input is: `(n, a)`
      And the range is: `loop@0.index ∈ [0:256:+=1]`
      We want the result to be: `(n + 256, a[i] ← *) where i ∈ [0:256:+=1]`
    -/
    let output ← applyOutputRelToInput [] (← normalizeRange range) output input

    --
    pure output
  catch e => do
    trace[Inv] "⚠ Aborted with error: {e.toMessageData}"
    throw e

where
  registerIndex (v : Var) : NormalizeM Unit := do
    let s ← get
    if s.varToRange.contains v then pure ()
    else
      match fp.varToLoop.get? v with
      | some (loopId, .index) =>
        -- This variable is used as an index: lookup the loop information and register the range
        let loop := fp.loopIters.get! loopId
        let range ← normalizeRange loop.range
        set { s with varToRange := s.varToRange.insert v range }
      | _ => pure ()

  normalizeRange (range : Range) : NormalizeM LinRange := do
    let { start, stop, step, kind } := range
    let start ← normalizeLinArithExpr start
    let stop ← normalizeLinArithExpr stop
    let step ← normalizeLinArithExpr step
    pure {start, stop, step, kind}

  normalizeLinArithExpr (e : FootprintExpr) : NormalizeM LinArithExpr := do
    match e.normalize with
    | none => throwError "Could not normalize to a LinArithExpr: {e}"
    | some e =>
      -- Register the ranges that we need
      e.coefs.forM fun v _ => registerIndex v.var
      --
      pure e

  /- Normalize an input (i.e., an expression of the shape `x.1.0` where `x` is an input
     variable). -/
  normalizeInput (e : FootprintExpr) : NormalizeM Input := do
    withTraceNode `Inv (fun _ => pure m!"normalizeInput") do
    trace[Inv] "e: {e}"
    match e with
    | .var fv => pure (.var fv)
    | .proj field e => pure (.proj field (← normalizeInput e))
    | .get _ _ | .set _ _ _ | .struct _ _ | .lit _ | .const _  | .binop _ _ _
    | .range _ _ _ _ | .unknown => throwError "Could not normalize input: {e}"

  /- Normalize an array expression -/
  normalizeArrayExpr (e : FootprintExpr) : NormalizeM (Input × Array LinArithExpr) := do
     withTraceNode `Inv (fun _ => pure m!"normalizeArrayExpr") do
    trace[Inv] "e: {e}"
    match e with
    | .var fv => pure (.var fv, #[])
    | .get a _ =>
      -- We ignore the read indices
      normalizeArrayExpr a
    | .set a indices _ =>
      let indices ← indices.mapM normalizeLinArithExpr
      let (input, indices') ← normalizeArrayExpr a
      pure (input, indices' ++ indices)
    | .proj _ _ =>
      pure (← normalizeInput e, #[])
    | .struct _ _ | .lit _ | .const _ | .binop _ _ _ | .range _ _ _ _ | .unknown =>
      throwError "Could not normalize array expression: {e}"

  /- Normalize an output expression -/
  normalizeOutput (projs : List Nat) (e : FootprintExpr) : NormalizeM Output := do
     withTraceNode `Inv (fun _ => pure m!"normalizeOutput") do
    trace[Inv] "e: {e}"
    match e with
    | .var v =>
      -- This may be a loop output, in which case we need to look it up
      if let some (loopId', .output) := fp.varToLoop.get? v then
        if let some (some output) := loopOutputs.get? loopId' then
          applyProjsToOutput projs output
        else throwError "Could not lookup the normalized output of loop {loopId'}"
      else pure (.input (.var v))
    | .get _ _ | .set _ _ _ | .proj _ _ =>
      let (input, writes) ← normalizeArrayExpr e
      pure (.array input writes)
    | .lit _ | .const _ | .binop _ _ _ | .range _ _ _ _ =>
      let e ← normalizeLinArithExpr e
      pure (.arith e)
    | .struct typename fields =>
      let fields ← fields.mapM (normalizeOutput projs)
      pure (.struct typename fields)
    | .unknown => throwError "Could not normalize output: {e}"

  mergeOutputs (out : Output × Output) : NormalizeM Output := do
    withTraceNode `Inv (fun _ => pure m!"mergeOutputs") do
    trace[Inv] "out: {out}"
    match out with
    | (.arith a1, .arith a2) =>
      if a1 == a2 then pure (.arith a1) else throwError "Could not merge: {out}"
    | (.array a1 i1, .array a2 i2) =>
      if a1 == a2 then
        let i2 := i2.filter (fun e => not (Array.elem e i1))
        pure (.array a1 (i1 ++ i2))
      else throwError "Could not merge: {out}"
    | (.struct typename fields1, .struct _ fields2) =>
      if fields1.size = fields2.size then
        let fields ← (fields1.zip fields2).mapM mergeOutputs
        pure (.struct typename fields)
      else throwError "Could not merge: {out}"
    | _ => throwError "Could not merge: {out}"

  -- TODO: remove
  checkOutput (projs : List Nat) (e : Output) : NormalizeM Unit := do
    withTraceNode `Inv (fun _ => pure m!"checkOutput") do
    trace[Inv] "projs: {projs}"
    trace[Inv] "e: {e}"
    match e with
    | .input _ => pure () -- TODO?
    | .arith a => checkOutputArith projs a
    | .array a _ =>
      -- No need to check the write indices: they've already been normalized
      checkInput projs a
    | .struct _ fields =>
      let _ ← fields.mapIdxM fun i => checkOutput (i :: projs)
      pure ()

  checkOutputArith (projs : List Nat) (e : LinArithExpr) : NormalizeM Unit := do
    withTraceNode `Inv (fun _ => pure m!"checkOutputArith") do
    trace[Inv] "projs: {projs}"
    trace[Inv] "e: {e}"
    match e.coefs.toList with
    | [] => pure ()
    | [(var, _)] =>
      if var.projs = projs then pure ()
      else throwError "Invalid output arith expr: expr: {e}, projs: {projs}"
    | _ => throwError "Invalid output arith expr: expr: {e}, projs: {projs}"

  checkInput (projs : List Nat) (e : Input) : NormalizeM Unit := do
    withTraceNode `Inv (fun _ => pure m!"checkInput") do
    trace[Inv] "projs: {projs}"
    trace[Inv] "e: {e}"
    match e with
    | .var v =>
      if projs = [] then
        if indices.contains v then pure ()
        else
          if let some (_, .input) := fp.varToLoop.get? v then pure ()
          else throwError "Invalid input: {e}"
      else throwError "Invalid input and projs: input: {e}, projs: {projs}"
    | .proj field e =>
      match projs with
      | [] => throwError "Invalid input: {e}"
      | p :: projs =>
        if p = field then checkInput projs e
        else throwError "Invalid input and projs: input: {e}, projs: {projs}"

  applyOutputRelToInput
    (projs : List Nat) (range : LinRange) (output : Output) (input : FootprintExpr) : NormalizeM Output := do
    withTraceNode `Inv (fun _ => pure m!"applyOutputRelToInput") do
    trace[Inv] "projs: {projs}"
    trace[Inv] "range: {range}"
    trace[Inv] "output: {output}"
    trace[Inv] "input: {input}"
    match output, input with
    | .struct typeName outFields, .struct _ inFields =>
      if outFields.size ≠ inFields.size
      then throwError "Could not apply output {output} to input {input}"
      else
        let fields := outFields.zip inFields
        pure (.struct typeName (← fields.mapIdxM (fun i f => applyOutputRelToInput (i :: projs) range f.fst f.snd)))
    | .struct typeName outFields, .var _
    | .struct typeName outFields, .proj _ _ =>
      -- The input may have been not fully expanded
      pure (.struct typeName (← outFields.mapIdxM (fun i f => applyOutputRelToInput (i :: projs) range f (.proj i input))))
    | .arith a, _ =>
      -- Normalize the input to a linear arithmetic expression and apply the transformation
      let input ← normalizeLinArithExpr input
      let output ← applyArithToInput projs a range input
      pure (.arith output)
    | .array a indices, _ =>
      let (input, indices') ← normalizeArrayExpr input
      -- Check that the output array corresponds to the input array (same projections)
      checkInput projs a
      -- Add the indices
      pure (.array input (indices ++ indices'))
    | _, _ => throwError "Could not apply output {output} to input {input}"

  applyArithToInput (projs : List Nat) (a : LinArithExpr) (range : LinRange) (input : LinArithExpr) :
    NormalizeM LinArithExpr := do
    withTraceNode `Inv (fun _ => pure m!"applyArithToInput") do
    trace[Inv] "a: {a}"
    trace[Inv] "range: {range}"
    trace[Inv] "input: {input}"
    -- Small helper
    let isCurrentLoopInput (v : Var) : Bool :=
      if let some (loopId', .input) := fp.varToLoop.get? v then loopId' = loopId
      else false

    /- Check that the output sub-field is consistent.

      We support the following case:
      `fun (x, y) => (a * x + e)`
            ^             ^
            the output is a linarith expression of the input
            e is a linarith expr in which all the factors are constant throughout the loop iterations
      We can do: `fun (x, y) => (x + 1, y)`
      but not: `fun (x, y) => (y, x + 1)` (we do not allow swapping fields).

      Also, for now we only allow adding/subtracting a single variable.
     -/
    -- First, either the output is constant, or there is exactly one term which refers the loop input
    let (lpCoefs, coefs) := a.coefs.toList.partition (fun (v, _) => isCurrentLoopInput v.var)
    match lpCoefs with
    | [] =>
      -- Constant output
      trace[Inv] "No current loop coef: the output is constant"
      pure a
    | [(var, coef)] =>
      trace[Inv] "exactly one coef"
      -- Check the variable and the projectors
      if var.projs ≠ projs then throwError "Could not apply linarith output {a} to input {input}: the projections don't match"
      let numSteps ← range.toNumSteps
      if coef ≠ 1 then
        if a.const ≠ 0 ∨ ¬ coefs.isEmpty then throwError "Could not apply linarith output {a} to input {input}: the coef ≠ 1 and the other coefficients/the constant are ≠ 0"
        else
          trace[Inv] "coef ≠ 1"
          if let some numSteps := numSteps.toConst then
            let output := input.mulConst (coef ^ numSteps.toNat)
            trace[Inv] "output: {output}"
            pure output
          else throwError "Could not compute: ({coef}) ^ ({numSteps})"
      else
        trace[Inv] "coef = 1"
        /- The coefficient in front of the input is 1, so we're just adding `numSteps * c` where `c` is the
           formula without the coefficient about the current input -/
        let toAdd : LinArithExpr := { coefs := Std.HashMap.ofList coefs, const := a.const }
        trace[Inv] "toAdd: {toAdd}, numSteps: {numSteps}"
        if let some toAdd := toAdd * numSteps then
          trace[Inv] "toAdd * numSteps: {toAdd}"
          let output := input + toAdd
          trace[Inv] "output: {output}"
          pure output
        else throwError "Could not compute ({toAdd}) * ({numSteps})"
    | _ =>
      trace[Inv] "⚠ Not handled yet"
      throwError "Could not apply linarith output {a} to input {input} because the input/output relation involves more than one input of the current loop"

partial def getLoopOutputDependencies (fp : Footprint) (outputs : Array FootprintExpr) :
  Std.HashSet LoopId :=
  let m := StateM (Std.HashSet LoopId)
  let getVarDeps (v : Var) : m Unit := do
    match fp.varToLoop.get? v with
    | some (lpId, .output) => set ((← get).insert lpId)
    | _ => pure ()
  let rec getInputDeps (x : Input) : m Unit :=
    match x with
    | .var v => getVarDeps v
    | .proj _ e => getInputDeps e
  let rec getDeps (output : FootprintExpr) : m Unit := do
    match output with
    | .var v => getVarDeps v
    | .get a indices => getDeps a; indices.forM getDeps
    | .set a indices value => getDeps a; indices.forM getDeps; getDeps value
    | .proj _ e => getDeps e
    | .struct _ fields => fields.forM getDeps
    | .lit _  | .const _ | .unknown => pure ()
    | .binop _ a b => getDeps a; getDeps b
    | .range start stop step _ => getDeps start; getDeps stop; getDeps step
  let runAll : m Unit := do
    outputs.forM getDeps
  let (_, s) := StateT.run runAll Std.HashSet.emptyWithCapacity
  s

partial def analyzeFootprint (fp : Footprint) (indices : Std.HashSet Var) :
  MetaM NormFootprint := do
  withTraceNode `Inv (fun _ => pure m!"analyzeFootprint") do

  let loopDeps ← fp.outputs.toArray.mapM fun (loopId, outputs) => do
    pure (loopId, getLoopOutputDependencies fp outputs)
  let loopDeps : Std.HashMap LoopId (Std.HashSet LoopId) :=
    Std.HashMap.ofList loopDeps.toList
  let mut loopOutputs := Std.HashMap.emptyWithCapacity
  let mut stack := Std.Queue.empty
  stack := stack.enqueueAll fp.outputs.toList

  let mut visited : Std.HashSet LoopId := Std.HashSet.emptyWithCapacity
  let mut monadState := NormalizeState.empty

  while ¬ stack.isEmpty do
    let some ((loopId, outputs), stack') := stack.dequeue?
      | throwError "Unreachable"
    stack := stack'
    -- Sanity check: we're not stuck in a loop
    if visited.contains loopId then
      continue
    visited := visited.insert loopId
    -- Check if we treated all the dependencies
    let deps := loopDeps.get! loopId
    if ¬ deps.all loopOutputs.contains then
      -- Not treated: enqueue the loop
      trace[Inv] "Enqueuing: {loopId}"
      stack := stack.enqueue (loopId, outputs)
    else
      -- Treated: normalize and add to the map
      let (output, monadState') ← do
        withTraceNode `Inv (fun _ => pure m!"Normalizing: {loopId}") do
        let loop := fp.loopIters.get! loopId
        try
          let (output, monadState') ←
            StateRefT'.run (normalizeLoop fp indices loopOutputs loopId loop.range loop.input outputs) monadState
          pure (some output, monadState')
        catch | e => do
          trace[Inv] "Aborted with error: {e.toMessageData}"
          pure (none, monadState)
      monadState := monadState'
      loopOutputs := loopOutputs.insert loopId output

  --
  pure { loopOutputs, varToRange := monadState.varToRange }

end Aeneas.Inv
