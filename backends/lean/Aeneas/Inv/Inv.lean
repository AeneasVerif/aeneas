import Aeneas.Std.Primitives

namespace Aeneas.Inv

open Lean Meta

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
  | get (p : FootprintExpr) (fn : Name) (index : ArithExpr)
  | set (p : FootprintExpr) (fn : Name) (index : ArithExpr)
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
    if let some e ← footprint.arrayExpr e then
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

partial def footprint.arrayExpr (e : Expr) : FootprintM (Option FootprintExpr) := do
  /- Attempt to deconstruct a getter/setter -/

  /- Minimize the array expression -/

  match ← trySynthInstance (← mkAppM ``ArrayExpr #[gty]) with
  | .some _ => pure true
  | _ => pure false
  sorry

end

end Aeneas.Inv
