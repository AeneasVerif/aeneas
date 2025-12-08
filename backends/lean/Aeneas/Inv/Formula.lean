import Aeneas.Inv.Loop

namespace Aeneas.Inv.Formula

open Lean Elab Meta
open Extensions

-- TODO: decompose formulae, then analyze them

inductive IneqKind where
| lt | le | gt | ge | eq
deriving BEq, Hashable, Ord

inductive VarOrConst where
| var (v : Var)
| const (e : Expr) -- TODO: also support constants in the footprint
deriving BEq, Hashable

structure MulGroup where
  elems : Array VarOrConst
  const : Int
deriving BEq, Hashable

structure AddGroup where
  elems : Array MulGroup
deriving BEq, Hashable

abbrev ArithExpr := AddGroup

inductive Clause where
| unknown
| and (c0 c1 : Clause)
| or (c0 c1 : Clause)
| arith (kind : IneqKind) (lhs rhs : AddGroup)
deriving BEq, Hashable

inductive Fml where
| forall (v : Var)
| exists (v : Var)
| imp (c : Clause) (f : Fml)
| clause (c : Clause)
deriving BEq, Hashable

structure State where
  /-- Var id counter -/
  varId : VarId := 0
  fvars : Std.HashMap FVarId Var := {}
  arrayGetters : Std.HashSet (VarProj × Array ArithExpr) := {}

abbrev M := StateRefT State MetaM

def pushFVar (fvar : FVarId) : M VarId := do
  let s ← get
  let varId := s.varId
  let name ← do
    if let some decl ← fvar.findDecl? then pure (some (decl.userName.toString))
    else pure none
  let var : Var := { id := varId, name }
  set ({s with varId := varId + 1, fvars := s.fvars.insert fvar var })
  pure varId

def pushFVars (fvars : Array FVarId) : M (Array VarId) := do
  fvars.mapM pushFVar

def pushArrayGetter (a : VarProj) (indices : Array ArithExpr) : M Unit := do
  let s ← get
  set { s with arrayGetters := s.arrayGetters.insert (a, indices) }

def propBinops : Std.HashMap Name IneqKind := Std.HashMap.ofList [
  (``LT.lt, .lt),
  (``LT.lt, .lt),
  (``HSub.hSub, .sub),
  (``HMul.hMul, .mul),
  (``HMod.hMod, .mod),
  (``HDiv.hDiv, .div),
  (``HPow.hPow, .pow),
]

mutual

partial def formula.formula (e : Expr) : M (Array (Expr × Fml)) := do
  match e with
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _
  | .lam _ _ _ _ | .letE _ _ _ _ _ | .proj _ _ _ =>
    /- Explore the expression to accumulate information about the array
       accesses, but return an unknown clause -/
    formula.unknown e
    pure #[(e, .clause .unknown)]
  | .app _ _ =>
    trace[Inv] ".app"
    formula.clause e
  | .mdata _ e => formula.formula e
  | .forallE _ _ _ _ =>
    trace[Inv] ".forallE"
    forallTelescope e fun fvars body => do
    /- Explore the introduced fvars. Depending on their type we want to introduce:
       - new variables
       - new clauses -/
    formula.forall fvars body

partial def formula.clause (e : Expr) : M (Array (Expr × Fml)) := do
  /- TODO: check if this is a clause:
      - and, or
      - eq, ineq
      - or unknown clause
  -/
  let f := e.getAppFn
  let args := e.getAppArgs

  if f.isConstOf ``And ∧ args.size = 2 then sorry
  if f.isConstOf ``Or ∧ args.size = 2 then sorry
  if f.isConstOf ``Eq ∧ args.size = 3 then sorry

  -- TODO: ineqs
  if f.isConstOf ``LT.lt ∧ args.size = 4 then sorry

  sorry

partial def formula.forall (fvars : Array Expr) (body : Expr) : M (Array (Expr × Fml)) := do
  sorry

/-- Simply explore the expression to accumulate information about the found
    arrays, etc. -/
partial def formula.unknown (e : Expr) : M Unit := do
  match e with
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _
  | .lam _ _ _ _ =>
    Meta.lambdaTelescope e fun fvars body => do
    formula.unknown body
  | .letE _ _ _ _ _ =>
    Meta.lambdaLetTelescope e fun fvars body => do
    for fvar in fvars do
      if let some decl ← fvar.fvarId!.findDecl? then
        if let some value := decl.value? then -- Should always be some?
          formula.unknown value
  | .app _ _ =>
    -- Check if this is a getter (note that we don't care about setters)
    if let some (array, indices) ← asGetter? e then
      try
        let array ← formula.array array
        let indices ← indices.mapM formula.arith
        pushArrayGetter array indices
      catch _ => pure ()
    -- Otherwise: simply explore the arguments
    let f := e.getAppFn
    formula.unknown f
    let args := e.getAppArgs
    args.forM formula.unknown
  | .mdata _ e => formula.unknown e
  | .proj _ _ struct =>
    formula.unknown struct
  | .forallE _ _ _ _ =>
    forallTelescope e fun fvars body => do
    -- Explore the type of the fvars
    fvars.forM fun fvar => do
      let ty ← inferType fvar
      formula.unknown ty
    -- Explore the body
    formula.unknown body

partial def formula.array (e : Expr) : M VarProj := do sorry

partial def formula.arith (e : Expr) : M ArithExpr := do sorry

end

end Aeneas.Inv.Formula
