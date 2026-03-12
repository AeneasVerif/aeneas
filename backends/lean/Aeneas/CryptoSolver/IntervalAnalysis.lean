import Lean
import Aeneas.CryptoSolver.Expr
import Aeneas.CryptoSolver.Interval

/-!
# Forward interval propagation

Given an `AExpr` and an environment mapping variables to intervals,
propagate intervals bottom-up through the expression tree.
-/

namespace Aeneas.CryptoSolver

open Lean

/-- Environment mapping free variables to their known intervals -/
structure IntervalEnv where
  map : List (FVarId × Interval) := []
  deriving Inhabited

namespace IntervalEnv

def empty : IntervalEnv := ⟨[]⟩

def find? (env : IntervalEnv) (fv : FVarId) : Option Interval :=
  env.map.lookup fv

def getD (env : IntervalEnv) (fv : FVarId) (default : Interval) : Interval :=
  (env.find? fv).getD default

def insert (env : IntervalEnv) (fv : FVarId) (ivl : Interval) : IntervalEnv :=
  -- Replace existing or add new
  let map' := env.map.filter (fun (k, _) => k != fv)
  ⟨(fv, ivl) :: map'⟩

end IntervalEnv

/-- Propagate intervals through an expression tree (bottom-up). -/
def propagate (env : IntervalEnv) : AExpr → Interval
  | .lit n      => Interval.singleton n
  | .var fv     => env.getD fv Interval.top
  | .add a b    => (propagate env a).add (propagate env b)
  | .sub a b    => (propagate env a).sub (propagate env b)
  | .mul a b    => (propagate env a).mul (propagate env b)
  | .div a b    => (propagate env a).div (propagate env b)
  | .mod a b    => (propagate env a).mod (propagate env b)
  | .neg a      => (propagate env a).neg
  | .pow a n    => (propagate env a).pow n
  | .shl a n    => (propagate env a).shl n
  | .shr a n    => (propagate env a).shr n
  | .band a b   => (propagate env a).band (propagate env b)
  | .bor a b    => (propagate env a).bor (propagate env b)
  | .bxor a b   => (propagate env a).bxor (propagate env b)
  | .unknown _  => Interval.top

/-- Can we prove `expr < bound` using interval analysis? -/
def canProveLt (env : IntervalEnv) (expr : AExpr) (bound : Int) : Bool :=
  (propagate env expr).hi < bound

/-- Can we prove `expr ≤ bound` using interval analysis? -/
def canProveLe (env : IntervalEnv) (expr : AExpr) (bound : Int) : Bool :=
  (propagate env expr).hi ≤ bound

/-- Can we prove `bound ≤ expr` using interval analysis? -/
def canProveGe (env : IntervalEnv) (expr : AExpr) (bound : Int) : Bool :=
  bound ≤ (propagate env expr).lo

/-- Can we prove `bound < expr` using interval analysis? -/
def canProveGt (env : IntervalEnv) (expr : AExpr) (bound : Int) : Bool :=
  bound < (propagate env expr).lo

end Aeneas.CryptoSolver
