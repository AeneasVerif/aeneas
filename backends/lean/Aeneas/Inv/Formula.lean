import Aeneas.Inv.Loop

namespace Aeneas.Inv

open Lean Elab Meta
open Extensions

inductive IneqKind where
| Lt | Le | Gt | Ge | Eq

inductive VarOrConst where
| var (v : Var)
| const (e : Expr) -- TODO: also support constants in the footprint

structure MulGroup where
  elems : Array VarOrConst
  const : Int

structure AddGroup where
  elems : Array MulGroup

inductive Clause where
| unknown
| and (c0 c1 : Clause)
| or (c0 c1 : Clause)
| arith (kind : IneqKind) (lhs rhs : AddGroup)

inductive Formula where
| forall (v : Var)
| exists (v : Var)
| imp (c : Clause) (f : Formula)
| clause (c : Clause)

def analyzeFormula (fp : Footprint) (isPre : Bool) (e : Expr) : MetaM (Array (Expr × Formula)) := do
  sorry

end Aeneas.Inv
