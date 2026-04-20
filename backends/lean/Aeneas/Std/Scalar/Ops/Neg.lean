import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Misc
import Aeneas.Std.Scalar.Elab
import Aeneas.Tactic.Solver.ScalarTac
import Mathlib.Data.BitVec

namespace Aeneas.Std

open Result Error Arith

/-!
# Negation: Definitions
-/
@[step_pure_def]
def IScalar.neg {ty : IScalarTy} (x : IScalar ty) : Result (IScalar ty) := IScalar.tryMk ty (- x.toInt)

class ResultNeg (α : Type u) where
  neg : α → Result α

prefix:75  "-?" => ResultNeg.neg

instance {ty} : ResultNeg (IScalar ty) where neg x := IScalar.neg x

end Aeneas.Std
