import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error ScalarElab

/-!
# Clone and Copy
-/

-- Remark: the command `uscalar` turns the name `Clone'S` into `CloneU8`, `CloneU16`, etc.
uscalar @[reducible, simp] def core.clone.impls.Clone'S.clone (x : «%S») : «%S» := x
uscalar @[reducible, simp] def core.clone.impls.Clone'S.clone_from (_ x : «%S») : «%S» := x
iscalar @[reducible, simp] def core.clone.impls.Clone'S.clone (x : «%S») : «%S» := x
iscalar @[reducible, simp] def core.clone.impls.Clone'S.clone_from (_ x : «%S») : «%S» := x

uscalar @[reducible] def core.clone.Clone'S : core.clone.Clone «%S» := {
  clone := liftFun1 core.clone.impls.Clone'S.clone
  clone_from := liftFun2 core.clone.impls.Clone'S.clone_from }

iscalar @[reducible] def core.clone.Clone'S : core.clone.Clone «%S» := {
  clone := liftFun1 core.clone.impls.Clone'S.clone
  clone_from := liftFun2 core.clone.impls.Clone'S.clone_from }

uscalar @[reducible]
def core.marker.Copy'S : core.marker.Copy «%S» := {
  cloneInst := core.clone.Clone'S
}

iscalar @[reducible]
def core.marker.Copy'S : core.marker.Copy «%S» := {
  cloneInst := core.clone.Clone'S
}

end Aeneas.Std
