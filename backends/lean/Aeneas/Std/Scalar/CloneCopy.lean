module
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Scalar.Elab
public section

namespace Aeneas.Std

open Result Error ScalarElab

/-!
# Clone and Copy
-/

-- Remark: the command `uscalar` turns the name `Clone'S` into `CloneU8`, `CloneU16`, etc.
uscalar @[expose, reducible, simp] def core.clone.impls.Clone'S.clone (x : SharedBorrow «%S») : «%S» := x.val
uscalar @[reducible, simp] def core.clone.impls.Clone'S.clone_from (_ : MutBorrow «%S») (x : SharedBorrow «%S») :
  «%S» := x.val
iscalar @[expose, reducible, simp] def core.clone.impls.Clone'S.clone (x : SharedBorrow «%S») : «%S» := x.val
iscalar @[reducible, simp] def core.clone.impls.Clone'S.clone_from (_ : MutBorrow «%S») (x : SharedBorrow «%S») :
  «%S» := x.val

uscalar @[expose, reducible] def core.clone.Clone'S : core.clone.Clone «%S» := {
  clone := liftFun1 core.clone.impls.Clone'S.clone
  clone_from := liftFun2 core.clone.impls.Clone'S.clone_from }

iscalar @[expose, reducible] def core.clone.Clone'S : core.clone.Clone «%S» := {
  clone := liftFun1 core.clone.impls.Clone'S.clone
  clone_from := liftFun2 core.clone.impls.Clone'S.clone_from }

uscalar @[expose, reducible]
def core.marker.Copy'S : core.marker.Copy «%S» := {
  cloneInst := core.clone.Clone'S
}

iscalar @[expose, reducible]
def core.marker.Copy'S : core.marker.Copy «%S» := {
  cloneInst := core.clone.Clone'S
}

end Aeneas.Std
