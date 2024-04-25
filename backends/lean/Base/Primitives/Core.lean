import Lean
import Base.Primitives.Base

open Primitives
open Result

namespace core

/- Trait declaration: [core::convert::From] -/
structure convert.From (Self T : Type) where
  from_ : T → Result Self

namespace ops -- core.ops

namespace index -- core.ops.index

/- Trait declaration: [core::ops::index::Index] -/
structure Index (Self Idx : Type) where
  Output : Type
  index : Self → Idx → Result Output

/- Trait declaration: [core::ops::index::IndexMut] -/
structure IndexMut (Self Idx : Type) where
  indexInst : Index Self Idx
  index_mut : Self → Idx → Result (indexInst.Output × (indexInst.Output → Result Self))

end index -- core.ops.index

namespace deref -- core.ops.deref

structure Deref (Self : Type) where
  Target : Type
  deref : Self → Result Target

structure DerefMut (Self : Type) where
  derefInst : Deref Self
  deref_mut : Self → Result (derefInst.Target × (Self → Result Self))

end deref -- core.ops.deref

end ops -- core.ops

/- Trait declaration: [core::clone::Clone] -/
structure clone.Clone (Self : Type) where
  clone : Self → Result Self

/- [core::clone::impls::{(core::clone::Clone for bool)#19}::clone] -/
def clone.impls.CloneBool.clone (b : Bool) : Bool := b

def clone.CloneBool : clone.Clone Bool := {
  clone := fun b => ok (clone.impls.CloneBool.clone b)
}

namespace option -- core.option

/- [core::option::{core::option::Option<T>}::unwrap] -/
def Option.unwrap (T : Type) (x : Option T) : Result T :=
  Result.ofOption x Error.panic

end option -- core.option

end core
