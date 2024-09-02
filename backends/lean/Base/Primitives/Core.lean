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
@[reducible, simp]
def clone.impls.CloneBool.clone (b : Bool) : Bool := b

@[reducible]
def clone.CloneBool : clone.Clone Bool := {
  clone := fun b => ok (clone.impls.CloneBool.clone b)
}

/- [core::mem::replace]

   This acts like a swap effectively in a functional pure world.
   We return the old value of `dst`, i.e. `dst` itself.
   The new value of `dst` is `src`. -/
@[simp] def mem.replace (a : Type) (dst : a) (src : a) : a × a := (dst, src)

/- [core::mem::swap] -/
@[simp] def mem.swap (T: Type) (a b: T): T × T := (b, a)

end core

/- [core::option::{core::option::Option<T>}::unwrap] -/
@[simp] def core.option.Option.unwrap (T : Type) (x : Option T) : Result T :=
  Result.ofOption x Error.panic

/- [core::option::Option::take] -/
@[simp] def core.option.Option.take (T: Type) (self: Option T): Option T × Option T := (self, .none)

/- [core::option::Option::is_none] -/
@[simp] def core.option.Option.is_none (T: Type) (self: Option T): Bool := self.isNone

/- [core::clone::Clone::clone_from]:
   Source: '/rustc/library/core/src/clone.rs', lines 175:4-175:43
   Name pattern: core::clone::Clone::clone_from -/
@[simp] def core.clone.Clone.clone_from
  {Self : Type} (cloneInst : core.clone.Clone Self) (_self : Self) (source : Self) : Result Self :=
  cloneInst.clone source
