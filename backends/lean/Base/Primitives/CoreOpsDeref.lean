import Lean
import Base.Primitives.Base

open Primitives
open Result

namespace core.ops.deref

structure Deref (Self : Type) where
  Target : Type
  deref : Self → Result Target

structure DerefMut (Self : Type) where
  derefInst : Deref Self
  deref_mut : Self → Result derefInst.Target
  deref_mut_back : Self → derefInst.Target → Result Self

end core.ops.deref
