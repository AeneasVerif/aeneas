import Lean
import Base.Primitives.Base

open Primitives
open Result

namespace core.ops

namespace index -- core.ops.index

/- Trait declaration: [core::ops::index::Index] -/
structure Index (Self Idx : Type) where
  Output : Type
  index : Self → Idx → Result Output

/- Trait declaration: [core::ops::index::IndexMut] -/
structure IndexMut (Self Idx : Type) where
  indexInst : Index Self Idx
  index_mut : Self → Idx → Result indexInst.Output
  index_mut_back : Self → Idx → indexInst.Output → Result Self

end index -- core.ops.index

namespace deref -- core.ops.deref

structure Deref (Self : Type) where
  Target : Type
  deref : Self → Result Target

structure DerefMut (Self : Type) where
  derefInst : Deref Self
  deref_mut : Self → Result derefInst.Target
  deref_mut_back : Self → derefInst.Target → Result Self

end deref -- core.ops.deref

end core.ops
