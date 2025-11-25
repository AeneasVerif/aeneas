import Lean
import Aeneas.Std.Alloc

namespace Aeneas

namespace Std

open Result

@[rust_trait "core::ops::index::Index"]
structure core.ops.index.Index (Self Idx Output : Type) where
  index : Self → Idx → Result Output

@[rust_trait "core::ops::index::IndexMut" (parentClauses := ["indexInst"])]
structure core.ops.index.IndexMut (Self Idx Output : Type) where
  indexInst : Index Self Idx Output
  index_mut : Self → Idx → Result (Output × (Output → Self))

@[rust_trait "core::ops::deref::Deref"]
structure core.ops.deref.Deref (Self Target : Type) where
  deref : Self → Result Target

@[rust_trait "core::ops::deref::DerefMut" (parentClauses := ["derefInst"])]
structure core.ops.deref.DerefMut (Self Target : Type) where
  derefInst : Deref Self Target
  deref_mut : Self → Result (Target × (Target → Self))

/-- Trait instance -/
@[rust_trait_impl "core::ops::deref::Deref<Box<@T>, @T>"]
def core.ops.deref.DerefBoxInst (T : Type) :
  core.ops.deref.Deref T T := {
  deref x := ok (alloc.boxed.Box.deref x)
}

/-- Trait instance -/
@[rust_trait_impl "core::ops::deref::DerefMut<Box<@T>, @T>"]
def core.ops.deref.DerefMutBoxInst (T : Type) :
  core.ops.deref.DerefMut T T := {
  derefInst := DerefBoxInst T
  deref_mut x := ok (alloc.boxed.Box.deref_mut x)
}

namespace Std

namespace Aeneas
