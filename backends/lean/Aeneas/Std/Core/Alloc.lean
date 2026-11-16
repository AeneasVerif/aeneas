/- `core::alloc` -/
module
public import Aeneas.Std.Core.Ptr
public section

namespace Aeneas.Std

@[rust_type "core::alloc::layout::Layout"]
structure core.alloc.layout.Layout where
  size : Usize
  align : core.ptr.alignment.Alignment

/-- `core::alloc::AllocatorClone`: allocators which can be cloned (`Allocator + Clone`). It bounds the
allocator parameter of `Arc::clone` and `Rc::clone`. -/
@[rust_trait "core::alloc::AllocatorClone" (parentClauses := ["cloneCloneInst"])]
structure core.alloc.AllocatorClone (Self : Type _) where
  cloneCloneInst : core.clone.Clone Self

@[rust_trait "core::alloc::global::GlobalAlloc"]
structure core.alloc.global.GlobalAlloc (Self : Type _) where
  alloc : Self → core.alloc.layout.Layout → Result (MutRawPtr U8)
  dealloc : Self → MutRawPtr U8 → core.alloc.layout.Layout → Result Unit

end Aeneas.Std
