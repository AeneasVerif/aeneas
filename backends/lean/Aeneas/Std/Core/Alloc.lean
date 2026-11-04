/- `core::alloc` -/
module
public import Aeneas.Std.Core.Ptr
public section

namespace Aeneas.Std

@[rust_type "core::alloc::layout::Layout"]
structure core.alloc.layout.Layout where
  size : Usize
  align : core.ptr.alignment.Alignment

@[rust_trait "core::alloc::global::GlobalAlloc"]
structure core.alloc.global.GlobalAlloc (Self : Type _) where
  alloc : SharedBorrow Self → core.alloc.layout.Layout → Result (MutRawPtr U8)
  dealloc : SharedBorrow Self → MutRawPtr U8 → core.alloc.layout.Layout → Result Unit

end Aeneas.Std
