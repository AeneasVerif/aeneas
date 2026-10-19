/- `alloc::alloc`: the global allocator.
It is the only allocator: registering another one with `#[global_allocator]` is currently not modelled. -/
module
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Core.Ptr
public section

namespace Aeneas.Std

/-- The type of the global allocator - note it shouldn't appear in the generated code because
    we systematically filter it when providing information about the definitions supported by the standard
    libary. -/
@[rust_type "alloc::alloc::Global"]
inductive alloc.alloc.Global where | mk

@[expose, rust_fun "alloc::alloc::{core::clone::Clone<alloc::alloc::Global>}::clone"]
def alloc.alloc.CloneGlobal.clone (_ : alloc.alloc.Global) : Result alloc.alloc.Global := .ok .mk

@[expose, reducible, rust_trait_impl "core::clone::Clone<alloc::alloc::Global>"]
def core.clone.CloneGlobal : core.clone.Clone alloc.alloc.Global := {
  clone := alloc.alloc.CloneGlobal.clone
}

variable {H : Type (uh + 1)}

-- [`Allocator::allocate`](https://doc.rust-lang.org/std/alloc/trait.Allocator.html#tymethod.allocate)
-- This signature is different from Rust's signature in the following ways:
-- TODO: it should return a NonNull<T>
-- TODO: it should take a Layout and return a NonNull <u8>
-- TODO: it should return an AllocError
def alloc.alloc.Global.allocate [Stores H T] (_ : alloc.alloc.Global) (values : List T) :
    ResultAt H (MutRawPtr T) :=
  Stores.modifySmall T (fun _ => True) fun h _ => h.alloc values

-- [`Allocator::deallocate`](https://doc.rust-lang.org/std/alloc/trait.Allocator.html#tymethod.deallocate).
-- This signature is different from Rust's signature in two ways:
-- TODO: it should take a NonNull<T>
-- TODO: then a NonNull<u8> and a Layout
def alloc.alloc.Global.deallocate [Stores H T] (_ : alloc.alloc.Global) (p : MutRawPtr T)
    (count : Nat) : ResultAt H Unit :=
  Stores.modifySmall T _ (Heap.dealloc p count)

end Aeneas.Std
