/- `alloc::alloc`: the global allocator.
It is the only allocator: registering another one with `#[global_allocator]` is not modelled. -/
module
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Core.Ptr
public section

open Aeneas SepLogic

namespace Aeneas.Std

/-- The type of the global allocator - note it shouldn't appear in the generated code because
    we systematically filter it when providing information about the definitions supported by the standard
    libary. -/
@[rust_type "alloc::alloc::Global"]
inductive Global where | mk

@[expose, rust_fun "alloc::alloc::{core::clone::Clone<alloc::alloc::Global>}::clone"]
def alloc.alloc.CloneGlobal.clone (_ : Global) : Result Global := .ok .mk

@[expose, reducible, rust_trait_impl "core::clone::Clone<alloc::alloc::Global>"]
def core.clone.CloneGlobal : core.clone.Clone Global := {
  clone := alloc.alloc.CloneGlobal.clone
}

-- [`Allocator::allocate`](https://doc.rust-lang.org/std/alloc/trait.Allocator.html#tymethod.allocate)
-- This signature is different from Rust's signature in the following ways:
-- TODO: it should return a NonNull<T>
-- TODO: it should take a Layout and return a NonNull <u8>
-- TODO: it should return an AllocError
def Global.allocate (_ : Global) (values : List T) : Result (MutRawPtr T) :=
  Result.guardedModify (fun _ => True) fun h _ => h.alloc values .global

-- [`Allocator::deallocate`](https://doc.rust-lang.org/std/alloc/trait.Allocator.html#tymethod.deallocate).
-- This signature is different from Rust's signature in two ways:
-- TODO: it should take a NonNull<T>
-- TODO: then a NonNull<u8> and a Layout
def Global.deallocate (_ : Global) (p : MutRawPtr T) (count : Nat) : Result Unit :=
  Result.guardedModify _ (Heap.dealloc p count .global)

@[step]
theorem Global.allocate.spec (g : Global) (values : List T) :
    ⦃ emp ⦄ g.allocate values ⦃ q => q ↦* values ∗ q.freeable values.length⦄ :=
  Heap.alloc.spec values .global

/-- `q.freeable` is required: without it, `q` could be an interior pointer or point to a local
behind a reference, and freeing it is undefined behaviour. -/
@[step]
theorem Global.deallocate.spec (g : Global) (q : MutRawPtr T) (values : List T) (count : Nat)
    (hCount : values.length = count) :
    ⦃ q ↦* values ∗ q.freeable count ⦄ g.deallocate q count ⦃ _ => emp⦄ := by
  subst hCount
  exact Heap.dealloc.spec q values .global

end Aeneas.Std
