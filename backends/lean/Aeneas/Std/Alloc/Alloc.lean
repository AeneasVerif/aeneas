module
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Core.Ptr
@[expose] public section

/-! `alloc::alloc`: the global allocator. It is the only allocator: registering another one with
`#[global_allocator]` is not modelled. Rust's allocator API is untyped (`Layout`, `*mut u8`,
uninitialised memory) while the heap is typed, so `Global.allocate` and `Global.deallocate` are the
typed counterparts of
[`Allocator::allocate`](https://doc.rust-lang.org/std/alloc/trait.Allocator.html#tymethod.allocate)
and
[`Allocator::deallocate`](https://doc.rust-lang.org/std/alloc/trait.Allocator.html#tymethod.deallocate)
for `Global` with `Layout::array::<T>(n)`, and have no `rust_fun`. -/

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

/-- `Allocator::allocate` with `Layout::array::<T>(values.length)`, followed by writing `values`:
the heap has no uninitialised memory. -/
def Global.allocate (_ : Global) (values : List T) : Result (MutRawPtr T) :=
  RawPtr.materialize values (freeable := true)

/-- `Allocator::deallocate` with `Layout::array::<T>(count)`. `p` must be "currently allocated" by
`allocate` with the same layout: the start of a live allocation of `count` slots. Anything else is
undefined behaviour, e.g. a local behind `from_mut`, an interior pointer, the wrong size, or memory
already deallocated. See the safety section of
[`Allocator::deallocate`](https://doc.rust-lang.org/std/alloc/trait.Allocator.html#tymethod.deallocate).
-/
def Global.deallocate (_ : Global) (p : MutRawPtr T) (count : Nat) : Result Unit :=
  Result.guardedModify (fun h => Heap.CanDealloc h p.loc count true) fun h hPre =>
    ((), h.dealloc p.loc count true hPre)

end Aeneas.Std
