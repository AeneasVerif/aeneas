/- `alloc::alloc`: the global allocator.
It is the only allocator: registering another one with `#[global_allocator]` is currently not modelled. -/
module
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Core.Ptr
public import Aeneas.Std.Core.NonNull
public section

open Aeneas SepLogic

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

-- [`Allocator::allocate`](https://doc.rust-lang.org/std/alloc/trait.Allocator.html#tymethod.allocate)
-- This signature is different from Rust's signature in the following ways:
-- TODO: it should take a Layout and return a NonNull <u8>
-- TODO: it should return an AllocError
def alloc.alloc.Global.allocate {T : Type} [Pointee T] (_ : alloc.alloc.Global) (values : List T) :
    Result (NonNull T) := do
  let p ← RawPtr.alloc values .heap
  .ok ⟨p⟩

-- [`Allocator::deallocate`](https://doc.rust-lang.org/std/alloc/trait.Allocator.html#tymethod.deallocate).
-- This signature is different from Rust's signature in the following way:
-- TODO: it should take a NonNull<u8> and a Layout
def alloc.alloc.Global.deallocate {T : Type} [Pointee T] (_ : alloc.alloc.Global) (p : NonNull T)
    (count : Nat) : Result Unit :=
  Result.guardedModify _ (Heap.dealloc p.ptr (count * Pointee.size T))

section

variable {T : Type} [Pointee T]

@[step]
theorem alloc.alloc.Global.allocate.spec [Pointee.Lawful T] (g : alloc.alloc.Global)
    (values : List T) :
    ⦃ emp ⦄ g.allocate values
      ⦃ q => ⌜q.ptr.Aligned⌝ ∗ q.ptr ↦* values ∗ q.ptr.freeable values.length⦄ := by
  unfold alloc.alloc.Global.allocate
  apply WP.ispec_bind (RawPtr.alloc.spec values .heap)
  · iframe
  · intro q
    apply (WP.ispec_ok _).2
    iframe

/-- `q.freeable` is required: without it, `q` could be an interior pointer or point to a local
behind a reference, and freeing it is undefined behaviour. -/
@[step]
theorem alloc.alloc.Global.deallocate.spec [Pointee.Lawful T] (g : alloc.alloc.Global)
    (q : NonNull T) (values : List T) (count : Nat)
    (hCount : values.length = count) :
    ⦃ q.ptr ↦* values ∗ q.ptr.freeable count ⦄ g.deallocate q count ⦃ _ => emp⦄ :=
  Heap.freeBlock.spec q.ptr _ count .heap (by rw [Pointee.length_flatMap_toCells, hCount])

/-- `deallocate` leaves the block of `q` freed. -/
theorem alloc.alloc.Global.deallocate.spec_freed [Pointee.Lawful T] (g : alloc.alloc.Global)
    (q : NonNull T) (values : List T) (count : Nat) (hCount : values.length = count) :
    ⦃ q.ptr ↦* values ∗ q.ptr.freeable count ⦄ g.deallocate q count ⦃ _ => q.ptr.freed⦄ :=
  Heap.freeBlock.spec_freed q.ptr _ count .heap (by rw [Pointee.length_flatMap_toCells, hCount])

/-- Deallocating a raw-pointer view fails: only the global allocator's memory can be freed. -/
theorem alloc.alloc.Global.deallocate.fails_view (g : alloc.alloc.Global) (q : NonNull T)
    (count : Nat) :
    WP.ifails (q.ptr.freeable count .view) (g.deallocate q count) := by
  apply WP.ifails_guardedModify
  rintro h ⟨-, hHeader⟩ h' hSub hDealloc
  nomatch Heap.kind_eq_of_subheap_header (hHeader.trans hSub) hDealloc rfl

end

end Aeneas.Std
