/- `alloc::sync::Arc` -/
module
public import Aeneas.Std.Alloc.Alloc
public import Aeneas.Std.Core.Borrow
public import Aeneas.Std.Core.Convert
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Core.Ops
public import Aeneas.Tactic.Step.Init
public section

namespace Aeneas.Std

/-- Model of `Arc<T>` (<https://doc.rust-lang.org/std/sync/struct.Arc.html>): a value.

Aeneas translates shared references as values, and an `Arc<T>` only gives shared access to its
content, so the model keeps the content and forgets the allocation: the reference counts and the
identity of the allocation are *not* modelled, and neither are the operations which observe them
(`strong_count`, `ptr_eq`, `try_unwrap`, `get_mut`, `make_mut`, `downgrade`...). This is sound only
for types without interior mutability, which Aeneas rejects (see issue #1525). -/
@[rust_type "alloc::sync::Arc"]
structure alloc.sync.Arc (T : Type _) where
  val : T

/-- Model of `Arc::new` (<https://doc.rust-lang.org/std/sync/struct.Arc.html#method.new>). -/
@[expose, simp, step_simps, rust_fun "alloc::sync::{alloc::sync::Arc<@T>}::new" -canFail -lift]
def alloc.sync.Arc.new {T : Type _} (x : T) : alloc.sync.Arc T := ⟨x⟩

/-- Model of `Arc::clone` (<https://doc.rust-lang.org/std/sync/struct.Arc.html#impl-Clone-for-Arc%3CT,+A%3E>):
the clone shares the content of the original, which is immutable. -/
@[expose, simp, step_simps, rust_fun "alloc::sync::{core::clone::Clone<alloc::sync::Arc<@T>>}::clone"
    -canFail -lift (keepParams := [true, false]) (keepTraitClauses := [false])]
def alloc.sync.CloneArc.clone {T : Type _} (a : alloc.sync.Arc T) : alloc.sync.Arc T := a

@[expose, reducible, rust_trait_impl "core::clone::Clone<alloc::sync::Arc<@T>>"
    (keepParams := [true, false]) (keepTraitClauses := [false])]
def core.clone.CloneArc {T : Type _} : core.clone.Clone (alloc.sync.Arc T) := {
  clone := fun a => .ok (alloc.sync.CloneArc.clone a)
}

/-- Model of `Arc::deref` (<https://doc.rust-lang.org/std/sync/struct.Arc.html#impl-Deref-for-Arc%3CT,+A%3E>). -/
@[expose, simp, step_simps, rust_fun "alloc::sync::{core::ops::deref::Deref<alloc::sync::Arc<@T>, @T>}::deref"
    -canFail -lift (keepParams := [true, false])]
def alloc.sync.Arc.deref {T : Type _} (a : alloc.sync.Arc T) : T := a.val

@[expose, reducible, rust_trait_impl "core::ops::deref::Deref<alloc::sync::Arc<@T>, @T>"
    (keepParams := [true, false])]
def core.ops.deref.DerefArc {T : Type _} : core.ops.deref.Deref (alloc.sync.Arc T) T := {
  deref := fun a => .ok (alloc.sync.Arc.deref a)
}

/-- Model of `Arc::from` (<https://doc.rust-lang.org/std/sync/struct.Arc.html#impl-From%3CT%3E-for-Arc%3CT%3E>). -/
@[expose, simp, step_simps, rust_fun "alloc::sync::{core::convert::From<alloc::sync::Arc<@T>, @T>}::from"
    -canFail -lift]
def alloc.sync.FromArc.from {T : Type _} (x : T) : alloc.sync.Arc T := ⟨x⟩

@[expose, reducible, rust_trait_impl "core::convert::From<alloc::sync::Arc<@T>, @T>"]
def core.convert.FromArc {T : Type _} : core.convert.From (alloc.sync.Arc T) T := {
  «from» := fun x => .ok (alloc.sync.FromArc.from x)
}

/-- Model of `Arc::as_ref` (<https://doc.rust-lang.org/std/sync/struct.Arc.html#impl-AsRef%3CT%3E-for-Arc%3CT,+A%3E>). -/
@[expose, simp, step_simps, rust_fun "alloc::sync::{core::convert::AsRef<alloc::sync::Arc<@T>, @T>}::as_ref"
    -canFail -lift (keepParams := [true, false])]
def alloc.sync.AsRefArc.as_ref {T : Type _} (a : alloc.sync.Arc T) : T := a.val

@[expose, reducible, rust_trait_impl "core::convert::AsRef<alloc::sync::Arc<@T>, @T>"
    (keepParams := [true, false])]
def core.convert.AsRefArc {T : Type _} : core.convert.AsRef (alloc.sync.Arc T) T := {
  as_ref := fun a => .ok (alloc.sync.AsRefArc.as_ref a)
}

/-- Model of `Arc::borrow` (<https://doc.rust-lang.org/std/sync/struct.Arc.html#impl-Borrow%3CT%3E-for-Arc%3CT,+A%3E>). -/
@[expose, simp, step_simps, rust_fun "alloc::sync::{core::borrow::Borrow<alloc::sync::Arc<@T>, @T>}::borrow"
    -canFail -lift (keepParams := [true, false])]
def alloc.sync.BorrowArc.borrow {T : Type _} (a : alloc.sync.Arc T) : T := a.val

@[expose, reducible, rust_trait_impl "core::borrow::Borrow<alloc::sync::Arc<@T>, @T>"
    (keepParams := [true, false])]
def core.borrow.BorrowArc {T : Type _} : core.borrow.Borrow (alloc.sync.Arc T) T := {
  borrow := fun a => .ok (alloc.sync.BorrowArc.borrow a)
}

end Aeneas.Std
