module
public import Aeneas.Std.Core.Core
public import Aeneas.Tactic.Step.Init
public section

namespace Aeneas.Std

open Result

/-- [core::borrow::Borrow] (<https://doc.rust-lang.org/std/borrow/trait.Borrow.html>):
    `fn borrow(&self) -> &Borrowed`. -/
@[rust_trait "core::borrow::Borrow"]
structure core.borrow.Borrow (Self : Type _) (Borrowed : Type _) where
  borrow : Self → Result Borrowed

/-- Model of the blanket `impl<T: ?Sized> Borrow<T> for T`
    (`library/core/src/borrow.rs`: `fn borrow(&self) -> &T { self }`): the identity. -/
@[expose, simp, rust_fun "core::borrow::{core::borrow::Borrow<@T, @T>}::borrow"]
def core.borrow.Borrow.Blanket.borrow {T : Type _} (x : T) : Result T := ok x

/-- **Spec theorem for `<T as core::borrow::Borrow<T>>::borrow`**: returns its argument. -/
@[step]
theorem core.borrow.Borrow.Blanket.borrow.spec {T : Type _} (x : T) :
    core.borrow.Borrow.Blanket.borrow x ⦃ (y : T) => y = x ⦄ := by
  simp [core.borrow.Borrow.Blanket.borrow, WP.spec_ok]

@[expose, reducible, rust_trait_impl "core::borrow::Borrow<@T, @T>"]
def core.borrow.Borrow.Blanket (T : Type _) : core.borrow.Borrow T T := {
  borrow := core.borrow.Borrow.Blanket.borrow
}

end Aeneas.Std
