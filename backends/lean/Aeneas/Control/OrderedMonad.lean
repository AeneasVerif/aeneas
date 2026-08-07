import Mathlib.Order.Defs.PartialOrder

namespace Aeneas

/-- A monad whose result types are preordered and whose bind is monotone in
both arguments. -/
class OrderedMonad (m : Type u → Type v) [Monad m] [LawfulMonad m]
    [∀ α : Type u, Preorder (m α)] : Prop where
  bind_mono :
    ∀ {α β} {m₁ m₂ : m α} {next₁ next₂ : α → m β},
      m₁ ≤ m₂ →
      (∀ value, next₁ value ≤ next₂ value) →
      m₁ >>= next₁ ≤ m₂ >>= next₂

/-- A monad morphism whose laws hold up to the target monad's setoid
equivalence. -/
structure MonadMorphism (m : Type u → Type v) (n : Type u → Type w)
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [∀ α : Type u, Setoid (n α)] where
  toFun : {α : Type u} → m α → n α
  map_pure :
    ∀ {α} (value : α),
      toFun (Pure.pure value : m α) ≈ (Pure.pure value : n α)
  map_bind :
    ∀ {α β} (x : m α) (next : α → m β),
      toFun (x >>= next) ≈
        toFun x >>= fun value => toFun (next value)

end Aeneas
