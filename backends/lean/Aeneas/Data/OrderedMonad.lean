import Mathlib.Order.Defs.PartialOrder

/-! Order-compatible monads. -/

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

end Aeneas
