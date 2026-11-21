module
public import Aeneas.NonPos.Domain.ITree
public import Aeneas.NonPos.Tactic
public import Aeneas.Std.Primitives

@[expose] public section
/-!
# Aeneas's `Result` as a supported monad

`Aeneas.Std.Result α` is `ITree RustEffect α`, ordered by the `CCPO` that `partial_fixpoint` uses.
This file registers it as a `NonPosMonad`, so that its values can be fields of `nonpos_structure`s
(the methods of a trait compiled by Aeneas), and tags the continuity of `ok` and `bind`
`@[nonpos_continuous]`, so that `nonpos_cont` can see through them.

The instance reuses Aeneas's own `Monad Result` instance: the `>>=` in generated code is then the
one `Cont.bind` is stated for.
-/
namespace NonPos.Std
open Aeneas.Std Aeneas.Data.Coinductive NonPos.Domain Lean.Order

universe u w

unseal Result in
/-- `Result` is a supported monad: its order is the `CCPO` of `Coinductive`, for which `bind` is
continuous (`ITree.continuous_bind`). -/
noncomputable instance : NonPosMonad Result.{u} where
  toMonad := inferInstance
  bind_cont := fun {α β} => by
    letI : Dom (Result α) := Dom.ofCCPO (Result α)
    letI : Dom (Result β) := Dom.ofCCPO (Result β)
    exact Cont.toPProd (g := fun x k => x >>= k) ITree.continuous_bind

/-! The `Result`-specific forms: Aeneas's names for `pure` and `bind`.  `Result.fail` and
`Result.div` need no form: they never depend on the dictionary, so `nonpos_cont` treats them as
constants. -/
section
variable {D : Type w} [Dom D]

@[nonpos_continuous]
theorem Cont.result_ok {A : Type u} {a : D → A} (ha : Cont (inst_1 := Dom.discrete A) a) :
    Cont (fun d => Result.ok (a d)) :=
  Cont.pure (M := Result) ha

@[nonpos_continuous]
theorem Cont.result_bind {A B : Type u} {m : D → Result A} {k : D → A → Result B}
    (hm : Cont m) (hk : ∀ a, Cont (fun d => k d a)) : Cont (fun d => Aeneas.Std.bind (m d) (k d)) :=
  Cont.bind (M := Result) hm hk

end

/-! The same forms on `FixFunctor.Cont` (as in section 1 of `Tactic.lean`). -/
section
universe pu v w₁
variable {I : Type pu} {H : I → (I → Type v) → Type v} [∀ k, FixFunctor (H k)]
  {G₁ : (I → Type v) → Type w₁} [FixFunctor G₁]

theorem FixFunctor.Cont.result_ok {A : Type u} {a : G₁ (Fix H) → A}
    (ha : FixFunctor.Cont H (G₂ := fun _ => A) (iG₂ := FixFunctor.data A) a) :
    FixFunctor.Cont H (G₂ := fun _ => Result A) (fun d => Result.ok (a d)) :=
  FixFunctor.Cont.pure (M := Result) ha
theorem FixFunctor.Cont.result_bind {A B : Type u} {m : G₁ (Fix H) → Result A} {k : G₁ (Fix H) → A → Result B}
    (hm : FixFunctor.Cont H (G₂ := fun _ => Result A) m) (hk : ∀ a, FixFunctor.Cont H (G₂ := fun _ => Result B) (fun d => k d a)) :
    FixFunctor.Cont H (G₂ := fun _ => Result B) (fun d => Aeneas.Std.bind (m d) (k d)) :=
  FixFunctor.Cont.bind (M := Result) hm hk
end

end NonPos.Std
