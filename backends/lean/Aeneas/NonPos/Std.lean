module
public import Aeneas.NonPos.Domain.ITree
public import Aeneas.NonPos.Tactic
public import Aeneas.Std.Primitives

@[expose] public section
/-!
# Aeneas's `Result` as a supported monad

`Aeneas.Std.Result α` is `ITree RustEffect α`, ordered by the `CCPO` that `partial_fixpoint` uses.
Its values can be fields of `nonpos_structure`s (the methods of a trait compiled by Aeneas) through
its `CCPO`.  This file proves that its `bind` satisfies the condition (`ITree.continuous_bind`), and
tags the forms of `ok` and `bind` (as `>>=`, from `do` notation, and as `Aeneas.Std.bind`)
`@[nonpos_continuous]`, so that `nonpos_cont` can see through them.
-/
namespace NonPos.Std
open Aeneas.Std Aeneas.Data.Coinductive NonPos.Domain Lean.Order

universe u w

unseal Result in
/-- `bind` satisfies the condition: the order of `Result` is the `CCPO` of `Coinductive`, for which
`bind` is continuous (`ITree.continuous_bind`). -/
theorem Cont.result_bindCont {α β : Type u} : Cont (fun p : Result α ×' (α → Result β) => p.1 >>= p.2) :=
  Proofs.Cont.bind_of_model (by
    let : Dom (Result α) := Dom.ofCCPO (Result α)
    let : Dom (Result β) := Dom.ofCCPO (Result β)
    exact DCont.toPProd (g := fun x k => x >>= k) ITree.continuous_bind)

/-! The `Result`-specific forms: Aeneas's names for `pure` and `bind`.  `Result.fail` and
`Result.div` need no form: they never depend on the dictionary, so `nonpos_cont` treats them as
constants. -/
section
variable {D : Type w} [Lean.Order.PartialOrder D]

@[nonpos_continuous]
theorem Cont.result_ok {A : Type u} {a : D → A} (ha : Cont (iB := discreteOrder A) a) :
    Cont (fun d => Result.ok (a d)) :=
  Cont.pure (M := Result) ha

@[nonpos_continuous]
theorem Cont.result_bind {A B : Type u} {m : D → Result A} {k : D → A → Result B}
    (hm : Cont m) (hk : ∀ a, Cont (fun d => k d a)) : Cont (fun d => Aeneas.Std.bind (m d) (k d)) :=
  Cont.bind Cont.result_bindCont hm hk

@[nonpos_continuous]
theorem Cont.result_bind' {A B : Type u} {m : D → Result A} {k : D → A → Result B}
    (hm : Cont m) (hk : ∀ a, Cont (fun d => k d a)) : Cont (fun d => m d >>= k d) :=
  Cont.bind Cont.result_bindCont hm hk

end

end NonPos.Std
