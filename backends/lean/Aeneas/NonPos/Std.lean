module
public import Aeneas.NonPos.Domain.ITree
public import Aeneas.NonPos.Tactic
public import Aeneas.Std.Primitives

@[expose] public section
/-!
# Aeneas's `Result`: the proofs of the forms of its operations

`Aeneas.Std.Result α` is `ITree RustEffect α`, ordered by the `CCPO` that `partial_fixpoint` uses.
Its values can be fields of `nonpos_structure`s (the methods of a trait compiled by Aeneas) through
its `CCPO`.  This file proves that `bind` and `vis` satisfy the condition, from their continuity in
the model of interaction trees (`ITree.continuous_bind`, `ITree.continuous_vis`, for any effect).
The forms themselves are stated, and tagged `@[nonpos_continuous]`, in `TrustedBase/Result.lean`.
-/
namespace NonPos.Std
open Aeneas.Std Aeneas.Data.Coinductive NonPos.Domain Lean.Order

universe u w

unseal Result in
/-- `bind` satisfies the condition: the order of `Result` is the `CCPO` of `Coinductive`, for which
`bind` is continuous (`ITree.continuous_bind`). -/
theorem result_bindCont {α β : Type u} : Cont (fun p : Result α ×' (α → Result β) => p.1 >>= p.2) :=
  Proofs.Cont.bind_of_model (by
    let : Dom (Result α) := Dom.ofCCPO (Result α)
    let : Dom (Result β) := Dom.ofCCPO (Result β)
    exact DCont.toPProd (g := fun x k => x >>= k) ITree.continuous_bind)

section
variable {D : Type w} [Lean.Order.PartialOrder D]

theorem result_bind {A B : Type u} {m : D → Result A} {k : D → A → Result B}
    (hm : Cont m) (hk : ∀ a, Cont (fun d => k d a)) : Cont (fun d => Aeneas.Std.bind (m d) (k d)) :=
  Cont.bind result_bindCont hm hk

theorem result_bind' {A B : Type u} {m : D → Result A} {k : D → A → Result B}
    (hm : Cont m) (hk : ∀ a, Cont (fun d => k d a)) : Cont (fun d => m d >>= k d) :=
  Cont.bind result_bindCont hm hk

unseal Result in
theorem result_vis {T : Type u} (i : RustEffect.Input) {k : D → RustEffect.Output i → Result T}
    (hk : ∀ o, Cont (fun d => k d o)) : Cont (fun d => Result.vis i (k d)) := by
  -- `vis i` satisfies the condition, from the model (`ITree.continuous_vis`); then composition
  have h1 : Cont (fun k : RustEffect.Output i → Result T => Result.vis i k) :=
    (Proofs.Cont.iff_model (@Dom.pi (RustEffect.Output i) (fun _ => Result T) (fun _ => Dom.ofCCPO (Result T)))
      (Dom.ofCCPO (Result T)) _).2 (ITree.continuous_vis (E := RustEffect) (R := T) i)
  exact Proofs.Cont.comp h1 (Cont.lam (f := fun d o => k d o) hk)

end

end NonPos.Std
