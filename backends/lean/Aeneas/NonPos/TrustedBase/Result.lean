module
public import Aeneas.NonPos.Implementation.ResultProofs

@[expose] public section
/-!
# Aeneas's `Result`: the forms of its operations

The forms of `Definitions.lean`, for the monad that Aeneas outputs: `bind` (as `Aeneas.Std.bind`,
and as `>>=`, from `do` notation) and `vis` (an effect, with its continuation) satisfy the condition
when their parts do.  `Result.ok x`, `Result.fail e` and `Result.div` need no form: they do not
mention the dictionary (a dictionary has no field of plain data), so they are `Cont.const`.
The proofs are in `NonPos/Implementation/ResultProofs.lean`.
-/
namespace NonPos
open Aeneas.Std

universe u w
variable {D : Type w} [Lean.Order.PartialOrder D]

@[nonpos_continuous]
theorem Cont.result_bind {A B : Type u} {m : D → Result A} {k : D → A → Result B}
    (hm : Cont m) (hk : ∀ a, Cont (fun d => k d a)) : Cont (fun d => Aeneas.Std.bind (m d) (k d)) :=
  Std.result_bind hm hk

@[nonpos_continuous]
theorem Cont.result_bind' {A B : Type u} {m : D → Result A} {k : D → A → Result B}
    (hm : Cont m) (hk : ∀ a, Cont (fun d => k d a)) : Cont (fun d => m d >>= k d) :=
  Std.result_bind' hm hk

@[nonpos_continuous]
theorem Cont.result_vis {T : Type u} (i : RustEffect.Input) {k : D → RustEffect.Output i → Result T}
    (hk : ∀ o, Cont (fun d => k d o)) : Cont (fun d => Result.vis i (k d)) :=
  Std.result_vis i hk

end NonPos
