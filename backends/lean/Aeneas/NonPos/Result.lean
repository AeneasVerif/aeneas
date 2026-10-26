module
public import Aeneas.NonPos.Domain.ITree
public import Aeneas.NonPos.Top

@[expose] public section
/-!
# The `Result` monad: interaction trees over a non-trivial effect

`Result T = ITree Eff T`, as in Aeneas, but with an effect that has a continuation (`input`), so
that the order on `Result` is not flat.  `partial_fixpoint` works on it through the `CCPO` instance of
`Coinductive`.  The continuity facts specific to `Result` (its own `bind`, `ok`, and `vis`) are tagged
`@[nonpos_continuous]`; the generic `Cont.bind`/`Cont.pure` cover `do` notation.
-/
namespace NonPos
open Aeneas.Data.Coinductive NonPos.Domain Lean.Order

universe w

inductive Eff.I : Type where
  | fail : String → Eff.I
  | input : Eff.I

-- `abbrev`, so that `Eff.O .input` is `Nat` for `simp`
abbrev Eff.O : Eff.I → Type
  | .fail _ => PEmpty
  | .input => Nat

abbrev Eff : Effect := ⟨Eff.I, Eff.O⟩

abbrev Result (T : Type) : Type := ITree Eff T

namespace Result
abbrev ok {T : Type} (a : T) : Result T := ITree.ret a
abbrev div {T : Type} : Result T := ITree.div
abbrev vis {T : Type} (i : Eff.I) (k : Eff.O i → Result T) : Result T := ITree.vis i k
def fail {T : Type} (e : String) : Result T := vis (.fail e) PEmpty.elim
def input {T : Type} (k : Nat → Result T) : Result T := vis .input k
abbrev bind {A B : Type} (x : Result A) (f : A → Result B) : Result B := ITree.bind x f

theorem bind_eq {A B : Type} (x : Result A) (f : A → Result B) : x >>= f = x.bind f := rfl
theorem pure_eq {A : Type} (a : A) : (pure a : Result A) = Result.ok a := rfl
end Result

/-- `Result` is a supported monad: its order is the `CCPO` of `Coinductive`, for which `bind` is
continuous (`ITree.continuous_bind`). -/
noncomputable instance : NonPosMonad Result where
  bind_cont := fun {α β} => by
    letI : Dom (Result α) := Dom.ofCCPO (Result α)
    letI : Dom (Result β) := Dom.ofCCPO (Result β)
    exact Cont.toPProd (g := fun x k => x >>= k) ITree.continuous_bind

/-! The `Result`-specific forms. -/
section
variable {D : Type w} [Dom D]
@[nonpos_continuous]
theorem Cont.rok {A : Type} {a : D → A} (ha : Cont (inst_1 := Dom.discrete A) a) : Cont (fun d => Result.ok (a d)) :=
  Cont.pure (M := Result) ha
@[nonpos_continuous]
theorem Cont.rbind {A B : Type} {m : D → Result A} {k : D → A → Result B}
    (hm : Cont m) (hk : ∀ a, Cont (fun d => k d a)) : Cont (fun d => Result.bind (m d) (k d)) :=
  Cont.bind (M := Result) hm hk
@[nonpos_continuous]
theorem Cont.vis {T : Type} (i : Eff.I) {k : D → Eff.O i → Result T}
    (hk : ∀ o, Cont (fun d => k d o)) : Cont (fun d => Result.vis i (k d)) := by
  letI := (Dom.po : PartialOrder D); letI := (Dom.os : OmegaSup D)
  have h1 : Continuous (fun k : Eff.O i → Result T => Result.vis i k) := ITree.continuous_vis (E := Eff) (R := T) i
  have h2 : Continuous (fun d : D => fun o => k d o) := Continuous.pi_lam (fun o => hk o)
  exact h1.comp h2
@[nonpos_continuous]
theorem Cont.input {T : Type} {k : D → Nat → Result T}
    (hk : ∀ n, Cont (fun d => k d n)) : Cont (fun d => Result.input (k d)) :=
  Cont.vis .input hk
end

end NonPos
