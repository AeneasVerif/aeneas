module
public import Aeneas.NonPos.TrustedBase.Command
public import Aeneas.NonPos.TrustedBase.Result

@[expose] public section
/-!
This file contains two examples of what the `nonpos_structure` command outputs.
One for a simple single structure, and the other is a mutual group of structures.
-/
namespace NonPos.Examples
open NonPos Aeneas.Std
noncomputable section
set_option linter.unusedVariables false

/-! ## 1. A single structure

```
nonpos_structure SimpleNonpos : Type where
  to_nat : Result Nat
  f : SimpleNonpos → Result Nat
```
-/

-- `I`: one constructor per structure of the group, taking its parameters (here: none).
inductive SimpleNonpos.I where
  | SimpleNonpos

-- The field types as written, with the structure names of the group as parameters.
abbrev SimpleNonpos.Fields (SimpleNonpos : Type) : Type :=
  Result Nat ×' (SimpleNonpos → Result Nat) ×' PUnit.{1}

-- `F`: the body of each structure, with the structures replaced by the family `X`.
abbrev SimpleNonpos.F : SimpleNonpos.I → (SimpleNonpos.I → Type) → Type
  | .SimpleNonpos, X => SimpleNonpos.Fields (X .SimpleNonpos)

-- The shape, found by instance search: `FixFunctor.prod (FixFunctor.base (Result Nat)) (FixFunctor.prod (FixFunctor.rec_input …) FixFunctor.unit)`.
@[reducible] instance SimpleNonpos.shape : ∀ k, FixFunctor (SimpleNonpos.F k)
  | .SimpleNonpos => inferInstance

-- The structure.
abbrev SimpleNonpos : Type := Fix SimpleNonpos.F .SimpleNonpos

-- `mk`, from the fields and the condition.  `macro_inline`, so that the fields are not evaluated
-- before `foldDelayed` delays them (`TrustedBase/Definitions.lean`, where `foldDelayed` is).
@[macro_inline] def SimpleNonpos.mk (to_nat : Result Nat) (f : SimpleNonpos → Result Nat)
    (h : FixFunctor.cond (X := Fix SimpleNonpos.F) (G := SimpleNonpos.F .SimpleNonpos) ⟨to_nat, f, ⟨⟩⟩) : SimpleNonpos :=
  Fix.foldDelayed SimpleNonpos.F (fun _ => ⟨to_nat, f, ⟨⟩⟩) h

-- The projections, with the types as written, and their `simp` lemmas (stated by section 1 of
-- `Command.lean`; there proved by `nonpos_proj_mk`, of `Tactic.lean`: `congrArg` of the projection on
-- `Fix.unfold_fold`).
def SimpleNonpos.to_nat (d : SimpleNonpos) : Result Nat :=
  no_implicit_lambda% (@PProd.fst _ _ (Fix.unfold SimpleNonpos.F d))
@[simp] theorem SimpleNonpos.to_nat_mk (to_nat : Result Nat) (f : SimpleNonpos → Result Nat)
    (h : FixFunctor.cond (X := Fix SimpleNonpos.F) (G := SimpleNonpos.F .SimpleNonpos) ⟨to_nat, f, ⟨⟩⟩) :
    SimpleNonpos.to_nat (SimpleNonpos.mk to_nat f h) = to_nat := by
  simp only [SimpleNonpos.to_nat, SimpleNonpos.mk, Fix.foldDelayed, Fix.unfold_fold]

def SimpleNonpos.f (d : SimpleNonpos) : SimpleNonpos → Result Nat :=
  no_implicit_lambda% (@PProd.fst _ _ (@PProd.snd _ _ (Fix.unfold SimpleNonpos.F d)))
@[simp] theorem SimpleNonpos.f_mk (to_nat : Result Nat) (f : SimpleNonpos → Result Nat)
    (h : FixFunctor.cond (X := Fix SimpleNonpos.F) (G := SimpleNonpos.F .SimpleNonpos) ⟨to_nat, f, ⟨⟩⟩) :
    SimpleNonpos.f (SimpleNonpos.mk to_nat f h) = f := by
  simp only [SimpleNonpos.f, SimpleNonpos.mk, Fix.foldDelayed, Fix.unfold_fold]

-- `mk` is continuous in its fields (section 4 of `Tactic.lean`): proved once here, and used by
-- `nonpos_cont` on any `mk` whose fields vary, instead of going through the tuple of fields.
theorem SimpleNonpos.mk_cont {D : Type _} [Lean.Order.PartialOrder D] (to_nat : D → Result Nat) (f : D → SimpleNonpos → Result Nat)
    (h : ∀ d, FixFunctor.cond (X := Fix SimpleNonpos.F) (G := SimpleNonpos.F SimpleNonpos.I.SimpleNonpos) ⟨to_nat d, f d, ⟨⟩⟩)
    (_ : Cont to_nat) (_ : Cont f) :
    Cont (fun d => SimpleNonpos.mk (to_nat d) (f d) (h d)) := by
  nonpos_cont 5000
attribute [nonpos_continuous] SimpleNonpos.mk_cont

-- The condition of `mk` from its conjuncts (section 4 of `Tactic.lean`; there built from the
-- condition unfolded by `nonpos_cond_dsimp`): `nonpos_cont` applies it to the condition of each `mk`,
-- instead of unfolding the condition there.  The conjuncts that are `True` are left out.
theorem SimpleNonpos.cond_intro (to_nat : Result Nat) (f : SimpleNonpos → Result Nat) (h0 : Cont f) :
    FixFunctor.cond (X := Fix SimpleNonpos.F) (G := SimpleNonpos.F .SimpleNonpos) ⟨to_nat, f, ⟨⟩⟩ :=
  ⟨trivial, ⟨h0, fun _ => trivial⟩, trivial⟩

-- `Fix.unfold` satisfies the condition, at the order of the tuple of fields.
theorem SimpleNonpos.unfold_cont {D : Type _} [Lean.Order.PartialOrder D] (g : D → SimpleNonpos) (hg : Cont g) :
    Cont (iB := FixFunctor.order (SimpleNonpos.F .SimpleNonpos) (Fix SimpleNonpos.F)) (fun d => Fix.unfold SimpleNonpos.F (g d)) :=
  Cont.unfold SimpleNonpos.F hg

-- Using it: the condition is `Cont f`, which `nonpos_cont` proves.
def ex1 : SimpleNonpos := SimpleNonpos.mk (.ok 3) (fun d => d.f d >>= fun n => Result.ok (n + 1)) (by nonpos_cont)
example : ex1.to_nat = .ok 3 := by simp [ex1]

/-! ## 2. A mutual group

```
mutual
nonpos_structure A (Self : Type) : Type 1 where
  fa : ∀ {O : Type} (BInst : B O), Self → O → Result Nat
nonpos_structure B (Self : Type) : Type 1 where
  fb : ∀ {O : Type} (AInst : A O), Self → O → Result Nat
end
```
The group is named after its first structure, `A`.
-/

-- The index type: the structures of the group at their parameters (`A.I.A Self` is `A Self`).
inductive A.I where
  | A (Self : Type)
  | B (Self : Type)

-- Every `Fields` takes all the structures of the group as parameters, so a field may mention any of them.
abbrev A.Fields (A : Type → Type 1) (B : Type → Type 1) (Self : Type) : Type 1 :=
  (∀ {O : Type} (BInst : B O), Self → O → Result Nat) ×' PUnit.{2}
abbrev B.Fields (A : Type → Type 1) (B : Type → Type 1) (Self : Type) : Type 1 :=
  (∀ {O : Type} (AInst : A O), Self → O → Result Nat) ×' PUnit.{2}

-- `A.F (.A Self) X` unfolds to `(∀ {O} (BInst : X (.B O)), Self → O → Result Nat) ×' PUnit`.
abbrev A.F : A.I → (A.I → Type 1) → Type 1
  | .A Self, X => A.Fields (fun Self => X (.A Self)) (fun Self => X (.B Self)) Self
  | .B Self, X => B.Fields (fun Self => X (.A Self)) (fun Self => X (.B Self)) Self

-- FixFunctor of `A.F (.A Self)`: `prod (plain_input Type (fun O => rec_input (.B O) (plain_input Self (plain_input O (base (Result Nat)))))) unit`.
@[reducible] instance A.shape : ∀ k, FixFunctor (A.F k)
  | .A Self => inferInstance
  | .B Self => inferInstance

-- Both structures, before any `mk` or projection (those of one mention the other).
abbrev A (Self : Type) : Type 1 := Fix A.F (.A Self)
abbrev B (Self : Type) : Type 1 := Fix A.F (.B Self)

@[macro_inline] def A.mk {Self : Type} (fa : ∀ {O : Type} (BInst : B O), Self → O → Result Nat)
    (h : FixFunctor.cond (X := Fix A.F) (G := A.F (.A Self)) ⟨fa, ⟨⟩⟩) : A Self :=
  Fix.foldDelayed A.F (fun _ => ⟨fa, ⟨⟩⟩) h
def A.fa {Self : Type} (d : A Self) : ∀ {O : Type} (BInst : B O), Self → O → Result Nat :=
  no_implicit_lambda% (@PProd.fst _ _ (Fix.unfold A.F d))
@[simp] theorem A.fa_mk {Self : Type} (fa : ∀ {O : Type} (BInst : B O), Self → O → Result Nat)
    (h : FixFunctor.cond (X := Fix A.F) (G := A.F (.A Self)) ⟨fa, ⟨⟩⟩) :
    @A.fa Self (A.mk fa h) = @fa := by
  simp only [A.fa, A.mk, Fix.foldDelayed, Fix.unfold_fold]

@[macro_inline] def B.mk {Self : Type} (fb : ∀ {O : Type} (AInst : A O), Self → O → Result Nat)
    (h : FixFunctor.cond (X := Fix A.F) (G := A.F (.B Self)) ⟨fb, ⟨⟩⟩) : B Self :=
  Fix.foldDelayed A.F (fun _ => ⟨fb, ⟨⟩⟩) h
def B.fb {Self : Type} (d : B Self) : ∀ {O : Type} (AInst : A O), Self → O → Result Nat :=
  no_implicit_lambda% (@PProd.fst _ _ (Fix.unfold A.F d))
@[simp] theorem B.fb_mk {Self : Type} (fb : ∀ {O : Type} (AInst : A O), Self → O → Result Nat)
    (h : FixFunctor.cond (X := Fix A.F) (G := A.F (.B Self)) ⟨fb, ⟨⟩⟩) :
    @B.fb Self (B.mk fb h) = @fb := by
  simp only [B.fb, B.mk, Fix.foldDelayed, Fix.unfold_fold]

-- `mk` of each structure is continuous in its fields (section 4 of `Tactic.lean`).
theorem A.mk_cont {Self : Type} {D : Type _} [Lean.Order.PartialOrder D] (fa : D → ∀ {O : Type} (BInst : B O), Self → O → Result Nat)
    (h : ∀ d, FixFunctor.cond (X := Fix A.F) (G := A.F (A.I.A Self)) ⟨fa d, ⟨⟩⟩) (_ : Cont fa) :
    Cont (fun d => A.mk (fa d) (h d)) := by
  nonpos_cont 5000
attribute [nonpos_continuous] A.mk_cont
theorem B.mk_cont {Self : Type} {D : Type _} [Lean.Order.PartialOrder D] (fb : D → ∀ {O : Type} (AInst : A O), Self → O → Result Nat)
    (h : ∀ d, FixFunctor.cond (X := Fix A.F) (G := A.F (A.I.B Self)) ⟨fb d, ⟨⟩⟩) (_ : Cont fb) :
    Cont (fun d => B.mk (fb d) (h d)) := by
  nonpos_cont 5000
attribute [nonpos_continuous] B.mk_cont

-- The condition of `A.mk`, unfolded: `fa` is continuous in its dictionary argument, for every `O`.
example {Self : Type} (fa : ∀ {O : Type} (BInst : B O), Self → O → Result Nat) :
    FixFunctor.cond (X := Fix A.F) (G := A.F (.A Self)) ⟨fa, ⟨⟩⟩ ↔
      ∀ O : Type, Cont (fun BInst : B O => (fa BInst : Self → O → Result Nat)) := by
  nonpos_cond_simp

-- Using it: an instance of `A` for `Nat` that calls back into the `B` dictionary it is given.
def natA₀ : A Nat := A.mk (fun {O} _ _ _ => Result.fail .panic) (by nonpos_cont)
def natA : A Nat := A.mk (fun {O} (BInst : B O) s o => BInst.fb natA₀ o s) (by nonpos_cont)
example {O : Type} (BInst : B O) (s : Nat) (o : O) : natA.fa BInst s o = BInst.fb natA₀ o s := by simp [natA]

end
end NonPos.Examples
