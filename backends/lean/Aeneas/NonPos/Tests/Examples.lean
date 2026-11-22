module
public import Aeneas.NonPos.Tests.Test

@[expose] public section
/-!
# What `nonpos_structure` generates, written out by hand

Two examples, expanded exactly as `nonpos_structure` would expand them: the definitions and `simp`
lemmas of section 1 of `Command.lean`, and the lemmas of section 4 of `Tactic.lean` (same names, same
shapes of terms), so that the output of the command can be read without running it.  The first has one structure with a
plain field (a value of the monad, as an associated constant is); the second is the mutual pair `A`/`B` of `Test.lean`.  Both use `Option` as the monad.
-/
namespace NonPos.Examples
open NonPos
noncomputable section
set_option linter.unusedVariables false

/-! ## 1. A single structure

```
nonpos_structure Example1 : Type where
  to_nat : Option Nat
  f : Example1 → Option Nat
```
-/

-- `I`: one constructor per structure of the group, taking its parameters (here: none).
inductive Example1.I where
  | Example1

-- The field types as written, with the structure names of the group as parameters.
abbrev Example1.Fields (Example1 : Type) : Type :=
  Option Nat ×' (Example1 → Option Nat) ×' PUnit.{1}

-- `F`: the body of each structure, with the structures replaced by the family `X`.
abbrev Example1.F : Example1.I → (Example1.I → Type) → Type
  | .Example1, X => Example1.Fields (X .Example1)

-- The shape, found by instance search: `FixFunctor.prod (FixFunctor.const (Option Nat)) (FixFunctor.prod (FixFunctor.arr …) FixFunctor.unit)`.
@[reducible] instance Example1.shape : ∀ k, FixFunctor (Example1.F k)
  | .Example1 => inferInstance
-- Its runtime implementation, never read (section 5 of `Top.lean`, assumption 3).
@[instance_reducible] unsafe def Example1.shapeImpl : ∀ k, FixFunctor (Example1.F k) := fun _ => FixFunctor.runtime
attribute [implemented_by Example1.shapeImpl] Example1.shape

-- The structure.
abbrev Example1 : Type := Fix Example1.F .Example1

-- `mk`, from the fields and the condition.  `macro_inline`, so that the fields are not evaluated
-- before `foldDelayed` delays them (section 5 of `Top.lean`).
@[macro_inline] def Example1.mk (to_nat : Option Nat) (f : Example1 → Option Nat)
    (h : FixFunctor.cond (X := Fix Example1.F) (G := Example1.F .Example1) ⟨to_nat, f, ⟨⟩⟩) : Example1 :=
  Fix.foldDelayed Example1.F (fun _ => ⟨to_nat, f, ⟨⟩⟩) h

-- The projections, with the types as written, and their `simp` lemmas (stated by section 1 of
-- `Command.lean`; there proved by `nonpos_proj_mk`, of `Tactic.lean`: `congrArg` of the projection on
-- `Fix.unfold_fold`).
def Example1.to_nat (d : Example1) : Option Nat :=
  no_implicit_lambda% (@PProd.fst _ _ (Fix.unfold Example1.F d))
@[simp] theorem Example1.to_nat_mk (to_nat : Option Nat) (f : Example1 → Option Nat)
    (h : FixFunctor.cond (X := Fix Example1.F) (G := Example1.F .Example1) ⟨to_nat, f, ⟨⟩⟩) :
    Example1.to_nat (Example1.mk to_nat f h) = to_nat := by
  simp only [Example1.to_nat, Example1.mk, Fix.foldDelayed, Fix.unfold_fold]

def Example1.f (d : Example1) : Example1 → Option Nat :=
  no_implicit_lambda% (@PProd.fst _ _ (@PProd.snd _ _ (Fix.unfold Example1.F d)))
@[simp] theorem Example1.f_mk (to_nat : Option Nat) (f : Example1 → Option Nat)
    (h : FixFunctor.cond (X := Fix Example1.F) (G := Example1.F .Example1) ⟨to_nat, f, ⟨⟩⟩) :
    Example1.f (Example1.mk to_nat f h) = f := by
  simp only [Example1.f, Example1.mk, Fix.foldDelayed, Fix.unfold_fold]

-- `mk` is continuous in its fields (section 4 of `Tactic.lean`): proved once here, and used by
-- `nonpos_cont` on any `mk` whose fields vary, instead of going through the tuple of fields.
theorem Example1.mk_cont {D : Type _} [Lean.Order.PartialOrder D] (to_nat : D → Option Nat) (f : D → Example1 → Option Nat)
    (h : ∀ d, FixFunctor.cond (X := Fix Example1.F) (G := Example1.F Example1.I.Example1) ⟨to_nat d, f d, ⟨⟩⟩)
    (_ : Cont to_nat) (_ : Cont f) :
    Cont (fun d => Example1.mk (to_nat d) (f d) (h d)) := by
  nonpos_cont 5000
attribute [nonpos_continuous] Example1.mk_cont

-- The condition of `mk` from its conjuncts (section 4 of `Tactic.lean`; there built from the
-- condition unfolded by `nonpos_cond_dsimp`): `nonpos_cont` applies it to the condition of each `mk`,
-- instead of unfolding the condition there.  The conjuncts that are `True` are left out.
theorem Example1.cond_intro (to_nat : Option Nat) (f : Example1 → Option Nat) (h0 : Cont f) :
    FixFunctor.cond (X := Fix Example1.F) (G := Example1.F .Example1) ⟨to_nat, f, ⟨⟩⟩ :=
  ⟨trivial, ⟨h0, fun _ => trivial⟩, trivial⟩

-- `Fix.unfold` satisfies the condition, at the order of the tuple of fields.
theorem Example1.unfold_cont {D : Type _} [Lean.Order.PartialOrder D] (g : D → Example1) (hg : Cont g) :
    Cont (iB := FixFunctor.order (Example1.F .Example1) (Fix Example1.F)) (fun d => Fix.unfold Example1.F (g d)) :=
  Cont.unfold Example1.F hg

-- Using it: the condition is `Cont f`, which `nonpos_cont` proves.
def ex1 : Example1 := Example1.mk (some 3) (fun d => d.f d >>= fun n => some (n + 1)) (by nonpos_cont)
example : ex1.to_nat = some 3 := by simp [ex1]

/-! ## 2. The same structure, through the command

Everything `#print`ed below is generated by `nonpos_structure`; compare with part 1, definition by
definition. -/

nonpos_structure Example2 : Type where
  to_nat : Option Nat
  f : Example2 → Option Nat

#print Example2.I            -- `I`
#print Example2.Fields
#print Example2.F
#print Example2.shape
#print Example2              -- `Fix Example2.F .Example2`
#print Example2.mk
#print Example2.to_nat
#print Example2.to_nat_mk
#print Example2.f
#print Example2.f_mk
#check @Example2.mk_cont
#check @Example2.cond_intro

def ex2 : Example2 := Example2.mk (some 3) (fun d => d.f d >>= fun n => some (n + 1)) (by nonpos_cont)
example : ex2.to_nat = some 3 := by simp [ex2]

/-! ## 3. A mutual group

```
mutual
nonpos_structure A (Self : Type) : Type 1 where
  fa : ∀ {O : Type} (BInst : B O), Self → O → Option Nat
nonpos_structure B (Self : Type) : Type 1 where
  fb : ∀ {O : Type} (AInst : A O), Self → O → Option Nat
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
  (∀ {O : Type} (BInst : B O), Self → O → Option Nat) ×' PUnit.{2}
abbrev B.Fields (A : Type → Type 1) (B : Type → Type 1) (Self : Type) : Type 1 :=
  (∀ {O : Type} (AInst : A O), Self → O → Option Nat) ×' PUnit.{2}

-- `A.F (.A Self) X` unfolds to `(∀ {O} (BInst : X (.B O)), Self → O → Option Nat) ×' PUnit`.
abbrev A.F : A.I → (A.I → Type 1) → Type 1
  | .A Self, X => A.Fields (fun Self => X (.A Self)) (fun Self => X (.B Self)) Self
  | .B Self, X => B.Fields (fun Self => X (.A Self)) (fun Self => X (.B Self)) Self

-- FixFunctor of `A.F (.A Self)`: `prod (pi Type (fun O => arr (.B O) (pi Self (pi O (const (Option Nat))))))) unit`.
@[reducible] instance A.shape : ∀ k, FixFunctor (A.F k)
  | .A Self => inferInstance
  | .B Self => inferInstance
-- Its runtime implementation, never read (section 5 of `Top.lean`, assumption 3).
@[instance_reducible] unsafe def A.shapeImpl : ∀ k, FixFunctor (A.F k) := fun _ => FixFunctor.runtime
attribute [implemented_by A.shapeImpl] A.shape

-- Both structures, before any `mk` or projection (those of one mention the other).
abbrev A (Self : Type) : Type 1 := Fix A.F (.A Self)
abbrev B (Self : Type) : Type 1 := Fix A.F (.B Self)

@[macro_inline] def A.mk {Self : Type} (fa : ∀ {O : Type} (BInst : B O), Self → O → Option Nat)
    (h : FixFunctor.cond (X := Fix A.F) (G := A.F (.A Self)) ⟨fa, ⟨⟩⟩) : A Self :=
  Fix.foldDelayed A.F (fun _ => ⟨fa, ⟨⟩⟩) h
def A.fa {Self : Type} (d : A Self) : ∀ {O : Type} (BInst : B O), Self → O → Option Nat :=
  no_implicit_lambda% (@PProd.fst _ _ (Fix.unfold A.F d))
@[simp] theorem A.fa_mk {Self : Type} (fa : ∀ {O : Type} (BInst : B O), Self → O → Option Nat)
    (h : FixFunctor.cond (X := Fix A.F) (G := A.F (.A Self)) ⟨fa, ⟨⟩⟩) :
    @A.fa Self (A.mk fa h) = @fa := by
  simp only [A.fa, A.mk, Fix.foldDelayed, Fix.unfold_fold]

@[macro_inline] def B.mk {Self : Type} (fb : ∀ {O : Type} (AInst : A O), Self → O → Option Nat)
    (h : FixFunctor.cond (X := Fix A.F) (G := A.F (.B Self)) ⟨fb, ⟨⟩⟩) : B Self :=
  Fix.foldDelayed A.F (fun _ => ⟨fb, ⟨⟩⟩) h
def B.fb {Self : Type} (d : B Self) : ∀ {O : Type} (AInst : A O), Self → O → Option Nat :=
  no_implicit_lambda% (@PProd.fst _ _ (Fix.unfold A.F d))
@[simp] theorem B.fb_mk {Self : Type} (fb : ∀ {O : Type} (AInst : A O), Self → O → Option Nat)
    (h : FixFunctor.cond (X := Fix A.F) (G := A.F (.B Self)) ⟨fb, ⟨⟩⟩) :
    @B.fb Self (B.mk fb h) = @fb := by
  simp only [B.fb, B.mk, Fix.foldDelayed, Fix.unfold_fold]

-- `mk` of each structure is continuous in its fields (section 4 of `Tactic.lean`).
theorem A.mk_cont {Self : Type} {D : Type _} [Lean.Order.PartialOrder D] (fa : D → ∀ {O : Type} (BInst : B O), Self → O → Option Nat)
    (h : ∀ d, FixFunctor.cond (X := Fix A.F) (G := A.F (A.I.A Self)) ⟨fa d, ⟨⟩⟩) (_ : Cont fa) :
    Cont (fun d => A.mk (fa d) (h d)) := by
  nonpos_cont 5000
attribute [nonpos_continuous] A.mk_cont
theorem B.mk_cont {Self : Type} {D : Type _} [Lean.Order.PartialOrder D] (fb : D → ∀ {O : Type} (AInst : A O), Self → O → Option Nat)
    (h : ∀ d, FixFunctor.cond (X := Fix A.F) (G := A.F (A.I.B Self)) ⟨fb d, ⟨⟩⟩) (_ : Cont fb) :
    Cont (fun d => B.mk (fb d) (h d)) := by
  nonpos_cont 5000
attribute [nonpos_continuous] B.mk_cont

-- The condition of `A.mk`, unfolded: `fa` is continuous in its dictionary argument, for every `O`.
example {Self : Type} (fa : ∀ {O : Type} (BInst : B O), Self → O → Option Nat) :
    FixFunctor.cond (X := Fix A.F) (G := A.F (.A Self)) ⟨fa, ⟨⟩⟩ ↔
      ∀ O : Type, Cont (fun BInst : B O => (fa BInst : Self → O → Option Nat)) := by
  nonpos_cond_simp

-- Using it: an instance of `A` for `Nat` that calls back into the `B` dictionary it is given.
def natA₀ : A Nat := A.mk (fun {O} _ _ _ => none) (by nonpos_cont)
def natA : A Nat := A.mk (fun {O} (BInst : B O) s o => BInst.fb natA₀ o s) (by nonpos_cont)
example {O : Type} (BInst : B O) (s : Nat) (o : O) : natA.fa BInst s o = BInst.fb natA₀ o s := by simp [natA]

end
end NonPos.Examples
