module
public import Lean
public import Aeneas.NonPos.FormsProofs

@[expose] public section
/-!
# The `nonpos_cont` tactic

Section 0 is read with `Top.lean`: it states the forms of term that satisfy the condition on
dictionary binders (`Shape.Cont`), which is how one sees that the condition holds of what Aeneas
outputs.  The rest is not part of the trusted surface: `Command.lean` (section 2) states what it is
expected to do, and every proof built here is checked by the kernel.  This file contains:

0. the forms, on `Shape.Cont`;
1. the same forms at the orders of the model, which the tactic uses, and the `@[nonpos_continuous]`
   attribute;
2. the `nonpos_cont` tactic, a thin wrapper around those theorems;
3. the `nonpos_continuity` command, which proves continuity theorems of functions with that tactic,
   so that it does not have to prove them again at each use;
4. the lemmas proved for each structure of a `nonpos_structure` group (`elabGroupLemmas`, which
   `Command.lean` calls), lemmas used by the tactic; and the proofs of the `simp` lemmas `Bla.f_mk`
   that `Command.lean` states (`nonpos_proj_mk`).
-/

namespace NonPos
open Lean Elab Command Term Meta
noncomputable section

universe pu v u w w₁ w₂ w₃

/-! ## 0. The forms

`Shape.Cont H f` (`Top.lean`): `f`, from the values of a body `G₁` to those of a body `G₂` over the
structures of the group `H`, satisfies the condition of a dictionary binder.  It holds of every term
built from the forms below, where `d` is the varying dictionary (or a value built from it).  A
definition is unfolded; a `partial_fixpoint` (or loop) is `Lean.Order.fix`.  Each form is proved
from the model, in `FormsProofs.lean` (`Proofs.ShapeCont`). -/

section Forms
variable {I : Type pu} {H : I → (I → Type v) → Type v} [∀ k, Shape (H k)]
  {G₁ : (I → Type v) → Type w₁} [Shape G₁]

/-- Constants and the identity. -/
theorem Shape.Cont.const {G : (I → Type v) → Type w₂} [Shape G] (b : G (Fix H)) :
    Shape.Cont H (G₁ := G₁) (fun _ => b) :=
  Proofs.ShapeCont.const b
theorem Shape.Cont.id : Shape.Cont H (G₁ := G₁) (G₂ := G₁) (fun d => d) :=
  Proofs.ShapeCont.id
/-- Lambda (pointwise), and application to an argument not depending on `d`. -/
theorem Shape.Cont.lam {T : Type w₂} {G : T → (I → Type v) → Type w₃} [∀ t, Shape (G t)] [∀ t, Shape.Pointed (G t)]
    {f : G₁ (Fix H) → (t : T) → G t (Fix H)} (h : ∀ t, Shape.Cont H (fun d => f d t)) :
    Shape.Cont H (G₂ := fun X => (t : T) → G t X) f :=
  Proofs.ShapeCont.lam h
theorem Shape.Cont.app {T : Type w₂} {G : T → (I → Type v) → Type w₃} [∀ t, Shape (G t)] [∀ t, Shape.Pointed (G t)]
    {f : G₁ (Fix H) → (t : T) → G t (Fix H)} (hf : Shape.Cont H (G₂ := fun X => (t : T) → G t X) f) (t : T) :
    Shape.Cont H (fun d => f d t) :=
  Proofs.ShapeCont.app hf t
/-- Application to a dictionary depending on `d`. -/
theorem Shape.Cont.app₂ {k : I} {G : (I → Type v) → Type w₂} [Shape G] [Shape.Pointed G]
    {f : G₁ (Fix H) → Fix H k → G (Fix H)} {a : G₁ (Fix H) → Fix H k}
    (hf : Shape.Cont H (G₂ := fun X => X k → G X) f) (hc : ∀ d, Shape.Cont H (G₁ := fun X => X k) (f d))
    (ha : Shape.Cont H (G₂ := fun X => X k) a) : Shape.Cont H (fun d => f d (a d)) :=
  Proofs.ShapeCont.app₂ hf hc ha
/-- Pairs. -/
theorem Shape.Cont.pair {G : (I → Type v) → Type w₂} {G' : (I → Type v) → Type w₃} [Shape G] [Shape G']
    {f : G₁ (Fix H) → G (Fix H)} {g : G₁ (Fix H) → G' (Fix H)} (hf : Shape.Cont H f) (hg : Shape.Cont H g) :
    Shape.Cont H (G₂ := fun X => G X ×' G' X) (fun d => (⟨f d, g d⟩ : G (Fix H) ×' G' (Fix H))) :=
  Proofs.ShapeCont.pair hf hg
theorem Shape.Cont.fst {G : (I → Type v) → Type w₂} {G' : (I → Type v) → Type w₃} [Shape G] [Shape G']
    {f : G₁ (Fix H) → G (Fix H) ×' G' (Fix H)}
    (hf : Shape.Cont H (G₂ := fun X => G X ×' G' X) f) : Shape.Cont H (fun d => (f d).1) :=
  Proofs.ShapeCont.fst hf
theorem Shape.Cont.snd {G : (I → Type v) → Type w₂} {G' : (I → Type v) → Type w₃} [Shape G] [Shape G']
    {f : G₁ (Fix H) → G (Fix H) ×' G' (Fix H)}
    (hf : Shape.Cont H (G₂ := fun X => G X ×' G' X) f) : Shape.Cont H (fun d => (f d).2) :=
  Proofs.ShapeCont.snd hf
/-- A condition not depending on `d`. -/
theorem Shape.Cont.ite {G : (I → Type v) → Type w₂} [Shape G] (c : Prop) [Decidable c] {t e : G₁ (Fix H) → G (Fix H)}
    (ht : Shape.Cont H t) (he : Shape.Cont H e) : Shape.Cont H (fun d => if c then t d else e d) :=
  Proofs.ShapeCont.ite c ht he
theorem Shape.Cont.dite {G : (I → Type v) → Type w₂} [Shape G] (c : Prop) [Decidable c]
    {t : c → G₁ (Fix H) → G (Fix H)} {e : ¬c → G₁ (Fix H) → G (Fix H)}
    (ht : ∀ h, Shape.Cont H (t h)) (he : ∀ h, Shape.Cont H (e h)) :
    Shape.Cont H (fun d => if h : c then t h d else e h d) :=
  Proofs.ShapeCont.dite c ht he
/-- `pure` and `bind`, for any supported monad. -/
theorem Shape.Cont.pure {M : Type u → Type u} [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] {α : Type u}
    {a : G₁ (Fix H) → α} (ha : Shape.Cont H (G₂ := fun _ => α) (iG₂ := Shape.data α) a) :
    Shape.Cont H (G₂ := fun _ => M α) (fun d => (Pure.pure (a d) : M α)) :=
  Proofs.ShapeCont.pure ha
theorem Shape.Cont.bind {M : Type u → Type u} [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] {α β : Type u}
    {m : G₁ (Fix H) → M α} {k : G₁ (Fix H) → α → M β}
    (hm : Shape.Cont H (G₂ := fun _ => M α) m) (hk : ∀ a, Shape.Cont H (G₂ := fun _ => M β) (fun d => k d a)) :
    Shape.Cont H (G₂ := fun _ => M β) (fun d => m d >>= k d) :=
  Proofs.ShapeCont.bind hm hk
/-- The fields of a dictionary depending on `d`, and building one. -/
theorem Shape.Cont.unfold {k : I} {g : G₁ (Fix H) → Fix H k} (hg : Shape.Cont H (G₂ := fun X => X k) g) :
    Shape.Cont H (G₂ := H k) (fun d => Fix.unfold H (g d)) :=
  Proofs.ShapeCont.unfold hg
theorem Shape.Cont.fold {k : I} {f : G₁ (Fix H) → H k (Fix H)} (h : ∀ d, Shape.cond H (f d))
    (hf : Shape.Cont H (G₂ := H k) f) : Shape.Cont H (G₂ := fun X => X k) (fun d => Fix.fold H (f d) (h d)) :=
  Proofs.ShapeCont.fold h hf
/-- Fixed points (`partial_fixpoint`, loops), through a type with `Shape.FixCompat` (below). -/
theorem Shape.Cont.fix {G : (I → Type v) → Type w₂} [Shape G] [Lean.Order.CCPO (G (Fix H))] [Shape.FixCompat H G]
    {f : G₁ (Fix H) → G (Fix H) → G (Fix H)} {hm : ∀ d, Lean.Order.monotone (f d)}
    (hf : Shape.Cont H (G₁ := fun X => G₁ X ×' G X) (fun p => f p.1 p.2)) :
    Shape.Cont H (fun d => Lean.Order.fix (f d) (hm d)) :=
  Proofs.ShapeCont.fix hf
/-- What `partial_fixpoint` asks of a self-referential instance. -/
theorem Shape.Cont.monotone {G₂ : (I → Type v) → Type w₂} [Shape G₂] [Lean.Order.CCPO (G₁ (Fix H))]
    [Lean.Order.CCPO (G₂ (Fix H))] [Shape.FixCompat H G₁] [Shape.FixCompat H G₂] {f : G₁ (Fix H) → G₂ (Fix H)}
    (h : Shape.Cont H f) : Lean.Order.monotone f :=
  Proofs.ShapeCont.monotone h
/-! `Shape.FixCompat`: the values of a supported monad, functions into such types, and the
structures in which `⊥` is total. -/
instance (M : Type u → Type u) [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] (α : Type u) :
    Shape.FixCompat H (fun _ => M α) := FixCompat.monad α
instance {T : Type w₂} {G : T → (I → Type v) → Type w₃} [∀ t, Shape (G t)] [∀ t, Shape.Pointed (G t)]
    [∀ t, Lean.Order.CCPO (G t (Fix H))] [∀ t, Shape.FixCompat H (G t)] :
    Shape.FixCompat H (fun X => (t : T) → G t X) :=
  Proofs.ShapeCont.fixCompat_pi
instance (k : I) [Fix.BotTotal H k] : Shape.FixCompat H (fun X => X k) := Fix.fixCompat H k
end Forms

/-! ## 1. The forms, at the orders (used by the tactic)

Everything the `nonpos_cont` tactic knows is one of the statements below, all of the shape
`Cont (fun d => ‹form›)`.  `D` is the type of the varying dictionary (or tuple of dictionaries).
The list `forms` after the theorems is what the tactic looks up by shape; `const`, `id`, `lam`,
`app` and `app₂` have no shape to look up and are the tactic's own cases.  Continuity facts proved
elsewhere (a monad's own operations, helper functions) are added to the same lookup with the
`@[nonpos_continuous]` attribute, declared at the end of this section. -/


section Cont
variable {D : Type w} [Dom D]

theorem Cont.const {B : Type w₁} [Dom B] (b : B) : Cont (fun _ : D => b) := Proofs.Cont.const b
theorem Cont.id : Cont (fun d : D => d) := Proofs.Cont.id
/-- Lambda: pointwise. -/
theorem Cont.lam {T : Type w₁} {B : T → Type w₂} [∀ t, Dom (B t)] {f : D → (t : T) → B t}
    (h : ∀ t, Cont (fun d => f d t)) : Cont f := Proofs.Cont.lam h
/-- Application to an argument not depending on `d` (a type, a value, a fixed dictionary, ...). -/
theorem Cont.app {T : Type w₁} {B : T → Type w₂} [∀ t, Dom (B t)] {f : D → (t : T) → B t}
    (hf : Cont f) (t : T) : Cont (fun d => f d t) := Proofs.Cont.app hf t
/-- Application to an argument depending on `d`: the function must satisfy the condition. -/
theorem Cont.app₂ {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] {f : D → A → B} {a : D → A}
    (hf : Cont f) (hc : ∀ d, Cont (f d)) (ha : Cont a) : Cont (fun d => f d (a d)) := Proofs.Cont.app₂ hf hc ha
/-- Pairs: the field tuples of a structure, and what a mutual `partial_fixpoint` is packed into. -/
theorem Cont.pair {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] {f : D → A} {g : D → B}
    (hf : Cont f) (hg : Cont g) : Cont (fun d => (⟨f d, g d⟩ : A ×' B)) := Proofs.Cont.pair hf hg
theorem Cont.fst {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] {f : D → A ×' B} (hf : Cont f) :
    Cont (fun d => (f d).1) := Proofs.Cont.fst hf
theorem Cont.snd {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] {f : D → A ×' B} (hf : Cont f) :
    Cont (fun d => (f d).2) := Proofs.Cont.snd hf
theorem Cont.ite {B : Type w₁} [Dom B] (c : Prop) [Decidable c] {t e : D → B}
    (ht : Cont t) (he : Cont e) : Cont (fun d => if c then t d else e d) := Proofs.Cont.ite c ht he
theorem Cont.dite {B : Type w₁} [Dom B] (c : Prop) [Decidable c] {t : c → D → B} {e : ¬c → D → B}
    (ht : ∀ h, Cont (t h)) (he : ∀ h, Cont (e h)) : Cont (fun d => if h : c then t h d else e h d) :=
  Proofs.Cont.dite c ht he
/-- `pure`, `bind`: this is what a supported monad provides. -/
theorem Cont.pure {M : Type u → Type u} [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] {α : Type u} {a : D → α}
    (ha : Cont (inst_1 := Dom.discrete α) a) : Cont (fun d => (pure (a d) : M α)) := Proofs.Cont.pure ha
theorem Cont.bind {M : Type u → Type u} [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] {α β : Type u}
    {m : D → M α} {k : D → α → M β}
    (hm : Cont m) (hk : ∀ a, Cont (fun d => k d a)) : Cont (fun d => m d >>= k d) := Proofs.Cont.bind hm hk

variable {I : Type pu} (F : I → Fam.{pu, v} I → Type v) [∀ k, Shape (F k)]
/-- Projections out of a structure, and `mk` of fields depending on `d`. -/
theorem Cont.unfold {k : I} {f : D → Fix F k} (hf : Cont f) :
    Cont (inst_1 := Shape.dom (F := F k) (Fix F)) (fun d => Fix.unfold F (f d)) := Proofs.Cont.unfold F hf
theorem Cont.fold {k : I} {f : D → F k (Fix F)} (h : ∀ d, Shape.cond F (f d))
    (hf : Cont (inst_1 := Shape.dom (F := F k) (Fix F)) f) : Cont (fun d => Fix.fold F (f d) (h d)) :=
  Proofs.Cont.fold F h hf

/-! `Cont.fst`, `Cont.snd` and `Cont.pair` for the field tuple of a structure, at the `Dom` that the
shape of the tuple gives it (`Shape.dom`, as in `Cont.unfold` and `Cont.fold`), so that a projection
out of a dictionary, and the tuple of a `mk`, are proved without comparing that `Dom` with the one
instance search builds for the whole tuple. -/
section ShapeForms
variable {G : Fam.{pu, v} I → Type w₁} {H : Fam.{pu, v} I → Type w₂} [Shape G] [Shape H]
  {X : Fam.{pu, v} I} [∀ k, Dom (X k)]
theorem Cont.shape_fst {f : D → G X ×' H X} (hf : Cont (inst_1 := Shape.dom (fun X => G X ×' H X) X) f) :
    Cont (inst_1 := Shape.dom G X) (fun d => (f d).1) :=
  @Proofs.Cont.fst D _ _ _ (Shape.dom G X) (Shape.dom H X) f hf
theorem Cont.shape_snd {f : D → G X ×' H X} (hf : Cont (inst_1 := Shape.dom (fun X => G X ×' H X) X) f) :
    Cont (inst_1 := Shape.dom H X) (fun d => (f d).2) :=
  @Proofs.Cont.snd D _ _ _ (Shape.dom G X) (Shape.dom H X) f hf
theorem Cont.shape_pair {f : D → G X} {g : D → H X}
    (hf : Cont (inst_1 := Shape.dom G X) f) (hg : Cont (inst_1 := Shape.dom H X) g) :
    Cont (inst_1 := Shape.dom (fun X => G X ×' H X) X) (fun d => (⟨f d, g d⟩ : G X ×' H X)) :=
  @Proofs.Cont.pair D _ _ _ (Shape.dom G X) (Shape.dom H X) f g hf hg
end ShapeForms

/-- Fixed points: `partial_fixpoint` elaborates to `Lean.Order.fix`, for functions and for
self-referential dictionaries alike. -/
theorem Cont.fix {α : Type w₁} [Dom α] [Lean.Order.CCPO α] [FixCompat α] {f : D → α → α}
    {hm : ∀ d, Lean.Order.monotone (f d)}
    (hf : Cont (fun p : D ×' α => f p.1 p.2)) : Cont (fun d => Lean.Order.fix (f d) (hm d)) := Proofs.Cont.fix hf
end Cont

/-! `FixCompat α`: the `Dom` and `CCPO` structures on `α` agree.  Holds for `M α`, pointwise, and on
products: exactly the types `partial_fixpoint` recurses through. -/
instance {M : Type u → Type u} [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] (α : Type u) : FixCompat (M α) :=
  FixCompat.monad α
instance {T : Type w₁} {B : T → Type w₂} [∀ t, Dom (B t)] [∀ t, Lean.Order.CCPO (B t)] [∀ t, FixCompat (B t)] :
    FixCompat ((t : T) → B t) := FixCompat.pi
instance {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] [Lean.Order.CCPO A] [Lean.Order.CCPO B]
    [FixCompat A] [FixCompat B] : FixCompat (A ×' B) := FixCompat.pprod
instance {I : Type pu} (F : I → Fam.{pu, v} I → Type v) [∀ k, Shape (F k)] (k : I) [Fix.BotTotal F k] :
    FixCompat (Fix F k) := Fix.fixCompat F k

/-- `partial_fixpoint`'s monotonicity obligation, from the condition: write a self-referential
instance as `def inst : Bla Int := Bla.mk … partial_fixpoint monotonicity Cont.monotone (by nonpos_cont)`. -/
theorem Cont.monotone {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] [Lean.Order.CCPO A] [Lean.Order.CCPO B]
    [FixCompat A] [FixCompat B] {f : A → B} (h : Cont f) : Lean.Order.monotone f := Proofs.Cont.monotone h

/-- The forms the tactic looks up by the shape of the body. -/
meta def forms : List Name :=
  [``Cont.pair, ``Cont.fst, ``Cont.snd, ``Cont.ite, ``Cont.dite,
   ``Cont.pure, ``Cont.bind, ``Cont.unfold, ``Cont.fold, ``Cont.fix]

/-- Gets a DiscrTree key from a theorem name.
Works for theormes that return `… → Cont (fun d => body)` -/
meta def contKeys (declName : Name) : MetaM (Array DiscrTree.Key) := do
  let (_, _, concl) ← forallMetaTelescopeReducing (← inferType (← mkConstWithLevelParams declName))
  let_expr Cont D _ _ _ f := concl | throwError "{declName}: not a `Cont` statement"
  DiscrTree.mkPath (f.beta #[← mkFreshExprMVar D])

/-- The store of tagged theorems: a discrimination tree of their names, keyed by `contKeys`. -/
meta initialize nonposContExt : SimpleScopedEnvExtension (Array DiscrTree.Key × Name) (DiscrTree Name) ←
  registerSimpleScopedEnvExtension { addEntry := fun t (ks, n) => t.insertKeyValue ks n, initial := {} }

/-- `@[nonpos_continuous]` on a theorem `… → Cont (fun d => body)` adds it to the store, keyed by the
shape of `body`.  (It can be used in any file importing this one, but not in this file.) -/
meta initialize registerBuiltinAttribute {
  name := `nonpos_continuous
  descr := "continuity theorem, applied by `nonpos_cont`"
  add := fun decl _ kind => do nonposContExt.add (← MetaM.run' (contKeys decl), decl) kind }

/-- Get continuity lemmas from `forms` and `@[nonpos_continuous]` tagged theorems. -/
meta def getContTheorems : MetaM (DiscrTree Name) := do
  forms.foldlM (init := nonposContExt.getState (← getEnv)) fun t n => return t.insertKeyValue (← contKeys n) n

/-! ## 2. The tactic

`nonpos_cont` on a goal `Cont (fun d => body)` looks up the forms and tagged theorems whose shape is
that of `body` (`getContTheorems`) and applies the first that fits.  The forms without a
shape to index are handled directly: a body not depending on `d` is `Cont.const`, a lambda is
`Cont.lam`, and an application with no matching form is peeled by `Cont.app` (last argument not
depending on `d`) or `Cont.app₂` (last argument depending on `d`; the function is then a projection
of a dictionary, whose condition comes from `Fix.cond`, read along the projection's path).  A `match` on a scrutinee not depending on
`d` is split by `cases`, and a remaining definition is unfolded (`delta`).  Around this, the loop
introduces binders, turns a `Shape.cond` goal into its conjuncts with `nonpos_cond_dsimp`, splits
conjunctions, and closes a goal by a hypothesis when one fits.

For performance:
* each step builds its proof term directly (`MVarId.apply`, `applyNamed`), not through tactic
  syntax; `Cont.lam`, `Bla.mk_cont` and `Bla.cond_intro` with their arguments read off the goal
  (`applyWith?`), without unifying them with it;
* the field tuple of a structure, and the projections out of it, are proved with the forms at the
  `Dom` of its shape (`nonposShapePair`, `nonposShapeProj`), and not compared with the `Dom` that
  instance search builds for the whole tuple;
* a lambda that is a tagged theorem's shape up to eta is proved by that theorem in one step;
* a condition is split into its conjuncts by `Bla.cond_intro` (section 4), or else unfolded by
  `dsimp` (no proof term); and its proof is an auxiliary theorem (`nonposCondAux`), so that the
  copies `partial_fixpoint` makes of it (in the definition, the functional, the `unsafe`
  definition and the monotonicity goal) are small;
* `assumption` only compares the goal with the hypotheses of the same head. -/

/-- Inputs an application of `Shape.cond`, and unfolds the functor and Shape instance arguments
so they can be matched against. -/
meta def normCond (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  -- `Shape.cond H x` is `Model.Shape.cond` at the order of the dictionaries
  let e ← if e.isAppOf ``Shape.cond then whnfR e else pure e
  let_expr Model.Shape.cond I F inst X instX x := e | return e
  let F' ← lambdaTelescope (← whnfR F) fun xs b => do mkLambdaFVars xs (← whnfR b)
  return mkAppN (.const ``Model.Shape.cond e.getAppFn.constLevels!) #[I, F', ← whnfR inst, X, instX, x]

open Tactic in
elab "nonpos_cond_norm" : tactic => withMainContext do
  let mut g ← getMainGoal
  g ← g.change (← normCond (← g.getType))
  for d in ← getLCtx do
    let t ← instantiateMVars d.type
    if !d.isImplementationDetail && (t.isAppOf ``Shape.cond || t.isAppOf ``Model.Shape.cond) then
      g ← g.changeLocalDecl d.fvarId (← normCond d.type)
  replaceMainGoal [g]

/-- Simplify `Shape.cond` conditions into a conjunction of `Cont` facts, one for each dictionary
binder, dropping the clauses that are `True`.  First `nonpos_cond_norm` rewrites every `Shape.cond`
in the goal and hypotheses (by definitional unfolding, checked by `change`) so that its functor is a
literal lambda and its instance is built from the pieces of section 2 of `Top.lean`; then `simp` unfolds the `cond`
of each piece. -/
macro "nonpos_cond_simp" loc:(Parser.Tactic.location)? : tactic =>
  `(tactic| (nonpos_cond_norm; simp only [Shape.cond, Model.Shape.cond, Shape.prod, Shape.pi, Shape.arr, Shape.data, Shape.monad,
      Shape.unit, Shape.dict, Shape.dictPointed, Shape.var, Shape.prodInst, Shape.piInst, Shape.arrInst,
      Shape.dataInst, Shape.monadInst, Shape.unitInst, Shape.dictInst, Shape.dictPointedInst, Shape.varInst, true_and, and_true, implies_true, forall_and] $[$loc]?))

/-- `nonpos_cond_simp` by definitional unfolding only (`dsimp`): no proof term, so the proof of a
condition is only the tree of its conjuncts.  What `simp` would also do (dropping `True`
conjuncts, splitting `∀ x, A ∧ B`) is left to `nonpos_cont`'s loop. -/
macro "nonpos_cond_dsimp" : tactic =>
  `(tactic| (nonpos_cond_norm; dsimp only [Shape.cond, Model.Shape.cond, Shape.prod, Shape.pi, Shape.arr, Shape.data,
      Shape.monad, Shape.unit, Shape.dict, Shape.dictPointed, Shape.var, Shape.prodInst, Shape.piInst,
      Shape.arrInst, Shape.dataInst, Shape.monadInst, Shape.unitInst, Shape.dictInst, Shape.dictPointedInst,
      Shape.varInst]))

/-- The proof of `Cont (fun d => fn' d)`, for `fn'` a field of a fixed dictionary `e` applied to
arguments `t₁ … tₖ` that do not depend on `d`: `fn'` is `(Fix.unfold F e).2. … .1 t₁ … tₖ`.  The
condition `Fix.cond F e` has the nested shape of the tuple (a plain field's part is `True`), so it
is read along the same path, then applied to the arguments (past a dictionary binder, its `.2`
first), and its `.1` is the fact.  `none` if `fn'` is not of this form. -/
meta def nonposProjCondProof? (fn' : Expr) : MetaM (Option Expr) := do
  let isProj (e : Expr) := e.isAppOf ``PProd.fst || e.isAppOf ``PProd.snd
  unless isProj fn' && fn'.getAppNumArgs ≥ 3 do return none
  let args := fn'.getAppArgs.extract 3 fn'.getAppNumArgs  -- `t₁ … tₖ`
  let mut e := fn'.getAppArgs[2]!
  let mut path := #[fn'.isAppOf ``PProd.fst]  -- the projections, outermost first (`true` for `.1`)
  while isProj e && e.getAppNumArgs == 3 do
    path := path.push (e.isAppOf ``PProd.fst)
    e := e.appArg!
  unless e.isAppOfArity ``Fix.unfold 5 do return none
  -- `.1` or `.2` of a proof of a conjunction (exposed by unfolding the `Shape` instances)
  let part (pf : Expr) (left : Bool) : MetaM Expr := do
    let_expr And a b := (← whnf (← inferType pf)) | throwError "not a conjunction"
    return mkApp3 (mkConst (if left then ``And.left else ``And.right)) a b pf
  try
    let mut pf ← mkAppOptM ``Fix.cond (e.getAppArgs.map some)
    for left in path.reverse do pf ← part pf left
    for t in args do
      pf ← if (← whnf (← inferType pf)).isForall then pure (mkApp pf t) else pure (mkApp (← part pf false) t)
    return some (← part pf true)
  catch _ => return none

syntax "nonpos_cont" (num)? : tactic
syntax "nonpos_cont_peel" : tactic

/-- `#[G, H, iG, iH]` if the `Shape` instance `inst` unfolds to `Shape.prod G H` (with `iG`, `iH`). -/
meta partial def shapeProdArgs? (inst : Expr) : MetaM (Option (Array Expr)) := do
  let inst ← whnfCore inst
  if inst.isAppOfArity ``Shape.prod 5 then return some (inst.getAppArgs.extract 1 5)
  match ← unfoldDefinition? inst with
  | some e => shapeProdArgs? e
  | none => return none

/-- `#[A, B, iA, iB]` if the `Dom` instance `inst` is `instDomPProd A B iA iB` (up to unfolding). -/
meta partial def pprodDomArgs? (inst : Expr) (fuel : Nat := 8) : MetaM (Option (Array Expr)) := do
  let inst ← whnfCore inst
  if inst.isAppOfArity ``instDomPProd 4 then return some inst.getAppArgs
  if fuel == 0 then return none
  match ← unfoldDefinition? inst with
  | some e => pprodDomArgs? e (fuel - 1)
  | none => return none

/-- The projection `fun d => (Fix.unfold F (g d)).2. … .1` (with `path`, outermost first, `true` for
`.1`) of structure `k`, from `Bla.unfold_cont` (section 4): `Cont.fst` and `Cont.snd`, with the parts
of the instance `instDomPProd …` of the tuple.  The goal `Cont g`, or `none` (on any failure). -/
meta def unfoldContChain? (goal : MVarId) (D iD : Expr) (n : Name) (dTy gd : Expr) (bi : BinderInfo)
    (k : Expr) (path : Array Bool) : MetaM (Option MVarId) := do
  let some ctor := k.getAppFn.constName? | return none
  let lem := ctor.getPrefix.getPrefix.getPrefix ++ Name.mkSimple ctor.getString! ++ `unfold_cont
  unless (← getEnv).contains lem do return none
  try
    let gFun := Expr.lam n dTy gd bi
    let hg ← mkFreshExprSyntheticOpaqueMVar (← mkAppOptM ``Cont #[D, none, iD, none, gFun])
    let mut pf ← mkAppOptM lem ((k.getAppArgs.map some) ++ #[some D, some iD, some gFun, some hg])
    let some iT := (← inferType pf).getAppArgs[3]? | return none
    let mut inst := iT
    for isFst in path.reverse do
      let some ab ← pprodDomArgs? inst | return none
      pf ← mkAppOptM (if isFst then ``Cont.fst else ``Cont.snd)
        #[D, iD, ab[0]!, ab[1]!, ab[2]!, ab[3]!, none, pf]
      inst := if isFst then ab[2]! else ab[3]!
    unless ← isDefEq (← goal.getType) (← inferType pf) do return none
    goal.assign pf
    return some hg.mvarId!
  catch _ => return none

open Tactic in
/-- A field of a varying dictionary, `fun d => (Fix.unfold F (g d)).2. … .1`: proved inside out, from
`Cont.unfold` (at the `Dom` of the shape of the tuple) by `Cont.shape_snd` and `Cont.shape_fst`, with
the parts read from the `Shape` instances, so that only the field's own `Dom` is
compared with the goal's (comparing the `Dom` of the whole tuple with the one instance search
builds would go through all the fields).  Leaves the goal `Cont g`.  `false` (and no change) if the
goal is not of this form. -/
meta def nonposShapeProj (goal : MVarId) (D iD f : Expr) : TacticM Bool := do
  let .lam n dTy body bi := f | return false
  let mut e := body
  let mut path : Array Bool := #[]  -- the projections, outermost first (`true` for `.1`)
  while e.isAppOfArity ``PProd.fst 3 || e.isAppOfArity ``PProd.snd 3 do
    path := path.push (e.isAppOfArity ``PProd.fst 3)
    e := e.appArg!
  if path.isEmpty || !e.isAppOfArity ``Fix.unfold 5 then return false
  let args := e.getAppArgs  -- `I F inst k (g d)`
  let (F, inst, k, gd) := (args[1]!, args[2]!, args[3]!, args[4]!)
  if F.hasLooseBVars || inst.hasLooseBVars || k.hasLooseBVars then return false
  let s ← saveState
  -- with `Bla.unfold_cont`: the chain at the `Dom` that instance search builds for the tuple
  if let some r ← unfoldContChain? goal D iD n dTy gd bi k path then
    replaceMainGoal [r]; return true
  s.restore
  try
    let gFun := Expr.lam n dTy gd bi
    let hg ← mkFreshExprSyntheticOpaqueMVar (← mkAppOptM ``Cont #[D, none, iD, none, gFun])
    let mut pf ← mkAppOptM ``Cont.unfold #[D, iD, none, F, inst, k, gFun, hg]
    -- `pf : Cont (inst_1 := Shape.dom (F k) X) …`: the family `X` and its `Dom`s
    let some iU := (← inferType pf).getAppArgs[3]? | throwError "unexpected"
    let (X, iX) := (iU.getAppArgs[3]!, iU.getAppArgs[4]!)
    let mut iP := mkApp inst k  -- the `Shape` instance of the current tuple
    for isFst in path.reverse do
      let some gh ← shapeProdArgs? iP | throwError "not a pair"
      pf ← mkAppOptM (if isFst then ``Cont.shape_fst else ``Cont.shape_snd)
        #[D, iD, none, gh[0]!, gh[1]!, gh[2]!, gh[3]!, X, iX, none, pf]
      iP := if isFst then gh[2]! else gh[3]!
    unless ← isDefEq (← goal.getType) (← inferType pf) do throwError "type mismatch"
    goal.assign pf
    replaceMainGoal [hg.mvarId!]
    return true
  catch _ =>
    s.restore
    return false

/-- Apply the theorem `n` to `g`, as `apply n`: the new goals, or `none` (and no change) if it does
not apply. -/
meta def applyConst? (g : MVarId) (n : Name) : MetaM (Option (List MVarId)) := do
  let s ← saveState
  try return some (← g.apply (← mkConstWithFreshMVarLevels n) { synthAssignedInstances := false })
  catch _ => s.restore; return none

/-- Apply the theorem `n` to `g`, with the arguments named in `named` given (as
`apply n (x := e) …`): its conclusion is unified with the goal, its remaining instance arguments are
synthesized, and its remaining explicit arguments are the new goals. -/
meta def applyNamed (g : MVarId) (n : Name) (named : Array (Name × Expr)) : MetaM (List MVarId) := do
  let c ← mkConstWithFreshMVarLevels n
  let names ← getParamNames n
  let (mvs, bis, concl) ← forallMetaTelescopeReducing (← inferType c)
  for (nm, v) in named do
    let some i := names.idxOf? nm | throwError "nonpos_cont: {n} has no argument {nm}"
    unless ← isDefEq mvs[i]! v do throwError "nonpos_cont: cannot give {nm} to {n}"
  unless ← isDefEq concl (← g.getType) do throwError "nonpos_cont: {n} does not apply"
  for m in mvs, bi in bis do
    if bi.isInstImplicit && !(← m.mvarId!.isAssigned) then
      unless ← isDefEq m (← synthInstance (← inferType m)) do throwError "nonpos_cont: instance of {n}"
  g.assign (mkAppN c mvs)
  let mut gs := #[]
  for m in mvs, bi in bis do
    if bi.isExplicit && !(← m.mvarId!.isAssigned) then gs := gs.push m.mvarId!
  return gs.toList

open Tactic in
/-- Peel the last argument of an application, or unfold its head: the new goals. -/
meta def nonposContPeel (g : MVarId) : TacticM (List MVarId) := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let_expr Cont _ _ _ _ f := ty | throwError "nonpos_cont: not a `Cont` goal"
  let env ← getEnv
  let f ← instantiateMVars f
  let f ← if f.isLambda then pure f else etaExpand f
  lambdaTelescope f fun ds body => do
    let d := ds[0]!
    let body := body.consumeMData.headBeta
    let dep (e : Expr) := e.containsFVar d.fvarId!
    let lam (e : Expr) : MetaM Expr := mkLambdaFVars #[d] e
    let isProj (e : Expr) := e.isAppOfArity ``Fix.unfold 5
    let fn := body.getAppFn
    let args := body.getAppArgs
    let unfoldable := fn.constName?.bind fun c => if (env.find? c).any (·.hasValue) then some c else none
    if args.isEmpty then throwError "nonpos_cont: no form matches {← ppExpr body}"
    let a := args.back!
    let fn' := mkAppN fn args.pop
    if !dep a then return ← applyNamed g ``Cont.app #[(`f, ← lam fn'), (`t, a)]
    if let some u := fn'.find? isProj then
      if a == d && !dep u then
        if !dep fn' then
          if let some pf ← nonposProjCondProof? fn' then g.assign pf; return []
        throwError "nonpos_cont: continuity of {← ppExpr fn'} in its dictionary argument is not known"
      return ← applyNamed g ``Cont.app₂ #[(`f, ← lam fn'), (`a, ← lam a)]
    if let some c := unfoldable then
      setGoals [g]; evalTactic (← `(tactic| delta $(mkIdent c):ident)); return ← getGoals
    if a == d then throwError "nonpos_cont: continuity of {← ppExpr fn'} is not known"
    applyNamed g ``Cont.app₂ #[(`f, ← lam fn'), (`a, ← lam a)]

/-- `e` eta-reduced, through metadata and beta-redexes: `fun x => (fun y => g y) x` is `g`. -/
meta partial def etaFull (e : Expr) : Expr :=
  match e.consumeMData.headBeta with
  | .lam n t b bi =>
    match etaFull b with
    | .app f (.bvar 0) => if f.hasLooseBVar 0 then .lam n t (.app f (.bvar 0)) bi else f.lowerLooseBVars 1 1
    | b => .lam n t b bi
  | .app f a => .app (etaFull f) a
  | e => e

/-- The head of a function `f`, up to eta: of its body if it is a lambda (a loose `bvar` if that is
the bound variable), else of `f`. -/
meta def funHead (f : Expr) : Expr :=
  match etaFull f with
  | .lam _ _ b _ => b.consumeMData.getAppFn
  | f => f.getAppFn

/-- Apply the theorem `n` to `g` with its arguments given in order (`some e`), or left as new goals
(`none`, for its hypotheses), without unifying its arguments with the goal: only its
conclusion is compared with the goal (which, built from the goal's own pieces, it equals).  The new
goals, or `none` (and no change). -/
meta def applyWith? (g : MVarId) (n : Name) (vals : Array (Option Expr)) : MetaM (Option (List MVarId)) := do
  let s ← saveState
  try
    let c ← mkConstWithFreshMVarLevels n
    let mut ty ← inferType c  -- not instantiated as we go (each step would walk the rest of the type)
    let mut args := #[]
    let mut goals := #[]
    for gv in vals do
      let .forallE _ d b _ := ty | s.restore; return none
      let a ← match gv with
        | some e => pure e
        | none => do
          let m ← mkFreshExprSyntheticOpaqueMVar (d.instantiateBetaRevRange 0 args.size args)
          goals := goals.push m.mvarId!
          pure m
      args := args.push a
      ty := b
    if ty.isForall then s.restore; return none
    -- substituted with beta-reduction where an argument lands in head position (`(fun x => …) a`),
    -- as Lean instantiates binders: the conclusion is then the goal itself (with its metavariables
    -- instantiated), which the comparison sees at once
    unless ← isDefEq (ty.instantiateBetaRevRange 0 args.size args) (← instantiateMVars (← g.getType)) do
      s.restore; return none
    g.assign (mkAppN c args)
    return some goals.toList
  catch _ => s.restore; return none

/-- The number of leading `∀`s of `e`. -/
meta def forallArity : Expr → Nat
  | .forallE _ _ b _ => forallArity b + 1
  | _ => 0

/-- `Cont.lam` on a goal `Cont f` at `instDomForall T B iB` (a function type), from the pieces of the
goal. -/
meta def lamDirect? (g : MVarId) : MetaM (Option (List MVarId)) := do
  let ty ← instantiateMVars (← g.getType)
  let_expr Cont D _ iD iB f := ty | return none
  unless iB.isAppOfArity ``instDomForall 3 do return none
  let a := iB.getAppArgs  -- `T B iB'`
  applyWith? g ``Cont.lam #[D, iD, a[0]!, a[1]!, a[2]!, f, none]

/-- `Bla.mk_cont` (the theorem `n`) on a goal `Cont (fun d => Bla.mk ps (f₁ d) … (fₙ d) (h d))`, from
the pieces of the goal. -/
meta def mkContDirect? (g : MVarId) (n : Name) : MetaM (Option (List MVarId)) := do
  let ty ← instantiateMVars (← g.getType)
  let_expr Cont D _ iD _ f := ty | return none
  let .lam dn dt body bi := f | return none
  let args := body.getAppArgs  -- `ps f₁ … fₙ h`, with `d` loose
  let total := forallArity (← getConstInfo n).type
  -- `mk_cont` takes `ps D iD f₁ … fₙ h` then `n` hypotheses: `total = |ps| + 2 + 2n + 1`
  if total < args.size + 2 then return none
  let nf := total - args.size - 2
  let np := args.size - nf - 1
  let lam (e : Expr) := Expr.lam dn dt e bi
  let vals := (args.extract 0 np).map some ++ #[some D, some iD] ++
    (args.extract np args.size).map (some ∘ lam) ++ Array.replicate nf none
  applyWith? g n vals

/-- What `nonposContStep` does on a goal. -/
meta inductive ContAct where
  | thms (ns : Array Name)  -- the first of these theorems that applies, else `nonposContPeel`
  | tac (stx : TSyntax `tactic)  -- a tactic

open Tactic in
/-- Run a `ContAct` on the main goal. -/
meta def runContAct : ContAct → TacticM Unit
  | .thms ns => do
    let g ← getMainGoal
    for n in ns do
      let direct ← do
        if n == ``Cont.lam then lamDirect? g
        else if n.getString! == "mk_cont" then mkContDirect? g n
        else pure none
      if let some gs := direct then replaceMainGoal gs; return
      if let some gs ← applyConst? g n then
        replaceMainGoal gs; return
    replaceMainGoal (← nonposContPeel g)
  | .tac stx => evalTactic stx

open Tactic in
/-- A tuple `fun d => ⟨a, b⟩` at the `Dom` of a shape, `Shape.dom P X` (the field tuple of a `mk`, as
`Cont.fold` leaves it): `Cont.shape_pair`, with the parts read from `P`'s `Shape` instance, so that
the `Dom` of the tuple is not compared with the one instance search builds (which would go through
all the fields).  `false` (and no change) if the goal is not of this form. -/
meta def nonposShapePair (goal : MVarId) (D iD iB f : Expr) : TacticM Bool := do
  let .lam _ _ body _ := f | return false
  unless body.isAppOfArity ``PProd.mk 4 && iB.isAppOfArity ``Shape.dom 5 do return false
  let a := iB.getAppArgs  -- `I P iP X iX`
  let some gh ← shapeProdArgs? a[2]! | return false
  let s ← saveState
  try
    let lem ← mkAppOptM ``Cont.shape_pair #[D, iD, none, gh[0]!, gh[1]!, gh[2]!, gh[3]!, a[3]!, a[4]!]
    replaceMainGoal (← goal.apply lem { synthAssignedInstances := false })
    return true
  catch _ =>
    s.restore
    return false

open Tactic in
/-- One step on a goal `Cont (fun d => body)`. -/
meta partial def nonposContStep (tree : DiscrTree Name) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let_expr Cont D _ iD iB f := ty | throwError "nonpos_cont: not a `Cont` goal:{indentExpr ty}"
  let f ← instantiateMVars f
  let f ← if f.isLambda then pure f else etaExpand f
  if ← nonposShapeProj g D iD f then return
  if ← nonposShapePair g D iD iB f then return
  let act ← lambdaTelescope f fun ds body => do
    let d := ds[0]!
    let body := body.consumeMData.headBeta
    let dep (e : Expr) := e.containsFVar d.fvarId!
    if !dep body then return .thms #[``Cont.const]
    if ds.size > 1 || body.isLambda then
      -- `fun d => fun xs => c … d xs` is `fun d => c … d` up to eta: if a tagged theorem has that
      -- shape, it proves the goal in one step (instead of `Cont.lam`, then `Cont.app` per binder)
      let fe := f.eta
      let pat ← if fe.isLambda then pure (fe.bindingBody!.instantiate1 (← mkFreshExprMVar (← inferType d)))
        else pure (mkApp fe (← mkFreshExprMVar (← inferType d)))
      if !pat.isLambda then return .thms ((← tree.getMatch pat).push ``Cont.lam)
      return .thms #[``Cont.lam]
    if body == d then return .thms #[``Cont.id]
    if body.isLet then return .tac (← `(tactic| dsimp only))
    if let some info := Meta.isMatcherAppCore? (← getEnv) body then
      let disc := body.getAppArgs[info.getFirstDiscrPos]!
      if !dep disc then
        if disc.isFVar then
          return .tac (← `(tactic| cases $(mkIdent (← disc.fvarId!.getUserName)):ident <;> dsimp only))
        return .tac (← `(tactic| (generalize $(← Term.exprToSyntax disc) = x; cases x <;> dsimp only)))
    -- the forms and tagged theorems with the shape of the body
    let pattern := body.replaceFVar d (← mkFreshExprMVar (← inferType d))
    return .thms (← tree.getMatch pattern)
  runContAct act

open Tactic in
/-- Peel the last argument of an application, or unfold its head. -/
elab_rules : tactic
  | `(tactic| nonpos_cont_peel) => do replaceMainGoal (← nonposContPeel (← getMainGoal))

/-- `assumption` on a goal `Cont f`, trying only the hypotheses `Cont g` where `g` has the head of `f`
(`funHead`): with many hypotheses (`Bla.mk_cont` has one per field), comparing the goal with each is
the cost. -/
meta def contAssumption (g : MVarId) (f : Expr) : MetaM Bool := g.withContext do
  let hf := funHead (← instantiateMVars f)
  for ld in ← getLCtx do
    if ld.isImplementationDetail then continue
    let t ← instantiateMVars ld.type
    let_expr Cont _ _ _ _ g' := t | continue
    unless funHead g' == hf do continue
    if ← isDefEq t (← g.getType) then g.assign ld.toExpr; return true
  return false

/-- On a goal `Shape.cond ⟨f₁, …, fₙ⟩` of structure `Bla` (its `F` is `G.F (G.I.Bla …)`), apply
`Bla.cond_intro` (section 4): the new goals are the conjuncts of the condition.  `none` if there is
no such lemma or it does not apply. -/
meta def condIntro? (g : MVarId) (ty : Expr) : MetaM (Option (List MVarId)) := do
  let_expr Model.Shape.cond _ F _ _ _ _ := ty | return none
  let some ctor := F.appArg!.getAppFn.constName? | return none
  -- `ctor` is `ns.G.I.Bla`
  let lem := ctor.getPrefix.getPrefix.getPrefix ++ Name.mkSimple ctor.getString! ++ `cond_intro
  unless (← getEnv).contains lem do return none
  let_expr Model.Shape.cond _ _ _ _ _ x := ty | return none
  -- the fields of the tuple `⟨f₁, …, fₙ, ⟨⟩⟩`
  let mut fs := #[]
  let mut x := x
  while x.isAppOfArity ``PProd.mk 4 do
    fs := fs.push x.appFn!.appArg!
    x := x.appArg!
  let ps := F.appArg!.getAppArgs
  let nh := forallArity (← getConstInfo lem).type - ps.size - fs.size
  if let some gs ← applyWith? g lem ((ps ++ fs).map some ++ Array.replicate nh none) then return some gs
  -- otherwise by unification (then the conjuncts, with the fields substituted, beta-reduced)
  let some gs ← applyConst? g lem | return none
  gs.mapM fun m => do m.change (← Core.betaReduce (← instantiateMVars (← m.getType)))

open Tactic in
meta partial def nonposContLoop (tree : DiscrTree Name) (fuel : Nat) : TacticM Unit := do
  let gs ← getUnsolvedGoals
  let some g := gs[0]? | return
  if fuel == 0 then throwError "nonpos_cont: no progress on{indentD (← g.withContext do Meta.ppGoal g)}"
  setGoals [g]
  let ty ← g.withContext do whnfR (← instantiateMVars (← g.getType))
  if ty.isForall then replaceMainGoal [(← g.intro1).2]
  else if ty.isAppOf ``Model.Shape.cond then
    match ← condIntro? g ty with
    | some gs => replaceMainGoal gs
    | none => evalTactic (← `(tactic| nonpos_cond_dsimp))
  else if ty.isAppOf ``Cont then
    unless ← contAssumption g ty.appArg! do nonposContStep tree
  else if ty.isConstOf ``True then g.assign (mkConst ``True.intro)
  else if ty.isAppOf ``And then replaceMainGoal (← g.apply (mkConst ``And.intro))
  else throwError "nonpos_cont: unexpected goal{indentExpr ty}"
  let gs' ← getUnsolvedGoals
  setGoals (gs' ++ gs.drop 1)
  nonposContLoop tree (fuel - 1)

open Tactic in
/-- `nonposContLoop` on a goal `Shape.cond …` (the condition of a `mk`), with the proof packaged as an
auxiliary theorem.  `partial_fixpoint` copies the condition of a self-referential definition: into
the definition, its functional, its `unsafe` version, and the monotonicity goal (whose `mk` takes
it).  Each copy is then that theorem applied to a few arguments, and the kernel checks the proof
once.  A recursive call `r a₁ … aₙ` in the goal is first generalized to a variable `self` (the
theorem is over `self`, and applied to `r a₁ … aₙ`): abstracted as a function, `r` would no longer
be applied to its fixed parameters, which `partial_fixpoint` needs to see. -/
meta def nonposCondAux (tree : DiscrTree Name) (fuel : Nat) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let lctx ← getLCtx
  let isRec (e : Expr) := e.getAppFn.isFVar && (lctx.find? e.getAppFn.fvarId!).any (·.isAuxDecl)
  let (self?, body) ← match ty.find? isRec with
    | some r => pure (some r, ← kabstract ty r)
    | none => pure (none, ty)
  let selfTy ← match self? with
    | some r => inferType r
    | none => pure (mkConst ``Unit)
  let pf ← withLocalDeclD `self selfTy fun self => do
    let ty' := body.instantiate1 self
    let m ← mkFreshExprSyntheticOpaqueMVar ty'
    setGoals [m.mvarId!]
    nonposContLoop tree fuel
    mkLambdaFVars #[self] (← mkAuxTheorem ty' (← instantiateMVars m) (zetaDelta := true))
  g.assign (pf.beta #[self?.getD (mkConst ``Unit.unit)])
  setGoals []

open Tactic in
/-- `nonpos_cont` with fuel `fuel`: `nonposCondAux` on a condition, `nonposContLoop` otherwise. -/
meta def nonposCont (fuel : Nat) : TacticM Unit := do
  let tree ← getContTheorems
  let ty ← whnfR (← instantiateMVars (← (← getMainGoal).getType))
  if ty.isAppOf ``Model.Shape.cond then nonposCondAux tree fuel else nonposContLoop tree fuel

elab_rules : tactic
  | `(tactic| nonpos_cont) => nonposCont 300
  | `(tactic| nonpos_cont $n:num) => nonposCont n.getNat

/-! ## 3. Continuity lemmas for functions

For performance, `nonpos_continuity` proves continuity lemmas for a function.

`nonpos_continuity f` proves, once, for each argument `x` of `f` whose type is one of the structures
(a `Fix`):
```
∀ (the arguments of f before x), Cont (f (the arguments before x))
```
that is, "`f` is continuous in `x`", and tags it `@[nonpos_continuous]`.
-/

/-- The statements `∀ (args before x), Cont (f args before)` for the arguments `x` of `f` whose
type is a structure, with their names `f.cont_j` (`j` the index of `x`). -/
meta def continuityStatements (f : Name) : MetaM (Array (Name × Expr)) := do
  let info ← getConstInfo f
  let lvls := info.levelParams.map fun _ => Level.zero
  forallTelescope (info.type.instantiateLevelParams info.levelParams lvls) fun xs _ => do
    let mut out := #[]
    for j in [0:xs.size] do
      unless (← whnfR (← inferType xs[j]!)).isAppOf ``Fix do continue
      let before := xs.extract 0 j
      let stmt ← mkForallFVars before (← mkAppM ``Cont #[mkAppN (Lean.mkConst f lvls) before])
      out := out.push (f ++ Name.mkSimple s!"cont_{j}", stmt)
    return out

/-- Prove a statement with `nonpos_cont` and add it as a theorem. -/
meta def proveContinuity (lemmaName : Name) (stmt : Expr) : TermElabM Unit := do
  let mvar ← mkFreshExprMVar stmt
  let goals ← Lean.Elab.Tactic.run mvar.mvarId! (nonposContLoop (← getContTheorems) 5000)
  unless goals.isEmpty do throwError "goals remain"
  addDecl (Declaration.thmDecl ⟨⟨lemmaName, [], stmt⟩, ← instantiateMVars mvar, [lemmaName]⟩)

elab "nonpos_continuity " id:ident : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverload id
  let stmts ← try liftTermElabM <| continuityStatements f catch e => do
    logWarning m!"nonpos_continuity: could not state the continuity theorems of {f} \
      ({e.toMessageData}); nonpos_cont will unfold {f} instead"
    pure #[]
  for (lemmaName, stmt) in stmts do
    try
      liftTermElabM <| proveContinuity lemmaName stmt
      elabCommand (← `(attribute [nonpos_continuous] $(mkIdent lemmaName)))
    catch e =>
      logWarning m!"nonpos_continuity: could not prove {lemmaName} ({e.toMessageData}); \
        nonpos_cont will unfold {f} instead"

/-! ## 4. The lemmas of each structure

`nonpos_structure` (`Command.lean`) also proves, by calling `elabGroupLemmas` (below), once for
each structure `Bla`, these facts.  (This section also implements `nonpos_proj_mk`, the tactic that
proves the `simp` lemmas `Bla.f_mk` stated by `Command.lean`, from a lemma
`Bla.mk_unfold : Fix.unfold F (Bla.mk f₁ … fₙ h) = ⟨f₁, …, fₙ⟩` that it proves once per structure.)
They are all for performance: each would otherwise be derived from the whole tuple of fields at
each use.  The ones built as terms (rather than elaborated from syntax) are built so to avoid
re-elaborating the tuple for each lemma, or a slow comparison by the elaborator of two `Dom`s which
the kernel checks quickly.
* `Bla.cond_intro`: the condition of `mk` from its conjuncts (`condIntroLemma`), so that
  `nonpos_cont` does not unfold the condition of each `mk` (and the kernel does not check that
  unfolding again and again).
* `Bla.unfold_cont`: `Fix.unfold` is continuous at the `Dom` that instance search builds for the
  tuple (`unfoldContLemma`), so that a projection out of a varying dictionary is proved by
  `Cont.fst` and `Cont.snd` with the parts of that instance.
* `Bla.mk_cont`: `mk` is continuous in its fields.  From `Cont f₁`, ..., `Cont fₙ` it gives
  `Cont (fun d => Bla.mk (f₁ d) ... (fₙ d) (h d))`.  It is proved with `nonpos_cont` and tagged
  `@[nonpos_continuous]`, so that on a `mk` (the body of a self-referential instance) the tactic is
  left with one goal per field.
* `Bla.botTotal`: `Fix.BotTotal` of the structure, as an instance, when instance search finds it at
  every value of the parameters (it does not when the structure has a plain field of unpointed
  type).  The `CCPO` instance of the structure, which `partial_fixpoint` and `Cont.monotone` look
  for, then does not re-derive it field by field at each search.
-/

/-- `Bla.unfold_cont : ∀ params {D} [Dom D] (g : D → Bla params), Cont g → Cont (fun d => Fix.unfold F (g d))`,
at the `Dom` that instance search builds for the tuple of fields (`instDomPProd …`), rather than at
the `Dom` of its shape as in `Cont.unfold`.  A projection out of a varying dictionary is then
proved by `Cont.fst` and `Cont.snd` with the parts of that instance (`nonposShapeProj`).  The two
`Dom`s are the same, which the kernel checks quickly; the proof is built as a term, so that the
elaborator does not compare them (slowly). -/
meta def unfoldContLemma (structName lemName : Name) : TermElabM Unit := do
  let info ← getConstInfo structName
  forallTelescope info.type fun ps _ => do
    let e ← whnfR (mkAppN (mkConst structName (info.levelParams.map Level.param)) ps)
    unless e.isAppOfArity ``Fix 4 do throwError "{structName} is not a structure of a group"
    let a := e.getAppArgs  -- `I F inst k`
    let u := Level.param `u_nonpos
    withLocalDecl `D .implicit (.sort (.succ u)) fun D => do
    withLocalDecl `iD .instImplicit (← mkAppM ``Dom #[D]) fun iD => do
    withLocalDeclD `g (← mkArrow D e) fun g => do
    withLocalDeclD `hg (← mkAppOptM ``Cont #[D, e, iD, none, g]) fun hg => do
      let T := mkApp2 a[1]! a[3]! (mkApp2 (mkConst ``Fix (e.getAppFn.constLevels!)) a[0]! a[1]! |>.app a[2]!)
      let instT ← synthInstance (← mkAppM ``Dom #[T])
      let body ← withLocalDeclD `d D fun d => do
        mkLambdaFVars #[d] (← mkAppOptM ``Fix.unfold #[a[0]!, a[1]!, a[2]!, a[3]!, mkApp g d])
      let type ← mkForallFVars (ps ++ #[D, iD, g, hg]) (← mkAppOptM ``Cont #[D, T, iD, instT, body])
      let value ← mkLambdaFVars (ps ++ #[D, iD, g, hg])
        (← mkAppOptM ``Cont.unfold #[D, iD, a[0]!, a[1]!, a[2]!, a[3]!, g, hg])
      let type ← instantiateMVars type
      let value ← instantiateMVars value
      let lps := (collectLevelParams (collectLevelParams {} type) value).params.toList
      addDecl (Declaration.thmDecl { name := lemName, levelParams := lps, type, value })

/-- `Bla.mk_cont : ∀ ps {D} [Dom D] (g₁ : D → τ₁) … (gₙ : D → τₙ) (h : ∀ d, Shape.cond ⟨g₁ d, …⟩),
Cont g₁ → … → Cont gₙ → Cont (fun d => Bla.mk ps (g₁ d) … (gₙ d) (h d))`, its statement built from
the type of `mk` (not elaborated from syntax), and proved by `nonpos_cont`. -/
meta def mkContLemma (mkName lemName : Name) (nf : Nat) : TermElabM Unit := do
  let info ← getConstInfo mkName
  let lvls := info.levelParams.map Level.param
  forallTelescope info.type fun xs _ => do  -- `xs` is `ps f₁ … fₙ h`
    let np := xs.size - nf - 1
    let (ps, fs, h) := (xs.extract 0 np, xs.extract np (np + nf), xs.back!)
    let u := Level.param `u_nonpos
    withLocalDecl `D .implicit (.sort (.succ u)) fun D => do
    withLocalDecl `iD .instImplicit (← mkAppM ``Dom #[D]) fun iD => do
    let gTys ← fs.mapM fun f => do mkArrow D (← inferType f)
    withLocalDeclsDND (gTys.mapIdx fun i t => (Name.mkSimple s!"g{i}", t)) fun gs => do
    let hTy ← withLocalDeclD `d D fun d => do
      mkForallFVars #[d] ((← inferType h).replaceFVars fs (gs.map (mkApp · d)))
    withLocalDeclD `h hTy fun hh => do
    let cTys ← gs.mapM fun g => mkAppM ``Cont #[g]
    withLocalDeclsDND (cTys.mapIdx fun i t => (Name.mkSimple s!"hc{i}", t)) fun hcs => do
      let fn ← withLocalDeclD `d D fun d => do
        mkLambdaFVars #[d] (mkAppN (mkConst mkName lvls) ((ps ++ gs.map (mkApp · d)).push (mkApp hh d)))
      let stmt ← mkAppM ``Cont #[fn]
      let m ← mkFreshExprSyntheticOpaqueMVar stmt
      let [] ← Tactic.run m.mvarId! (nonposCont 5000) | throwError "mk_cont: not proved"
      let xs' := ps ++ #[D, iD] ++ gs ++ #[hh] ++ hcs
      let type ← instantiateMVars (← mkForallFVars xs' stmt)
      let value ← instantiateMVars (← mkLambdaFVars xs' m)
      addDecl (Declaration.thmDecl { name := lemName, levelParams := info.levelParams ++ [`u_nonpos], type, value })

/-- `∀ x₁ … xₙ, True` (`n ≥ 0`). -/
meta partial def isForallTrue (e : Expr) : Bool :=
  if e.isForall then isForallTrue e.bindingBody! else e.isConstOf ``True

/-- The proof `fun x₁ … xₙ => True.intro` of `∀ x₁ … xₙ, True`. -/
meta partial def forallTrueProof (e : Expr) : Expr :=
  if e.isForall then .lam e.bindingName! e.bindingDomain! (forallTrueProof e.bindingBody!) e.binderInfo
  else mkConst ``True.intro

/-- The conjuncts of a tree of `∧` that are not `∀ …, True`, left to right. -/
meta partial def conjLeaves (e : Expr) (acc : Array Expr) : Array Expr :=
  if e.isAppOfArity ``And 2 then conjLeaves e.appArg! (conjLeaves e.appFn!.appArg! acc)
  else if isForallTrue e then acc else acc.push e

/-- A proof of a tree of `∧`, from the proofs `hs` of its conjuncts that are not `∀ …, True` (from
the `i`-th on); and the index of the next. -/
meta partial def conjProof (hs : Array Expr) (e : Expr) (i : Nat) : Expr × Nat :=
  if e.isAppOfArity ``And 2 then
    let (p, i) := conjProof hs e.appFn!.appArg! i
    let (q, i) := conjProof hs e.appArg! i
    (mkApp4 (mkConst ``And.intro) e.appFn!.appArg! e.appArg! p q, i)
  else if isForallTrue e then (forallTrueProof e, i)
  else (hs[i]!, i + 1)

/-- `Bla.cond_intro : ∀ params f₁ … fₙ, C₁ → … → Cₘ → Shape.cond ⟨f₁, …, fₙ⟩`, with `C₁ … Cₘ` the
conjuncts that are not `True` in the condition unfolded by `nonpos_cond_dsimp`: proved once per
structure, so that `nonpos_cont` does not unfold the condition (and the kernel does not check the
unfolding) in each `mk`. -/
meta def condIntroLemma (mkName lemName : Name) : TermElabM Unit := do
  let info ← getConstInfo mkName
  forallTelescope info.type fun xs _ => do
    let (vs, h) := (xs.pop, xs.back!)
    let hTy ← inferType h
    withErasedFVars #[h.fvarId!] do
    let g ← mkFreshExprSyntheticOpaqueMVar hTy
    let gs ← Tactic.run g.mvarId! (Tactic.evalTactic (← `(tactic| nonpos_cond_dsimp)))
    let [g'] := gs | throwError "unexpected goals"
    let n ← instantiateMVars (← g'.getType)
    let ls := conjLeaves n #[]
    withLocalDeclsDND (ls.mapIdx fun i l => (Name.mkSimple s!"h{i}", l)) fun hs => do
      g'.assign (conjProof hs n 0).1
      let type ← instantiateMVars (← mkForallFVars (vs ++ hs) hTy)
      let value ← instantiateMVars (← mkLambdaFVars (vs ++ hs) g)
      addDecl (Declaration.thmDecl { name := lemName, levelParams := info.levelParams, type, value })

/-- Proves the `simp` lemmas `Bla.f_mk` of the projections, which `Command.lean` states. -/
syntax "nonpos_proj_mk" : tactic

open Tactic in
/-- The proof of `Bla.f_mk : ∀ ps f₁ … fₙ h, Bla.f ps (Bla.mk ps f₁ … fₙ h) = fⱼ` (stated by `Command.lean`):
`congrArg` of the `j`-th component of the tuple on `Fix.unfold_fold`, built as a term (no `simp`,
which goes through the whole tuple). -/
elab_rules : tactic
  | `(tactic| nonpos_proj_mk) => do
    let (_, g) ← (← getMainGoal).intros
    g.withContext do
    let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq? | throwError "nonpos_proj_mk: not an equation"
    -- `Bla.mk ps f₁ … fₙ h` is `Fix.fold F x h`, with `x = ⟨f₁, …, fₙ, ⟨⟩⟩`
    let some fold ← unfoldDefinition? lhs.appArg! | throwError "nonpos_proj_mk: cannot unfold {lhs.appArg!}"
    let fold := fold.headBeta
    unless fold.isAppOfArity ``Fix.fold 6 do throwError "nonpos_proj_mk: unexpected {fold}"
    let a := fold.getAppArgs  -- `I F inst k x h`
    -- `Bla.mk_unfold : ∀ ps f₁ … fₙ h, Fix.unfold F (Bla.mk ps f₁ … fₙ h) = ⟨f₁, …, fₙ, ⟨⟩⟩`, proved
    -- (by `Fix.unfold_fold`) at the first of these lemmas: the kernel checks that the tuple has its
    -- type once per structure, and not once per lemma
    let mkApp := lhs.appArg!
    let some mkName := mkApp.getAppFn.constName? | throwError "nonpos_proj_mk: unexpected {mkApp}"
    let xs := mkApp.getAppArgs
    let lem := mkName.getPrefix ++ `mk_unfold
    let lvls := mkApp.getAppFn.constLevels!
    unless (← getEnv).contains lem do
      let info ← getConstInfo mkName
      let unfold := mkAppN (mkConst ``Fix.unfold fold.getAppFn.constLevels!) (a.extract 0 4 |>.push mkApp)
      let type ← instantiateMVars (← mkForallFVars xs (← mkEq unfold a[4]!))
      let value ← instantiateMVars (← mkLambdaFVars xs (mkAppN (mkConst ``Fix.unfold_fold fold.getAppFn.constLevels!) a))
      addDecl (Declaration.thmDecl { name := lem, levelParams := info.levelParams, type, value })
    let uf := mkAppN (mkConst lem lvls) xs
    -- `fun t => t.2. … .1`, the component of the field `rhs` (up to eta: a field with implicit
    -- binders is `fun {…} => f` in the tuple), with the types of the components read from the
    -- tuple `⟨f₁, ⟨f₂, …⟩⟩` (`PProd.mk α β a b`), so that nothing has to be inferred
    let x := a[4]!
    unless x.isAppOfArity ``PProd.mk 4 do throwError "nonpos_proj_mk: unexpected tuple {x}"
    let get ← withLocalDeclD `t (mkApp2 (mkConst ``PProd x.getAppFn.constLevels!) x.appFn!.appFn!.appFn!.appArg! x.appFn!.appFn!.appArg!) fun t => do
      let mut x := x
      let mut e := t
      while x.isAppOfArity ``PProd.mk 4 do
        let (α, β, ls) := (x.appFn!.appFn!.appFn!.appArg!, x.appFn!.appFn!.appArg!, x.getAppFn.constLevels!)
        if etaFull x.appFn!.appArg! == rhs then return ← mkLambdaFVars #[t] (mkApp3 (mkConst ``PProd.fst ls) α β e)
        e := mkApp3 (mkConst ``PProd.snd ls) α β e
        x := x.appArg!
      throwError "nonpos_proj_mk: {rhs} is not a field of the tuple"
    g.assign (← mkCongrArg get uf)
    replaceMainGoal []

/-- The lemmas of section 4 for each structure of a group made by `nonpos_structure`, given by the
full names of the structures (everything else is read from the environment). -/
meta def elabGroupLemmas (structs : Array Name) : CommandElabM Unit := do
  for bla in structs do
    let some mkInfo := (← getEnv).find? (bla ++ `mk) | throwError "nonpos_structure: no {bla ++ `mk}"
    let blaInfo ← getConstInfo bla
    -- the number of fields: the arguments of `mk` after the parameters, but the condition
    let np := forallArity blaInfo.type
    let nf := forallArity mkInfo.type - np - 1
    -- `Bla.cond_intro`, `Bla.unfold_cont`
    if nf > 0 then
      try liftTermElabM (condIntroLemma (bla ++ `mk) (bla ++ `cond_intro))
      catch e => logWarning m!"nonpos_structure: no `cond_intro` lemma for {bla} ({e.toMessageData})"
      try liftTermElabM (unfoldContLemma bla (bla ++ `unfold_cont))
      catch e => logWarning m!"nonpos_structure: no `unfold_cont` lemma for {bla} ({e.toMessageData})"
    -- `Bla.botTotal : ∀ ps, Fix.BotTotal F k`: only if instance search finds `Fix.BotTotal` for every
    -- value of the parameters (declared with the instance found, rather than searched for again)
    let botName := bla ++ `botTotal
    let found ← liftTermElabM do
      try
        let some (ty, v) ← forallTelescope blaInfo.type fun xs _ => do
            -- `Bla ps` unfolds to `Fix F k`
            let e ← whnfR (mkAppN (mkConst bla (blaInfo.levelParams.map Level.param)) xs)
            unless e.isAppOfArity ``Fix 4 do return none
            let b ← mkAppOptM ``Fix.BotTotal (e.getAppArgs.map some)
            let some i ← synthInstance? b | return none
            return some (← mkForallFVars xs b, ← instantiateMVars (← mkLambdaFVars xs i))
          | return false
        let ty ← instantiateMVars ty
        let lps := (collectLevelParams (collectLevelParams {} ty) v).params.toList
        addDecl (Declaration.thmDecl { name := botName, levelParams := lps, type := ty, value := v })
        return true
      catch _ => return false
    if found then elabCommand (← `(attribute [instance high] $(mkIdent (`_root_ ++ botName))))
    -- `Bla.mk_cont`
    if nf == 0 then continue
    liftTermElabM <| mkContLemma (bla ++ `mk) (bla ++ `mk_cont) nf
    elabCommand (← `(attribute [nonpos_continuous] $(mkIdent (`_root_ ++ bla ++ `mk_cont))))

/-! ## 5. Axioms

The theorems above, with their proofs, use only the standard axioms.  The build fails if this
changes. -/

/-- info: 'NonPos.Cont.fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cont.fold
/-- info: 'NonPos.Cont.fix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cont.fix
/-- info: 'NonPos.Cont.bind' depends on axioms: [Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cont.bind
/-- info: 'NonPos.Cont.monotone' does not depend on any axioms -/
#guard_msgs in #print axioms Cont.monotone

end
end NonPos
