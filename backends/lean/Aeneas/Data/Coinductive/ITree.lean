-- TODO: can we make this a non-public import and hide all CoInd things from clients of this?
import Aeneas.Data.Coinductive.CoInd
import Aeneas.Data.Coinductive.Effect

namespace Aeneas.Data.Coinductive

open Lean.Order

-- compared to the original version at https://github.com/ISTA-PLV/coinductive/tree/main
-- which uses the traditional tau constructor, this version instead has a bottom element
-- div. tau is not needed to guard recursion, since we are using partial_fixpoint
-- instead of coinduction.
inductive ITreeF.{u,v} (E : Effect.{u}) (R : Type v) (ITree : Type (max u v)) : Type (max u v) where
  | ret (r : R)
  | div -- equivalent to infinite tau stream from traditional ITrees
  | vis (i : E.I) (k : E.O i → ITree)


inductive ITreeF.In (E : Effect.{u}) (R : Type v) : Type (max u v) where
  | ret (r : R)
  | div
  | vis (i : E.I)

instance (E : Effect.{u}) (R : Type v) : PF (ITreeF E R) where
  P := ⟨ITreeF.In E R, fun
    | .ret _ => PEmpty
    | .div => PEmpty
    | .vis i => E.O i⟩
  unpack
    | .ret r => .obj (.ret r) nofun
    | .div => .obj .div nofun
    | .vis i k => .obj (.vis i) k
  pack
    | .obj (.ret r) _ => .ret r
    | .obj .div k => .div
    | .obj (.vis i) k => .vis i k
  unpack_pack := by rintro _ ⟨⟩ <;> simp
  pack_unpack := by rintro _ (⟨⟨⟩, _⟩ | ⟨⟨⟩⟩) <;> simp <;> funext x <;> cases x

abbrev ITree.{u, v} (E : Effect.{v}) (R : Type u) : Type (max u v) := CoInd (ITreeF E R)
abbrev ITreeN (E : Effect.{u}) (R : Type u) (n : Nat) : Type u := CoIndN (ITreeF E R) n

variable {E : Effect.{v}} {R : Type u}

def ITree.fold (t : ITreeF E R (ITree E R)) : ITree E R := CoInd.fold _ t
def ITree.ret (r : R) : ITree E R := ITree.fold (.ret r)
def ITree.div : ITree E R := ITree.fold .div
def ITree.vis (i : E.I) (k : E.O i → ITree E R) : ITree E R := ITree.fold (.vis i k)
def ITree.unfold (t : ITree E R) : ITreeF E R (ITree E R) := CoInd.unfold _ t

/- Ideally everything above this would be automatically generated -/

instance : Inhabited (ITreeF E R PUnit) where default := .div

-- TODO: are all these little simp theorems every used or needed?
@[simp]
theorem ITree.unfold_fold (t : ITree E R) :
  ITree.fold (ITree.unfold t) = t := by simp [ITree.fold, ITree.unfold]

@[simp]
theorem ret_approx_1 (r : R) n :
  (ITree.ret (E:=E) r).approx (n + 1) = ITreeF.ret r := by
    simp [ITree.ret, ITree.fold, CoInd.fold, PF.map, PF.pack, PF.unpack]
    --

@[simp]
theorem fold_ret_approx_1 (r : R) n :
  (ITree.fold (ITreeF.ret (E:=E) r)).approx (n + 1) = ITreeF.ret r :=
    ret_approx_1 r n

@[simp]
theorem div_approx_1 n :
  (ITree.div (E:=E) (R:=R)).approx  (n + 1) = ITreeF.div := by
    simp [ITree.div, ITree.fold, CoInd.fold, PF.map, PF.pack, PF.unpack]

@[simp]
theorem fold_div_approx_1 n :
  (ITree.fold (ITreeF.div)).approx (F := ITreeF E R) (n + 1) = ITreeF.div :=
    div_approx_1 n

@[simp]
theorem vis_approx_1 i (t : E.O i → ITree E R) n :
  (ITree.vis i t).approx (n + 1) = ITreeF.vis i (λ o => (t o).approx n) := by
    simp [ITree.vis, ITree.fold, CoInd.fold, PF.map, PF.pack]
    rfl

@[simp]
theorem fold_vis_approx_1 i (t : E.O i → ITree E R) n :
  (ITree.fold (ITreeF.vis i t)).approx (n + 1) = ITreeF.vis i (λ o => (t o).approx n) := vis_approx_1 i t n

@[simp]
theorem unfold_ret (r : R) :
  ITree.unfold (ITree.ret r) = ITreeF.ret (E:=E) r := by
    simp [ITree.ret, ITree.fold, ITree.unfold]

@[simp]
theorem unfold_tau :
  ITree.unfold (E:=E) (R:=R) (ITree.div) = ITreeF.div := by
    simp [ITree.div, ITree.fold, ITree.unfold]

@[simp]
theorem unfold_vis i (t : E.O i → ITree E R) :
  ITree.unfold (ITree.vis i t) = ITreeF.vis i t := by
    simp [ITree.vis, ITree.fold, ITree.unfold]

theorem vis_monoN i (t1 t2 : E.O i → ITree E R) n :
  (∀ o, CoIndN.le _ ((t1 o).approx n) ((t2 o).approx n)) →
  CoIndN.le _ ((ITree.vis i t1).approx (n + 1)) ((ITree.vis i t2).approx (n + 1))
 := by
    intro hs
    simp [CoIndN.le, PF.unpack]
    right
    constructor <;> try rfl
    grind [coherent1]

@[partial_fixpoint_monotone]
theorem vis_mono α [PartialOrder α] i (f : α → E.O i → ITree E R) :
  monotone f →
  monotone (λ x => ITree.vis i (f x)) := by
    intro hf t1 t2 hle
    apply CoInd.le_leN
    rintro ⟨n⟩; simp [CoIndN.le]
    apply vis_monoN
    intro o
    have := hf t1 t2 hle o
    grind [CoInd.leN_le]

def ITree.spin : ITree E R := ITree.div

@[simp]
theorem ITree.bot_eq :
  CoInd.bot (ITreeF E R) = ITree.spin := by
    ext n
    induction n; congr 0
    rw [CoInd.bot_eq, spin]
    simp [PF.map, PF.pack, CoInd.fold, *, PF.unpack, default]

theorem ITree.le_unfold (t1 t2 : ITree E R) :
  (t1 ⊑ t2) = (t1 = .spin ∨
    (∃ r, t1 = .ret r ∧ t2 = .ret r) ∨
    (∃ i t1' t2', t1 = .vis i t1' ∧ t2 = .vis i t2' ∧ ∀ o, t1' o ⊑ t2' o)) := by
    ext
    constructor
    · intro h
      rw [CoInd.le_unfold] at h
      rcases h with (rfl|⟨i, _, _, _, _, h1, h2⟩); simp
      rw [<-Coinductive.unfold_fold _ t1, <-Coinductive.unfold_fold _ t2]
      rw [<-PF.unpack_pack (CoInd.unfold _ t1), <-PF.unpack_pack (CoInd.unfold _ t2)]
      simp only [h1, h2]
      cases i <;> simp [PF.pack, ret, spin, div, vis, fold]
      · grind
      · grind
    · rintro (rfl| ⟨_, rfl, rfl⟩ | ⟨_, _, _, rfl, rfl, _⟩)
      · simp [CoInd.le_unfold]
      · apply PartialOrder.rel_refl
      · simp [CoInd.le_unfold]
        right
        simp [PF.unpack, ITree.vis, ITree.fold]
        constructor <;> try rfl
        grind

-- use Bind.bind instead
def ITree.bind.{w} {S : Type w} (t1 : ITree E R) (t2 : R → ITree E S) :=
  match t1.unfold with
  | .ret r => t2 r
  | .div => .div
  | .vis i k => .vis i (λ o => ITree.bind (k o) t2)
partial_fixpoint

@[simp]
theorem itree_ret_bind {S} r (t : S → ITree E R) :
  ITree.bind (.ret r) t = t r := by
    rw [ITree.bind]
    simp [ITree.ret, ITree.fold, ITree.unfold]

@[simp]
theorem itree_vis_bind {S} i k (t : S → ITree E R) :
  ITree.bind (.vis i k) t = .vis i (λ o => ITree.bind (k o) t) := by
    rw [ITree.bind]
    simp [ITree.vis, ITree.fold, ITree.unfold]

@[simp]
theorem itree_div_bind {S} (t : S → ITree E R) :
  ITree.bind .div t = .div := by
    simp [ITree.bind]


@[partial_fixpoint_monotone]
theorem bind_mono {α} {S} [PartialOrder α]
  (f : α → ITree E R) (g : α → R → ITree E S) :
  monotone f →
  monotone g →
  monotone (λ x => ITree.bind (f x) (g x)) := by
    intro hf hg t1 t2 hle
    apply CoInd.le_leN
    intro n
    dsimp only
    have hlef : (f t1) ⊑ (f t2) := by apply hf; assumption
    generalize f t1 = t1, f t2 = t2 at hlef
    induction n generalizing t1 t2; simp [CoIndN.le]
    unfold ITree.bind
    rw [ITree.le_unfold] at hlef
    rcases hlef with (rfl|⟨_, rfl, rfl⟩|⟨_, _, _, rfl, rfl, _⟩)
    · simp [ITree.spin]
      simp [CoIndN.le, CoIndN.bot]
      left
      simp [ITree.spin]
    · rename_i x
      simp
      have := hg t1 t2 hle x
      grind [CoInd.leN_le, monotone]
    · simp
      apply vis_monoN
      grind [CoInd.leN_le, monotone]


instance : Monad (ITree.{u} E) where
  pure := ITree.ret
  bind := ITree.bind

@[elab_as_elim, cases_eliminator]
def ITree.cases {E : Effect.{u}} {R}
    {motive : ITree E R → Sort v}
    (ret : ∀ r, motive (pure r))
    (div :  motive (.div))
    (vis : ∀ i k, motive (ITree.vis i k))
    (t : ITree E R) : motive t := by
    rw [<-ITree.unfold_fold t]
    cases t.unfold
    · apply ret
    · apply div
    · apply vis

@[simp]
theorem unfold_pure (r : R) :
  ITree.unfold (pure r) = ITreeF.ret (E:=E) r := by
    simp [pure]

@[simp]
theorem pure_approx_1 (r : R) n :
  (pure r : ITree _ _).approx (n + 1) = ITreeF.ret (E:=E) r := by
    simp [pure]

instance : LawfulMonad (ITree E) := LawfulMonad.mk' (ITree E)
  (id_map := by
    simp [Functor.map]
    intro _ t
    ext n
    induction n generalizing t; congr 0
    unfold ITree.bind
    cases t <;> simp [*])
  (pure_bind := by simp [pure, Bind.bind])
  (bind_assoc := by
    simp [Bind.bind]
    intro _ _ _ t1 t2 t3
    ext n
    induction n generalizing t1; congr 0
    rw [ITree.bind.eq_def t1]
    rw [ITree.bind.eq_def t1]
    split <;> simp [*])

instance : MonoBind (ITree E) where
  bind_mono_left := by
    intro _ _ _ _ _ _
    dsimp [Bind.bind]
    apply bind_mono (λ x => x) <;> grind [monotone, PartialOrder.rel_refl]
  bind_mono_right := by
    intro _ _ a _ _ _
    dsimp [Bind.bind]
    apply bind_mono (λ x => a) (λ x => x)
    · grind [monotone, PartialOrder.rel_refl]
    · grind [monotone, PartialOrder.rel_refl]
    · intro _; grind

@[simp]
theorem div_bind (t : S → ITree E R) :
  .div >>= t = .div := by simp [Bind.bind]

@[simp]
theorem vis_bind i k (t : S → ITree E R) :
  (.vis i k) >>= t = .vis i (λ o => k o >>= t) := by simp [Bind.bind]


def Effect.trigger (E₁ : Effect.{u}) {E₂ : Effect.{u}} [E₁ -< E₂] (i : E₁.I) : ITree.{u} E₂ (E₁.O i) :=
  let ⟨i₂, f⟩ := (Subeffect.map i);
  ITree.vis i₂ (λ x => return (f x))

def ITree.iter {α : Type a} {β : Type b} (t : α → ITree E (α ⊕ β)) : α → ITree E β :=
  λ a => do
    bind (t a) λ val =>
    match val with
    | .inl a => .iter t a
    | .inr b => return b
partial_fixpoint

-- TODO: do we need interp?
-- def ITree.interp {F : Effect.{w}} (f : (i : E.I) → ITree F (E.O i)) : ITree E R → ITree F R :=
--   ITree.iter λ t =>
--     match t.unfold with
--     | .ret r => return (.inr r)
--     | .div => ITree.div
--     -- | .vis i k => f i >>= λ o => return (.inl (k o))
--     | .vis i k => bind (f i) λ o => return (.inl (k o))

-- @[simp]
-- theorem interp_pure {F} (f : (i : E.I) → ITree F (E.O i)) (r : R) :
--   ITree.interp f (pure r) = pure r := by
--     unfold ITree.interp ITree.iter ITree.bind
--     simp

-- @[simp]
-- theorem interp_div {F} (f : (i : E.I) → ITree F (E.O i)) :
--   ITree.interp (R:=R) f .div = .div := by
--     unfold ITree.interp
--     rw (occs := [1]) [ITree.iter]
--     simp

-- -- #synth LawfulMonad (ITree E)
-- -- #check instLawfulMonadITree.bind_assoc
-- @[simp]
-- theorem interp_vis {F : Effect.{v}} (f : (i : E.I) → ITree F (E.O i)) i (k : E.O i → ITree E R) :
--   ITree.interp f (ITree.vis i k) = (f i) >>= (λ o => (ITree.interp f (k o))) := by
--     unfold ITree.interp
--     rw (occs := [1]) [ITree.iter]
--     simp
--     rw [instLawfulMonadITree.bind_assoc]
--     simp [(Eq.refl _ : ITree.bind = Bind.bind)]
--     rw [bind_assoc]
    --

-- #synth CCPO (ITree E R)
-- #synth MonoBind (ITree E)
-- #synth Bind (ITree E)

-- TODO: These have been added on top of original library. I'm not sure if there's a better
-- way to do this yet.

-- @[simp, grind .]
theorem not_vis_ret {E} {α} {x : α} {e k} : ¬ ITree.ret (E := E) x = ITree.vis e k := by
  intros eq
  have eq := congrArg (fun i => i.approx 1) eq
  simp at eq

-- @[simp, grind .]
theorem not_ret_div {E} {α} {x : α} : ¬ ITree.ret (E := E) x = ITree.div := by
  intros eq
  have eq := congrArg (fun i => i.approx 1) eq
  simp at eq

-- @[simp, grind .]
theorem not_div_vis {E} {α} {e k} : ¬  @ITree.div α E = ITree.vis e k := by
  intros eq
  have eq := congrArg (fun i => i.approx 1) eq
  simp at eq

-- @[simp, grind .]
theorem ret_inj {E} {α} {x y} : @ITree.ret α E x = ITree.ret y → x = y := by
  intros eq
  have eq := congrArg (fun i => i.approx 1) eq
  simp at eq
  grind only

theorem vis_inj_effect {E} {α} {e1 e2 k1 k2} : @ITree.vis α E e1 k1 = ITree.vis e2 k2
  → e1 = e2 := by
  intros eq
  have eq := congrArg (fun i => i.approx 1) eq
  simp at eq
  grind


-- TODO: probably dont need this:
def Eqrec3.{w, u_1} {α : Sort u_1} {a' : α} {motive : (a : α) → a' = a → Sort w}
  {a'1 : α}
  (t : a' = a'1)
  (refl : motive a'1 t)
  :
  motive a' (Eq.refl a')
  := by
  subst t
  apply refl

-- theorems to make ITree.cases actually compute with simp
@[simp]
theorem ITree.cases.ret {E R motive r d v x}
  : @ITree.cases E R motive r d v (.ret x) = r x := by
  simp [cases]
  -- simp [ITree.ret] -- uncomment to see where the rewrite target is supposed to be in the goal
  have to_rewrite_by : (fold (ITreeF.ret x)).unfold = ITreeF.ret x
    := fold_unfold (ITreeF E R) (ITreeF.ret x)
  -- rw [to_rewrite_by] -- we want to do this.... but we are in transport hell!
  let rwmotive : (i : ITreeF E R (ITree E R)) -> (eq : (fold (ITreeF.ret x)).unfold = i)
    -> Prop := fun i eq =>
      ITreeF.rec (motive := fun t => (fold (ITreeF.ret x)).unfold = t → motive (fold (ITree.ret x).unfold))
        (fun r_1 h => cast (by simp [fold, unfold] at h; rw[unfold_fold]; simp[pure, *] ) (r r_1))
        (fun h => cast (by contradiction) d)
        (fun i k h => cast (by contradiction) (v i k)) i eq = r x
  refine @Eq.rec _ (ITreeF.ret x) rwmotive ?_ _ (Eq.symm to_rewrite_by)
  unfold rwmotive
  simp [cast]

@[simp]
theorem ITree.cases.div {E R motive r d v}
  : @ITree.cases E R motive r d v .div = d := by
  simp [cases]
  -- simp [ITree.div] -- uncomment to see where the rewrite target is supposed to be in the goal
  have to_rewrite_by : (fold ITreeF.div).unfold = ITreeF.div
    := fold_unfold (ITreeF E R) (ITreeF.div)
  -- rw [to_rewrite_by] -- we want to do this.... but we are in transport hell!
  let rwmotive : (i : ITreeF E R (ITree E R)) -> (eq : (fold ITreeF.div).unfold = i)
    -> Prop := fun i eq =>
      ITreeF.rec (motive := fun t => (fold ITreeF.div).unfold = t → motive (fold ITree.div.unfold))
        (fun r_1 h => cast (by contradiction) (r r_1))
        (fun h => cast (by simp [fold, unfold]) d)
        (fun i k h => cast (by contradiction) (v i k)) i eq = d
  refine @Eq.rec _ ITreeF.div rwmotive ?_ _ (Eq.symm to_rewrite_by)
  unfold rwmotive
  simp [cast]

@[simp]
theorem ITree.cases.vis {E R motive r d v e k}
  : @ITree.cases E R motive r d v (.vis e k) = v e k := by
  simp [cases]
  -- simp [ITree.vis] -- uncomment to see where the rewrite target is supposed to be in the goal
  have to_rewrite_by : (fold (ITreeF.vis e k)).unfold = ITreeF.vis e k
    := fold_unfold (ITreeF E R) (ITreeF.vis e k)
  -- rw [to_rewrite_by] -- we want to do this.... but we are in transport hell!
  let rwmotive : (i : ITreeF E R (ITree E R)) -> (eq : (fold (ITreeF.vis e k)).unfold = i)
    -> Prop := fun i eq =>
      ITreeF.rec (motive := fun t => (fold (ITreeF.vis e k)).unfold = t → motive (fold (ITree.vis e k).unfold))
        (fun r_1 h => cast (by contradiction) (r r_1))
        (fun h => cast (by contradiction) d)
        (fun i k h => cast (by simp [fold, unfold] at h; rw [unfold_fold]; grind) (v i k)) i eq = v e k
  refine @Eq.rec _ (ITreeF.vis e k) rwmotive ?_ _ (Eq.symm to_rewrite_by)
  unfold rwmotive
  simp [cast]

-- TODO: delete non-dependent eliminator if we indeed don't need it
-- -- @[cases_eliminator]
-- def ITree.reccases {E : Effect.{u}} {R}
--     {Out : Sort v}
--     (ret : R → Out)
--     (div : Out)
--     (vis : (i : E.I) → (k : E.O i → ITree E R) → Out)
--     (t : ITree E R) : Out := by
--     -- rw [<-ITree.unfold_fold t]
--     cases t.unfold with
--     | ret x => apply ret x
--     | div => apply div
--     | vis e k => apply vis e k

-- #check ITreeF.rec

-- @[simp]
-- theorem ITree.reccases.ret {E R motive r d v x}
--   : @ITree.reccases E R motive r d v (.ret x) = r x := by
--   simp [reccases]
--   simp [ITree.ret]
--   have to_rewrite_by : (fold (ITreeF.ret x)).unfold = ITreeF.ret x
--     := fold_unfold (ITreeF E R) (ITreeF.ret x)
--   -- rw [to_rewrite_by] -- we want to do this.... but we are in transport hell!
--   let rwmotive : (i : ITreeF E R (ITree E R)) -> (eq : (fold (ITreeF.ret x)).unfold = i)
--     -> Prop := fun i eq =>
--       ITreeF.rec (motive := fun t => (fold (ITreeF.ret x)).unfold = t → motive)
--         (fun r_1 h => r r_1) (fun h => d)
--         (fun i k h => v i k) i eq = r x
--   refine @Eq.rec _ (ITreeF.ret x) rwmotive ?_ _ (Eq.symm to_rewrite_by)
--   unfold rwmotive
--   simp

-- @[simp]
-- theorem ITree.reccases.div {E R motive r d v}
--   : @ITree.reccases E R motive r d v .div = d := by
--   -- simp [ITree.div, fold]
--   --
--   rw [<-ITree.unfold_fold (E := E) (ITree.div)]
--   cases h : (ITree.div.unfold) with
--   | div =>
--     simp [reccases]
--     have to_rewrite_by : (fold (ITreeF.div)).unfold = ITreeF.div
--       := fold_unfold (ITreeF E R) (ITreeF.div)
--     -- rw [to_rewrite_by] -- again, rw is not smart enough
--     let motive : (i : ITreeF E R (ITree E R)) -> (eq : (fold (ITreeF.div)).unfold = i)
--       -> Prop := fun i eq =>
--         ITreeF.rec (motive := fun t => (fold (ITreeF.div)).unfold = t → motive)
--           (fun r_1 h => r r_1) (fun h => d)
--           (fun i k h => v i k) i eq = d
--     refine @Eq.rec _ (ITreeF.div) motive ?_ _ (Eq.symm to_rewrite_by)
--     simp [motive]
--   | _ => simp at h

-- @[simp]
-- theorem ITree.reccases.vis {E R motive r d v e k}
--   : @ITree.reccases E R motive r d v (.vis e k) = v e k := by
--   rw [<-ITree.unfold_fold (E := E) (ITree.vis e k)]
--   cases h : (ITree.vis e k).unfold with
--   | vis e' k' =>
--     simp at h
--     cases h
--     subst_vars
--     simp [reccases]
--     have to_rewrite_by : (fold (ITreeF.vis e' k)).unfold = ITreeF.vis e' k
--       := fold_unfold (ITreeF E R) (ITreeF.vis e' k)
--     -- rw [to_rewrite_by] -- again, rw is not smart enough
--     let motive : (i : ITreeF E R (ITree E R)) -> (eq : (fold (ITreeF.vis e' k)).unfold = i)
--       -> Prop := fun i eq =>
--         ITreeF.rec (motive := fun t => (fold (ITreeF.vis e' k)).unfold = t → motive)
--           (fun r_1 h => r r_1) (fun h => d)
--           (fun i k h => v i k) i eq = v e' k
--     refine @Eq.rec _ (ITreeF.vis e' k) motive ?_ _ (Eq.symm to_rewrite_by)
--     simp [motive]
--   | _ => simp at h


namespace Aeneas.Data.Coinductive
