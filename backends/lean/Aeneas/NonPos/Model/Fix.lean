module
public import Aeneas.NonPos.Model.Shape

@[expose] public section
/-!
# The fixed point

`Fix F k` is the set of total elements of the solution `solve (Fix.sig F) k` of the recursive
domain equations given by the operators of the shapes.  Totality is the least fixed point of the
totality of the shapes (`Fix.Tn n`: total at stage `n`), so that a plain field whose type is a
structure of the group is total when that field is.  `unfold`/`fold` go through the retraction of
the shape at the pointed family `Fix.Φ F`.
-/
namespace NonPos
open NonPos.Domain NonPos.Model Lean.Order

universe pu v w w₁

noncomputable section
set_option warn.classDefReducibility false
attribute [local instance] Dom.unit Dom.prod Dom.pi Dom.pprod NonPosMonad.dom
attribute [local instance] Pointed.unit Pointed.prod Pointed.pprod Pointed.pi Pointed.ofCCPO Pointed.monad FixCompat.pointed FixCompat.ofCCPO FixCompat.monad FixCompat.pi FixCompat.prod FixCompat.pprod
attribute [local instance] TFam.instDom

section Fix
variable {I : Type pu} (F : I → Fam.{pu, v} I → Type v) [∀ k, Shape (F k)]

/-- The shape data of structure `k`. -/
abbrev Fix.sd (k : I) : ShapeData (F k) (Shape.cond (F := F k)) := Shape.sd (F := F k)

/-- The signature: the operator of each structure. -/
abbrev Fix.sig : Signature.{pu, v} (I) := fun k => (Fix.sd F k).op

/-- The solution. -/
abbrev Fix.D (k : I) : Domain.{v} := solve (Fix.sig F) k

/-- The admissible structure of the solution. -/
abbrev Fix.dD (k : I) : Dom (Fix.D F k).Carrier := Dom.ofDomain (Fix.D F k)
/-- The admissible structure of the unfolding of the solution. -/
abbrev Fix.dU (k : I) : Dom ((Fix.sd F k).op.obj (Fix.D F)).Carrier :=
  Dom.ofDomain ((Fix.sd F k).op.obj (Fix.D F))

theorem Fix.cont_unroll' (k : I) : @Cont _ _ (Fix.dD F k) (Fix.dU F k) (unroll (Fix.sig F) k) :=
  unroll_continuous (Fix.sig F) k
theorem Fix.cont_roll' (k : I) : @Cont _ _ (Fix.dU F k) (Fix.dD F k) (roll (Fix.sig F) k) :=
  roll_continuous (Fix.sig F) k
theorem Fix.unroll_bottom (k : I) : unroll (Fix.sig F) k OmegaComplete.bottom = OmegaComplete.bottom :=
  EP.embed_bottom (familySolution (Fix.sig F) k).toEP

/-! ## Totality, as a least fixed point -/

/-- Totality at stage `n`: nothing at stage `0`; at stage `n + 1`, the unfolding is total for the shape,
with the plain dictionary fields total at stage `n`. -/
def Fix.Tn : Nat → TPred (Fix.D F)
  | 0 => fun _ _ => False
  | n + 1 => fun k d => (Fix.sd F k).total (Fix.D F) (Fix.Tn n) (unroll (Fix.sig F) k d)

theorem Fix.Tn_step : ∀ n k d, Fix.Tn F n k d → Fix.Tn F (n + 1) k d
  | 0, _, _, h => h.elim
  | n + 1, k, _, h => (Fix.sd F k).total_imp _ _ _ (Fix.Tn_step n) _ h

/-- The properties of a totality predicate needed by the shapes (those of `TFam`). -/
structure Fix.TProps (T : TPred (Fix.D F)) : Prop where
  mono : ∀ k {x y : (Fix.D F k).Carrier}, @Dom.le _ (Fix.dD F k) x y → T k x → T k y
  sup : ∀ k (c : @Dom.Chain _ (Fix.dD F k)), (∀ n, T k (c n)) → T k (@Dom.sup _ (Fix.dD F k) c)
  ev : ∀ k (c : @Dom.Chain _ (Fix.dD F k)), T k (@Dom.sup _ (Fix.dD F k) c) → ∃ n, T k (c n)

/-- The family with totality `T`. -/
abbrev Fix.fam (T : TPred (Fix.D F)) (h : Fix.TProps F T) : TFam.{pu, v} I :=
  { D := Fix.D F, T := T, mono := h.mono, sup := h.sup, ev := h.ev }

theorem Fix.Tn_props : ∀ n, Fix.TProps F (Fix.Tn F n)
  | 0 => ⟨fun _ {_ _} _ h => h.elim, fun _ _ h => (h 0).elim, fun _ _ h => h.elim⟩
  | n + 1 =>
    let Φ := Fix.fam F (Fix.Tn F n) (Fix.Tn_props n)
    { mono := fun k {_ _} h hx => (Fix.sd F k).total_mono Φ (Cont.mono' (Fix.cont_unroll' F k) h) hx
      sup := fun k c h => by
        show (Fix.sd F k).total (Fix.D F) (Fix.Tn F n) (unroll (Fix.sig F) k (@Dom.sup _ (Fix.dD F k) c))
        rw [Cont.sup_eq' (Fix.cont_unroll' F k)]
        exact (Fix.sd F k).total_sup Φ _ h
      ev := fun k c h => by
        have h' : (Fix.sd F k).total (Fix.D F) (Fix.Tn F n) (unroll (Fix.sig F) k (@Dom.sup _ (Fix.dD F k) c)) := h
        rw [Cont.sup_eq' (Fix.cont_unroll' F k)] at h'
        exact (Fix.sd F k).total_ev Φ _ h' }

/-- Totality: total at some stage. -/
def Fix.T : TPred (Fix.D F) := fun k d => ∃ n, Fix.Tn F n k d

theorem Fix.T_props : Fix.TProps F (Fix.T F) where
  mono := fun k {_ _} h ⟨n, hx⟩ => ⟨n, (Fix.Tn_props F n).mono k h hx⟩
  sup := fun k c h =>
    let ⟨n, hn⟩ := h 0
    ⟨n, (Fix.Tn_props F n).sup k c fun m => (Fix.Tn_props F n).mono k (Dom.chain_le' c (Nat.zero_le m)) hn⟩
  ev := fun k c ⟨n, hn⟩ =>
    let ⟨m, hm⟩ := (Fix.Tn_props F n).ev k c hn
    ⟨m, n, hm⟩

/-- The pointed family with totality. -/
abbrev Fix.Φ : TFam.{pu, v} I := Fix.fam F (Fix.T F) (Fix.T_props F)

/-- Totality is a fixed point of the totality of the shapes. -/
theorem Fix.T_iff (k : I) (d : (Fix.D F k).Carrier) :
    Fix.T F k d ↔ (Fix.sd F k).total (Fix.D F) (Fix.T F) (unroll (Fix.sig F) k d) := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => exact hn.elim
    | succ n => exact (Fix.sd F k).total_imp _ _ _ (fun k d h => ⟨n, h⟩) _ hn
  · intro h
    obtain ⟨n, hn⟩ := (Fix.sd F k).total_fin _ _ (Fix.Tn_step F) _ h
    exact ⟨n + 1, hn⟩

/-! ## The structures -/

/-- Closure of totality under suprema (ω-chains: `T_props`; chains: totality is upward closed). -/
theorem Fix.closedT (k : I) : Dom.Closed (Fix.dD F k) (Fix.T F k) :=
  ⟨(Fix.T_props F).sup k, Dom.ChainClosed.of_mono ((Fix.T_props F).mono k)⟩

/-- The structures: the total elements of the solution. -/
def Fix : Fam.{pu, v} I := fun k => {d : (Fix.D F k).Carrier // Fix.T F k d}

abbrev Fix.dom (k : I) : Dom (Fix F k) :=
  Dom.subtype (Fix.dD F k) (Fix.T F k) (Fix.closedT F k)
attribute [local instance] Fix.dom

/-- The retraction of structure `k` at the solution. -/
def Fix.r (k : I) :
    ContRetract {y // (Fix.sd F k).total (Fix.D F) (Fix.T F) y} {x : F k (Fix F) // Shape.cond (F := F k) x}
      (Dom.subtype (Fix.dU F k) _ ⟨(Fix.sd F k).total_sup (Fix.Φ F), Dom.ChainClosed.of_mono ((Fix.sd F k).total_mono (Fix.Φ F))⟩)
      (Dom.subtype (Shape.dom (F k) (Fix F)) _ ⟨(Fix.sd F k).cond_sup _, (Fix.sd F k).cond_csup _⟩) :=
  (Fix.sd F k).conv (Fix.Φ F)

def Model.Fix.unfold {k : I} (d : Fix F k) : F k (Fix F) :=
  ((Fix.r F k).toFun ⟨unroll (Fix.sig F) k d.1, (Fix.T_iff F _ _).1 d.2⟩).1

theorem Model.Fix.cond {k : I} (d : Fix F k) : Shape.cond (F := F k) (Model.Fix.unfold F d) :=
  ((Fix.r F k).toFun ⟨unroll (Fix.sig F) k d.1, (Fix.T_iff F _ _).1 d.2⟩).2

def Model.Fix.fold {k : I} (x : F k (Fix F)) (h : Shape.cond (F := F k) x) : Fix F k :=
  ⟨roll (Fix.sig F) k ((Fix.r F k).invFun ⟨x, h⟩).1,
    (Fix.T_iff F _ _).2 (Eq.mpr (congrArg ((Fix.sd F k).total (Fix.D F) (Fix.T F)) (unroll_roll (Fix.sig F) k _))
      ((Fix.r F k).invFun ⟨x, h⟩).2)⟩

theorem Model.Fix.unfold_fold {k : I} (x : F k (Fix F)) (h : Shape.cond (F := F k) x) :
    Model.Fix.unfold F (Model.Fix.fold F x h) = x :=
  have e : (⟨unroll (Fix.sig F) k (Model.Fix.fold F x h).1, (Fix.T_iff F _ _).1 (Model.Fix.fold F x h).2⟩ :
      {y // (Fix.sd F k).total (Fix.D F) (Fix.T F) y}) = (Fix.r F k).invFun ⟨x, h⟩ :=
    Subtype.ext (unroll_roll _ _ _)
  (congrArg (fun y => ((Fix.r F k).toFun y).1) e).trans
    (congrArg Subtype.val ((Fix.r F k).right_inv ⟨x, h⟩))

/-! ## Continuity of `unfold` and `fold` -/

/-- `unroll`, as a map between the subtypes of total elements. -/
theorem Fix.cont_unroll (k : I) :
    @Cont (Fix F k) {y // (Fix.sd F k).total (Fix.D F) (Fix.T F) y} (Fix.dom F k)
      (Dom.subtype (Fix.dU F k) _ ⟨(Fix.sd F k).total_sup (Fix.Φ F), Dom.ChainClosed.of_mono ((Fix.sd F k).total_mono (Fix.Φ F))⟩)
      (fun d => ⟨unroll (Fix.sig F) k d.1, (Fix.T_iff F _ _).1 d.2⟩) := by
  refine Cont.intoSubtype _ _ (f := fun d : Fix F k => ⟨unroll (Fix.sig F) k d.1, (Fix.T_iff F _ _).1 d.2⟩) ?_
  exact Cont.comp' (g := unroll (Fix.sig F) k) (f := fun d : Fix F k => d.1) (dB := Fix.dD F k)
    (Fix.cont_unroll' F k) (Cont.subtypeVal (Fix.dD F k) (p := Fix.T F k) (hp := Fix.closedT F k))

theorem Model.Cont.unfold₀ {k : I} :
    Cont (inst_1 := Shape.dom (F := F k) (Fix F)) (fun d : Fix F k => Model.Fix.unfold F d) := by
  refine Cont.comp' (g := fun y => y.1)
    (f := fun d : Fix F k => (Fix.r F k).toFun ⟨unroll (Fix.sig F) k d.1, (Fix.T_iff F _ _).1 d.2⟩)
    (dB := Dom.subtype (Shape.dom (F k) (Fix F)) _ ⟨(Fix.sd F k).cond_sup _, (Fix.sd F k).cond_csup _⟩) (Cont.subtypeVal _) ?_
  exact Cont.comp' (g := (Fix.r F k).toFun)
    (f := fun d : Fix F k => ⟨unroll (Fix.sig F) k d.1, (Fix.T_iff F _ _).1 d.2⟩)
    (Fix.r F k).cont_toFun (Fix.cont_unroll F k)

theorem Model.Cont.unfold {D : Type w} [Dom D] {k : I} {f : D → Fix F k} (hf : Cont f) :
    Cont (inst_1 := Shape.dom (F := F k) (Fix F)) (fun d => Model.Fix.unfold F (f d)) :=
  Cont.comp' (g := Model.Fix.unfold F) (f := f) (dB := Fix.dom F k) (Model.Cont.unfold₀ F) hf

theorem Model.Cont.fold {D : Type w} [Dom D] {k : I} {f : D → F k (Fix F)}
    (h : ∀ d, Shape.cond (F := F k) (f d)) (hf : Cont (inst_1 := Shape.dom (F := F k) (Fix F)) f) :
    Cont (fun d => Model.Fix.fold F (f d) (h d)) := by
  refine Cont.intoSubtype (Fix.dD F k) _ (q := Fix.T F k) (hq := Fix.closedT F k)
    (f := fun d => Model.Fix.fold F (f d) (h d)) ?_
  refine Cont.comp' (g := roll (Fix.sig F) k) (f := fun d => ((Fix.r F k).invFun ⟨f d, h d⟩).1)
    (dB := Fix.dU F k) (Fix.cont_roll' F k) ?_
  refine Cont.comp' (g := fun y => y.1) (f := fun d => (Fix.r F k).invFun ⟨f d, h d⟩)
    (dB := Dom.subtype (Fix.dU F k) _ ⟨(Fix.sd F k).total_sup (Fix.Φ F), Dom.ChainClosed.of_mono ((Fix.sd F k).total_mono (Fix.Φ F))⟩) (Cont.subtypeVal _) ?_
  refine Cont.comp' (g := (Fix.r F k).invFun) (f := fun d => ⟨f d, h d⟩)
    (dB := Dom.subtype (Shape.dom (F k) (Fix F)) _ ⟨(Fix.sd F k).cond_sup _, (Fix.sd F k).cond_csup _⟩)
    (Fix.r F k).cont_invFun ?_
  exact Cont.intoSubtype _ _ (f := fun d => ⟨f d, h d⟩) hf

/-! ## Pointedness

`⊥` is total in structure `k` when every plain field of `k` is pointed or a structure of the group in
which `⊥` is total (`Shape.BotTotal`, decided by instances in `Top`). -/

/-- `⊥` is total for the shape `G`, at the totality of the group `F`. -/
class Shape.BotTotal (G : Fam.{pu, v} I → Type w) [Shape G] : Prop where
  bot : (Shape.sd (F := G)).total (Fix.D F) (Fix.T F) OmegaComplete.bottom

/-- `⊥` is a total element of structure `k` of the group. -/
class Fix.BotTotal (k : I) : Prop where
  bot : Fix.T F k OmegaComplete.bottom

theorem Shape.BotTotal.ofPointed (G : Fam.{pu, v} I → Type w) [Shape G] [Shape.Pointed G] : Shape.BotTotal F G :=
  ⟨Shape.Pointed.total _ _ _⟩
attribute [local instance] Shape.BotTotal.ofPointed

theorem Model.Shape.botTotal_prod (G₁ : Fam.{pu, v} I → Type w) (G₂ : Fam.{pu, v} I → Type w₁)
    [Shape G₁] [Shape G₂] [Shape.BotTotal F G₁] [Shape.BotTotal F G₂] :
    (Model.Shape.prod G₁ G₂).total (Fix.D F) (Fix.T F) OmegaComplete.bottom :=
  ⟨Shape.BotTotal.bot (F := F) (G := G₁), Shape.BotTotal.bot (F := F) (G := G₂)⟩

theorem Model.Shape.botTotal_var (k : I) [h : Fix.BotTotal F k] :
    (Model.Shape.var k).total (Fix.D F) (Fix.T F) OmegaComplete.bottom := h.bot

theorem Fix.BotTotal.ofShape (k : I) [h : Shape.BotTotal F (F k)] : Fix.BotTotal F k :=
  ⟨(Fix.T_iff F k _).2 (by rw [Fix.unroll_bottom]; exact h.bot)⟩
attribute [local instance] Fix.BotTotal.ofShape

theorem Fix.pointed {k : I} [h : Fix.BotTotal F k] : Pointed (Fix F k) :=
  ⟨⟨⟨OmegaComplete.bottom, h.bot⟩, fun x => OmegaComplete.bottom_le x.1⟩⟩
attribute [local instance] Fix.pointed

/-- Under `Fix.BotTotal`, a dictionary type is a `CCPO`, with the order of its `Dom`: a nonempty chain
has a supremum (`Dom.cc`), and the empty chain has the total `⊥`. -/
@[instance_reducible] def Fix.ccpo (k : I) [h : Fix.BotTotal F k] : CCPO (Fix F k) :=
  letI := (Fix.dom F k).po
  { toPartialOrder := (Fix.dom F k).po
    has_csup := fun {c} hc => by
      by_cases hne : ∃ x, c x
      · exact (Fix.dom F k).cc.has_sup c hc hne
      · exact ⟨⟨OmegaComplete.bottom, h.bot⟩, fun u =>
          ⟨fun _ x hx => absurd ⟨x, hx⟩ hne, fun _ => OmegaComplete.bottom_le u.1⟩⟩ }

/-- The `CCPO` of a dictionary type has the order of its `Dom`. -/
theorem Fix.fixCompat (k : I) [Fix.BotTotal F k] : @FixCompat (Fix F k) (Fix.dom F k) (Fix.ccpo F k) :=
  @FixCompat.mk (Fix F k) (Fix.dom F k) (Fix.ccpo F k) (fun _ _ => Iff.rfl)

end Fix

end
end NonPos
