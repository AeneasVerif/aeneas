module
public import Aeneas.NonPos.Model.Shape

@[expose] public section
/-!
# The fixed point

`MFix F k` is the set of total elements of the solution `solve (MFix.sig F) k` of the recursive
domain equations given by the operators of the shapes.  Totality is the least fixed point of the
totality of the shapes (`MFix.Tn n`: total at stage `n`), so that a plain field whose type is a
structure of the group is total when that field is.  `unfold`/`fold` go through the retraction of
the shape at the pointed family `MFix.Φ F`.
-/
namespace NonPos
open NonPos.Domain NonPos.Model Lean.Order

universe pu v w w₁

noncomputable section
set_option warn.classDefReducibility false
attribute [local instance] Dom.unit Dom.prod Dom.pi Dom.pprod NonPosMonad.dom
attribute [local instance] Pointed.unit Pointed.prod Pointed.pprod Pointed.pi Pointed.ofCCPO Pointed.monad FixCompat.pointed FixCompat.ofCCPO FixCompat.monad FixCompat.pi FixCompat.prod FixCompat.pprod
attribute [local instance] TFam.instDom

section MFix
variable {I : Type pu} (F : I → Fam.{pu, v} I → Type v) [∀ k, Shape (F k)]

/-- The shape data of structure `k`. -/
abbrev MFix.sd (k : I) : ShapeData (F k) (Model.Shape.cond (F := F k)) := Model.Shape.sd (F := F k)

/-- The signature: the operator of each structure. -/
abbrev MFix.sig : Signature.{pu, v} (I) := fun k => (MFix.sd F k).op

/-- The solution. -/
abbrev MFix.D (k : I) : Domain.{v} := solve (MFix.sig F) k

/-- The admissible structure of the solution. -/
abbrev MFix.dD (k : I) : Dom (MFix.D F k).Carrier := Dom.ofDomain (MFix.D F k)
/-- The admissible structure of the unfolding of the solution. -/
abbrev MFix.dU (k : I) : Dom ((MFix.sd F k).op.obj (MFix.D F)).Carrier :=
  Dom.ofDomain ((MFix.sd F k).op.obj (MFix.D F))

theorem MFix.cont_unroll' (k : I) : @DCont _ _ (MFix.dD F k) (MFix.dU F k) (unroll (MFix.sig F) k) :=
  unroll_continuous (MFix.sig F) k
theorem MFix.cont_roll' (k : I) : @DCont _ _ (MFix.dU F k) (MFix.dD F k) (roll (MFix.sig F) k) :=
  roll_continuous (MFix.sig F) k
theorem MFix.unroll_bottom (k : I) : unroll (MFix.sig F) k OmegaComplete.bottom = OmegaComplete.bottom :=
  EP.embed_bottom (familySolution (MFix.sig F) k).toEP

/-! ## Totality, as a least fixed point -/

/-- Totality at stage `n`: nothing at stage `0`; at stage `n + 1`, the unfolding is total for the shape,
with the plain dictionary fields total at stage `n`. -/
def MFix.Tn : Nat → TPred (MFix.D F)
  | 0 => fun _ _ => False
  | n + 1 => fun k d => (MFix.sd F k).total (MFix.D F) (MFix.Tn n) (unroll (MFix.sig F) k d)

theorem MFix.Tn_step : ∀ n k d, MFix.Tn F n k d → MFix.Tn F (n + 1) k d
  | 0, _, _, h => h.elim
  | n + 1, k, _, h => (MFix.sd F k).total_imp _ _ _ (MFix.Tn_step n) _ h

/-- The properties of a totality predicate needed by the shapes (those of `TFam`). -/
structure MFix.TProps (T : TPred (MFix.D F)) : Prop where
  mono : ∀ k {x y : (MFix.D F k).Carrier}, @Dom.le _ (MFix.dD F k) x y → T k x → T k y
  sup : ∀ k (c : @Dom.Chain _ (MFix.dD F k)), (∀ n, T k (c n)) → T k (@Dom.sup _ (MFix.dD F k) c)
  ev : ∀ k (c : @Dom.Chain _ (MFix.dD F k)), T k (@Dom.sup _ (MFix.dD F k) c) → ∃ n, T k (c n)

/-- The family with totality `T`. -/
abbrev MFix.fam (T : TPred (MFix.D F)) (h : MFix.TProps F T) : TFam.{pu, v} I :=
  { D := MFix.D F, T := T, mono := h.mono, sup := h.sup, ev := h.ev }

theorem MFix.Tn_props : ∀ n, MFix.TProps F (MFix.Tn F n)
  | 0 => ⟨fun _ {_ _} _ h => h.elim, fun _ _ h => (h 0).elim, fun _ _ h => h.elim⟩
  | n + 1 =>
    let Φ := MFix.fam F (MFix.Tn F n) (MFix.Tn_props n)
    { mono := fun k {_ _} h hx => (MFix.sd F k).total_mono Φ (DCont.mono' (MFix.cont_unroll' F k) h) hx
      sup := fun k c h => by
        show (MFix.sd F k).total (MFix.D F) (MFix.Tn F n) (unroll (MFix.sig F) k (@Dom.sup _ (MFix.dD F k) c))
        rw [DCont.sup_eq' (MFix.cont_unroll' F k)]
        exact (MFix.sd F k).total_sup Φ _ h
      ev := fun k c h => by
        have h' : (MFix.sd F k).total (MFix.D F) (MFix.Tn F n) (unroll (MFix.sig F) k (@Dom.sup _ (MFix.dD F k) c)) := h
        rw [DCont.sup_eq' (MFix.cont_unroll' F k)] at h'
        exact (MFix.sd F k).total_ev Φ _ h' }

/-- Totality: total at some stage. -/
def MFix.T : TPred (MFix.D F) := fun k d => ∃ n, MFix.Tn F n k d

theorem MFix.T_props : MFix.TProps F (MFix.T F) where
  mono := fun k {_ _} h ⟨n, hx⟩ => ⟨n, (MFix.Tn_props F n).mono k h hx⟩
  sup := fun k c h =>
    let ⟨n, hn⟩ := h 0
    ⟨n, (MFix.Tn_props F n).sup k c fun m => (MFix.Tn_props F n).mono k (Dom.chain_le' c (Nat.zero_le m)) hn⟩
  ev := fun k c ⟨n, hn⟩ =>
    let ⟨m, hm⟩ := (MFix.Tn_props F n).ev k c hn
    ⟨m, n, hm⟩

/-- The pointed family with totality. -/
abbrev MFix.Φ : TFam.{pu, v} I := MFix.fam F (MFix.T F) (MFix.T_props F)

/-- Totality is a fixed point of the totality of the shapes. -/
theorem MFix.T_iff (k : I) (d : (MFix.D F k).Carrier) :
    MFix.T F k d ↔ (MFix.sd F k).total (MFix.D F) (MFix.T F) (unroll (MFix.sig F) k d) := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => exact hn.elim
    | succ n => exact (MFix.sd F k).total_imp _ _ _ (fun k d h => ⟨n, h⟩) _ hn
  · intro h
    obtain ⟨n, hn⟩ := (MFix.sd F k).total_fin _ _ (MFix.Tn_step F) _ h
    exact ⟨n + 1, hn⟩

/-! ## The structures -/

/-- Closure of totality under suprema (ω-chains: `T_props`; chains: totality is upward closed). -/
theorem MFix.closedT (k : I) : Dom.Closed (MFix.dD F k) (MFix.T F k) :=
  ⟨(MFix.T_props F).sup k, Dom.ChainClosed.of_mono ((MFix.T_props F).mono k)⟩

/-- The structures: the total elements of the solution. -/
def MFix : Fam.{pu, v} I := fun k => {d : (MFix.D F k).Carrier // MFix.T F k d}

abbrev MFix.dom (k : I) : Dom (MFix F k) :=
  Dom.subtype (MFix.dD F k) (MFix.T F k) (MFix.closedT F k)
attribute [local instance] MFix.dom

/-- The retraction of structure `k` at the solution. -/
def MFix.r (k : I) :
    ContRetract {y // (MFix.sd F k).total (MFix.D F) (MFix.T F) y} {x : F k (MFix F) // Model.Shape.cond (F := F k) x}
      (Dom.subtype (MFix.dU F k) _ ⟨(MFix.sd F k).total_sup (MFix.Φ F), Dom.ChainClosed.of_mono ((MFix.sd F k).total_mono (MFix.Φ F))⟩)
      (Dom.subtype (Shape.dom (F k) (MFix F)) _ ⟨(MFix.sd F k).cond_sup _, (MFix.sd F k).cond_csup _⟩) :=
  (MFix.sd F k).conv (MFix.Φ F)

def Model.MFix.unfold {k : I} (d : MFix F k) : F k (MFix F) :=
  ((MFix.r F k).toFun ⟨unroll (MFix.sig F) k d.1, (MFix.T_iff F _ _).1 d.2⟩).1

theorem Model.MFix.cond {k : I} (d : MFix F k) : Model.Shape.cond (F := F k) (Model.MFix.unfold F d) :=
  ((MFix.r F k).toFun ⟨unroll (MFix.sig F) k d.1, (MFix.T_iff F _ _).1 d.2⟩).2

def Model.MFix.fold {k : I} (x : F k (MFix F)) (h : Model.Shape.cond (F := F k) x) : MFix F k :=
  ⟨roll (MFix.sig F) k ((MFix.r F k).invFun ⟨x, h⟩).1,
    (MFix.T_iff F _ _).2 (Eq.mpr (congrArg ((MFix.sd F k).total (MFix.D F) (MFix.T F)) (unroll_roll (MFix.sig F) k _))
      ((MFix.r F k).invFun ⟨x, h⟩).2)⟩

theorem Model.MFix.unfold_fold {k : I} (x : F k (MFix F)) (h : Model.Shape.cond (F := F k) x) :
    Model.MFix.unfold F (Model.MFix.fold F x h) = x :=
  have e : (⟨unroll (MFix.sig F) k (Model.MFix.fold F x h).1, (MFix.T_iff F _ _).1 (Model.MFix.fold F x h).2⟩ :
      {y // (MFix.sd F k).total (MFix.D F) (MFix.T F) y}) = (MFix.r F k).invFun ⟨x, h⟩ :=
    Subtype.ext (unroll_roll _ _ _)
  (congrArg (fun y => ((MFix.r F k).toFun y).1) e).trans
    (congrArg Subtype.val ((MFix.r F k).right_inv ⟨x, h⟩))

/-! ## Continuity of `unfold` and `fold` -/

/-- `unroll`, as a map between the subtypes of total elements. -/
theorem MFix.cont_unroll (k : I) :
    @DCont (MFix F k) {y // (MFix.sd F k).total (MFix.D F) (MFix.T F) y} (MFix.dom F k)
      (Dom.subtype (MFix.dU F k) _ ⟨(MFix.sd F k).total_sup (MFix.Φ F), Dom.ChainClosed.of_mono ((MFix.sd F k).total_mono (MFix.Φ F))⟩)
      (fun d => ⟨unroll (MFix.sig F) k d.1, (MFix.T_iff F _ _).1 d.2⟩) := by
  refine DCont.intoSubtype _ _ (f := fun d : MFix F k => ⟨unroll (MFix.sig F) k d.1, (MFix.T_iff F _ _).1 d.2⟩) ?_
  exact DCont.comp' (g := unroll (MFix.sig F) k) (f := fun d : MFix F k => d.1) (dB := MFix.dD F k)
    (MFix.cont_unroll' F k) (DCont.subtypeVal (MFix.dD F k) (p := MFix.T F k) (hp := MFix.closedT F k))

theorem Model.DCont.unfold₀ {k : I} :
    DCont (inst_1 := Shape.dom (F := F k) (MFix F)) (fun d : MFix F k => Model.MFix.unfold F d) := by
  refine DCont.comp' (g := fun y => y.1)
    (f := fun d : MFix F k => (MFix.r F k).toFun ⟨unroll (MFix.sig F) k d.1, (MFix.T_iff F _ _).1 d.2⟩)
    (dB := Dom.subtype (Shape.dom (F k) (MFix F)) _ ⟨(MFix.sd F k).cond_sup _, (MFix.sd F k).cond_csup _⟩) (DCont.subtypeVal _) ?_
  exact DCont.comp' (g := (MFix.r F k).toFun)
    (f := fun d : MFix F k => ⟨unroll (MFix.sig F) k d.1, (MFix.T_iff F _ _).1 d.2⟩)
    (MFix.r F k).cont_toFun (MFix.cont_unroll F k)

theorem Model.DCont.unfold {D : Type w} [Dom D] {k : I} {f : D → MFix F k} (hf : DCont f) :
    DCont (inst_1 := Shape.dom (F := F k) (MFix F)) (fun d => Model.MFix.unfold F (f d)) :=
  DCont.comp' (g := Model.MFix.unfold F) (f := f) (dB := MFix.dom F k) (Model.DCont.unfold₀ F) hf

theorem Model.DCont.fold {D : Type w} [Dom D] {k : I} {f : D → F k (MFix F)}
    (h : ∀ d, Model.Shape.cond (F := F k) (f d)) (hf : DCont (inst_1 := Shape.dom (F := F k) (MFix F)) f) :
    DCont (fun d => Model.MFix.fold F (f d) (h d)) := by
  refine DCont.intoSubtype (MFix.dD F k) _ (q := MFix.T F k) (hq := MFix.closedT F k)
    (f := fun d => Model.MFix.fold F (f d) (h d)) ?_
  refine DCont.comp' (g := roll (MFix.sig F) k) (f := fun d => ((MFix.r F k).invFun ⟨f d, h d⟩).1)
    (dB := MFix.dU F k) (MFix.cont_roll' F k) ?_
  refine DCont.comp' (g := fun y => y.1) (f := fun d => (MFix.r F k).invFun ⟨f d, h d⟩)
    (dB := Dom.subtype (MFix.dU F k) _ ⟨(MFix.sd F k).total_sup (MFix.Φ F), Dom.ChainClosed.of_mono ((MFix.sd F k).total_mono (MFix.Φ F))⟩) (DCont.subtypeVal _) ?_
  refine DCont.comp' (g := (MFix.r F k).invFun) (f := fun d => ⟨f d, h d⟩)
    (dB := Dom.subtype (Shape.dom (F k) (MFix F)) _ ⟨(MFix.sd F k).cond_sup _, (MFix.sd F k).cond_csup _⟩)
    (MFix.r F k).cont_invFun ?_
  exact DCont.intoSubtype _ _ (f := fun d => ⟨f d, h d⟩) hf

/-! ## Monotonicity of `unfold` and `fold` -/

theorem Model.MFix.unfold_mono {k : I} {d₁ d₂ : MFix F k} (h : @Dom.le _ (MFix.dom F k) d₁ d₂) :
    @Dom.le _ (Shape.dom (F k) (MFix F)) (Model.MFix.unfold F d₁) (Model.MFix.unfold F d₂) :=
  DCont.mono' (Model.DCont.unfold₀ F) h

theorem Model.MFix.fold_mono {k : I} {x₁ x₂ : F k (MFix F)} (h₁ : Model.Shape.cond (F := F k) x₁)
    (h₂ : Model.Shape.cond (F := F k) x₂) (h : @Dom.le _ (Shape.dom (F k) (MFix F)) x₁ x₂) :
    @Dom.le _ (MFix.dom F k) (Model.MFix.fold F x₁ h₁) (Model.MFix.fold F x₂ h₂) :=
  DCont.mono' (MFix.cont_roll' F k) (DCont.mono' (MFix.r F k).cont_invFun (x := ⟨x₁, h₁⟩) (y := ⟨x₂, h₂⟩) h)

/-! ## Pointedness

`⊥` is total in structure `k` when every plain field of `k` is pointed or a structure of the group in
which `⊥` is total (`Shape.BotTotal`, decided by instances in `Top`). -/

/-- `⊥` is total for the shape `G`, at the totality of the group `F`. -/
class Shape.BotTotal (G : Fam.{pu, v} I → Type w) [Shape G] : Prop where
  bot : (Model.Shape.sd (F := G)).total (MFix.D F) (MFix.T F) OmegaComplete.bottom

/-- `⊥` is a total element of structure `k` of the group. -/
class MFix.BotTotal (k : I) : Prop where
  bot : MFix.T F k OmegaComplete.bottom

theorem Shape.BotTotal.ofPointed (G : Fam.{pu, v} I → Type w) [Shape G] [Shape.Pointed G] : Shape.BotTotal F G :=
  ⟨Shape.Pointed.total _ _ _⟩
attribute [local instance] Shape.BotTotal.ofPointed

theorem Model.Shape.botTotal_prod (G₁ : Fam.{pu, v} I → Type w) (G₂ : Fam.{pu, v} I → Type w₁)
    [Shape G₁] [Shape G₂] [Shape.BotTotal F G₁] [Shape.BotTotal F G₂] :
    (Model.Shape.prod G₁ G₂).total (MFix.D F) (MFix.T F) OmegaComplete.bottom :=
  ⟨Shape.BotTotal.bot (F := F) (G := G₁), Shape.BotTotal.bot (F := F) (G := G₂)⟩

theorem Model.Shape.botTotal_var (k : I) [h : MFix.BotTotal F k] :
    (Model.Shape.var k).total (MFix.D F) (MFix.T F) OmegaComplete.bottom := h.bot

theorem MFix.BotTotal.ofShape (k : I) [h : Shape.BotTotal F (F k)] : MFix.BotTotal F k :=
  ⟨(MFix.T_iff F k _).2 (by rw [MFix.unroll_bottom]; exact h.bot)⟩
attribute [local instance] MFix.BotTotal.ofShape

theorem MFix.pointed {k : I} [h : MFix.BotTotal F k] : Pointed (MFix F k) :=
  ⟨⟨⟨OmegaComplete.bottom, h.bot⟩, fun x => OmegaComplete.bottom_le x.1⟩⟩
attribute [local instance] MFix.pointed

/-- Under `MFix.BotTotal`, a dictionary type is a `CCPO`, with the order of its `Dom`: a nonempty chain
has a supremum (`Dom.cc`), and the empty chain has the total `⊥`. -/
@[instance_reducible] def MFix.ccpo (k : I) [h : MFix.BotTotal F k] : CCPO (MFix F k) :=
  letI := (MFix.dom F k).po
  { toPartialOrder := (MFix.dom F k).po
    has_csup := fun {c} hc => by
      by_cases hne : ∃ x, c x
      · exact (MFix.dom F k).cc.has_sup c hc hne
      · exact ⟨⟨OmegaComplete.bottom, h.bot⟩, fun u =>
          ⟨fun _ x hx => absurd ⟨x, hx⟩ hne, fun _ => OmegaComplete.bottom_le u.1⟩⟩ }

/-- The `CCPO` of a dictionary type has the order of its `Dom`. -/
theorem MFix.fixCompat (k : I) [MFix.BotTotal F k] : @FixCompat (MFix F k) (MFix.dom F k) (MFix.ccpo F k) :=
  @FixCompat.mk (MFix F k) (MFix.dom F k) (MFix.ccpo F k) (fun _ _ => Iff.rfl)

end MFix

/-- The condition of a body `G` over the structures of the group `H` (for `G = H k`, the condition
for folding into `MFix H k`): its condition at the order of the dictionaries. -/
abbrev Shape.cond {I : Type pu} (H : I → Fam.{pu, v} I → Type v) [∀ k, Shape (H k)]
    {G : Fam.{pu, v} I → Type w} [iG : Shape G] (x : G (MFix H)) : Prop :=
  @Model.Shape.cond _ G _ (MFix H) (MFix.dom H) x

end
end NonPos
