module
public import Aeneas.NonPos.Model.Shape

@[expose] public section
/-!
# The fixed point

`MFix F k` is the solution `solve (MFix.sig F) k` of the recursive domain equations given by the
operators of the shapes.  `unfold`/`fold` go through the isomorphism of the shape at the solution.
-/
namespace NonPos
open NonPos.Domain NonPos.Model Lean.Order

universe pu v w w₁

noncomputable section
set_option warn.classDefReducibility false
attribute [local instance] Dom.unit Dom.prod Dom.pi Dom.pprod NonPosMonad.dom
attribute [local instance] Pointed.unit Pointed.prod Pointed.pprod Pointed.pi Pointed.ofCCPO Pointed.monad FixCompat.pointed FixCompat.ofCCPO FixCompat.monad FixCompat.pi FixCompat.prod FixCompat.pprod

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

/-! ## The structures -/

/-- The structures: the solution. -/
def MFix : Fam.{pu, v} I := fun k => (MFix.D F k).Carrier

abbrev MFix.dom (k : I) : Dom (MFix F k) := MFix.dD F k
attribute [local instance] MFix.dom

/-- The isomorphism of structure `k` at the solution. -/
def MFix.r (k : I) :
    ContRetract ((MFix.sd F k).op.obj (MFix.D F)).Carrier {x : F k (MFix F) // Model.Shape.cond (F := F k) x}
      (MFix.dU F k)
      (Dom.subtype (Shape.dom (F k) (MFix F)) _ ⟨(MFix.sd F k).cond_sup _, (MFix.sd F k).cond_csup _⟩) :=
  (MFix.sd F k).conv (MFix.D F)

def Model.MFix.unfold {k : I} (d : MFix F k) : F k (MFix F) :=
  ((MFix.r F k).toFun (unroll (MFix.sig F) k d)).1

theorem Model.MFix.cond {k : I} (d : MFix F k) : Model.Shape.cond (F := F k) (Model.MFix.unfold F d) :=
  ((MFix.r F k).toFun (unroll (MFix.sig F) k d)).2

def Model.MFix.fold {k : I} (x : F k (MFix F)) (h : Model.Shape.cond (F := F k) x) : MFix F k :=
  roll (MFix.sig F) k ((MFix.r F k).invFun ⟨x, h⟩)

theorem Model.MFix.unfold_fold {k : I} (x : F k (MFix F)) (h : Model.Shape.cond (F := F k) x) :
    Model.MFix.unfold F (Model.MFix.fold F x h) = x :=
  (congrArg (fun y => ((MFix.r F k).toFun y).1) (unroll_roll (MFix.sig F) k _)).trans
    (congrArg Subtype.val ((MFix.r F k).right_inv ⟨x, h⟩))

theorem Model.MFix.fold_unfold {k : I} (d : MFix F k) :
    Model.MFix.fold F (Model.MFix.unfold F d) (Model.MFix.cond F d) = d :=
  (congrArg (roll (MFix.sig F) k) ((MFix.r F k).left_inv (unroll (MFix.sig F) k d))).trans
    (roll_unroll (MFix.sig F) k d)

/-! ## Continuity of `unfold` and `fold` -/

theorem Model.DCont.unfold₀ {k : I} :
    DCont (inst_1 := Shape.dom (F := F k) (MFix F)) (fun d : MFix F k => Model.MFix.unfold F d) := by
  refine DCont.comp' (g := fun y => y.1) (f := fun d : MFix F k => (MFix.r F k).toFun (unroll (MFix.sig F) k d))
    (dB := Dom.subtype (Shape.dom (F k) (MFix F)) _ ⟨(MFix.sd F k).cond_sup _, (MFix.sd F k).cond_csup _⟩)
    (DCont.subtypeVal _) ?_
  exact DCont.comp' (g := (MFix.r F k).toFun) (f := unroll (MFix.sig F) k) (dB := MFix.dU F k)
    (MFix.r F k).cont_toFun (MFix.cont_unroll' F k)

theorem Model.DCont.unfold {D : Type w} [Dom D] {k : I} {f : D → MFix F k} (hf : DCont f) :
    DCont (inst_1 := Shape.dom (F := F k) (MFix F)) (fun d => Model.MFix.unfold F (f d)) :=
  DCont.comp' (g := Model.MFix.unfold F) (f := f) (dB := MFix.dom F k) (Model.DCont.unfold₀ F) hf

theorem Model.DCont.fold {D : Type w} [Dom D] {k : I} {f : D → F k (MFix F)}
    (h : ∀ d, Model.Shape.cond (F := F k) (f d)) (hf : DCont (inst_1 := Shape.dom (F := F k) (MFix F)) f) :
    DCont (fun d => Model.MFix.fold F (f d) (h d)) := by
  refine DCont.comp' (g := roll (MFix.sig F) k) (f := fun d => (MFix.r F k).invFun ⟨f d, h d⟩)
    (dB := MFix.dU F k) (MFix.cont_roll' F k) ?_
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

/-! ## The least element

Every structure has a least element, so it is a `CCPO`, with the order of its `Dom`: a nonempty
chain has a supremum (`Dom.cc`), and the empty chain has `⊥`. -/

/-- The least element of structure `k`. -/
def MFix.bot (k : I) : MFix F k := (OmegaComplete.bottom : (MFix.D F k).Carrier)
theorem MFix.bot_le {k : I} (x : MFix F k) : @Dom.le _ (MFix.dom F k) (MFix.bot F k) x :=
  OmegaComplete.bottom_le (α := (MFix.D F k).Carrier) x

theorem MFix.pointed {k : I} : Pointed (MFix F k) := ⟨⟨MFix.bot F k, MFix.bot_le F⟩⟩

@[instance_reducible] def MFix.ccpo (k : I) : CCPO (MFix F k) :=
  letI := (MFix.dom F k).po
  { toPartialOrder := (MFix.dom F k).po
    has_csup := fun {c} hc => by
      by_cases hne : ∃ x, c x
      · exact (MFix.dom F k).cc.has_sup c hc hne
      · exact ⟨MFix.bot F k, fun u =>
          ⟨fun _ x hx => absurd ⟨x, hx⟩ hne, fun _ => MFix.bot_le F u⟩⟩ }

end MFix

end
end NonPos
