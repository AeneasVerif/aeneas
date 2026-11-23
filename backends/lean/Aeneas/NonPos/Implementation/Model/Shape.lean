module
public import Aeneas.NonPos.Implementation.Domain.Operator
public import Aeneas.NonPos.Implementation.Model.Cont

@[expose] public section
/-!
# Shapes

A shape of a functor `F : Fam I → Type w` is: a domain operator `op`, the order on `F X`, the
condition `cond`, and a continuous isomorphism between `op.obj D` and the elements of `F X`
satisfying the condition (for `X` the carriers of `D`), for every family of domains `D`.

In this file `Dom`s are passed explicitly (the ones of subtypes are not instances).
-/
namespace NonPos
open NonPos.Domain NonPos.Model Lean.Order

universe pu v w w₁ w₂

noncomputable section
set_option warn.classDefReducibility false
attribute [local instance] Dom.unit Dom.prod Dom.pi Dom.pprod
attribute [local instance] Pointed.unit Pointed.prod Pointed.pprod Pointed.pi Pointed.ofCCPO

/-- Families of types indexed by the structures of a group (`I`: a structure applied to parameters). -/
abbrev Fam (I : Type pu) : Type (max pu (v + 1)) := I → Type v

/-! ## Admissible structures from bundled domains and on subtypes -/

/-- `Dom` of a bundled pointed domain. -/
def Dom.ofDomain (D : Domain.{v}) : Dom D.Carrier := ⟨D.order, D.complete.toOmegaSup, D.chainComplete⟩

theorem Dom.ofDomain_sup (D : Domain.{v}) (c : @Domain.Chain D.Carrier D.order) :
    @Dom.sup _ (Dom.ofDomain D) c = OmegaSup.sup c := rfl

/-- The pointed domain of a pointed admissible type. -/
def Dom.toOmegaComplete (A : Type w) [Dom A] [NonPos.Pointed A] : @OmegaComplete A Dom.po :=
  @OmegaComplete.mk A Dom.po Dom.os (Dom.bot A) Dom.bot_le
def Domain.ofDom (A : Type w) [Dom A] [NonPos.Pointed A] : Domain.{w} := ⟨A, Dom.po, Dom.toOmegaComplete A, Dom.cc⟩

/-- The order of a subtype. -/
def Dom.subtypePO {A : Type w} (d : Dom A) (p : A → Prop) : PartialOrder {a // p a} where
  rel x y := @Dom.le A d x.1 y.1
  rel_refl {x} := @Dom.le_refl A d x.1
  rel_trans {_ _ _} h₁ h₂ := @Dom.le_trans A d _ _ _ h₁ h₂
  rel_antisymm {_ _} h₁ h₂ := Subtype.ext (@Dom.le_antisymm A d _ _ h₁ h₂)

/-- `p` is closed under suprema of nonempty chains. -/
def Dom.ChainClosed {A : Type w} (d : Dom A) (p : A → Prop) : Prop :=
  ∀ c : A → Prop, @chain A d.po c → (∃ x, c x) → (∀ x, c x → p x) → ∀ s, @is_sup A d.po c s → p s

/-- `p` is closed under suprema of ω-chains and of nonempty chains. -/
structure Dom.Closed {A : Type w} (d : Dom A) (p : A → Prop) : Prop where
  sup : ∀ c : @Dom.Chain A d, (∀ n, p (c n)) → p (@Dom.sup A d c)
  csup : Dom.ChainClosed d p

/-- A subtype closed under suprema. -/
def Dom.subtype {A : Type w} (d : Dom A) (p : A → Prop) (hp : Dom.Closed d p) : Dom {a // p a} where
  po := Dom.subtypePO d p
  os := @OmegaSup.mk _ (Dom.subtypePO d p)
    (fun c => ⟨@Dom.sup A d (@Chain.mk A d.po (fun n => (c n).1) (fun n => @Chain.step _ (Dom.subtypePO d p) c n)),
               hp.sup _ (fun n => (c n).2)⟩)
    (fun c n => @Dom.le_sup A d (@Chain.mk A d.po (fun n => (c n).1) (fun n => @Chain.step _ (Dom.subtypePO d p) c n)) n)
    (fun c x h => @Dom.sup_le A d _ _ h)
  cc := by
    letI := d.po; letI := d.cc; letI := Dom.subtypePO d p
    refine ⟨fun c hc hne => ?_⟩
    have hc' : chain (image Subtype.val c) :=
      @chain_image {a // p a} A (Dom.subtypePO d p) d.po Subtype.val (fun _ _ h => h) c hc
    have hs := chainSup_spec _ hc' (image_nonempty _ hne)
    have hp' : p (chainSup _ hc' (image_nonempty _ hne)) :=
      hp.csup _ hc' (image_nonempty _ hne) (fun _ ⟨x, _, e⟩ => e ▸ x.2) _ hs
    refine ⟨⟨_, hp'⟩, fun u => ⟨fun hu x hx => ?_, fun hu => ?_⟩⟩
    · exact @PartialOrder.rel_trans A d.po _ _ _ (isSup_le hs ⟨x, hx, rfl⟩) hu
    · exact (isSup_le_of hs fun _ ⟨x, hx, e⟩ => e ▸ hu x hx : @PartialOrder.rel A d.po _ u.1)

/-- An upward-closed predicate is closed under suprema of nonempty chains. -/
theorem Dom.ChainClosed.of_mono {A : Type w} {d : Dom A} {p : A → Prop}
    (h : ∀ {x y : A}, @Dom.le A d x y → p x → p y) : Dom.ChainClosed d p :=
  fun _ _ ⟨x, hx⟩ hp _ hs => h (@isSup_le A d.po _ _ hs x hx) (hp x hx)

/-- A supremum in `A ×' B` is computed componentwise. -/
theorem Dom.isSup_pprod {A : Type w₁} {B : Type w₂} (dA : Dom A) (dB : Dom B) {c : A ×' B → Prop}
    (hc : @chain _ (@Dom.pprod A B dA dB).po c) (hne : ∃ x, c x) {s : A ×' B}
    (h : @is_sup _ (@Dom.pprod A B dA dB).po c s) :
    @is_sup A dA.po (image PProd.fst c) s.1 ∧ @is_sup B dB.po (image PProd.snd c) s.2 := by
  letI := dA.po; letI := dB.po; letI := dA.cc; letI := dB.cc; letI := (@Dom.pprod A B dA dB).po
  have h₁ : chain (image PProd.fst c) := @chain_image (A ×' B) A (@Dom.pprod A B dA dB).po dA.po PProd.fst (fun _ _ h => h.1) c hc
  have h₂ : chain (image PProd.snd c) := @chain_image (A ×' B) B (@Dom.pprod A B dA dB).po dB.po PProd.snd (fun _ _ h => h.2) c hc
  have hs₁ := chainSup_spec _ h₁ (image_nonempty _ hne)
  have hs₂ := chainSup_spec _ h₂ (image_nonempty _ hne)
  have hss : s ⊑ (⟨chainSup _ h₁ (image_nonempty _ hne), chainSup _ h₂ (image_nonempty _ hne)⟩ : A ×' B) :=
    isSup_le_of h fun x hx => ⟨isSup_le hs₁ ⟨x, hx, rfl⟩, isSup_le hs₂ ⟨x, hx, rfl⟩⟩
  exact ⟨isSup_of (fun _ ⟨x, hx, e⟩ => e ▸ (isSup_le h hx).1)
      (fun u hu => PartialOrder.rel_trans hss.1 (isSup_le_of hs₁ hu)),
    isSup_of (fun _ ⟨x, hx, e⟩ => e ▸ (isSup_le h hx).2)
      (fun u hu => PartialOrder.rel_trans hss.2 (isSup_le_of hs₂ hu))⟩

/-- A supremum in a product `(t : T) → B t` is computed pointwise. -/
theorem Dom.isSup_pi {T : Type w₁} {B : T → Type w₂} (d : ∀ t, Dom (B t)) {c : ((t : T) → B t) → Prop}
    (hc : @chain _ (@Dom.pi T B d).po c) (hne : ∃ x, c x) {s : (t : T) → B t}
    (h : @is_sup _ (@Dom.pi T B d).po c s) (t : T) :
    @is_sup (B t) (d t).po (image (fun f : (t : T) → B t => f t) c) (s t) := by
  letI : ∀ t, PartialOrder (B t) := fun t => (d t).po
  letI : ∀ t, ChainComplete (B t) := fun t => (d t).cc
  exact isSup_pi_apply hc hne h t

/-- The pointwise supremum of a chain of continuous functions is continuous. -/
theorem DCont.of_isSup {D : Type w₁} {B : Type w₂} (dD : Dom D) (dB : Dom B) {c : (D → B) → Prop}
    (hcont : ∀ f, c f → @DCont D B dD dB f) {s : D → B}
    (hs : ∀ x, @is_sup B dB.po (image (fun f : D → B => f x) c) (s x)) : @DCont D B dD dB s := by
  letI := dB.po
  have mono : ∀ x y, @Dom.le D dD x y → @Dom.le B dB (s x) (s y) := fun x y hxy =>
    isSup_le_of (hs x) fun _ ⟨f, hf, e⟩ => e ▸
      PartialOrder.rel_trans (DCont.mono' (hcont f hf) hxy) (isSup_le (hs y) ⟨f, hf, rfl⟩)
  refine DCont.mk' s mono (fun d => @Dom.le_antisymm B dB _ _ ?_ ?_)
  · refine isSup_le_of (hs _) fun _ ⟨f, hf, e⟩ => ?_
    subst e
    show @Dom.le B dB (f (@Dom.sup D dD d)) _
    rw [DCont.sup_eq' (hcont f hf)]
    exact @Dom.sup_le B dB _ _ fun n => @Dom.le_trans B dB _ _ _ (isSup_le (hs (d n)) ⟨f, hf, rfl⟩)
      (@Dom.le_sup B dB (@Chain.map D B dD.po dB.po d s mono) n)
  · exact @Dom.sup_le B dB _ _ fun n => mono _ _ (@Dom.le_sup D dD d n)

section Subtype
variable {A : Type w₁} {B : Type w₂} (dA : Dom A) (dB : Dom B) {p : A → Prop} {q : B → Prop}
  {hp : Dom.Closed dA p} {hq : Dom.Closed dB q}

/-- The chain of values of a chain in a subtype. -/
def Dom.vals (c : @Dom.Chain {a // p a} (Dom.subtype dA p hp)) : @Dom.Chain A dA :=
  @Chain.mk A dA.po (fun n => (c n).1) (fun n => @Chain.step _ (Dom.subtype dA p hp).po c n)

theorem Dom.subtype_sup_val (c : @Dom.Chain {a // p a} (Dom.subtype dA p hp)) :
    (@Dom.sup _ (Dom.subtype dA p hp) c).1 = @Dom.sup A dA (Dom.vals dA c) := rfl

theorem DCont.subtypeVal : @DCont {a // p a} A (Dom.subtype dA p hp) dA (fun x => x.1) :=
  DCont.mk' _ (fun _ _ h => h) (fun _ => rfl)

/-- A continuous map which preserves the predicates, as a map between the subtypes. -/
theorem DCont.subtypeMk {f : A → B} (hf : @DCont A B dA dB f) (h : ∀ a, p a → q (f a)) :
    @DCont {a // p a} {b // q b} (Dom.subtype dA p hp) (Dom.subtype dB q hq) (fun x => ⟨f x.1, h x.1 x.2⟩) := by
  refine DCont.mk' _ (fun x y hxy => DCont.mono' hf hxy) (fun c => ?_)
  apply Subtype.ext
  show f (@Dom.sup A dA (Dom.vals dA c)) = _
  rw [DCont.sup_eq' hf]; rfl

/-- Continuity of a map into a subtype, from continuity of its value. -/
theorem DCont.intoSubtype {D : Type w} (dD : Dom D) {f : D → {b // q b}}
    (hf : @DCont D B dD dB (fun d => (f d).1)) : @DCont D {b // q b} dD (Dom.subtype dB q hq) f := by
  refine DCont.mk' _ (fun x y hxy => DCont.mono' hf hxy) (fun c => ?_)
  apply Subtype.ext
  exact DCont.sup_eq' hf c
end Subtype

/-! ## Families of domains -/

/-- The carriers of a family of domains. -/
abbrev Carriers (D : I → Domain.{v}) : Fam.{pu, v} I := fun k => (D k).Carrier
attribute [local instance] Dom.ofDomain

/-! ## Continuous isomorphisms -/

structure ContRetract (A : Type w₁) (B : Type w₂) (dA : Dom A) (dB : Dom B) where
  toFun : A → B
  invFun : B → A
  right_inv : ∀ b, toFun (invFun b) = b
  left_inv : ∀ a, invFun (toFun a) = a
  cont_toFun : @DCont A B dA dB toFun
  cont_invFun : @DCont B A dB dA invFun

/-! ## Shape data

The model of a functor `F` with condition `cond`: a domain operator `op`, the order `dom` on the
bodies, and, for every family of domains `D`, a continuous isomorphism between the domain
`op.obj D` and the bodies over the carriers of `D` that satisfy the condition. -/

structure ShapeData (F : Fam.{pu, v} I → Type w)
    (cond : ∀ {X : Fam.{pu, v} I} [∀ k, Dom (X k)], F X → Prop) where
  op : DomainOperator.{pu, v, w} (I)
  dom : ∀ (X : Fam.{pu, v} I) [∀ k, Dom (X k)], Dom (F X)
  cond_sup : ∀ (X : Fam.{pu, v} I) [∀ k, Dom (X k)] (c : @Dom.Chain (F X) (dom X)),
    (∀ n, cond (c n)) → cond (@Dom.sup _ (dom X) c)
  cond_csup : ∀ (X : Fam.{pu, v} I) [∀ k, Dom (X k)], Dom.ChainClosed (dom X) (fun x => cond x)
  conv : ∀ (D : I → Domain.{v}),
    ContRetract (op.obj D).Carrier {x : F (Carriers D) // cond x}
      (Dom.ofDomain (op.obj D))
      (Dom.subtype (dom (Carriers D)) _ ⟨cond_sup (Carriers D), cond_csup (Carriers D)⟩)

/-- `Model.Shape F`: `F` is built from the pieces, with the condition `cond` on its bodies over any
family `X` of admissible types. -/
class Model.Shape (F : Fam.{pu, v} I → Type w) where
  cond : ∀ {X : Fam.{pu, v} I} [∀ k, Dom (X k)], F X → Prop
  sd : ShapeData F cond

/-- `Shape F`: `F` is built from the pieces. -/
abbrev Shape (F : Fam.{pu, v} I → Type w) := Model.Shape F

abbrev Shape.dom (F : Fam.{pu, v} I → Type w) [Shape F] (X : Fam.{pu, v} I) [∀ k, Dom (X k)] : Dom (F X) :=
  (Model.Shape.sd (F := F)).dom X

/-! ## The pieces -/

theorem PProd.ext' {A : Type w₁} {B : Type w₂} {x y : A ×' B} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x = y := by
  cases x; cases y; cases h₁; cases h₂; rfl

/-- A type and its subtype for a trivial predicate (for `const` and `var`). -/
def ContRetract.toTrue {A : Type w} (d : Dom A) (hp : Dom.Closed d (fun _ => True)) :
    ContRetract A (Subtype fun _ : A => True) d (Dom.subtype d _ hp) where
  toFun a := ⟨a, trivial⟩
  invFun x := x.1
  right_inv _ := rfl
  left_inv _ := rfl
  cont_toFun := DCont.intoSubtype d d (f := fun x => ⟨x, trivial⟩) (DCont.mk' _ (fun _ _ h => h) (fun _ => rfl))
  cont_invFun := DCont.subtypeVal d

/-- Constant: a plain field of a pointed admissible type. -/
def Shape.const' (A : Type w) [Dom A] [NonPos.Pointed A] : ShapeData (fun _ : Fam.{pu, v} I => A) (fun _ => True) where
  op := DomainOperator.constant (Domain.ofDom A)
  dom := fun _ _ => inferInstance
  cond_sup := fun X [∀ k, Dom (X k)] _ _ => trivial
  cond_csup := fun X [∀ k, Dom (X k)] _ _ _ _ _ _ => trivial
  conv _ := ContRetract.toTrue _ _

/-- The recursive occurrence `X k`, as a plain field. -/
def Shape.var' (k : I) : ShapeData (fun X : Fam.{pu, v} I => X k) (fun _ => True) where
  op := DomainOperator.variable k
  dom := fun _ inst => inst k
  cond_sup := fun X [∀ k, Dom (X k)] _ _ => trivial
  cond_csup := fun X [∀ k, Dom (X k)] _ _ _ _ _ _ => trivial
  conv _ := ContRetract.toTrue _ _

section Prod
variable {F : Fam.{pu, v} I → Type w₁} {G : Fam.{pu, v} I → Type w₂}
  {cF : ∀ {X : Fam.{pu, v} I} [∀ k, Dom (X k)], F X → Prop}
  {cG : ∀ {X : Fam.{pu, v} I} [∀ k, Dom (X k)], G X → Prop}
  (dF : ShapeData F cF) (dG : ShapeData G cG)

/-- Two fields. -/
def Shape.prod' : ShapeData (fun X => F X ×' G X) (fun x => cF x.1 ∧ cG x.2) where
  op := DomainOperator.product dF.op dG.op
  dom := fun X _ => @Dom.pprod _ _ (dF.dom X) (dG.dom X)
  cond_sup := fun X [∀ k, Dom (X k)] c h =>
    ⟨dF.cond_sup X (@Chain.mk _ (dF.dom X).po (fun n => (c n).1) (fun n => (@Chain.step _ (@Dom.pprod _ _ (dF.dom X) (dG.dom X)).po c n).1))
      (fun n => (h n).1),
     dG.cond_sup X (@Chain.mk _ (dG.dom X).po (fun n => (c n).2) (fun n => (@Chain.step _ (@Dom.pprod _ _ (dF.dom X) (dG.dom X)).po c n).2))
      (fun n => (h n).2)⟩
  cond_csup := fun X [∀ k, Dom (X k)] c hc hne hcond s hs => by
    obtain ⟨h₁, h₂⟩ := Dom.isSup_pprod (dF.dom X) (dG.dom X) hc hne hs
    exact ⟨dF.cond_csup X _ (@chain_image _ _ (@Dom.pprod _ _ (dF.dom X) (dG.dom X)).po (dF.dom X).po PProd.fst
        (fun _ _ h => h.1) c hc) (image_nonempty _ hne) (fun _ ⟨x, hx, e⟩ => e ▸ (hcond x hx).1) _ h₁,
      dG.cond_csup X _ (@chain_image _ _ (@Dom.pprod _ _ (dF.dom X) (dG.dom X)).po (dG.dom X).po PProd.snd
        (fun _ _ h => h.2) c hc) (image_nonempty _ hne) (fun _ ⟨x, hx, e⟩ => e ▸ (hcond x hx).2) _ h₂⟩
  conv D :=
    let rF := dF.conv D
    let rG := dG.conv D
    { toFun := fun y => ⟨⟨(rF.toFun y.1).1, (rG.toFun y.2).1⟩, (rF.toFun y.1).2, (rG.toFun y.2).2⟩
      invFun := fun x => (rF.invFun ⟨x.1.1, x.2.1⟩, rG.invFun ⟨x.1.2, x.2.2⟩)
      right_inv := fun x => by
        apply Subtype.ext
        apply PProd.ext'
        · exact congrArg Subtype.val (rF.right_inv ⟨x.1.1, x.2.1⟩)
        · exact congrArg Subtype.val (rG.right_inv ⟨x.1.2, x.2.2⟩)
      left_inv := fun y => by
        apply Prod.ext
        · exact rF.left_inv y.1
        · exact rG.left_inv y.2
      cont_toFun := DCont.mk' _ (fun x y h => ⟨DCont.mono' rF.cont_toFun h.1, DCont.mono' rG.cont_toFun h.2⟩) (fun c => by
        apply Subtype.ext
        apply PProd.ext'
        · exact congrArg Subtype.val (DCont.sup_eq' rF.cont_toFun (Dom.mkChain (fun n => (c n).1) (fun n => (Dom.step' c n).1)))
        · exact congrArg Subtype.val (DCont.sup_eq' rG.cont_toFun (Dom.mkChain (fun n => (c n).2) (fun n => (Dom.step' c n).2))))
      cont_invFun := DCont.mk' _ (fun x y h => ⟨DCont.mono' rF.cont_invFun h.1, DCont.mono' rG.cont_invFun h.2⟩) (fun c => by
        apply Prod.ext
        · exact DCont.sup_eq' rF.cont_invFun (Dom.mkChain (fun n => ⟨(c n).1.1, (c n).2.1⟩) (fun n => (Dom.step' c n).1))
        · exact DCont.sup_eq' rG.cont_invFun (Dom.mkChain (fun n => ⟨(c n).1.2, (c n).2.2⟩) (fun n => (Dom.step' c n).2))) }
end Prod

section Pi
variable {T : Type w₁} {G : T → Fam.{pu, v} I → Type w₂}
  {cG : ∀ t {X : Fam.{pu, v} I} [∀ k, Dom (X k)], G t X → Prop}
  (dG : ∀ t, ShapeData (G t) (cG t))

/-- A binder `(t : T) → G t X`. -/
def Shape.pi' : ShapeData (fun X => (t : T) → G t X) (fun f => ∀ t, cG t (f t)) where
  op := DomainOperator.pi (fun t => (dG t).op)
  dom := fun X _ => @Dom.pi T (fun t => G t X) (fun t => (dG t).dom X)
  cond_sup := fun X [∀ k, Dom (X k)] c h t => (dG t).cond_sup X
    (@Chain.mk _ ((dG t).dom X).po (fun n => c n t)
      (fun n => (@Chain.step _ (@Dom.pi T (fun t => G t X) (fun t => (dG t).dom X)).po c n) t))
    (fun n => h n t)
  cond_csup := fun X [∀ k, Dom (X k)] c hc hne hcond s hs t =>
    (dG t).cond_csup X _ (@chain_image _ _ (@Dom.pi T (fun t => G t X) (fun t => (dG t).dom X)).po ((dG t).dom X).po
        (fun f => f t) (fun _ _ h => h t) c hc) (image_nonempty _ hne)
      (fun _ ⟨f, hf, e⟩ => e ▸ hcond f hf t) _ (Dom.isSup_pi (fun t => (dG t).dom X) hc hne hs t)
  conv D :=
    let r := fun t => (dG t).conv D
    { toFun := fun y => ⟨fun t => ((r t).toFun (y t)).1, fun t => ((r t).toFun (y t)).2⟩
      invFun := fun x => fun t => (r t).invFun ⟨x.1 t, x.2 t⟩
      right_inv := fun x => by
        apply Subtype.ext
        funext t
        exact congrArg Subtype.val ((r t).right_inv ⟨x.1 t, x.2 t⟩)
      left_inv := fun y => by
        funext t
        exact (r t).left_inv (y t)
      cont_toFun := DCont.mk' _ (fun x y h t => DCont.mono' (r t).cont_toFun (h t)) (fun c => by
        apply Subtype.ext
        funext t
        exact congrArg Subtype.val (DCont.sup_eq' (r t).cont_toFun (Dom.mkChain (fun n => c n t) (fun n => (Dom.step' c n) t))))
      cont_invFun := DCont.mk' _ (fun x y h t => DCont.mono' (r t).cont_invFun (h t)) (fun c => by
        funext t
        exact DCont.sup_eq' (r t).cont_invFun (Dom.mkChain (fun n => ⟨(c n).1 t, (c n).2 t⟩) (fun n => (Dom.step' c n) t))) }
end Pi

section Arr
variable (k : I) {G : Fam.{pu, v} I → Type w}
  {cG : ∀ {X : Fam.{pu, v} I} [∀ k, Dom (X k)], G X → Prop}
  (dG : ShapeData G cG)

/-- The order on `X k → G X` is the pointwise one. -/
abbrev Shape.arrDom (X : Fam.{pu, v} I) [∀ k, Dom (X k)] : Dom (X k → G X) :=
  @Dom.pi (X k) (fun _ => G X) (fun _ => dG.dom X)

/-- The condition on `X k → G X`: continuity, and the condition of the body at every argument. -/
abbrev Shape.arrCond (X : Fam.{pu, v} I) [∀ k, Dom (X k)] (f : X k → G X) : Prop :=
  @DCont _ _ (inferInstance : Dom (X k)) (dG.dom X) f ∧ ∀ d, cG (f d)

/-- The continuous map of a plain field `f` satisfying the condition: convert the body. -/
def Shape.arrFrom (D : I → Domain.{v})
    (f : {x : (D k).Carrier → G (Carriers D) // Shape.arrCond k dG (Carriers D) x}) :
    ContinuousMap (D k) (dG.op.obj D) :=
  { toFun := fun d => (dG.conv D).invFun ⟨f.1 d, f.2.2 d⟩
    cont := DCont.comp' (dB := Dom.subtype (dG.dom (Carriers D)) _ ⟨dG.cond_sup _, dG.cond_csup _⟩)
      (dG.conv D).cont_invFun
      (DCont.intoSubtype (dG.dom (Carriers D)) (Dom.ofDomain (D k)) (f := fun d => ⟨f.1 d, f.2.2 d⟩) f.2.1) }

/-- The plain field of a continuous map: convert the body. -/
def Shape.arrTo (D : I → Domain.{v}) (φ : ContinuousMap (D k) (dG.op.obj D)) :
    {x : (D k).Carrier → G (Carriers D) // Shape.arrCond k dG (Carriers D) x} :=
  ⟨fun x => ((dG.conv D).toFun (φ x)).1, by
    refine ⟨?_, fun x => ((dG.conv D).toFun _).2⟩
    refine DCont.comp' (dB := Dom.subtype (dG.dom (Carriers D)) _ ⟨dG.cond_sup _, dG.cond_csup _⟩) (DCont.subtypeVal _) ?_
    exact DCont.comp' (dB := Dom.ofDomain (dG.op.obj D)) (dG.conv D).cont_toFun φ.cont⟩

/-- `X k → G X`: a dictionary binder. -/
def Shape.arr' : ShapeData (fun X => X k → G X) (fun f => Shape.arrCond k dG _ f) where
  op := DomainOperator.arrow (DomainOperator.variable k) dG.op
  dom := fun X _ => Shape.arrDom k dG X
  cond_sup := fun X [∀ k, Dom (X k)] c h =>
    ⟨DCont.congr' (DCont.supChain' (dD := (inferInstance : Dom (X k))) (dB := dG.dom X)
        (g := fun n d => c n d) (fun n => (h n).1) (fun n d => Dom.step' c n d)) (fun d => rfl),
     fun d => dG.cond_sup X (Dom.mkChain (fun n => c n d) (fun n => Dom.step' c n d)) (fun n => (h n).2 d)⟩
  cond_csup := fun X [∀ k, Dom (X k)] c hc hne hcond s hs =>
    ⟨DCont.of_isSup _ (dG.dom X) (fun f hf => (hcond f hf).1) (Dom.isSup_pi (fun _ => dG.dom X) hc hne hs),
     fun d => dG.cond_csup X _ (@chain_image _ _ (Shape.arrDom k dG X).po (dG.dom X).po
        (fun f => f d) (fun _ _ h => h d) c hc) (image_nonempty _ hne)
      (fun _ ⟨f, hf, e⟩ => e ▸ (hcond f hf).2 d) _ (Dom.isSup_pi (fun _ => dG.dom X) hc hne hs d)⟩
  conv D :=
    let r := dG.conv D
    { toFun := fun φ => Shape.arrTo k dG D φ
      invFun := fun f => Shape.arrFrom k dG D f
      right_inv := fun f => by
        apply Subtype.ext
        funext x
        exact congrArg Subtype.val (r.right_inv ⟨f.1 x, f.2.2 x⟩)
      left_inv := fun φ => by
        apply ContinuousMap.ext
        intro d
        exact r.left_inv (φ d)
      cont_toFun := DCont.mk' _
        (fun φ φ' h x => DCont.mono' r.cont_toFun ((ContinuousMap.rel_iff _ _).1 h x))
        (fun c => by
          apply Subtype.ext
          funext x
          exact congrArg Subtype.val (DCont.sup_eq' r.cont_toFun
            (Dom.mkChain (fun n => (c n) x) (fun n => (ContinuousMap.rel_iff _ _).1 (Dom.step' c n) x))))
      cont_invFun := DCont.mk' _
        (fun f f' h => (ContinuousMap.rel_iff _ _).2 fun d => DCont.mono' r.cont_invFun (h d))
        (fun c => by
          apply ContinuousMap.ext
          intro d
          exact DCont.sup_eq' r.cont_invFun
            (Dom.mkChain (fun n => ⟨(c n).1 d, (c n).2.2 d⟩) (fun n => Dom.step' c n d))) }
end Arr

section Arg
variable (A : Type w₁) [Dom A] [NonPos.Pointed A] {G : Fam.{pu, v} I → Type w}
  {cG : ∀ {X : Fam.{pu, v} I} [∀ k, Dom (X k)], G X → Prop}
  (dG : ShapeData G cG)

/-- The order on `A → G X` is the pointwise one. -/
abbrev Shape.argDom (X : Fam.{pu, v} I) [∀ k, Dom (X k)] : Dom (A → G X) :=
  @Dom.pi A (fun _ => G X) (fun _ => dG.dom X)

/-- The condition on `A → G X`: continuity, and the condition of the body at every argument. -/
abbrev Shape.argCond (X : Fam.{pu, v} I) [∀ k, Dom (X k)] (f : A → G X) : Prop :=
  @DCont _ _ ‹Dom A› (dG.dom X) f ∧ ∀ a, cG (f a)

/-- The continuous map of a field `f` satisfying the condition: convert the body. -/
def Shape.argFrom (D : I → Domain.{v})
    (f : {x : A → G (Carriers D) // Shape.argCond A dG (Carriers D) x}) :
    ContinuousMap (Domain.ofDom A) (dG.op.obj D) :=
  { toFun := fun a => (dG.conv D).invFun ⟨f.1 a, f.2.2 a⟩
    cont := DCont.comp' (dB := Dom.subtype (dG.dom (Carriers D)) _ ⟨dG.cond_sup _, dG.cond_csup _⟩)
      (dG.conv D).cont_invFun
      (DCont.intoSubtype (dG.dom (Carriers D)) (Dom.ofDomain (Domain.ofDom A))
        (f := fun a => ⟨f.1 a, f.2.2 a⟩) f.2.1) }

/-- The field of a continuous map: convert the body. -/
def Shape.argTo (D : I → Domain.{v}) (φ : ContinuousMap (Domain.ofDom A) (dG.op.obj D)) :
    {x : A → G (Carriers D) // Shape.argCond A dG (Carriers D) x} :=
  ⟨fun x => ((dG.conv D).toFun (φ x)).1, by
    refine ⟨?_, fun x => ((dG.conv D).toFun _).2⟩
    refine DCont.comp' (dB := Dom.subtype (dG.dom (Carriers D)) _ ⟨dG.cond_sup _, dG.cond_csup _⟩) (DCont.subtypeVal _) ?_
    exact DCont.comp' (dB := Dom.ofDomain (dG.op.obj D)) (dG.conv D).cont_toFun φ.cont⟩

/-- `A → G X`, for a fixed `A`: an argument of a type with an order. -/
def Shape.arg' : ShapeData (fun X => A → G X) (fun f => Shape.argCond A dG _ f) where
  op := DomainOperator.arrow (DomainOperator.constant (Domain.ofDom A)) dG.op
  dom := fun X _ => Shape.argDom A dG X
  cond_sup := fun X [∀ k, Dom (X k)] c h =>
    ⟨DCont.congr' (DCont.supChain' (dD := ‹Dom A›) (dB := dG.dom X)
        (g := fun n a => c n a) (fun n => (h n).1) (fun n a => Dom.step' c n a)) (fun a => rfl),
     fun a => dG.cond_sup X (Dom.mkChain (fun n => c n a) (fun n => Dom.step' c n a)) (fun n => (h n).2 a)⟩
  cond_csup := fun X [∀ k, Dom (X k)] c hc hne hcond s hs =>
    ⟨DCont.of_isSup _ (dG.dom X) (fun f hf => (hcond f hf).1) (Dom.isSup_pi (fun _ => dG.dom X) hc hne hs),
     fun a => dG.cond_csup X _ (@chain_image _ _ (Shape.argDom A dG X).po (dG.dom X).po
        (fun f => f a) (fun _ _ h => h a) c hc) (image_nonempty _ hne)
      (fun _ ⟨f, hf, e⟩ => e ▸ (hcond f hf).2 a) _ (Dom.isSup_pi (fun _ => dG.dom X) hc hne hs a)⟩
  conv D :=
    let r := dG.conv D
    { toFun := fun φ => Shape.argTo A dG D φ
      invFun := fun f => Shape.argFrom A dG D f
      right_inv := fun f => by
        apply Subtype.ext
        funext x
        exact congrArg Subtype.val (r.right_inv ⟨f.1 x, f.2.2 x⟩)
      left_inv := fun φ => by
        apply ContinuousMap.ext
        intro a
        exact r.left_inv (φ a)
      cont_toFun := DCont.mk' _
        (fun φ φ' h x => DCont.mono' r.cont_toFun ((ContinuousMap.rel_iff _ _).1 h x))
        (fun c => by
          apply Subtype.ext
          funext x
          exact congrArg Subtype.val (DCont.sup_eq' r.cont_toFun
            (Dom.mkChain (fun n => (c n) x) (fun n => (ContinuousMap.rel_iff _ _).1 (Dom.step' c n) x))))
      cont_invFun := DCont.mk' _
        (fun f f' h => (ContinuousMap.rel_iff _ _).2 fun a => DCont.mono' r.cont_invFun (h a))
        (fun c => by
          apply ContinuousMap.ext
          intro a
          exact DCont.sup_eq' r.cont_invFun
            (Dom.mkChain (fun n => ⟨(c n).1 a, (c n).2.2 a⟩) (fun n => Dom.step' c n a))) }
end Arg

/-! ## The shapes: the model of each piece -/

section Instances
variable {I : Type pu}

/-- Constant: a plain field of a pointed admissible type. -/
@[reducible] def Model.Shape.const (A : Type w) [Dom A] [NonPos.Pointed A] :
    ShapeData (fun _ : Fam.{pu, v} I => A) (fun _ => True) :=
  { Shape.const' A with dom := fun _ _ => ‹Dom A› }
/-- A plain field of a structure of the group. -/
@[reducible] def Model.Shape.var (k : I) : ShapeData (fun X : Fam.{pu, v} I => X k) (fun _ => True) :=
  { Shape.var' k with dom := fun _ inst => inst k }
/-- A binder. -/
@[reducible] def Model.Shape.pi (T : Type w₁) (G : T → Fam.{pu, v} I → Type w₂) [∀ t, Shape (G t)] :
    ShapeData (fun X => (t : T) → G t X) (fun f => ∀ t, Model.Shape.cond (F := G t) (f t)) :=
  { Shape.pi' (fun t => Model.Shape.sd (F := G t)) with
    dom := fun X [∀ k, Dom (X k)] => @Dom.pi T (fun t => G t X) (fun t => Shape.dom (G t) X) }
/-- A dictionary binder. -/
@[reducible] def Model.Shape.arr (k : I) (G : Fam.{pu, v} I → Type w) [Shape G] :
    ShapeData (fun X => X k → G X)
      (fun f => DCont (inst_1 := Shape.dom (F := G) _) f ∧ ∀ d, Model.Shape.cond (F := G) (f d)) :=
  { Shape.arr' k (Model.Shape.sd (F := G)) with
    dom := fun X [∀ k, Dom (X k)] => @Dom.pi (X k) (fun _ => G X) (fun _ => Shape.dom G X) }
/-- An argument of a type with an order (`A → G X`, `A` fixed). -/
@[reducible] def Model.Shape.arg (A : Type w₁) [Dom A] [NonPos.Pointed A] (G : Fam.{pu, v} I → Type w) [Shape G] :
    ShapeData (fun X => A → G X)
      (fun f => DCont (inst_1 := Shape.dom (F := G) _) f ∧ ∀ a, Model.Shape.cond (F := G) (f a)) :=
  { Shape.arg' A (Model.Shape.sd (F := G)) with
    dom := fun X [∀ k, Dom (X k)] => @Dom.pi A (fun _ => G X) (fun _ => Shape.dom G X) }
/-- Two fields. -/
@[reducible] def Model.Shape.prod (F : Fam.{pu, v} I → Type w₁) (G : Fam.{pu, v} I → Type w₂) [Shape F] [Shape G] :
    ShapeData (fun X => F X ×' G X) (fun x => Model.Shape.cond (F := F) x.1 ∧ Model.Shape.cond (F := G) x.2) :=
  { Shape.prod' (Model.Shape.sd (F := F)) (Model.Shape.sd (F := G)) with
    dom := fun X [∀ k, Dom (X k)] => @Dom.pprod (F X) (G X) (Shape.dom F X) (Shape.dom G X) }
end Instances

end
end NonPos
