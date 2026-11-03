module
public import Aeneas.NonPos.Domain.Operator
public import Aeneas.NonPos.Model.Lift

@[expose] public section
/-!
# Shapes

A shape of a functor `F : Fam I → Type w` is: a domain operator `op` (the lifted, pointed version of
`F`), the plain order on `F X`, the condition `cond`, the own-data totality `total` on `op.obj D`, the
var targets, and a continuous retraction between the total elements of `op.obj D` and the elements
of `F X` satisfying the condition, for every pointed family `D` with totality `T`.

In this file `Dom`s are passed explicitly (the ones of subtypes are not instances).
-/
namespace NonPos
open NonPos.Domain NonPos.Model Lean.Order

universe pu v w w₁ w₂

noncomputable section
set_option warn.classDefReducibility false
attribute [local instance] Dom.unit Dom.prod Dom.pi Dom.pprod NonPosMonad.dom
attribute [local instance] Pointed.unit Pointed.prod Pointed.pprod Pointed.pi Pointed.ofCCPO Pointed.monad FixCompat.pointed FixCompat.ofCCPO FixCompat.monad FixCompat.pi FixCompat.prod FixCompat.pprod

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
  fun _ _ ⟨x, hx⟩ hp s hs => h (@isSup_le A d.po _ _ hs x hx) (hp x hx)

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
theorem Cont.of_isSup {D : Type w₁} {B : Type w₂} (dD : Dom D) (dB : Dom B) {c : (D → B) → Prop}
    (hcont : ∀ f, c f → @Cont D B dD dB f) {s : D → B}
    (hs : ∀ x, @is_sup B dB.po (image (fun f : D → B => f x) c) (s x)) : @Cont D B dD dB s := by
  letI := dB.po
  have mono : ∀ x y, @Dom.le D dD x y → @Dom.le B dB (s x) (s y) := fun x y hxy =>
    isSup_le_of (hs x) fun _ ⟨f, hf, e⟩ => e ▸
      PartialOrder.rel_trans (Cont.mono' (hcont f hf) hxy) (isSup_le (hs y) ⟨f, hf, rfl⟩)
  refine Cont.mk' s mono (fun d => @Dom.le_antisymm B dB _ _ ?_ ?_)
  · refine isSup_le_of (hs _) fun _ ⟨f, hf, e⟩ => ?_
    subst e
    show @Dom.le B dB (f (@Dom.sup D dD d)) _
    rw [Cont.sup_eq' (hcont f hf)]
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

theorem Cont.subtypeVal : @Cont {a // p a} A (Dom.subtype dA p hp) dA (fun x => x.1) :=
  Cont.mk' _ (fun _ _ h => h) (fun _ => rfl)

/-- A continuous map which preserves the predicates, as a map between the subtypes. -/
theorem Cont.subtypeMk {f : A → B} (hf : @Cont A B dA dB f) (h : ∀ a, p a → q (f a)) :
    @Cont {a // p a} {b // q b} (Dom.subtype dA p hp) (Dom.subtype dB q hq) (fun x => ⟨f x.1, h x.1 x.2⟩) := by
  refine Cont.mk' _ (fun x y hxy => Cont.mono' hf hxy) (fun c => ?_)
  apply Subtype.ext
  show f (@Dom.sup A dA (Dom.vals dA c)) = _
  rw [Cont.sup_eq' hf]; rfl

/-- Continuity of a map into a subtype, from continuity of its value. -/
theorem Cont.intoSubtype {D : Type w} (dD : Dom D) {f : D → {b // q b}}
    (hf : @Cont D B dD dB (fun d => (f d).1)) : @Cont D {b // q b} dD (Dom.subtype dB q hq) f := by
  refine Cont.mk' _ (fun x y hxy => Cont.mono' hf hxy) (fun c => ?_)
  apply Subtype.ext
  exact Cont.sup_eq' hf c
end Subtype

/-! ## Pointed families with totality -/

structure TFam (I : Type pu) : Type (max pu (v + 1)) where
  D : I → Domain.{v}
  T : ∀ k, (D k).Carrier → Prop
  mono : ∀ k {x y : (D k).Carrier}, x ⊑ y → T k x → T k y
  sup : ∀ k (c : Chain (D k).Carrier), (∀ n, T k (c n)) → T k (OmegaSup.sup c)
  ev : ∀ k (c : Chain (D k).Carrier), T k (OmegaSup.sup c) → ∃ n, T k (c n)

/-- The plain family: the total elements. -/
def TFam.X (Φ : TFam.{pu, v} I) : Fam.{pu, v} I := fun k => {d : (Φ.D k).Carrier // Φ.T k d}

/-- The admissible structure of `Φ.X k`. -/
def TFam.dom (Φ : TFam.{pu, v} I) (k : I) : Dom (Φ.X k) :=
  Dom.subtype (Dom.ofDomain (Φ.D k)) _ ⟨Φ.sup k, Dom.ChainClosed.of_mono (Φ.mono k)⟩
@[instance_reducible] def TFam.instDom (Φ : TFam.{pu, v} I) (k : I) : Dom (Φ.X k) := Φ.dom k
attribute [local instance] TFam.instDom

/-! ## Continuous retractions -/

structure ContRetract (A : Type w₁) (B : Type w₂) (dA : Dom A) (dB : Dom B) where
  toFun : A → B
  invFun : B → A
  right_inv : ∀ b, toFun (invFun b) = b
  cont_toFun : @Cont A B dA dB toFun
  cont_invFun : @Cont B A dB dA invFun

/-! ## Shape data

The model of a functor `F` with condition `cond`.  Totality `total D T y` of an element of the
operator's domain is relative to a totality predicate `T` on the family `D` (used by the plain
fields of structures of the group); it must be monotone in `T` and finitary (`total_imp`,
`total_fin`), so that the totality of the group can be defined as a least fixed point. -/

/-- The type of totality predicates on a family of domains. -/
abbrev TPred (D : I → Domain.{v}) := ∀ k, (D k).Carrier → Prop

structure ShapeData (F : Fam.{pu, v} I → Type w)
    (cond : ∀ {X : Fam.{pu, v} I} [∀ k, Dom (X k)], F X → Prop) where
  op : DomainOperator.{pu, v, w} (I)
  dom : ∀ (X : Fam.{pu, v} I) [∀ k, Dom (X k)], Dom (F X)
  cond_sup : ∀ (X : Fam.{pu, v} I) [∀ k, Dom (X k)] (c : @Dom.Chain (F X) (dom X)),
    (∀ n, cond (c n)) → cond (@Dom.sup _ (dom X) c)
  cond_csup : ∀ (X : Fam.{pu, v} I) [∀ k, Dom (X k)], Dom.ChainClosed (dom X) (fun x => cond x)
  total : ∀ (D : I → Domain.{v}), TPred D → (op.obj D).Carrier → Prop
  total_mono : ∀ (Φ : TFam.{pu, v} I) {y y' : (op.obj Φ.D).Carrier}, y ⊑ y' → total Φ.D Φ.T y → total Φ.D Φ.T y'
  total_sup : ∀ (Φ : TFam.{pu, v} I) (c : Chain (op.obj Φ.D).Carrier),
    (∀ n, total Φ.D Φ.T (c n)) → total Φ.D Φ.T (OmegaSup.sup c)
  total_ev : ∀ (Φ : TFam.{pu, v} I) (c : Chain (op.obj Φ.D).Carrier),
    total Φ.D Φ.T (OmegaSup.sup c) → ∃ n, total Φ.D Φ.T (c n)
  total_imp : ∀ D (T T' : TPred D), (∀ k d, T k d → T' k d) → ∀ y, total D T y → total D T' y
  total_fin : ∀ D (Tn : Nat → TPred D), (∀ n k d, Tn n k d → Tn (n + 1) k d) →
    ∀ y, total D (fun k d => ∃ n, Tn n k d) y → ∃ n, total D (Tn n) y
  conv : ∀ (Φ : TFam.{pu, v} I),
    ContRetract {y : (op.obj Φ.D).Carrier // total Φ.D Φ.T y} {x : F Φ.X // cond x}
      (Dom.subtype (Dom.ofDomain (op.obj Φ.D)) _ ⟨total_sup Φ, Dom.ChainClosed.of_mono (total_mono Φ)⟩)
      (Dom.subtype (dom Φ.X) _ ⟨cond_sup Φ.X, cond_csup Φ.X⟩)

/-- `Shape F`: `F` is built from the pieces, with the condition `cond` on its bodies. -/
class Shape (F : Fam.{pu, v} I → Type w) where
  cond : ∀ {X : Fam.{pu, v} I} [∀ k, Dom (X k)], F X → Prop
  sd : ShapeData F cond

def Shape.dom (F : Fam.{pu, v} I → Type w) [Shape F] (X : Fam.{pu, v} I) [∀ k, Dom (X k)] : Dom (F X) :=
  (Shape.sd (F := F)).dom X

/-- A pointed shape: no plain field of unpointed type (so no lifting, totality is trivial). -/
class Shape.Pointed (F : Fam.{pu, v} I → Type w) [inst : Shape F] : Prop where
  total : ∀ D T y, (Shape.sd (F := F)).total D T y

/-- Stages of totality are monotone. -/
theorem TPred.le {D : I → Domain.{v}} {Tn : Nat → TPred D} (h : ∀ n k d, Tn n k d → Tn (n + 1) k d)
    {n m : Nat} (hnm : n ≤ m) {k d} (hd : Tn n k d) : Tn m k d := by
  induction hnm with
  | refl => exact hd
  | step _ ih => exact h _ _ _ ih

/-! ## The pieces -/

theorem PProd.ext' {A : Type w₁} {B : Type w₂} {x y : A ×' B} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x = y := by
  cases x; cases y; cases h₁; cases h₂; rfl

/-- The identity retraction between two subtypes of the same type (for `const` and `var`). -/
def ContRetract.trivialOfId {A : Type w} (d : Dom A) {p q : A → Prop} (hp hq)
    (h₁ : ∀ a, p a → q a) (h₂ : ∀ a, q a → p a) :
    ContRetract {a // p a} {a // q a} (Dom.subtype d p hp) (Dom.subtype d q hq) where
  toFun x := ⟨x.1, h₁ _ x.2⟩
  invFun x := ⟨x.1, h₂ _ x.2⟩
  right_inv _ := rfl
  cont_toFun := Cont.subtypeMk d d (f := fun a => a) (hp := hp) (hq := hq) (Cont.mk' _ (fun _ _ h => h) (fun _ => rfl)) h₁
  cont_invFun := Cont.subtypeMk d d (f := fun a => a) (hp := hq) (hq := hp) (Cont.mk' _ (fun _ _ h => h) (fun _ => rfl)) h₂

/-- A chain of total lifted elements is the lift of the chain of their values. -/
theorem Lift.vals_eq_upChain {A : Type w} [Dom A]
    (c : @Dom.Chain {y : Lift A // Lift.isUp y}
      (Dom.subtype (Dom.ofDomain (Lift.domain A)) _
        ⟨fun c h => Lift.isUp_sup c h, Dom.ChainClosed.of_mono (fun h hx => Lift.isUp_mono h hx)⟩)) :
    Dom.vals (Dom.ofDomain (Lift.domain A)) c =
      Lift.upChain (@Domain.Chain.mk A Dom.po (fun n => Lift.get (c n).1 (c n).2)
        (fun n => Lift.get_mono (@Domain.Chain.step _ (Dom.subtype (Dom.ofDomain (Lift.domain A)) _ _).po c n))) :=
  Domain.Chain.ext fun n => (Lift.up_get (c n).1 (c n).2).symm

/-- Data: a plain field of any admissible type, lifted. -/
def Shape.data' (A : Type w) [Dom A] : ShapeData (fun _ : Fam.{pu, v} I => A) (fun _ => True) where
  op := DomainOperator.constant (Lift.domain A)
  dom _ := inferInstance
  cond_sup := fun X [∀ k, Dom (X k)] _ _ => trivial
  cond_csup := fun X [∀ k, Dom (X k)] _ _ _ _ _ _ => trivial
  total := fun _ _ y => Lift.isUp y
  total_mono := fun _ {_ _} h hy => Lift.isUp_mono h hy
  total_sup := fun _ c h => Lift.isUp_sup c h
  total_ev := fun _ c h => Lift.isUp_eventually c h
  total_imp := fun _ _ _ _ _ h => h
  total_fin := fun _ _ _ _ h => ⟨0, h⟩
  conv Φ :=
    { toFun := fun y => ⟨Lift.get y.1 y.2, trivial⟩
      invFun := fun x => ⟨Lift.up x.1, Lift.isUp_up _⟩
      right_inv := fun _ => rfl
      cont_toFun := by
        refine Cont.mk' _ (fun x y h => Lift.get_mono h) (fun c => ?_)
        apply Subtype.ext
        apply Lift.get_of_eq
        show @Dom.sup (Lift A) (Dom.ofDomain (Lift.domain A)) (Dom.vals (Dom.ofDomain (Lift.domain A)) c) = _
        rw [Lift.vals_eq_upChain c]
        exact Lift.sup_upChain _
      cont_invFun := by
        refine Cont.mk' _ (fun x y h => Lift.up_mono h) (fun c => ?_)
        apply Subtype.ext
        exact (Lift.sup_upChain (Dom.vals _ c)).symm }

/-- Constant: a plain field of a pointed admissible type. -/
def Shape.const' (A : Type w) [Dom A] [NonPos.Pointed A] : ShapeData (fun _ : Fam.{pu, v} I => A) (fun _ => True) where
  op := DomainOperator.constant (Domain.ofDom A)
  dom _ := inferInstance
  cond_sup := fun X [∀ k, Dom (X k)] _ _ => trivial
  cond_csup := fun X [∀ k, Dom (X k)] _ _ _ _ _ _ => trivial
  total := fun _ _ _ => True
  total_mono := fun _ {_ _} _ _ => trivial
  total_sup := fun _ _ _ => trivial
  total_ev := fun _ _ _ => ⟨0, trivial⟩
  total_imp := fun _ _ _ _ _ _ => trivial
  total_fin := fun _ _ _ _ _ => ⟨0, trivial⟩
  conv _ := ContRetract.trivialOfId _ _ _ (fun _ _ => trivial) (fun _ _ => trivial)

/-- The recursive occurrence `X k`, as a plain field: total when the field is. -/
def Shape.var' (k : I) : ShapeData (fun X : Fam.{pu, v} I => X k) (fun _ => True) where
  op := DomainOperator.variable k
  dom X := inferInstance
  cond_sup := fun X [∀ k, Dom (X k)] _ _ => trivial
  cond_csup := fun X [∀ k, Dom (X k)] _ _ _ _ _ _ => trivial
  total := fun _ T y => T k y
  total_mono := fun Φ {_ _} h hy => Φ.mono k h hy
  total_sup := fun Φ c h => Φ.sup k c h
  total_ev := fun Φ c h => Φ.ev k c h
  total_imp := fun _ _ _ h _ hy => h k _ hy
  total_fin := fun _ _ _ _ h => h
  conv Φ :=
    { toFun := fun y => ⟨⟨y.1, y.2⟩, trivial⟩
      invFun := fun x => ⟨x.1.1, x.1.2⟩
      right_inv := fun _ => rfl
      cont_toFun := Cont.mk' _ (fun _ _ h => h) (fun _ => rfl)
      cont_invFun := Cont.mk' _ (fun _ _ h => h) (fun _ => rfl) }

section Prod
variable {F : Fam.{pu, v} I → Type w₁} {G : Fam.{pu, v} I → Type w₂}
  {cF : ∀ {X : Fam.{pu, v} I} [∀ k, Dom (X k)], F X → Prop}
  {cG : ∀ {X : Fam.{pu, v} I} [∀ k, Dom (X k)], G X → Prop}
  (dF : ShapeData F cF) (dG : ShapeData G cG)

/-- Two fields. -/
def Shape.prod' : ShapeData (fun X => F X ×' G X) (fun x => cF x.1 ∧ cG x.2) where
  op := DomainOperator.product dF.op dG.op
  dom := fun X [∀ k, Dom (X k)] => @Dom.pprod _ _ (dF.dom X) (dG.dom X)
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
  total := fun D T y => dF.total D T y.1 ∧ dG.total D T y.2
  total_mono := fun Φ {_ _} h hy => ⟨dF.total_mono Φ h.1 hy.1, dG.total_mono Φ h.2 hy.2⟩
  total_sup := fun Φ c h => ⟨dF.total_sup Φ c.fst (fun n => (h n).1), dG.total_sup Φ c.snd (fun n => (h n).2)⟩
  total_ev := fun Φ c h =>
    let ⟨n₁, h₁⟩ := dF.total_ev Φ c.fst h.1
    let ⟨n₂, h₂⟩ := dG.total_ev Φ c.snd h.2
    ⟨max n₁ n₂, dF.total_mono Φ (c.le (Nat.le_max_left n₁ n₂)).1 h₁, dG.total_mono Φ (c.le (Nat.le_max_right n₁ n₂)).2 h₂⟩
  total_imp := fun D T T' h y hy => ⟨dF.total_imp D T T' h y.1 hy.1, dG.total_imp D T T' h y.2 hy.2⟩
  total_fin := fun D Tn hTn y hy =>
    let ⟨n₁, h₁⟩ := dF.total_fin D Tn hTn y.1 hy.1
    let ⟨n₂, h₂⟩ := dG.total_fin D Tn hTn y.2 hy.2
    ⟨max n₁ n₂, dF.total_imp D _ _ (fun _ _ => TPred.le hTn (Nat.le_max_left n₁ n₂)) y.1 h₁,
      dG.total_imp D _ _ (fun _ _ => TPred.le hTn (Nat.le_max_right n₁ n₂)) y.2 h₂⟩
  conv Φ :=
    let rF := dF.conv Φ
    let rG := dG.conv Φ
    { toFun := fun y => ⟨⟨(rF.toFun ⟨y.1.1, y.2.1⟩).1, (rG.toFun ⟨y.1.2, y.2.2⟩).1⟩, (rF.toFun _).2, (rG.toFun _).2⟩
      invFun := fun x => ⟨((rF.invFun ⟨x.1.1, x.2.1⟩).1, (rG.invFun ⟨x.1.2, x.2.2⟩).1), (rF.invFun _).2, (rG.invFun _).2⟩
      right_inv := fun x => by
        apply Subtype.ext
        apply PProd.ext'
        · exact congrArg Subtype.val (rF.right_inv ⟨x.1.1, x.2.1⟩)
        · exact congrArg Subtype.val (rG.right_inv ⟨x.1.2, x.2.2⟩)
      cont_toFun := Cont.mk' _ (fun x y h => ⟨Cont.mono' rF.cont_toFun h.1, Cont.mono' rG.cont_toFun h.2⟩) (fun c => by
        apply Subtype.ext
        apply PProd.ext'
        · exact congrArg Subtype.val (Cont.sup_eq' rF.cont_toFun (Dom.mkChain (fun n => ⟨(c n).1.1, (c n).2.1⟩) (fun n => (Dom.step' c n).1)))
        · exact congrArg Subtype.val (Cont.sup_eq' rG.cont_toFun (Dom.mkChain (fun n => ⟨(c n).1.2, (c n).2.2⟩) (fun n => (Dom.step' c n).2))))
      cont_invFun := Cont.mk' _ (fun x y h => ⟨Cont.mono' rF.cont_invFun h.1, Cont.mono' rG.cont_invFun h.2⟩) (fun c => by
        apply Subtype.ext
        apply Prod.ext
        · exact congrArg Subtype.val (Cont.sup_eq' rF.cont_invFun (Dom.mkChain (fun n => ⟨(c n).1.1, (c n).2.1⟩) (fun n => (Dom.step' c n).1)))
        · exact congrArg Subtype.val (Cont.sup_eq' rG.cont_invFun (Dom.mkChain (fun n => ⟨(c n).1.2, (c n).2.2⟩) (fun n => (Dom.step' c n).2)))) }
end Prod

section Pi
variable {T : Type w₁} {G : T → Fam.{pu, v} I → Type w₂}
  {cG : ∀ t {X : Fam.{pu, v} I} [∀ k, Dom (X k)], G t X → Prop}
  (dG : ∀ t, ShapeData (G t) (cG t)) (hG : ∀ t D T y, (dG t).total D T y)

/-- A binder `(t : T) → G t X`, whose body is pointed. -/
def Shape.pi' : ShapeData (fun X => (t : T) → G t X) (fun f => ∀ t, cG t (f t)) where
  op := DomainOperator.pi (fun t => (dG t).op)
  dom := fun X [∀ k, Dom (X k)] => @Dom.pi T (fun t => G t X) (fun t => (dG t).dom X)
  cond_sup := fun X [∀ k, Dom (X k)] c h t => (dG t).cond_sup X
    (@Chain.mk _ ((dG t).dom X).po (fun n => c n t)
      (fun n => (@Chain.step _ (@Dom.pi T (fun t => G t X) (fun t => (dG t).dom X)).po c n) t))
    (fun n => h n t)
  cond_csup := fun X [∀ k, Dom (X k)] c hc hne hcond s hs t =>
    (dG t).cond_csup X _ (@chain_image _ _ (@Dom.pi T (fun t => G t X) (fun t => (dG t).dom X)).po ((dG t).dom X).po
        (fun f => f t) (fun _ _ h => h t) c hc) (image_nonempty _ hne)
      (fun _ ⟨f, hf, e⟩ => e ▸ hcond f hf t) _ (Dom.isSup_pi (fun t => (dG t).dom X) hc hne hs t)
  total := fun _ _ _ => True
  total_mono := fun _ {_ _} _ _ => trivial
  total_sup := fun _ _ _ => trivial
  total_ev := fun _ _ _ => ⟨0, trivial⟩
  total_imp := fun _ _ _ _ _ _ => trivial
  total_fin := fun _ _ _ _ _ => ⟨0, trivial⟩
  conv Φ :=
    let r := fun t => (dG t).conv Φ
    { toFun := fun y => ⟨fun t => ((r t).toFun ⟨y.1 t, hG t _ _ _⟩).1, fun t => ((r t).toFun _).2⟩
      invFun := fun x => ⟨fun t => ((r t).invFun ⟨x.1 t, x.2 t⟩).1, trivial⟩
      right_inv := fun x => by
        apply Subtype.ext
        funext t
        exact congrArg Subtype.val ((r t).right_inv ⟨x.1 t, x.2 t⟩)
      cont_toFun := Cont.mk' _ (fun x y h t => Cont.mono' (r t).cont_toFun (h t)) (fun c => by
        apply Subtype.ext
        funext t
        exact congrArg Subtype.val (Cont.sup_eq' (r t).cont_toFun (Dom.mkChain (fun n => ⟨(c n).1 t, hG t _ _ _⟩) (fun n => (Dom.step' c n) t))))
      cont_invFun := Cont.mk' _ (fun x y h t => Cont.mono' (r t).cont_invFun (h t)) (fun c => by
        apply Subtype.ext
        funext t
        exact congrArg Subtype.val (Cont.sup_eq' (r t).cont_invFun (Dom.mkChain (fun n => ⟨(c n).1 t, (c n).2 t⟩) (fun n => (Dom.step' c n) t)))) }
end Pi

section Arr
open Classical
variable (k : I) {G : Fam.{pu, v} I → Type w}
  {cG : ∀ {X : Fam.{pu, v} I} [∀ k, Dom (X k)], G X → Prop}
  (dG : ShapeData G cG) (hG : ∀ D T y, dG.total D T y)

/-- The order on `X k → G X` is the pointwise one. -/
abbrev Shape.arrDom (X : Fam.{pu, v} I) [∀ k, Dom (X k)] : Dom (X k → G X) :=
  @Dom.pi (X k) (fun _ => G X) (fun _ => dG.dom X)

/-- The condition on `X k → G X`: continuity, and the condition of the body at every argument. -/
abbrev Shape.arrCond (X : Fam.{pu, v} I) [∀ k, Dom (X k)] (f : X k → G X) : Prop :=
  @Cont _ _ (inferInstance : Dom (X k)) (dG.dom X) f ∧ ∀ d, cG (f d)

/-- The extension of a plain field `f : Φ.X k → G Φ.X` satisfying the condition to all of `Φ.D k`,
by `⊥` off the total elements. -/
def Shape.arrExt (Φ : TFam.{pu, v} I)
    (f : {x : Φ.X k → G Φ.X // Shape.arrCond k dG Φ.X x}) :
    ContinuousMap (Φ.D k) (dG.op.obj Φ.D) :=
  let r := dG.conv Φ
  { toFun := fun d => if h : Φ.T k d then (r.invFun ⟨f.1 ⟨d, h⟩, f.2.2 _⟩).1 else OmegaComplete.bottom
    cont := by
      refine Continuous.of_le (fun d d' hdd' => ?_) (fun c => ?_)
      · by_cases h : Φ.T k d
        · have h' : Φ.T k d' := Φ.mono k hdd' h
          rw [dite_eq_left h, dite_eq_left h']
          exact Cont.mono' r.cont_invFun (Cont.mono' f.2.1 hdd')
        · rw [dite_eq_right h]; exact OmegaComplete.bottom_le _
      · by_cases hs : Φ.T k (OmegaSup.sup c)
        · obtain ⟨n₀, hn₀⟩ := Φ.ev k c hs
          have ht : ∀ n, Φ.T k (c (n₀ + n)) := fun n => Φ.mono k (c.le (Nat.le_add_right n₀ n)) hn₀
          let c' : @Dom.Chain (Φ.X k) (Φ.dom k) :=
            Dom.mkChain (fun n => ⟨c (n₀ + n), ht n⟩) (fun n => c.step (n₀ + n))
          have hsup : (@Dom.sup _ (Φ.dom k) c').1 = OmegaSup.sup c := sup_drop c n₀
          rw [dite_eq_left hs]
          have e1 : (⟨OmegaSup.sup c, hs⟩ : Φ.X k) = @Dom.sup _ (Φ.dom k) c' := Subtype.ext hsup.symm
          rw [e1]
          have e2 : (⟨f.1 (@Dom.sup _ (Φ.dom k) c'), f.2.2 _⟩ : {x // cG x}) =
              @Dom.sup _ (Dom.subtype (dG.dom Φ.X) _ ⟨dG.cond_sup Φ.X, dG.cond_csup Φ.X⟩)
                (Dom.mkChain (fun n => ⟨f.1 (c' n), f.2.2 _⟩) (fun n => Cont.mono' f.2.1 (Dom.step' c' n))) :=
            Subtype.ext (Cont.sup_eq' f.2.1 c')
          rw [e2, Cont.sup_eq' r.cont_invFun]
          apply @Dom.sup_le _ (Dom.ofDomain (dG.op.obj Φ.D))
          intro n
          refine PartialOrder.rel_trans ?_ (@Dom.le_sup _ (Dom.ofDomain (dG.op.obj Φ.D)) _ (n₀ + n))
          show (r.invFun ⟨f.1 (c' n), _⟩).1 ⊑ (if h : Φ.T k (c (n₀ + n)) then _ else _)
          rw [dite_eq_left (ht n)]
          exact PartialOrder.rel_refl
        · rw [dite_eq_right hs]
          exact OmegaComplete.bottom_le _ }

theorem Shape.arrExt_apply_total (Φ : TFam.{pu, v} I) (f) (d : (Φ.D k).Carrier) (h : Φ.T k d) :
    Shape.arrExt k dG Φ f d = ((dG.conv Φ).invFun ⟨f.1 ⟨d, h⟩, f.2.2 _⟩).1 := by
  show (if h : Φ.T k d then _ else _) = _
  rw [dite_eq_left h]

theorem Shape.arrExt_apply_not (Φ : TFam.{pu, v} I) (f) (d : (Φ.D k).Carrier) (h : ¬ Φ.T k d) :
    Shape.arrExt k dG Φ f d = OmegaComplete.bottom := by
  show (if h : Φ.T k d then _ else _) = _
  rw [dite_eq_right h]

/-- The plain field of a bundled continuous map: restrict to the total elements and convert the body. -/
def Shape.arrTo (Φ : TFam.{pu, v} I)
    (φ : ContinuousMap (Φ.D k) (dG.op.obj Φ.D)) : {x : Φ.X k → G Φ.X // Shape.arrCond k dG Φ.X x} :=
  let r := dG.conv Φ
  ⟨fun x => (r.toFun ⟨φ x.1, hG _ _ _⟩).1, by
    refine ⟨?_, fun x => (r.toFun _).2⟩
    refine Cont.comp' (dB := Dom.subtype (dG.dom Φ.X) _ ⟨dG.cond_sup Φ.X, dG.cond_csup Φ.X⟩) (Cont.subtypeVal _) ?_
    refine Cont.comp' (dB := Dom.subtype (Dom.ofDomain (dG.op.obj Φ.D)) _ ⟨dG.total_sup Φ, Dom.ChainClosed.of_mono (dG.total_mono Φ)⟩) r.cont_toFun ?_
    refine Cont.intoSubtype (Dom.ofDomain (dG.op.obj Φ.D)) (Φ.dom k) (f := fun x => ⟨φ x.1, hG _ _ _⟩) ?_
    exact Cont.comp' (dB := Dom.ofDomain (Φ.D k)) φ.cont (Cont.subtypeVal _)⟩

/-- `X k → G X`: a dictionary binder, whose body is pointed. -/
def Shape.arr' : ShapeData (fun X => X k → G X) (fun f => Shape.arrCond k dG _ f) where
  op := DomainOperator.arrow (DomainOperator.variable k) dG.op
  dom := fun X [∀ k, Dom (X k)] => Shape.arrDom k dG X
  cond_sup := fun X [∀ k, Dom (X k)] c h =>
    ⟨Cont.congr' (Cont.supChain' (dD := (inferInstance : Dom (X k))) (dB := dG.dom X)
        (g := fun n d => c n d) (fun n => (h n).1) (fun n d => Dom.step' c n d)) (fun d => rfl),
     fun d => dG.cond_sup X (Dom.mkChain (fun n => c n d) (fun n => Dom.step' c n d)) (fun n => (h n).2 d)⟩
  cond_csup := fun X [∀ k, Dom (X k)] c hc hne hcond s hs =>
    ⟨Cont.of_isSup _ (dG.dom X) (fun f hf => (hcond f hf).1) (Dom.isSup_pi (fun _ => dG.dom X) hc hne hs),
     fun d => dG.cond_csup X _ (@chain_image _ _ (Shape.arrDom k dG X).po (dG.dom X).po
        (fun f => f d) (fun _ _ h => h d) c hc) (image_nonempty _ hne)
      (fun _ ⟨f, hf, e⟩ => e ▸ (hcond f hf).2 d) _ (Dom.isSup_pi (fun _ => dG.dom X) hc hne hs d)⟩
  total := fun _ _ _ => True
  total_mono := fun _ {_ _} _ _ => trivial
  total_sup := fun _ _ _ => trivial
  total_ev := fun _ _ _ => ⟨0, trivial⟩
  total_imp := fun _ _ _ _ _ _ => trivial
  total_fin := fun _ _ _ _ _ => ⟨0, trivial⟩
  conv Φ :=
    let r := dG.conv Φ
    { toFun := fun φ => Shape.arrTo k dG hG Φ φ.1
      invFun := fun f => ⟨Shape.arrExt k dG Φ f, trivial⟩
      right_inv := fun f => by
        apply Subtype.ext
        funext x
        show (r.toFun ⟨Shape.arrExt k dG Φ f x.1, _⟩).1 = f.1 x
        have := congrArg Subtype.val (r.right_inv ⟨f.1 x, f.2.2 x⟩)
        refine Eq.trans ?_ this
        exact congrArg (fun y => (r.toFun y).1) (Subtype.ext (Shape.arrExt_apply_total k dG Φ f x.1 x.2))
      cont_toFun := Cont.mk' _
        (fun φ φ' h x => Cont.mono' r.cont_toFun ((ContinuousMap.rel_iff _ _).1 h x.1))
        (fun c => by
          apply Subtype.ext
          funext x
          have e : (⟨(@Dom.sup _ (Dom.subtype (Dom.ofDomain (functionSpace (Φ.D k) (dG.op.obj Φ.D))) _ _) c).1 x.1, hG _ _ _⟩ :
                {y // dG.total Φ.D Φ.T y}) =
              @Dom.sup _ (Dom.subtype (Dom.ofDomain (dG.op.obj Φ.D)) _ ⟨dG.total_sup Φ, Dom.ChainClosed.of_mono (dG.total_mono Φ)⟩)
                (Dom.mkChain (fun n => ⟨(c n).1 x.1, hG _ _ _⟩) (fun n => (ContinuousMap.rel_iff _ _).1 (Dom.step' c n) x.1)) :=
            Subtype.ext rfl
          show (r.toFun ⟨(@Dom.sup _ (Dom.subtype (Dom.ofDomain (functionSpace (Φ.D k) (dG.op.obj Φ.D))) _ _) c).1 x.1, _⟩).1 = _
          rw [e, Cont.sup_eq' r.cont_toFun]
          rfl)
      cont_invFun := Cont.mk' _
        (fun f f' h => (ContinuousMap.rel_iff _ _).2 fun d => by
          by_cases hd : Φ.T k d
          · rw [Shape.arrExt_apply_total k dG Φ f d hd, Shape.arrExt_apply_total k dG Φ f' d hd]
            exact Cont.mono' r.cont_invFun (h ⟨d, hd⟩)
          · rw [Shape.arrExt_apply_not k dG Φ f d hd]; exact OmegaComplete.bottom_le _)
        (fun c => by
          apply Subtype.ext
          apply ContinuousMap.ext
          intro d
          show Shape.arrExt k dG Φ _ d =
            OmegaSup.sup (ContinuousMap.evalChain (Dom.vals (Dom.ofDomain (functionSpace (Φ.D k) (dG.op.obj Φ.D))) _) d)
          by_cases hd : Φ.T k d
          · rw [Shape.arrExt_apply_total k dG Φ _ d hd]
            have e : (⟨(@Dom.sup _ (Dom.subtype (Shape.arrDom k dG Φ.X) _ _) c).1 ⟨d, hd⟩, _⟩ : {x // cG x}) =
                @Dom.sup _ (Dom.subtype (dG.dom Φ.X) _ ⟨dG.cond_sup Φ.X, dG.cond_csup Φ.X⟩)
                  (Dom.mkChain (fun n => ⟨(c n).1 ⟨d, hd⟩, (c n).2.2 _⟩) (fun n => Dom.step' c n ⟨d, hd⟩)) :=
              Subtype.ext rfl
            rw [e, Cont.sup_eq' r.cont_invFun]
            apply @Dom.le_antisymm _ (Dom.ofDomain (dG.op.obj Φ.D))
            · apply @Dom.sup_le _ (Dom.ofDomain (dG.op.obj Φ.D)); intro n
              refine PartialOrder.rel_trans ?_ (@Dom.le_sup _ (Dom.ofDomain (dG.op.obj Φ.D))
                (ContinuousMap.evalChain (Dom.vals (Dom.ofDomain (functionSpace (Φ.D k) (dG.op.obj Φ.D))) _) d) n)
              show _ ⊑ Shape.arrExt k dG Φ _ d
              rw [Shape.arrExt_apply_total k dG Φ _ d hd]
              exact PartialOrder.rel_refl
            · apply @Dom.sup_le _ (Dom.ofDomain (dG.op.obj Φ.D)); intro n
              refine PartialOrder.rel_trans ?_ (@Dom.le_sup _ (Dom.ofDomain (dG.op.obj Φ.D)) _ n)
              show Shape.arrExt k dG Φ _ d ⊑ _
              rw [Shape.arrExt_apply_total k dG Φ _ d hd]
              exact PartialOrder.rel_refl
          · rw [Shape.arrExt_apply_not k dG Φ _ d hd]
            symm
            refine (@sup_eq_of_attained _ (dG.op.obj Φ.D).order (dG.op.obj Φ.D).complete.toOmegaSup _ 0 ?_).trans ?_
            · intro m
              have e := fun f => Shape.arrExt_apply_not k dG Φ f d hd
              show Shape.arrExt k dG Φ _ d ⊑ Shape.arrExt k dG Φ _ d
              simp only [e]
              exact PartialOrder.rel_refl
            · exact Shape.arrExt_apply_not k dG Φ _ d hd) }
end Arr

/-! ## The shapes: the model of each piece, for the condition written in `Top` -/

section Instances
variable {I : Type pu}

/-- Data: a plain field of any admissible type (lifted in the model). -/
def Model.Shape.data (A : Type w) [Dom A] : ShapeData (fun _ : Fam.{pu, v} I => A) (fun _ => True) :=
  Shape.data' A
/-- Constant: a plain field of a pointed admissible type. -/
def Model.Shape.const (A : Type w) [Dom A] [NonPos.Pointed A] :
    ShapeData (fun _ : Fam.{pu, v} I => A) (fun _ => True) := Shape.const' A
/-- A plain field of a structure of the group. -/
def Model.Shape.var (k : I) : ShapeData (fun X : Fam.{pu, v} I => X k) (fun _ => True) :=
  Shape.var' k
/-- A binder, whose body is pointed. -/
def Model.Shape.pi (T : Type w₁) (G : T → Fam.{pu, v} I → Type w₂) [∀ t, Shape (G t)] [∀ t, Shape.Pointed (G t)] :
    ShapeData (fun X => (t : T) → G t X) (fun f => ∀ t, Shape.cond (F := G t) (f t)) :=
  Shape.pi' (fun t => Shape.sd (F := G t)) (fun t D T y => Shape.Pointed.total D T y)
/-- A dictionary binder, whose body is pointed. -/
def Model.Shape.arr (k : I) (G : Fam.{pu, v} I → Type w) [Shape G] [Shape.Pointed G] :
    ShapeData (fun X => X k → G X)
      (fun f => Cont (inst_1 := Shape.dom (F := G) _) f ∧ ∀ d, Shape.cond (F := G) (f d)) :=
  Shape.arr' k (Shape.sd (F := G)) (fun D T y => Shape.Pointed.total D T y)
/-- Two fields. -/
def Model.Shape.prod (F : Fam.{pu, v} I → Type w₁) (G : Fam.{pu, v} I → Type w₂) [Shape F] [Shape G] :
    ShapeData (fun X => F X ×' G X) (fun x => Shape.cond (F := F) x.1 ∧ Shape.cond (F := G) x.2) :=
  Shape.prod' (Shape.sd (F := F)) (Shape.sd (F := G))

/-! Pointedness, piece by piece. -/

theorem Model.Shape.pointed_const (A : Type w) [Dom A] [NonPos.Pointed A] :
    ∀ D T y, (Model.Shape.const.{pu, v} (I := I) A).total D T y := fun _ _ _ => trivial
theorem Model.Shape.pointed_pi (T : Type w₁) (G : T → Fam.{pu, v} I → Type w₂) [∀ t, Shape (G t)]
    [∀ t, Shape.Pointed (G t)] : ∀ D T' y, (Model.Shape.pi T G).total D T' y := fun _ _ _ => trivial
theorem Model.Shape.pointed_arr (k : I) (G : Fam.{pu, v} I → Type w) [Shape G] [Shape.Pointed G] :
    ∀ D T y, (Model.Shape.arr k G).total D T y := fun _ _ _ => trivial
theorem Model.Shape.pointed_prod (F : Fam.{pu, v} I → Type w₁) (G : Fam.{pu, v} I → Type w₂) [Shape F] [Shape G]
    [Shape.Pointed F] [Shape.Pointed G] : ∀ D T y, (Model.Shape.prod F G).total D T y :=
  fun D T y => ⟨Shape.Pointed.total D T y.1, Shape.Pointed.total D T y.2⟩
end Instances

end
end NonPos
