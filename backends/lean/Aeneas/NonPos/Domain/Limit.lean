module
public import Aeneas.NonPos.Domain.Basic

@[expose] public section

/-!
# Domain theory: embedding-projection pairs and inverse limits

This is the standard inverse-limit construction of Smyth and Plotkin ("The Category-Theoretic
Solution of Recursive Domain Equations", 1982). Given a tower of domains

```
D₀ → D₁ → D₂ → ...
```

related by embedding-projection pairs, the inverse limit is the domain of *coherent threads*:
sequences `x : ∀ n, Dₙ` such that projecting `x (n+1)` gives back `x n`. Every element of the
limit is the supremum of its finite approximations (`approximation_sup`): this is the key
property used in `NonPos.Domain.Operator` to solve recursive domain equations.
-/

namespace NonPos.Domain

open Lean.Order OmegaComplete OmegaSup

universe u v w x

/-! ## Embedding-projection pairs and isomorphisms -/

/-- An embedding-projection pair: `project ∘ embed = id` and `embed ∘ project ⊑ id`. -/
structure EP (A : Domain.{u}) (B : Domain.{v}) where
  embed : ContinuousMap A B
  project : ContinuousMap B A
  project_embed : ∀ x, project (embed x) = x
  embed_project : ∀ y, embed (project y) ⊑ y

def EP.id (A : Domain.{u}) : EP A A :=
  ⟨ContinuousMap.id A, ContinuousMap.id A, fun _ => rfl, fun _ => PartialOrder.rel_refl⟩

def EP.comp {A : Domain.{u}} {B : Domain.{v}} {C : Domain.{w}}
    (second : EP B C) (first : EP A B) : EP A C where
  embed := second.embed.comp first.embed
  project := first.project.comp second.project
  project_embed x := by
    simp only [ContinuousMap.comp_apply, second.project_embed, first.project_embed]
  embed_project y :=
    PartialOrder.rel_trans
      (second.embed.mono _ _ (first.embed_project (second.project y)))
      (second.embed_project y)

theorem EP.embed_bottom {A : Domain.{u}} {B : Domain.{v}} (p : EP A B) :
    p.embed bottom = bottom := by
  apply PartialOrder.rel_antisymm
  · exact PartialOrder.rel_trans
      (p.embed.mono _ _ (bottom_le (p.project bottom)))
      (p.embed_project bottom)
  · exact bottom_le _

theorem EP.project_bottom {A : Domain.{u}} {B : Domain.{v}} (p : EP A B) :
    p.project bottom = bottom := by
  rw [← p.embed_bottom, p.project_embed]

/-- An order isomorphism preserves chain suprema, hence is continuous. -/
def continuousOfInverse {A : Domain.{u}} {B : Domain.{v}}
    (f : A → B) (g : B → A) (hf : monotone f) (hg : monotone g)
    (gf : ∀ x, g (f x) = x) (fg : ∀ y, f (g y) = y) : ContinuousMap A B where
  toFun := f
  cont := {
    mono := hf
    sup_eq := fun c => by
      apply PartialOrder.rel_antisymm
      · have bound : sup c ⊑ g (sup (c.map f hf)) := by
          apply OmegaSup.sup_le
          intro n
          exact PartialOrder.rel_trans
            (PartialOrder.rel_of_eq (gf (c n)).symm)
            (hg _ _ (OmegaSup.le_sup (c.map f hf) n))
        have upper := hf _ _ bound
        rw [fg] at upper
        exact upper
      · exact OmegaSup.sup_le _ _ (fun n => hf _ _ (OmegaSup.le_sup c n))
  }

/-- An isomorphism of domains. -/
structure DomainIso (A : Domain.{u}) (B : Domain.{v}) where
  forward : ContinuousMap A B
  backward : ContinuousMap B A
  backward_forward : ∀ x, backward (forward x) = x
  forward_backward : ∀ y, forward (backward y) = y

def DomainIso.toEP {A : Domain.{u}} {B : Domain.{v}} (i : DomainIso A B) : EP A B :=
  ⟨i.forward, i.backward, i.backward_forward,
    fun y => PartialOrder.rel_of_eq (i.forward_backward y)⟩

def DomainIso.refl (A : Domain.{u}) : DomainIso A A :=
  ⟨ContinuousMap.id A, ContinuousMap.id A, fun _ => rfl, fun _ => rfl⟩

def DomainIso.symm {A : Domain.{u}} {B : Domain.{v}} (p : DomainIso A B) : DomainIso B A :=
  ⟨p.backward, p.forward, p.forward_backward, p.backward_forward⟩

def DomainIso.trans {A : Domain.{u}} {B : Domain.{v}} {C : Domain.{w}}
    (p : DomainIso A B) (q : DomainIso B C) : DomainIso A C where
  forward := q.forward.comp p.forward
  backward := p.backward.comp q.backward
  backward_forward x := by
    simp only [ContinuousMap.comp_apply, q.backward_forward, p.backward_forward]
  forward_backward x := by
    simp only [ContinuousMap.comp_apply, p.forward_backward, q.forward_backward]

/-! ## Lifting EP pairs through function spaces, products and dependent products -/

def precompose {A : Domain.{u}} {B : Domain.{v}} (p : ContinuousMap B A) (R : Domain.{w}) :
    ContinuousMap (functionSpace A R) (functionSpace B R) where
  toFun f := f.comp p
  cont := {
    mono := fun _ _ related x => related (p x)
    sup_eq := fun _ => ContinuousMap.ext (fun _ => rfl)
  }

def postcompose {B : Domain.{v}} {C : Domain.{w}} (p : ContinuousMap B C) (A : Domain.{u}) :
    ContinuousMap (functionSpace A B) (functionSpace A C) where
  toFun f := p.comp f
  cont := {
    mono := fun _ _ related x => p.mono _ _ (related x)
    sup_eq := fun c => by
      apply ContinuousMap.ext
      intro x
      exact p.continuous (ContinuousMap.evalChain c x)
  }

/-- Both variance directions are handled by the embedding-projection laws: the negative
occurrence is transported using the projection in the embedding direction. -/
def arrowEP {A : Domain.{u}} {B : Domain.{v}} {C : Domain.{w}} {D : Domain.{x}}
    (p : EP A B) (q : EP C D) : EP (functionSpace A C) (functionSpace B D) where
  embed := (postcompose q.embed B).comp (precompose p.project C)
  project := (postcompose q.project A).comp (precompose p.embed D)
  project_embed f := by
    apply ContinuousMap.ext
    intro x
    change q.project (q.embed (f (p.project (p.embed x)))) = f x
    rw [p.project_embed, q.project_embed]
  embed_project f x := by
    change q.embed (q.project (f (p.embed (p.project x)))) ⊑ f x
    exact PartialOrder.rel_trans (q.embed_project _) (f.mono _ _ (p.embed_project x))

def arrowIso {A : Domain.{u}} {B : Domain.{v}} {C : Domain.{w}} {D : Domain.{x}}
    (p : DomainIso A B) (q : DomainIso C D) :
    DomainIso (functionSpace A C) (functionSpace B D) where
  forward := (arrowEP p.toEP q.toEP).embed
  backward := (arrowEP p.toEP q.toEP).project
  backward_forward := (arrowEP p.toEP q.toEP).project_embed
  forward_backward f := by
    apply ContinuousMap.ext
    intro x
    change q.forward (q.backward (f (p.forward (p.backward x)))) = f x
    rw [p.forward_backward, q.forward_backward]

def piEP {ι : Type w} {A : ι → Domain.{u}} {B : ι → Domain.{v}}
    (p : ∀ j, EP (A j) (B j)) : EP (piDomain A) (piDomain B) where
  embed := piMap (fun j => (p j).embed.comp (piCoordinate A j))
  project := piMap (fun j => (p j).project.comp (piCoordinate B j))
  project_embed f := funext (fun j => (p j).project_embed (f j))
  embed_project f j := (p j).embed_project (f j)

def piIso {ι : Type w} {A : ι → Domain.{u}} {B : ι → Domain.{v}}
    (p : ∀ j, DomainIso (A j) (B j)) : DomainIso (piDomain A) (piDomain B) where
  forward := (piEP (fun j => (p j).toEP)).embed
  backward := (piEP (fun j => (p j).toEP)).project
  backward_forward f := funext (fun j => (p j).backward_forward (f j))
  forward_backward f := funext (fun j => (p j).forward_backward (f j))

def prodEP {A : Domain.{u}} {B : Domain.{v}} {C : Domain.{w}} {D : Domain.{x}}
    (p : EP A B) (q : EP C D) : EP (prodDomain A C) (prodDomain B D) where
  embed := prodMap (p.embed.comp (prodFst A C)) (q.embed.comp (prodSnd A C))
  project := prodMap (p.project.comp (prodFst B D)) (q.project.comp (prodSnd B D))
  project_embed x := Prod.ext (p.project_embed x.1) (q.project_embed x.2)
  embed_project x := ⟨p.embed_project x.1, q.embed_project x.2⟩

def prodIso {A : Domain.{u}} {B : Domain.{v}} {C : Domain.{w}} {D : Domain.{x}}
    (p : DomainIso A B) (q : DomainIso C D) :
    DomainIso (prodDomain A C) (prodDomain B D) where
  forward := (prodEP p.toEP q.toEP).embed
  backward := (prodEP p.toEP q.toEP).project
  backward_forward x := Prod.ext (p.backward_forward x.1) (q.backward_forward x.2)
  forward_backward x := Prod.ext (p.forward_backward x.1) (q.forward_backward x.2)

/-! ## Towers and their inverse limits -/

/-- A tower of domains related by embedding-projection pairs. -/
structure Tower : Type (u + 1) where
  obj : Nat → Domain.{u}
  bond : ∀ n, EP (obj n) (obj (n + 1))

def Tower.tail (T : Tower.{u}) : Tower.{u} where
  obj n := T.obj (n + 1)
  bond n := T.bond (n + 1)

/-- A coherent thread: an element of the inverse limit. -/
structure Thread (T : Tower.{u}) : Type u where
  coord : ∀ n, T.obj n
  coherent : ∀ n, (T.bond n).project (coord (n + 1)) = coord n

instance {T : Tower.{u}} : CoeFun (Thread T) (fun _ => (n : Nat) → T.obj n) := ⟨Thread.coord⟩

@[ext] theorem Thread.ext {T : Tower.{u}} {x y : Thread T} (h : ∀ n, x n = y n) : x = y := by
  cases x
  cases y
  cases funext h
  rfl

instance {T : Tower.{u}} : PartialOrder (Thread T) where
  rel x y := ∀ n, x n ⊑ y n
  rel_refl _ := PartialOrder.rel_refl
  rel_trans h₁ h₂ n := PartialOrder.rel_trans (h₁ n) (h₂ n)
  rel_antisymm h₁ h₂ := Thread.ext (fun n => PartialOrder.rel_antisymm (h₁ n) (h₂ n))

theorem Thread.rel_iff {T : Tower.{u}} (x y : Thread T) : (x ⊑ y) ↔ ∀ n, x n ⊑ y n := Iff.rfl

def Thread.coordChain {T : Tower.{u}} (c : Chain (Thread T)) (n : Nat) : Chain (T.obj n) :=
  ⟨fun k => c k n, fun k => c.step k n⟩

def Thread.bottom (T : Tower.{u}) : Thread T where
  coord _ := OmegaComplete.bottom
  coherent n := (T.bond n).project_bottom

def Thread.sup {T : Tower.{u}} (c : Chain (Thread T)) : Thread T where
  coord n := OmegaSup.sup (coordChain c n)
  coherent n := by
    rw [(T.bond n).project.continuous]
    apply sup_congr
    intro k
    exact (c k).coherent n

instance {T : Tower.{u}} : OmegaComplete (Thread T) where
  bottom := Thread.bottom T
  bottom_le := fun x n => OmegaComplete.bottom_le (x n)
  sup := Thread.sup
  le_sup := fun c k n => OmegaSup.le_sup (Thread.coordChain c n) k
  sup_le := fun c x h n =>
    OmegaSup.sup_le (Thread.coordChain c n) (x n) (fun k => h k n)

theorem Thread.sup_coord {T : Tower.{u}} (c : Chain (Thread T)) (n : Nat) :
    (OmegaSup.sup c) n = OmegaSup.sup (Thread.coordChain c n) := rfl

/-! ### Threads: shifting, and embedding the stages (as plain functions) -/

def Thread.drop {T : Tower.{u}} (x : Thread T) : Thread T.tail where
  coord n := x (n + 1)
  coherent n := x.coherent (n + 1)

def Thread.cons {T : Tower.{u}} (x : Thread T.tail) : Thread T where
  coord
    | 0 => (T.bond 0).project (x 0)
    | n + 1 => x n
  coherent n := by
    cases n with
    | zero => rfl
    | succ n => exact x.coherent n

theorem Thread.drop_cons {T : Tower.{u}} (x : Thread T.tail) : x.cons.drop = x :=
  Thread.ext (fun _ => rfl)

theorem Thread.cons_drop {T : Tower.{u}} (x : Thread T) : x.drop.cons = x := by
  apply Thread.ext
  intro n
  cases n with
  | zero => exact x.coherent 0
  | succ n => rfl

def Tower.forward (T : Tower.{u}) : (n : Nat) → ContinuousMap (T.obj 0) (T.obj n)
  | 0 => ContinuousMap.id _
  | n + 1 => (T.bond n).embed.comp (T.forward n)

def Thread.start (T : Tower.{u}) (x : T.obj 0) : Thread T where
  coord n := T.forward n x
  coherent n := (T.bond n).project_embed (T.forward n x)

theorem start_below (T : Tower.{u}) (x : Thread T) : (Thread.start T (x 0)) ⊑ x := by
  intro n
  induction n with
  | zero => exact PartialOrder.rel_refl
  | succ n ih =>
    apply PartialOrder.rel_trans ((T.bond n).embed.mono _ _ ih)
    rw [← x.coherent n]
    exact (T.bond n).embed_project (x (n + 1))

theorem Tower.forward_tail (T : Tower.{u}) (n : Nat) (x : T.obj 0) :
    T.forward (n + 1) x = T.tail.forward n ((T.bond 0).embed x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (T.bond (n + 1)).embed (T.forward (n + 1) x) =
      (T.bond (n + 1)).embed (T.tail.forward n ((T.bond 0).embed x))
    rw [ih]

/-- The embedding of the `n`-th stage into the threads, as a plain function (the embedding of the
EP pair `approx T n` below, which needs `limit T`, which needs this for its chain completeness). -/
def Thread.embedAt (T : Tower.{u}) : (n : Nat) → T.obj n → Thread T
  | 0 => Thread.start T
  | n + 1 => fun a => Thread.cons (Thread.embedAt T.tail n a)

theorem Thread.embedAt_coord (T : Tower.{u}) (n : Nat) (a : T.obj n) : Thread.embedAt T n a n = a := by
  induction n generalizing T with
  | zero => rfl
  | succ n ih => exact ih T.tail a

theorem Thread.cons_mono {T : Tower.{u}} {x y : Thread T.tail} (h : x ⊑ y) : x.cons ⊑ y.cons := by
  intro n
  cases n with
  | zero => exact (T.bond 0).project.mono _ _ (h 0)
  | succ n => exact h n

theorem Thread.embedAt_mono (T : Tower.{u}) (n : Nat) {a b : T.obj n} (h : a ⊑ b) :
    Thread.embedAt T n a ⊑ Thread.embedAt T n b := by
  induction n generalizing T with
  | zero => intro m; exact (T.forward m).mono _ _ h
  | succ n ih => exact Thread.cons_mono (ih T.tail h)

theorem Thread.embedAt_le (T : Tower.{u}) (n : Nat) (x : Thread T) : Thread.embedAt T n (x n) ⊑ x := by
  induction n generalizing T with
  | zero => exact start_below T x
  | succ n ih =>
    have h := Thread.cons_mono (ih T.tail x.drop)
    rw [x.cons_drop] at h
    exact h

/-- `embedAt` is left adjoint to taking the `n`-th coordinate. -/
theorem Thread.embedAt_le_iff (T : Tower.{u}) (n : Nat) (a : T.obj n) (x : Thread T) :
    Thread.embedAt T n a ⊑ x ↔ a ⊑ x n := by
  constructor
  · intro h
    have := h n
    rwa [Thread.embedAt_coord] at this
  · intro h
    exact PartialOrder.rel_trans (Thread.embedAt_mono T n h) (Thread.embedAt_le T n x)

theorem Thread.embedAt_step (T : Tower.{u}) (n : Nat) (a : T.obj n) :
    Thread.embedAt T n a = Thread.embedAt T (n + 1) ((T.bond n).embed a) := by
  induction n generalizing T with
  | zero =>
    apply Thread.ext
    intro k
    cases k with
    | zero => exact ((T.bond 0).project_embed a).symm
    | succ k => exact T.forward_tail k a
  | succ n ih => exact congrArg Thread.cons (ih T.tail a)

theorem EP.embed_le_iff {A : Domain.{u}} {B : Domain.{v}} (p : EP A B) (a : A) (b : B) :
    p.embed a ⊑ b ↔ a ⊑ p.project b := by
  constructor
  · intro h
    rw [← p.project_embed a]
    exact p.project.mono _ _ h
  · intro h
    exact PartialOrder.rel_trans (p.embed.mono _ _ h) (p.embed_project b)

/-- Every thread is the supremum of the embeddings of its coordinates. -/
theorem Thread.eq_sup_embedAt (T : Tower.{u}) (x : Thread T) (hc : ∀ n,
    Thread.embedAt T n (x n) ⊑ Thread.embedAt T (n + 1) (x (n + 1))) :
    x = OmegaSup.sup (⟨fun n => Thread.embedAt T n (x n), hc⟩ : Chain (Thread T)) := by
  apply PartialOrder.rel_antisymm
  · intro n
    have h := OmegaSup.le_sup (⟨fun n => Thread.embedAt T n (x n), hc⟩ : Chain (Thread T)) n n
    rwa [show (⟨fun n => Thread.embedAt T n (x n), hc⟩ : Chain (Thread T)) n n = x n from
      Thread.embedAt_coord T n (x n)] at h
  · exact OmegaSup.sup_le _ _ (fun n => Thread.embedAt_le T n x)

theorem Thread.embedAt_coord_step (T : Tower.{u}) (x : Thread T) (n : Nat) :
    Thread.embedAt T n (x n) ⊑ Thread.embedAt T (n + 1) (x (n + 1)) := by
  rw [Thread.embedAt_step]
  apply Thread.embedAt_mono
  rw [← x.coherent n]
  exact (T.bond n).embed_project (x (n + 1))

/-- The threads have suprema of nonempty chains: embed the coordinatewise suprema and take their
ω-supremum.  (Only the embeddings are used, never the projections, which need not preserve suprema
of chains.) -/
instance {T : Tower.{u}} : ChainComplete (Thread T) := by
  refine ⟨fun C hC hne => ?_⟩
  have hCn (n : Nat) : chain (image (fun x : Thread T => x n) C) :=
    chain_image (fun _ _ h => (Thread.rel_iff _ _).1 h n) hC
  let s (n : Nat) : T.obj n := chainSup _ (hCn n) (image_nonempty _ hne)
  have hs (n : Nat) : is_sup (image (fun x : Thread T => x n) C) (s n) := chainSup_spec _ _ _
  have hstep (n : Nat) : Thread.embedAt T n (s n) ⊑ Thread.embedAt T (n + 1) (s (n + 1)) := by
    rw [Thread.embedAt_step]
    apply Thread.embedAt_mono
    rw [EP.embed_le_iff]
    refine isSup_le_of (hs n) fun _ ⟨x, hx, e⟩ => ?_
    subst e
    show x n ⊑ _
    rw [← x.coherent n]
    exact (T.bond n).project.mono _ _ (isSup_le (hs (n + 1)) ⟨x, hx, rfl⟩)
  let e : Chain (Thread T) := ⟨fun n => Thread.embedAt T n (s n), hstep⟩
  refine ⟨OmegaSup.sup e, isSup_of (fun x hx => ?_) (fun u hu => ?_)⟩
  · rw [Thread.eq_sup_embedAt T x (Thread.embedAt_coord_step T x)]
    exact sup_mono _ _ (fun n => Thread.embedAt_mono T n (isSup_le (hs n) ⟨x, hx, rfl⟩))
  · exact OmegaSup.sup_le _ _ (fun n => (Thread.embedAt_le_iff T n _ u).2
      (isSup_le_of (hs n) fun _ ⟨x, hx, e⟩ => e ▸ hu x hx n))

/-- The inverse limit consists of all coherent infinite approximation sequences. -/
abbrev limit (T : Tower.{u}) : Domain.{u} := Domain.of (Thread T)

def coordinate (T : Tower.{u}) (n : Nat) : ContinuousMap (limit T) (T.obj n) where
  toFun x := x n
  cont := ⟨fun _ _ related => related n, fun _ => rfl⟩

@[simp] theorem coordinate_apply (T : Tower.{u}) (n : Nat) (x : limit T) : coordinate T n x = x n := rfl

def dropMap (T : Tower.{u}) : ContinuousMap (limit T) (limit T.tail) where
  toFun := Thread.drop
  cont := ⟨fun _ _ related n => related (n + 1), fun _ => Thread.ext (fun _ => rfl)⟩

def consMap (T : Tower.{u}) : ContinuousMap (limit T.tail) (limit T) where
  toFun := Thread.cons
  cont := {
    mono := fun _ _ related n => by
      cases n with
      | zero => exact (T.bond 0).project.mono _ _ (related 0)
      | succ n => exact related n
    sup_eq := fun c => by
      apply Thread.ext
      intro n
      cases n with
      | zero => exact (T.bond 0).project.continuous (Thread.coordChain c 0)
      | succ n => rfl
  }

def tailEP (T : Tower.{u}) : EP (limit T.tail) (limit T) where
  embed := consMap T
  project := dropMap T
  project_embed := Thread.drop_cons
  embed_project x := PartialOrder.rel_of_eq x.cons_drop

def startMap (T : Tower.{u}) : ContinuousMap (T.obj 0) (limit T) where
  toFun := Thread.start T
  cont := {
    mono := fun _ _ related n => (T.forward n).mono _ _ related
    sup_eq := fun c => by
      apply Thread.ext
      intro n
      exact (T.forward n).continuous c
  }

/-- The embedding-projection pair between the `n`-th stage and the limit. -/
def approx (T : Tower.{u}) : (n : Nat) → EP (T.obj n) (limit T)
  | 0 => {
      embed := startMap T
      project := coordinate T 0
      project_embed := fun _ => rfl
      embed_project := start_below T
    }
  | n + 1 => (tailEP T).comp (approx T.tail n)

theorem approx_project (T : Tower.{u}) (n : Nat) (x : Thread T) :
    (approx T n).project x = x n := by
  induction n generalizing T with
  | zero => rfl
  | succ n ih => exact ih T.tail x.drop

theorem approx_coordinate (T : Tower.{u}) (n : Nat) (x : T.obj n) :
    ((approx T n).embed x) n = x := by
  rw [← approx_project T n, (approx T n).project_embed]

theorem approx_step (T : Tower.{u}) (n : Nat) (x : T.obj n) :
    (approx T n).embed x = (approx T (n + 1)).embed ((T.bond n).embed x) := by
  induction n generalizing T with
  | zero =>
    apply Thread.ext
    intro k
    cases k with
    | zero => exact ((T.bond 0).project_embed x).symm
    | succ k => exact T.forward_tail k x
  | succ n ih =>
    exact congrArg Thread.cons (ih T.tail x)

/-- The chain of finite approximations of an element of the limit. -/
def approximationChain (T : Tower.{u}) (x : Thread T) : Chain (Thread T) where
  val n := (approx T n).embed ((approx T n).project x)
  step n := by
    rw [approx_step]
    apply (approx T (n + 1)).embed.mono
    rw [approx_project, approx_project, ← x.coherent n]
    exact (T.bond n).embed_project (x (n + 1))

/-- Every element of the limit is the supremum of its finite approximations. -/
theorem approximation_sup (T : Tower.{u}) (x : Thread T) :
    OmegaSup.sup (approximationChain T x) = x := by
  apply PartialOrder.rel_antisymm
  · apply OmegaSup.sup_le
    intro n
    exact (approx T n).embed_project x
  · intro n
    have h := OmegaSup.le_sup (approximationChain T x) n
    simpa only [approximationChain, approx_coordinate, approx_project] using h n

end NonPos.Domain
