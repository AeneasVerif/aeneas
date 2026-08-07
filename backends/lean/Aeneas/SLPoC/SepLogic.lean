import Aeneas.Control.OrderedMonad
import Aeneas.SLPoC.Computation

namespace Aeneas.SLPoC

/- Heap predicates describe heap fragments. -/
abbrev HProp := Heap → Prop

/- Postconditions describe both a returned value and a heap fragment. -/
abbrev Postcondition (α : Type) := α → HProp

def himpl (H₁ H₂ : HProp) : Prop :=
  ∀ h, H₁ h → H₂ h

def hequiv (H₁ H₂ : HProp) : Prop :=
  ∀ h, H₁ h ↔ H₂ h

def hempty : HProp :=
  fun h => h = empty

def hpure (P : Prop) : HProp :=
  fun h => P ∧ h = empty

def hsingle {α : Type} (r : ref α) (value : α) : HProp :=
  fun h => h = Finmap.singleton r.allocId ⟨α, false, value⟩

def hstar (H₁ H₂ : HProp) : HProp :=
  fun h =>
    ∃ h₁ h₂,
      Finmap.Disjoint h₁ h₂ ∧
      h = h₁ ∪ h₂ ∧
      H₁ h₁ ∧
      H₂ h₂

def hexists {α : Sort _} (J : α → HProp) : HProp :=
  fun h => ∃ x, J x h

def qstar {α : Type} (Q : Postcondition α) (H : HProp) :
    Postcondition α :=
  fun value => hstar (Q value) H


namespace SepLogic

scoped syntax:max "iprop(" term ")" : term
scoped notation "emp" => hempty
scoped syntax "⌜" term "⌝" : term
scoped macro_rules
  | `(⌜$P⌝) => `(hpure $P)
scoped macro_rules
  | `(iprop(∃ $x:ident, $H)) => `(hexists fun $x => iprop($H))
  | `(iprop(∃ $x:ident : $type, $H)) =>
      `(hexists fun ($x : $type) => iprop($H))
  | `(iprop(∃ ($x:ident : $type), $H)) =>
      `(hexists fun ($x : $type) => iprop($H))
  | `(iprop($H)) => `($H)
scoped infixr:35 " ∗ " => hstar
scoped infixr:40 " ∗+ " => qstar
scoped infix:25 " ⊢ " => himpl
scoped infix:25 " ⊣⊢ " => hequiv
scoped notation:52 r:53 " ↦ " value:53 => hsingle r value

end SepLogic

/-- Monotone predicate transformers, corresponding to `Wᴾᵘʳᵉ` in
"Dijkstra Monads for All". -/
structure Wp (α : Type) where
  run : Postcondition α → HProp
  monotone :
    ∀ {Q₁ Q₂ : Postcondition α},
      (∀ value, himpl (Q₁ value) (Q₂ value)) →
      himpl (run Q₁) (run Q₂)

namespace Wp

instance : CoeFun (Wp α) (fun _ => Postcondition α → HProp) :=
  ⟨Wp.run⟩

def pure (value : α) : Wp α :=
  ⟨fun Q => Q value, fun hQ => hQ value⟩

def bind (m : Wp α) (next : α → Wp β) : Wp β :=
  ⟨fun Q => m (fun value => next value Q), fun hQ =>
    m.monotone (fun value => (next value).monotone hQ)⟩

/-- Specification weakening is reverse implication between preconditions. -/
instance : LE (Wp α) where
  le w₁ w₂ := ∀ Q, himpl (w₂ Q) (w₁ Q)

instance : Preorder (Wp α) where
  le_refl w Q h hPre := hPre
  le_trans w₁ w₂ w₃ h₁₂ h₂₃ Q h hPre :=
    h₁₂ Q h (h₂₃ Q h hPre)

/-- Equivalence of specifications induced by the `Wp` preorder. -/
def Equiv (w₁ w₂ : Wp α) : Prop :=
  w₁ ≤ w₂ ∧ w₂ ≤ w₁

instance : Setoid (Wp α) where
  r := Equiv
  iseqv := {
    refl := fun w => ⟨le_refl w, le_refl w⟩
    symm := fun h => ⟨h.2, h.1⟩
    trans := fun h₁₂ h₂₃ =>
      ⟨le_trans h₁₂.1 h₂₃.1, le_trans h₂₃.2 h₁₂.2⟩
  }

theorem equiv_iff {w₁ w₂ : Wp α} :
    w₁ ≈ w₂ ↔ w₁ ≤ w₂ ∧ w₂ ≤ w₁ :=
  Iff.rfl

@[refl]
theorem equiv_refl (w : Wp α) : w ≈ w :=
  ⟨le_refl w, le_refl w⟩

theorem bind_mono {m₁ m₂ : Wp α} {next₁ next₂ : α → Wp β}
    (hm : m₁ ≤ m₂) (hnext : ∀ value, next₁ value ≤ next₂ value) :
    bind m₁ next₁ ≤ bind m₂ next₂ := by
  intro Q h hBind
  apply m₁.monotone (fun value => hnext value Q) h
  exact hm (fun value => next₂ value Q) h hBind

theorem bind_congr {m₁ m₂ : Wp α} {next₁ next₂ : α → Wp β}
    (hm : m₁ ≈ m₂) (hnext : ∀ value, next₁ value ≈ next₂ value) :
    bind m₁ next₁ ≈ bind m₂ next₂ :=
  ⟨bind_mono hm.1 (fun value => (hnext value).1),
    bind_mono hm.2 (fun value => (hnext value).2)⟩

end Wp

instance : Monad Wp where
  pure := Wp.pure
  bind := Wp.bind

instance : LawfulMonad Wp where
  map_const := by intros; rfl
  id_map := by intros; rfl
  seqLeft_eq := by intros; rfl
  seqRight_eq := by intros; rfl
  pure_seq := by intros; rfl
  pure_bind := by intros; rfl
  bind_assoc := by intros; rfl
  bind_pure_comp := by intros; rfl
  bind_map := by intros; rfl

instance : OrderedMonad Wp where
  bind_mono := Wp.bind_mono

def theta_ev : StEvents α → Wp α
  | .Alloc value => {
      run := fun Q h =>
        let allocation := alloc value h
        Q allocation.1 allocation.2
      monotone := by
        intro Q₁ Q₂ hQ h hPre
        exact hQ _ _ hPre
    }
  | .Read r => {
      run := fun Q h =>
        ∃ hLive : live h r, Q (read r h hLive) h
      monotone := by
        intro Q₁ Q₂ hQ h hPre
        obtain ⟨hLive, hPost⟩ := hPre
        exact ⟨hLive, hQ _ _ hPost⟩
    }
  | .Update r value => {
      run := fun Q h =>
        ∃ hLive : live h r, Q () (update r value h hLive)
      monotone := by
        intro Q₁ Q₂ hQ h hPre
        obtain ⟨hLive, hPost⟩ := hPre
        exact ⟨hLive, hQ _ _ hPost⟩
    }
  | .Free r => {
      run := fun Q h =>
        ∃ hLive : live h r, Q () (free r h hLive)
      monotone := by
        intro Q₁ Q₂ hQ h hPre
        obtain ⟨hLive, hPost⟩ := hPre
        exact ⟨hLive, hQ _ _ hPost⟩
    }

def theta : St α → Wp α
  | .ok value => Wp.pure value
  | .event event next =>
      Wp.bind (theta_ev event) (fun value => theta (next value))

/-- `theta` preserves the monad operations up to `Wp` equivalence. -/
def thetaMorphism : MonadMorphism St Wp where
  toFun := theta
  map_pure := by
    intro α value
    rfl
  map_bind := by
    intro α β m next
    induction m
    · rfl
    · rename_i γ event k ih
      change
        Wp.bind (theta_ev event) (fun value => theta (k value >>= next)) ≈
          Wp.bind (theta_ev event) (fun value =>
            Wp.bind (theta (k value)) (fun result => theta (next result)))
      exact Wp.bind_congr (by rfl) ih

end Aeneas.SLPoC
