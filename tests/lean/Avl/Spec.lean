import Avl.Tree
import Aesop

namespace avl

open Primitives (Result Scalar)
open avl Node Ordering Tree

-- TODO: move
@[simp]
def Option.allP {α : Type u} (p : α → Prop) (x : Option α) : Prop :=
  match x with
  | none => true
  | some x => p x

mutual
@[simp] def Child.forall (p: Node T -> Prop) (child : Child T) : Prop :=
  match child with
  | none => true
  | some child => child.forall p
termination_by Child.size child
decreasing_by simp_wf

def Node.forall (p: Node T -> Prop) (node : Node T) : Prop :=
  p node ∧
  Child.forall p node.left ∧ Child.forall p node.right
termination_by Node.size node
decreasing_by all_goals (simp_wf <;> split <;> simp <;> scalar_tac)
end

@[simp]
theorem Child.forall_left {p: Node T -> Prop} {t: Node T}: Node.forall p t -> Child.forall p t.left := by
  cases t; simp_all [Node.forall]

@[simp]
theorem Child.forall_right {p: Node T -> Prop} {t: Node T}: Child.forall p t -> Child.forall p t.right := by
  cases t; simp_all [Node.forall]

/-
theorem Child.forall_not_mem {a: T} (p: Node T -> Prop) (t: Child T): ¬ p a -> Child.forall p t -> a ∉ Child.v t
  := fun Hnpa Hpt => by
  cases t <;> simp
  unfold Child.forall Node.forall at Hpt
  split at Hpt; simp_all
  split_conjs
  . by_contra hab; rw [hab] at Hnpa; simp_all
  . apply (forall_not_mem p) <;> simp [*]
  . apply (forall_not_mem p) <;> simp [*]

theorem Child.forall_not_mem' {a: T} (p: T -> Prop) (t: Option (Node T)):
  p a -> Child.forall (fun x =>  ¬p x) t -> a ∉ Child.v t
  := by
  intro Hpa Hnpt
  refine' Child.forall_not_mem (fun x => ¬ p x) t _ _
  simp [Hpa]
  exact Hnpt
-/

mutual
theorem Child.forall_imp {p q: Node T -> Prop} {t: Child T}: (∀ x, p x -> q x) -> Child.forall p t -> Child.forall q t
  := by
  match t with
  | none => simp
  | some node =>
    simp
    intros
    apply @Node.forall_imp T p q <;> tauto

theorem Node.forall_imp {p q: Node T -> Prop} {t: Node T}: (∀ x, p x -> q x) -> Node.forall p t -> Node.forall q t := by
  match t with
  | .mk x left right height =>
    simp [Node.forall]
    intros Himp Hleft Hright Hx
    simp [*]
    split_conjs <;> apply @Child.forall_imp T p q <;> tauto

end

def Node.balancingFactor (node : Node T) : ℤ :=
  Child.compute_height node.left - Child.compute_height node.right

def Child.balancingFactor (t: Child T): ℤ :=
  match t with
  | .none => 0
  | .some x => x.balancingFactor

def Node.inv_aux [LinearOrder T] (node : Node T) : Prop :=
  node.height.val = node.compute_height ∧
  (∀ x ∈ Child.v node.left, x < node.value) ∧
  (∀ x ∈ Child.v node.right, node.value < x) ∧
  --Child.forall (fun node' => node'.value < node.value) node.left ∧
  --Child.forall (fun node' => node.value < node'.value) node.right ∧
  -1 ≤ node.balancingFactor ∧ node.balancingFactor ≤ 1

@[reducible]
def Node.inv [LinearOrder T] (node : Node T) : Prop :=
  Node.forall Node.inv_aux node

-- TODO: use a custom set
@[aesop safe forward]
theorem Node.inv_imp_current [LinearOrder T] {node : Node T} (hInv : node.inv) :
  node.height.val = node.compute_height ∧
  (∀ x ∈ Child.v node.left, x < node.value) ∧
  (∀ x ∈ Child.v node.right, node.value < x) ∧
  -1 ≤ node.balancingFactor ∧ node.balancingFactor ≤ 1 := by
  simp_all [Node.inv, Node.forall, Node.inv_aux]

@[simp, reducible]
def Child.inv [LinearOrder T] (child : Child T) : Prop :=
  match child with
  | none => true
  | some node => node.inv

@[reducible]
def Tree.inv [LinearOrder T] (t : Tree T) : Prop := Child.inv t.root

@[simp]
theorem Node.inv_left [LinearOrder T] {t: Node T}: t.inv -> Child.inv t.left := by
  simp [Node.inv]
  intro
  cases t; simp
  split <;> try simp_all [Node.forall]

@[simp]
theorem Node.inv_right [LinearOrder T] {t: Node T}: t.inv -> Child.inv t.right := by
  simp [Node.inv]
  intro
  cases t; simp
  split <;> try simp_all [Node.forall]

theorem Node.inv_imp_height_eq [LinearOrder T] {t: Node T} (hInv : t.inv) : t.height.val = t.compute_height := by
  simp [inv, Node.forall, inv_aux] at hInv
  cases t; simp_all

/-
-- TODO: ask at most for LT + Irreflexive (lt_irrefl) + Trichotomy (le_of_not_lt)?
theorem left_pos {left right: Option (Node T)} {a x: T}: BST.Invariant (some (Node.mk a left right h)) -> x ∈ Tree.set (Node.mk a left right h) -> x < a -> x ∈ Tree.set left := fun Hbst Hmem Hxa => by
   simp [Tree.set_some] at Hmem
   rcases Hmem with (Heq | Hleft) | Hright
   . rewrite [Heq] at Hxa; exact absurd Hxa (lt_irrefl _)
   . assumption
   . exfalso

     -- Hbst -> x ∈ right -> ForallNode (fun v => ¬ v < a)
     refine' ForallNode.not_mem' (fun v => v < a) right Hxa _ _
     simp [le_of_not_lt]
     cases Hbst with
     | some _ _ _ _ Hforall _ =>
       refine' ForallNode.imp _ Hforall
       exact fun x => le_of_lt
     assumption

theorem right_pos {left right: Option (Node T)} {a x: T}: BST.Invariant (some (Node.mk a left right h)) -> x ∈ Tree.set (Node.mk a left right h) -> a < x -> x ∈ Tree.set right := fun Hbst Hmem Hax => by
   simp [Tree.set_some] at Hmem
   rcases Hmem with (Heq | Hleft) | Hright
   . rewrite [Heq] at Hax; exact absurd Hax (lt_irrefl _)
   . exfalso
     refine' ForallNode.not_mem' (fun v => a < v) left Hax _ _
     simp [le_of_not_lt]
     cases Hbst with
     | some _ _ _ Hforall _ _ =>
       refine' ForallNode.imp _ Hforall
       exact fun x => le_of_lt
     assumption
   . assumption
-/

@[simp]
theorem Node.lt_imp_not_in_right [LinearOrder T] (node : Node T) (hInv : node.inv) (x : T)
  (hLt : x < node.value) :
  x ∉ Child.v node.right := by
  have ⟨ _, _, h, _ ⟩ := Node.inv_imp_current hInv
  intro hIn
  have := h x hIn
  have := lt_asymm this
  tauto

@[simp]
theorem Node.lt_imp_not_in_left [LinearOrder T] (node : Node T) (hInv : node.inv) (x : T)
  (hLt : node.value < x) :
  x ∉ Child.v node.left := by
  have ⟨ _, h, _, _ ⟩ := Node.inv_imp_current hInv
  intro hIn
  have := h x hIn
  have := lt_asymm this
  tauto

@[simp]
theorem Node.value_not_in_right [LinearOrder T] (node : Node T) (hInv : node.inv) :
  node.value ∉ Child.v node.right := by
  have ⟨ _, _, h, _ ⟩ := Node.inv_imp_current hInv
  intro hIn
  have := h node.value hIn
  have := ne_of_lt this
  tauto

@[simp]
theorem Node.value_not_in_left [LinearOrder T] (node : Node T) (hInv : node.inv) :
  node.value ∉ Child.v node.left := by
  have ⟨ _, h, _, _ ⟩ := Node.inv_imp_current hInv
  intro hIn
  have := h node.value hIn
  have := ne_of_lt this
  tauto

end avl
