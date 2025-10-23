import Avl.Funs
import Avl.Types
import Avl.OrderSpec

namespace avl

open Aeneas.Std Result

-- This rewriting lemma is problematic below
attribute [-simp] Bool.exists_bool

-- TODO: move
@[simp]
def Option.allP {α : Type u} (p : α → Prop) (x : Option α) : Prop :=
  match x with
  | none => true
  | some x => p x

abbrev Subtree (T : Type) := Option (Node T)

mutual
@[simp]
def Node.height: Node T -> Nat
| Node.mk _ left right _ => 1 + max (Subtree.height left) (Subtree.height right)

@[simp]
def Subtree.height: Subtree T -> Nat
| none => 0
| some n => Node.height n
end

mutual
@[simp]
def Node.size: Node T -> Nat
| Node.mk _ left right _ => 1 + Subtree.size left + Subtree.size right

@[simp]
def Subtree.size: Subtree T -> Nat
| none => 0
| some n => 1 + Node.size n
end

def Tree.nil: Tree T := { root := none }

-- Automatic synthesization of this seems possible at the Lean level?
instance: Inhabited (Tree T) where
  default := Tree.nil

instance [Inhabited T]: Inhabited (Node T) where
  default := ⟨ Inhabited.default, none, none, 0#i8 ⟩

mutual
@[simp, reducible] def Subtree.v (tree: Subtree T) : Set T :=
  match tree with
  | none => ∅
  | some node => node.v

@[simp, reducible] def Node.v (node : Node T) : Set T :=
  match node with
  | .mk x left right _ => {x} ∪ Subtree.v left ∪ Subtree.v right
end

@[reducible]
def Tree.v (t: Tree T): Set T := Subtree.v t.root

mutual
@[simp] def Subtree.forall (p: Node T -> Prop) (st : Subtree T) : Prop :=
  match st with
  | none => true
  | some st => st.forall p
termination_by Subtree.size st
decreasing_by simp_wf

def Node.forall (p: Node T -> Prop) (node : Node T) : Prop :=
  p node ∧
  Subtree.forall p node.left ∧ Subtree.forall p node.right
termination_by Node.size node
decreasing_by all_goals (simp_wf; fsimp [Node.left, Node.right]; split; fsimp <;> scalar_tac)
end

@[simp]
theorem Subtree.forall_left {p: Node T -> Prop} {t: Node T}: Node.forall p t -> Subtree.forall p t.left := by
  cases t; fsimp_all [Node.forall]

@[simp]
theorem Subtree.forall_right {p: Node T -> Prop} {t: Node T}: Subtree.forall p t -> Subtree.forall p t.right := by
  cases t; fsimp_all [Node.forall]

mutual
theorem Subtree.forall_imp {p q: Node T -> Prop} {t: Subtree T}: (∀ x, p x -> q x) -> Subtree.forall p t -> Subtree.forall q t
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
    fsimp [Node.forall]
    intros Himp Hleft Hright Hx
    fsimp [*]
    split_conjs <;> apply @Subtree.forall_imp T p q <;> tauto

end

def Node.balanceFactor (node : Node T) : ℤ :=
  Subtree.height node.right - Subtree.height node.left

def Subtree.balanceFactor (t: Subtree T): ℤ :=
  match t with
  | .none => 0
  | .some x => x.balanceFactor

@[simp]
theorem Subtree.some_balanceFactor (t: Node T) :
  Subtree.balanceFactor (some t) = t.balanceFactor := by
  fsimp [balanceFactor]

@[simp, reducible]
def Node.invAuxNotBalanced [LinearOrder T] (node : Node T) : Prop :=
  node.balance_factor.val = node.balanceFactor ∧
  (∀ x ∈ Subtree.v node.left, x < node.value) ∧
  (∀ x ∈ Subtree.v node.right, node.value < x)

def Node.invAux [LinearOrder T] (node : Node T) : Prop :=
  Node.invAuxNotBalanced node ∧
  -1 ≤ node.balanceFactor ∧ node.balanceFactor ≤ 1

@[reducible]
def Node.inv [LinearOrder T] (node : Node T) : Prop :=
  Node.forall Node.invAux node

-- TODO: use scalar_tac
@[aesop safe forward]
theorem Node.inv_imp_current [LinearOrder T] {node : Node T} (hInv : node.inv) :
  node.balance_factor.val = node.balanceFactor ∧
  (∀ x ∈ Subtree.v node.left, x < node.value) ∧
  (∀ x ∈ Subtree.v node.right, node.value < x) ∧
  -1 ≤ node.balanceFactor ∧ node.balanceFactor ≤ 1 := by
  fsimp_all [Node.inv, Node.forall, Node.invAux]

@[reducible]
def Subtree.inv [LinearOrder T] (st : Subtree T) : Prop :=
  match st with
  | none => true
  | some node => node.inv

@[simp]
theorem Subtree.inv_some [LinearOrder T] (s : Node T) : Subtree.inv (some s) = s.inv := by
  rfl

@[reducible]
def Tree.height (t : Tree T) := Subtree.height t.root

@[reducible]
def Tree.inv [LinearOrder T] (t : Tree T) : Prop := Subtree.inv t.root

@[simp]
theorem Node.inv_mk [LinearOrder T] (value : T) (left right : Option (Node T)) (bf : I8):
  (Node.mk value left right bf).inv ↔
  ((Node.mk value left right bf).invAux ∧
   Subtree.inv left ∧ Subtree.inv right) := by
  have : ∀ (n : Option (Node T)), Subtree.forall invAux n = Subtree.inv n := by
    unfold Subtree.forall
    fsimp [Subtree.inv]
  constructor <;>
  fsimp [*, Node.inv, Node.forall]

@[simp]
theorem Node.inv_left [LinearOrder T] {t: Node T}: t.inv -> Subtree.inv t.left := by
  fsimp [Node.inv]
  intro
  cases t; fsimp_all

@[simp]
theorem Node.inv_right [LinearOrder T] {t: Node T}: t.inv -> Subtree.inv t.right := by
  fsimp [Node.inv]
  intro
  cases t; fsimp_all

theorem Node.inv_imp_balance_factor_eq [LinearOrder T] {t: Node T} (hInv : t.inv) :
  t.balance_factor.val = t.balanceFactor := by
  fsimp [inv, Node.forall, invAux] at hInv
  cases t; fsimp_all

@[simp]
theorem Node.lt_imp_not_in_right [LinearOrder T] (node : Node T) (hInv : node.inv) (x : T)
  (hLt : x < node.value) :
  x ∉ Subtree.v node.right := by
  have ⟨ _, _, h, _ ⟩ := Node.inv_imp_current hInv
  intro hIn
  have := h x hIn
  have := lt_asymm this
  tauto

@[simp]
theorem Node.lt_imp_not_in_left [LinearOrder T] (node : Node T) (hInv : node.inv) (x : T)
  (hLt : node.value < x) :
  x ∉ Subtree.v node.left := by
  have ⟨ _, h, _, _ ⟩ := Node.inv_imp_current hInv
  intro hIn
  have := h x hIn
  have := lt_asymm this
  tauto

@[simp]
theorem Node.value_not_in_right [LinearOrder T] (node : Node T) (hInv : node.inv) :
  node.value ∉ Subtree.v node.right := by
  have ⟨ _, _, h, _ ⟩ := Node.inv_imp_current hInv
  intro hIn
  have := h node.value hIn
  have := ne_of_lt this
  tauto

@[simp]
theorem Node.value_not_in_left [LinearOrder T] (node : Node T) (hInv : node.inv) :
  node.value ∉ Subtree.v node.left := by
  have ⟨ _, h, _, _ ⟩ := Node.inv_imp_current hInv
  intro hIn
  have := h node.value hIn
  have := ne_of_lt this
  tauto

attribute [scalar_tac_simps]
  Subtree.height
  Node.height
  Subtree.some_balanceFactor
  Node.value._simpLemma_
  Node.left._simpLemma_
  Node.right._simpLemma_
  Node.balanceFactor
  Node.balance_factor._simpLemma_

@[progress]
theorem Tree.find_loop_spec
  {T : Type} (OrdInst : Ord T)
  [DecidableEq T] [LinOrd : LinearOrder T] [Ospec: OrdSpecLinearOrderEq OrdInst]
  (value : T) (t : Subtree T) (hInv : Subtree.inv t) :
  ∃ b, Tree.find_loop OrdInst value t = ok b ∧
  (b ↔ value ∈ Subtree.v t) := by
  unfold find_loop
  match t with
  | none => simp
  | some (.mk v left right height) =>
    fsimp only
    have hCmp := Ospec.infallible -- TODO
    progress keep Hordering as ⟨ ordering ⟩; clear hCmp
    have hInvLeft := Node.inv_left hInv
    have hInvRight := Node.inv_right hInv
    cases ordering <;> fsimp only
    . /- node.value < value -/
      progress
      have hNotIn := Node.lt_imp_not_in_left _ hInv
      fsimp_all
      intro; fsimp_all
    . /- node.value = value -/
      fsimp_all
    . /- node.value > value -/
      progress
      have hNotIn := Node.lt_imp_not_in_right _ hInv
      fsimp_all
      intro; fsimp_all

theorem Tree.find_spec
  {T : Type} (OrdInst : Ord T)
  [DecidableEq T] [LinOrd : LinearOrder T] [Ospec: OrdSpecLinearOrderEq OrdInst]
  (t : Tree T) (value : T) (hInv : t.inv) :
  ∃ b, Tree.find OrdInst t value = ok b ∧
  (b ↔ value ∈ t.v) := by
  rw [find]
  progress
  fsimp [Tree.v]; assumption

-- TODO: move
set_option maxHeartbeats 5000000

@[progress]
theorem Node.rotate_left_spec
  {T : Type} [LinearOrder T]
  (x z : T) (a b c : Option (Node T)) (bf_x bf_z : I8)
  -- Invariants for the subtrees
  (hInvA : Subtree.inv a)
  (hInvZ : Node.inv ⟨ z, b, c, bf_z ⟩)
  -- Invariant for the complete tree (but without the bounds on the balancing operation)
  (hInvX : Node.invAuxNotBalanced ⟨ x, a, some ⟨ z, b, c, bf_z ⟩, bf_x ⟩)
  -- The tree is not balanced
  (hBfX : bf_x.val = 2)
  -- Z has a positive balance factor
  (hBfZ : 0 ≤ bf_z.val)
  :
  ∃ ntree, rotate_left ⟨ x, a, none, bf_x ⟩ ⟨ z, b, c, bf_z ⟩ = ok ntree ∧
  let tree : Node T := ⟨ x, a, some ⟨ z, b, c, bf_z ⟩, bf_x ⟩
  -- We reestablished the invariant
  Node.inv ntree ∧
  -- The tree contains the nodes we expect
  Node.v ntree = Node.v tree ∧
  -- The height is the same as before. The original height is 2 + height b, and by
  -- inserting an element (which produced subtree c) we got a new height of
  -- 3 + height b; after the rotation we get back to 2 + height b.
  Node.height ntree = 2 + Subtree.height b
  := by
  rw [rotate_left]
  fsimp [core.mem.replace]
  -- Some proofs common to both cases
  -- Elements in the left subtree are < z
  have : ∀ (y : T), (y = x ∨ y ∈ Subtree.v a) ∨ y ∈ Subtree.v b → y < z := by
    fsimp [invAux] at hInvZ
    intro y hIn
    -- TODO: automate that
    cases hIn
    . rename _ => hIn
      cases hIn
      . fsimp_all
      . -- Proving: y ∈ a → y < z
        -- Using: y < x ∧ x < z
        rename _ => hIn
        have hInv1 : y < x := by tauto
        have hInv2 := hInvX.right.right z
        fsimp at hInv2
        apply lt_trans hInv1 hInv2
    . tauto
  -- Elements in the right subtree are < z
  have : ∀ y ∈ Subtree.v c, z < y := by
    fsimp [invAux] at hInvZ
    tauto
  -- Two cases depending on whether the BF of Z is 0 or 1
  split
  . -- BF(Z) == 0
    fsimp at *
    fsimp [*]
    -- TODO: scalar_tac should succeed below
    have hHeightEq : Subtree.height b = Subtree.height c := by
      fsimp_all [balanceFactor, Node.invAux]
      scalar_tac
    -- TODO: scalar_tac should succeed below
    have : 1 + Subtree.height c = Subtree.height a + 2 := by
      fsimp_all [balanceFactor, Node.invAux]
      scalar_tac
    fsimp_all
    split_conjs
    . -- Partial invariant for the final tree starting at z
      fsimp [Node.invAux, balanceFactor, *]
      split_conjs <;> (try omega)
    . -- Partial invariant for the subtree x
      fsimp [Node.invAux, balanceFactor, *]
      split_conjs <;> (try omega) <;> fsimp_all
    . -- The sets are the same
      apply Set.ext; simp; tauto
    . -- The height didn't change
      fsimp [balanceFactor] at *
      replace hInvX := hInvX.left
      fsimp_all
      scalar_tac
  . -- BF(Z) == 1
    rename _ => hNotEq
    fsimp at *
    fsimp [*]
    fsimp_all
    have : bf_z.val = 1 := by
      fsimp [Node.invAux] at hInvZ
      omega
    clear hNotEq hBfZ
    have : Subtree.height c = 1 + Subtree.height b := by
      fsimp [balanceFactor, Node.invAux] at *
      replace hInvZ := hInvZ.left
      omega
    have : max (Subtree.height c) (Subtree.height b) = Subtree.height c := by
      scalar_tac
    -- TODO: we shouldn't need this: scalar_tac should succeed
    have : Subtree.height c = 1 + Subtree.height a := by
      -- TODO: scalar_tac fails here (conversion int/nat)
      fsimp_all [balanceFactor, Node.invAux]
      omega
    have : Subtree.height a = Subtree.height b := by
      fsimp_all
    split_conjs
    . -- Invariant for whole tree (starting at z)
      fsimp [invAux, balanceFactor]
      split_conjs <;> (try omega)
    . -- Invariant for subtree x
      fsimp [invAux, balanceFactor]
      split_conjs <;> (try omega) <;> fsimp_all
    . -- The sets are the same
      apply Set.ext; simp; tauto
    . -- The height didn't change
      fsimp [balanceFactor] at *
      replace hInvX := hInvX.left
      fsimp_all
      scalar_tac

@[progress]
theorem Node.rotate_right_spec
  {T : Type} [LinearOrder T]
  (x z : T) (a b c : Option (Node T)) (bf_x bf_z : I8)
  -- Invariants for the subtrees
  (hInvC : Subtree.inv c)
  (hInvZ : Node.inv ⟨ z, a, b, bf_z ⟩)
  -- Invariant for the complete tree (but without the bounds on the balancing operation)
  (hInvX : Node.invAuxNotBalanced ⟨ x, some ⟨ z, a, b, bf_z ⟩, c, bf_x ⟩)
  -- The tree is not balanced
  (hBfX : bf_x.val = -2)
  -- Z has a positive balance factor
  (hBfZ : bf_z.val ≤ 0)
  :
  ∃ ntree, rotate_right ⟨ x, none, c, bf_x ⟩ ⟨ z, a, b, bf_z ⟩ = ok ntree ∧
  let tree : Node T := ⟨ x, some ⟨ z, a, b, bf_z ⟩, c, bf_x ⟩
  -- We reestablished the invariant
  Node.inv ntree ∧
  -- The tree contains the nodes we expect
  Node.v ntree = Node.v tree ∧
  -- The height is the same as before. The original height is 2 + height b, and by
  -- inserting an element (which produced subtree c) we got a new height of
  -- 3 + height b; after the rotation we get back to 2 + height b.
  Node.height ntree = 2 + Subtree.height b
  := by
  rw [rotate_right]
  fsimp [core.mem.replace]
  -- Some proofs common to both cases
  -- Elements in the right subtree are > z
  have : ∀ (y : T), (y = x ∨ y ∈ Subtree.v b) ∨ y ∈ Subtree.v c → z < y := by
    fsimp [invAux] at *
    intro y hIn
    -- TODO: automate that
    cases hIn
    . rename _ => hIn
      cases hIn
      . fsimp [*]
      . tauto
    . -- Proving: y ∈ c → z < y
      -- Using: z < x ∧ x < y
      have : z < x := by tauto
      have : x < y := by tauto
      apply lt_trans <;> tauto
  -- Elements in the left subtree are < z
  have : ∀ y ∈ Subtree.v a, y < z := by
    fsimp_all [invAux]
  -- Two cases depending on whether the BF of Z is 0 or 1
  split
  . -- BF(Z) == 0
    fsimp at *
    fsimp [*]
    have hHeightEq : Subtree.height a = Subtree.height b := by
      fsimp_all [balanceFactor, Node.invAux]
      -- TODO: scalar_tac fails here (conversion int/nat)
      omega
    -- TODO: we shouldn't need this: scalar_tac should succeed
    have : 1 + Subtree.height a = Subtree.height c + 2 := by
      -- TODO: scalar_tac fails here (conversion int/nat)
      fsimp_all [balanceFactor, Node.invAux]
      omega
    fsimp_all
    split_conjs
    . -- Partial invariant for the final tree starting at z
      fsimp [Node.invAux, balanceFactor, *]
      split_conjs <;> (try omega)
    . -- Partial invariant for the subtree x
      fsimp [Node.invAux, balanceFactor, *]
      split_conjs <;> (try omega) <;> fsimp_all
    . -- The sets are the same
      apply Set.ext; simp; tauto
    . -- The height didn't change
      fsimp [balanceFactor] at *
      replace hInvX := hInvX.left
      fsimp_all
      scalar_tac
  . -- BF(Z) == -1
    rename _ => hNotEq
    fsimp at *
    fsimp [*]
    fsimp_all
    have : bf_z.val = -1 := by
      fsimp [Node.invAux] at hInvZ
      omega
    clear hNotEq hBfZ
    have : Subtree.height a = 1 + Subtree.height b := by
      fsimp [balanceFactor, Node.invAux] at *
      replace hInvZ := hInvZ.left
      omega
    have : max (Subtree.height a) (Subtree.height b) = Subtree.height a := by
      scalar_tac
    -- TODO: we shouldn't need this: scalar_tac should succeed
    have : Subtree.height a = 1 + Subtree.height c := by
      -- TODO: scalar_tac fails here (conversion int/nat)
      fsimp_all [balanceFactor, Node.invAux]
      omega
    have : Subtree.height c = Subtree.height b := by
      fsimp_all
    split_conjs
    . -- Invariant for whole tree (starting at z)
      fsimp [invAux, balanceFactor]
      split_conjs <;> (try omega)
    . -- Invariant for subtree x
      fsimp [invAux, balanceFactor]
      split_conjs <;> (try omega) <;> fsimp_all
    . -- The sets are the same
      apply Set.ext; simp; tauto
    . -- The height didn't change
      fsimp [balanceFactor] at *
      replace hInvX := hInvX.left
      fsimp_all
      scalar_tac

@[progress]
theorem Node.rotate_left_right_spec
  {T : Type} [LinearOrder T]
  (x y z : T) (bf_x bf_y bf_z : I8)
  (a b t0 t1 : Option (Node T))
  -- Invariants for the subtrees
  (hInvX : Node.invAuxNotBalanced ⟨ x, some ⟨ z, t0, some ⟨ y, a, b, bf_y ⟩, bf_z ⟩, t1, bf_x ⟩)
  (hInvZ : Node.inv ⟨ z, t0, some ⟨ y, a, b, bf_y ⟩, bf_z ⟩)
  (hInv1 : Subtree.inv t1)
  -- The tree is not balanced
  (hBfX : bf_x.val = -2)
  -- Z has a positive balance factor
  (hBfZ : bf_z.val = 1)
  :
  let x_tree := ⟨ x, none, t1, bf_x ⟩
  let y_tree := ⟨ y, a, b, bf_y ⟩
  let z_tree := ⟨ z, t0, some y_tree, bf_z ⟩
  let tree : Node T := ⟨ x, some z_tree, t1, bf_x ⟩
  ∃ ntree, rotate_left_right x_tree z_tree = ok ntree ∧
  -- We reestablished the invariant
  Node.inv ntree ∧
  -- The tree contains the nodes we expect
  Node.v ntree = Node.v tree ∧
  -- The height is the same as before. The original height is 2 + height a, and by
  -- inserting an element (which produced subtree c) we got a new height of
  -- 3 + height b; after the rotation we get back to 2 + height b.
  Node.height ntree = 2 + Subtree.height t0
  := by
  intro x_tree y_tree z_tree tree
  fsimp [rotate_left_right] -- TODO: this inlines the local decls
  -- Some facts about the heights and the balance factors
  -- TODO: automate that
  have : Node.height z_tree = Subtree.height t1 + 2 := by
    fsimp [y_tree, z_tree, inv, invAux, balanceFactor] at *; omega
  have : Node.height y_tree = Subtree.height t0 + 1 := by
    fsimp [y_tree, z_tree, inv, invAux, balanceFactor] at *; omega
  have : bf_y.val + Subtree.height a = Subtree.height b := by
    fsimp [y_tree, z_tree, inv, invAux, balanceFactor] at *; omega
  fsimp [x_tree, y_tree, z_tree] at *
  -- TODO: automate the < proofs
  -- Auxiliary proofs for invAux for y
  have : ∀ (e : T), (e = z ∨ e ∈ Subtree.v t0) ∨ e ∈ Subtree.v a → e < y := by
    intro e hIn
    fsimp [invAux] at *
    cases hIn
    . rename _ => hIn
      -- TODO: those cases are cumbersome
      cases hIn
      . fsimp_all
      . have : e < z := by tauto
        have : z < y := by tauto
        apply lt_trans <;> tauto
    . tauto
  have : ∀ (e : T), (e = x ∨ e ∈ Subtree.v b) ∨ e ∈ Subtree.v t1 → y < e := by
    intro e hIn; fsimp [invAux] at *
    cases hIn
    . rename _ => hIn
      cases hIn
      . fsimp_all
      . tauto
    . have : y < x := by
        replace hInvX := hInvX.right.left y
        tauto
      have : x < e := by tauto
      apply lt_trans <;> tauto
  -- Auxiliary proofs for invAux for z
  have : ∀ e ∈ Subtree.v t0, e < z := by
    intro x hIn; fsimp [invAux] at *
    tauto
  have : ∀ e ∈ Subtree.v a, z < e := by
    intro e hIn; fsimp [invAux] at *
    replace hInvZ := hInvZ.right.right.left e
    tauto
  -- Auxiliary proofs for invAux for x
  have : ∀ e ∈ Subtree.v b, e < x := by
    intro e hIn; fsimp [invAux] at *
    replace hInvX := hInvX.right.left e
    tauto
  have : ∀ e ∈ Subtree.v t1, x < e := by
    intro e hIn; fsimp [invAux] at *
    tauto
  -- Case disjunction on the balance factor of Y
  split
  . -- BF(Y) = 0
    fsimp [balanceFactor] at *
    split_conjs <;> (try fsimp [Node.invAux, balanceFactor, *])
    . -- invAux for y
      split_conjs <;> (try omega)
    . -- invAux for z
      split_conjs <;> (try assumption) <;> (try scalar_tac)
    . -- invAux for x
      split_conjs <;> (try assumption) <;> (try scalar_tac)
    . -- The sets are the same
      apply Set.ext; fsimp [tree, z_tree, y_tree]; tauto
    . -- Height
      scalar_tac
  . split <;> simp
    . -- BF(Y) < 0
      have : bf_y.val = -1 := by fsimp [Node.invAux] at *; omega
      fsimp [balanceFactor] at *
      split_conjs <;> (try fsimp [Node.invAux, balanceFactor, *])
      . -- invAux for y
        split_conjs <;> (try omega)
      . -- invAux for z
        split_conjs <;> (try assumption) <;> (try scalar_tac)
      . -- invAux for x
        split_conjs <;> (try assumption) <;> (try scalar_tac)
      . -- The sets are the same
        apply Set.ext; fsimp [tree, z_tree, y_tree]; tauto
      . -- Height
        scalar_tac
    . -- BF(Y) > 0
      have : bf_y.val = 1 := by fsimp [Node.invAux] at *; omega
      split_conjs <;> (try fsimp [Node.invAux, balanceFactor, *])
      . -- invAux for y
        split_conjs <;> (try omega)
      . -- invAux for z
        split_conjs <;> (try assumption) <;> (try scalar_tac)
      . -- invAux for x
        split_conjs <;> (try assumption) <;> (try scalar_tac)
      . -- The sets are the same
        apply Set.ext; fsimp [tree, z_tree, y_tree]; tauto
      . -- Height
        scalar_tac

@[progress]
theorem Node.rotate_right_left_spec
  {T : Type} [LinearOrder T]
  (x y z : T) (bf_x bf_y bf_z : I8)
  (a b t0 t1 : Option (Node T))
  -- Invariants for the subtrees
  (hInvX : Node.invAuxNotBalanced ⟨ x, t1, some ⟨ z, some ⟨ y, b, a, bf_y ⟩, t0, bf_z ⟩, bf_x ⟩)
  (hInvZ : Node.inv ⟨ z, some ⟨ y, b, a, bf_y ⟩, t0, bf_z ⟩)
  (hInv1 : Subtree.inv t1)
  -- The tree is not balanced
  (hBfX : bf_x.val = 2)
  -- Z has a negative balance factor
  (hBfZ : bf_z.val = -1)
  :
  let x_tree := ⟨ x, t1, none, bf_x ⟩
  let y_tree := ⟨ y, b, a, bf_y ⟩
  let z_tree := ⟨ z, some y_tree, t0, bf_z ⟩
  let tree : Node T := ⟨ x, t1, some z_tree, bf_x ⟩
  ∃ ntree, rotate_right_left x_tree z_tree = ok ntree ∧
  -- We reestablished the invariant
  Node.inv ntree ∧
  -- The tree contains the nodes we expect
  Node.v ntree = Node.v tree ∧
  -- The height is the same as before. The original height is 2 + height b, and by
  -- inserting an element (which produced subtree c) we got a new height of
  -- 3 + height b; after the rotation we get back to 2 + height b.
  Node.height ntree = 2 + Subtree.height t1
  := by
  intro x_tree y_tree z_tree tree
  fsimp [rotate_right_left] -- TODO: this inlines the local decls
  -- Some facts about the heights and the balance factors
  -- TODO: automate that
  have : Node.height z_tree = Subtree.height t1 + 2 := by
    fsimp [y_tree, z_tree, inv, invAux, balanceFactor] at *; omega
  have : Node.height y_tree = Subtree.height t0 + 1 := by
    fsimp [y_tree, z_tree, inv, invAux, balanceFactor] at *; omega
  have : bf_y.val + Subtree.height b = Subtree.height a := by
    fsimp [y_tree, z_tree, inv, invAux, balanceFactor] at *; omega
  fsimp [x_tree, y_tree, z_tree] at *
  -- TODO: automate the < proofs
  -- Auxiliary proofs for invAux for y
  have : ∀ (e : T), (e = z ∨ e ∈ Subtree.v a) ∨ e ∈ Subtree.v t0 → y < e := by
    intro e hIn
    fsimp [invAux] at *
    cases hIn
    . rename _ => hIn
      -- TODO: those cases are cumbersome
      cases hIn
      . fsimp_all
      . tauto
    . have : z < e := by tauto
      have : y < z := by tauto
      apply lt_trans <;> tauto
  have : ∀ (e : T), (e = x ∨ e ∈ Subtree.v t1) ∨ e ∈ Subtree.v b → e < y := by
    intro e hIn; fsimp [invAux] at *
    cases hIn
    . rename _ => hIn
      cases hIn
      . fsimp_all
      . have : x < y := by
          replace hInvX := hInvX.right.right y
          tauto
        have : e < x := by tauto
        apply lt_trans <;> tauto
    . tauto
  -- Auxiliary proofs for invAux for z
  have : ∀ e ∈ Subtree.v t0, z < e := by
    intro x hIn; fsimp [invAux] at *
    tauto
  have : ∀ e ∈ Subtree.v a, e < z := by
    intro e hIn; fsimp [invAux] at *
    replace hInvZ := hInvZ.right.left e
    tauto
  -- Auxiliary proofs for invAux for x
  have : ∀ e ∈ Subtree.v b, x < e := by
    intro e hIn; fsimp [invAux] at *
    replace hInvX := hInvX.right.right e
    tauto
  have : ∀ e ∈ Subtree.v t1, e < x := by
    intro e hIn; fsimp [invAux] at *
    tauto
  -- Case disjunction on the balance factor of Y
  split
  . -- BF(Y) = 0
    fsimp [balanceFactor] at *
    split_conjs <;> (try fsimp [Node.invAux, balanceFactor, *])
    . -- invAux for y
      split_conjs <;> (try omega)
    . -- invAux for z
      split_conjs <;> (try assumption) <;> (try scalar_tac)
    . -- invAux for x
      split_conjs <;> (try assumption) <;> (try scalar_tac)
    . -- The sets are the same
      apply Set.ext; fsimp [tree, z_tree, y_tree]; tauto
    . -- Height
      scalar_tac
  . split <;> simp
    . -- BF(Y) > 0
      have : bf_y.val = 1 := by fsimp [Node.invAux] at *; omega
      fsimp [balanceFactor] at *
      split_conjs <;> (try fsimp [Node.invAux, balanceFactor, *])
      . -- invAux for y
        split_conjs <;> (try omega)
      . -- invAux for z
        split_conjs <;> (try assumption) <;> (try scalar_tac)
      . -- invAux for x
        split_conjs <;> (try assumption) <;> (try scalar_tac)
      . -- The sets are the same
        apply Set.ext; fsimp [tree, z_tree, y_tree]; tauto
      . -- Height
        scalar_tac
    . -- BF(Y) < 0
      have : bf_y.val = -1 := by fsimp [Node.invAux] at *; omega
      split_conjs <;> (try fsimp [Node.invAux, balanceFactor, *])
      . -- invAux for y
        split_conjs <;> (try omega)
      . -- invAux for z
        split_conjs <;> (try assumption) <;> (try scalar_tac)
      . -- invAux for x
        split_conjs <;> (try assumption) <;> (try scalar_tac)
      . -- The sets are the same
        apply Set.ext; fsimp [tree, z_tree, y_tree]; tauto
      . -- Height
        scalar_tac

-- For the proofs of termination
@[simp]
theorem Node.left_height_lt_height (n : Node T) :
  Subtree.height n.left < n.height := by
  cases n; simp; scalar_tac

@[simp]
theorem Node.right_height_lt_height (n : Node T) :
  Subtree.height n.right < n.height := by
  cases n; simp; scalar_tac

mutual

@[progress]
theorem Node.insert_spec
  {T : Type} (OrdInst : Ord T) [LinOrd : LinearOrder T] [Ospec: OrdSpecLinearOrderEq OrdInst]
  (node : Node T) (value : T)
  (hInv : Node.inv node) :
  ∃ b node', Node.insert OrdInst node value = ok (b, node') ∧
  Node.inv node' ∧
  Node.v node' = Node.v node ∪ {value} ∧
  (if b then node'.height = node.height + 1 else node'.height = node.height) ∧
  -- This is important for some of the proofs
  (b → node'.balanceFactor ≠ 0) := by
  unfold Node.insert
  have hCmp := Ospec.infallible -- TODO
  progress as ⟨ ordering ⟩
  split <;> rename _ => hEq <;> clear hCmp <;> fsimp at *
  . -- value < node.value
    progress as ⟨ updt, node', h1, h2 ⟩
    fsimp_all
  . -- value = node.value
    cases node; fsimp_all
  . -- node.value < value
    progress as ⟨ updt, node', h1, h2 ⟩
    fsimp_all
termination_by (node.height, 1)
decreasing_by all_goals simp_wf

@[progress]
theorem Tree.insert_in_opt_node_spec
  {T : Type} (OrdInst : Ord T) [LinOrd : LinearOrder T] [Ospec: OrdSpecLinearOrderEq OrdInst]
  (tree : Option (Node T)) (value : T)
  (hInv : Subtree.inv tree) :
  ∃ b tree', Tree.insert_in_opt_node OrdInst tree value = ok (b, tree') ∧
  Subtree.inv tree' ∧
  Subtree.v tree' = Subtree.v tree ∪ {value} ∧
  (if b then Subtree.height tree' = Subtree.height tree + 1
   else Subtree.height tree' = Subtree.height tree) ∧
  (b → Subtree.height tree > 0 → Subtree.balanceFactor tree' ≠ 0) := by
  unfold Tree.insert_in_opt_node
  cases hNode : tree <;> fsimp [hNode]
  . -- tree = none
    fsimp [Node.invAux, Node.balanceFactor]
  . -- tree = some
    rename Node T => node
    have hNodeInv : Node.inv node := by fsimp_all
    progress as ⟨ updt, tree' ⟩
    fsimp_all
termination_by (Subtree.height tree, 2)
decreasing_by simp_wf; fsimp [*]

-- TODO: any modification triggers the replay of the whole proof
@[progress]
theorem Node.insert_in_left_spec
  {T : Type} (OrdInst : Ord T)
  [LinOrd : LinearOrder T] [Ospec: OrdSpecLinearOrderEq OrdInst]
  (node : Node T) (value : T)
  (hInv : Node.inv node)
  (hLt : value < node.value) :
  ∃ b node', Node.insert_in_left OrdInst node value = ok (b, node') ∧
  Node.inv node' ∧
  Node.v node' = Node.v node ∪ {value} ∧
  (if b then node'.height = node.height + 1 else node'.height = node.height) ∧
  (b → node'.balanceFactor ≠ 0) := by
  unfold Node.insert_in_left
  have hInvLeft : Subtree.inv node.left := by cases node; fsimp_all
  progress as ⟨ updt, left_opt' ⟩
  split
  . -- the height of the subtree changed
    have hBalanceFactor : node.balance_factor = node.balanceFactor ∧
           -1 ≤ node.balanceFactor ∧ node.balanceFactor ≤ 1 := by
      cases node; fsimp_all [Node.invAux]
    progress as ⟨ i ⟩
    split
    . -- i = -2
      simp
      cases h: left_opt'
      . fsimp_all -- absurd
      . rename_i left'
        fsimp [h]
        cases node with | mk x left right balance_factor =>
        split
        . -- rotate_right
          -- TODO: fix progress
          cases h:left' with | mk z a b bf_z =>
          progress as ⟨ tree', hInv', hTree'Set, hTree'Height ⟩
          -- TODO: syntax for preconditions
          . fsimp_all
          . fsimp_all
          . fsimp_all [Node.inv, Node.invAux, Node.invAuxNotBalanced, Node.balanceFactor]
            scalar_tac
          . fsimp [*]
            split_conjs
            . -- set reasoning
              fsimp_all
              apply Set.ext; simp
              intro x; tauto
            . -- height
              fsimp_all [Node.invAux, Node.balanceFactor]
              -- This assertion is not necessary for the proof, but it is important that it holds.
              -- We can prove it because of the post-conditions `b → node'.balanceFactor ≠ 0` (see above)
              have : bf_z.val = -1 := by scalar_tac
              scalar_tac
        . -- rotate_left_right
          simp
          cases h:left'
          rename_i z t0 y bf_z
          cases h: y
          . -- Can't get there
            fsimp_all [Node.balanceFactor, Node.invAux]
          . rename_i y
            cases h: y with | mk y a b bf_y =>
            progress as ⟨ tree', hInv', hTree'Set, hTree'Height ⟩
            -- TODO: syntax for preconditions
            . fsimp_all [Node.inv, Node.invAux, Node.invAuxNotBalanced, Node.balanceFactor]; scalar_tac
            . fsimp_all
            . fsimp_all
            . fsimp_all [Node.invAux, Node.balanceFactor]; scalar_tac
            . -- End of the proof
              fsimp [*]
              split_conjs
              . apply Set.ext; fsimp_all
                intro x; tauto
              . fsimp_all [Node.invAux, Node.balanceFactor]
                scalar_tac
    . -- i ≠ -2: the height of the tree did not change
      fsimp [*]
      split_conjs
      . cases node; fsimp_all [Node.invAux, Node.balanceFactor]
        split_conjs <;> scalar_tac
      . apply Set.ext; simp
        cases node; fsimp_all
        tauto
      . fsimp_all
        cases node with | mk node_value left right balance_factor =>
        split <;> fsimp [Node.balanceFactor] at * <;> scalar_tac
      . fsimp_all [Node.balanceFactor]
        scalar_tac
  . -- the height of the subtree did not change
    fsimp [*]
    split_conjs
    . cases node;
      fsimp_all [Node.invAux, Node.balanceFactor]
    . apply Set.ext; simp; intro x
      cases node; fsimp_all
      tauto
    . fsimp_all
      cases node; fsimp_all
termination_by (node.height, 0)
decreasing_by simp_wf

@[progress]
theorem Node.insert_in_right_spec
  {T : Type} (OrdInst : Ord T)
  [LinOrd : LinearOrder T] [Ospec: OrdSpecLinearOrderEq OrdInst]
  (node : Node T) (value : T)
  (hInv : Node.inv node)
  (hGt : value > node.value) :
  ∃ b node', Node.insert_in_right OrdInst node value = ok (b, node') ∧
  Node.inv node' ∧
  Node.v node' = Node.v node ∪ {value} ∧
  (if b then node'.height = node.height + 1 else node'.height = node.height) ∧
  (b → node'.balanceFactor ≠ 0) := by
  unfold Node.insert_in_right
  have hInvLeft : Subtree.inv node.right := by cases node; fsimp_all
  progress as ⟨ updt, right_opt' ⟩
  split
  . -- the height of the subtree changed
    have hBalanceFactor : node.balance_factor = node.balanceFactor ∧
           -1 ≤ node.balanceFactor ∧ node.balanceFactor ≤ 1 := by
      cases node; fsimp_all [Node.invAux]
    progress as ⟨ i ⟩
    split
    . -- i = 2
      simp
      cases h: right_opt'
      . fsimp_all -- absurd
      . rename_i right'
        fsimp [h]
        split
        . -- rotate_left
          cases node
          rename_i x a right balance_factor
          -- TODO: fix progress
          cases h:right'
          rename_i z b c bf_z
          progress as ⟨ tree', hInv', hTree'Set, hTree'Height ⟩
          -- TODO: syntax for preconditions
          . fsimp_all
          . fsimp_all
          . fsimp_all [Node.inv, Node.invAux, Node.invAuxNotBalanced, Node.balanceFactor]; scalar_tac
          . -- End of the proof
            fsimp [*]
            split_conjs
            . -- set reasoning
              fsimp_all
            . -- height
              fsimp_all [Node.invAux, Node.balanceFactor]
              -- Remark: here we have:
              -- bf_z.val = -1
              scalar_tac
        . -- rotate_right_left
          cases node
          rename_i x t1 right balance_factor
          simp
          cases h:right'
          rename_i z y t0 bf_z
          cases h: y
          . -- Can't get there
            fsimp_all [Node.balanceFactor, Node.invAux]
          . rename_i y
            cases h: y
            rename_i y b a bf_y
            progress as ⟨ tree', hInv', hTree'Set, hTree'Height ⟩
            -- TODO: syntax for preconditions
            . fsimp_all [Node.inv, Node.invAux, Node.invAuxNotBalanced, Node.balanceFactor]; scalar_tac
            . fsimp_all
            . fsimp_all
            . fsimp_all [Node.invAux, Node.balanceFactor]; scalar_tac
            . -- End of the proof
              fsimp [*]
              split_conjs
              . apply Set.ext; fsimp_all
              . fsimp (config := {maxDischargeDepth := 1}) [Node.invAux, Node.balanceFactor] at *
                scalar_tac
    . -- i ≠ -2: the height of the tree did not change
      fsimp [*]
      split_conjs
      . cases node; fsimp_all [Node.invAux, Node.balanceFactor]
        split_conjs <;> scalar_tac
      . apply Set.ext; simp
        cases node; fsimp_all
      . fsimp_all
        cases node with | mk node_value left right balance_factor =>
        split <;> fsimp [Node.balanceFactor] at * <;> scalar_tac
      . fsimp_all [Node.balanceFactor]
        scalar_tac
  . -- the height of the subtree did not change
    fsimp [*] -- TODO: annoying to use this fsimp everytime: put this in progress
    split_conjs
    . cases node;
      fsimp_all [Node.invAux, Node.balanceFactor]
    . apply Set.ext; simp; intro x
      cases node; fsimp_all
    . fsimp_all
      cases node; fsimp_all
termination_by (node.height, 0)
decreasing_by simp_wf

end

@[progress]
theorem Tree.insert_spec {T : Type}
  (OrdInst : Ord T) [LinOrd : LinearOrder T] [Ospec: OrdSpecLinearOrderEq OrdInst]
  (tree : Tree T) (value : T)
  (hInv : tree.inv) :
  ∃ updt tree', Tree.insert OrdInst tree value = ok (updt, tree') ∧
  tree'.inv ∧
  (if updt then tree'.height = tree.height + 1 else tree'.height = tree.height) ∧
  tree'.v = tree.v ∪ {value} := by
  unfold Tree.insert
  progress as ⟨ updt, tree' ⟩
  fsimp [*]

@[progress]
theorem Tree.new_spec {T : Type} (OrdInst : Ord T) :
  ∃ t, Tree.new OrdInst = ok t ∧ t.v = ∅ ∧ t.height = 0 := by
  fsimp [new, Tree.v, Tree.height]

end avl
