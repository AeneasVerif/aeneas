import Avl.Funs
import Avl.Types
import Avl.OrderSpec

namespace avl

open Primitives Result

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
| Node.mk y left right _ => 1 + max (Subtree.height left) (Subtree.height right)

@[simp]
def Subtree.height: Subtree T -> Nat
| none => 0
| some n => Node.height n
end

mutual
@[simp]
def Node.size: Node T -> Nat
| Node.mk y left right _ => 1 + Subtree.size left + Subtree.size right

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
decreasing_by all_goals (simp_wf <;> simp [Node.left, Node.right] <;> split <;> simp <;> scalar_tac)
end

@[simp]
theorem Subtree.forall_left {p: Node T -> Prop} {t: Node T}: Node.forall p t -> Subtree.forall p t.left := by
  cases t; simp_all [Node.forall]

@[simp]
theorem Subtree.forall_right {p: Node T -> Prop} {t: Node T}: Subtree.forall p t -> Subtree.forall p t.right := by
  cases t; simp_all [Node.forall]

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
    simp [Node.forall]
    intros Himp Hleft Hright Hx
    simp [*]
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
  simp [balanceFactor]

@[simp, reducible]
def Node.invNoBalance [LinearOrder T] (node : Node T) : Prop :=
  node.balance_factor.val = node.balanceFactor ∧
  (∀ x ∈ Subtree.v node.left, x < node.value) ∧
  (∀ x ∈ Subtree.v node.right, node.value < x)

def Node.inv_aux [LinearOrder T] (node : Node T) : Prop :=
  Node.invNoBalance node ∧
  -1 ≤ node.balanceFactor ∧ node.balanceFactor ≤ 1

@[reducible]
def Node.inv [LinearOrder T] (node : Node T) : Prop :=
  Node.forall Node.inv_aux node

-- TODO: use a custom set
@[aesop safe forward]
theorem Node.inv_imp_current [LinearOrder T] {node : Node T} (hInv : node.inv) :
  node.balance_factor.val = node.balanceFactor ∧
  (∀ x ∈ Subtree.v node.left, x < node.value) ∧
  (∀ x ∈ Subtree.v node.right, node.value < x) ∧
  -1 ≤ node.balanceFactor ∧ node.balanceFactor ≤ 1 := by
  simp_all [Node.inv, Node.forall, Node.inv_aux]

@[reducible]
def Subtree.inv [LinearOrder T] (st : Subtree T) : Prop :=
  match st with
  | none => true
  | some node => node.inv

@[simp]
theorem Subtree.inv_some [LinearOrder T] (s : Node T) : Subtree.inv (some s) = s.inv := by
  rfl

@[reducible]
def Tree.inv [LinearOrder T] (t : Tree T) : Prop := Subtree.inv t.root

@[simp]
theorem Node.inv_mk [LinearOrder T] (value : T) (left right : Option (Node T)) (bf : I8):
  (Node.mk value left right bf).inv ↔
  ((Node.mk value left right bf).inv_aux ∧
   Subtree.inv left ∧ Subtree.inv right) := by
  have : ∀ (n : Option (Node T)), Subtree.forall inv_aux n = Subtree.inv n := by
    unfold Subtree.forall
    simp [Subtree.inv]
  constructor <;>
  simp [*, Node.inv, Node.forall]

@[simp]
theorem Node.inv_left [LinearOrder T] {t: Node T}: t.inv -> Subtree.inv t.left := by
  simp [Node.inv]
  intro
  cases t; simp_all

@[simp]
theorem Node.inv_right [LinearOrder T] {t: Node T}: t.inv -> Subtree.inv t.right := by
  simp [Node.inv]
  intro
  cases t; simp_all

theorem Node.inv_imp_balance_factor_eq [LinearOrder T] {t: Node T} (hInv : t.inv) :
  t.balance_factor.val = t.balanceFactor := by
  simp [inv, Node.forall, inv_aux] at hInv
  cases t; simp_all

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

@[pspec]
theorem Tree.find_loop_spec
  {T : Type} (OrdInst : Ord T)
  [DecidableEq T] [LinOrd : LinearOrder T] [Ospec: OrdSpecLinearOrderEq OrdInst]
  (value : T) (t : Subtree T) (hInv : Subtree.inv t) :
  ∃ b, Tree.find_loop T OrdInst value t = ok b ∧
  (b ↔ value ∈ Subtree.v t) := by
  rewrite [find_loop]
  match t with
  | none => simp
  | some (.mk v left right height) =>
    dsimp only
    have hCmp := Ospec.infallible
    progress keep Hordering as ⟨ ordering ⟩; clear hCmp
    have hInvLeft := Node.inv_left hInv
    have hInvRight := Node.inv_right hInv
    cases ordering <;> dsimp only
    . /- node.value < value -/
      progress
      have hNotIn := Node.lt_imp_not_in_left _ hInv
      simp_all
      intro; simp_all
    . /- node.value = value -/
      simp_all
    . /- node.value > value -/
      progress
      have hNotIn := Node.lt_imp_not_in_right _ hInv
      simp_all
      intro; simp_all

theorem Tree.find_spec
  {T : Type} (OrdInst : Ord T)
  [DecidableEq T] [LinOrd : LinearOrder T] [Ospec: OrdSpecLinearOrderEq OrdInst]
  (t : Tree T) (value : T) (hInv : t.inv) :
  ∃ b, Tree.find T OrdInst t value = ok b ∧
  (b ↔ value ∈ t.v) := by
  rw [find]
  progress
  simp [Tree.v]; assumption

-- TODO: generalize and move
@[scalar_tac max x y]
theorem Nat.max_equiv (x y : Nat) :
  x ≤ max x y ∧ y ≤ max x y ∧ (max x y = x ∨ max x y = y) := by
  omega

-- TODO: generalize and move
@[scalar_tac max x y]
theorem Int.max_equiv (x y : Int) :
  x ≤ max x y ∧ y ≤ max x y ∧ (max x y = x ∨ max x y = y) := by
  omega

set_option maxHeartbeats 5000000

theorem Node.rotate_left_spec
  {T : Type} [LinearOrder T]
  (x : T) (a : Option (Node T)) (bf_x : I8) (z : T) (b c : Option (Node T))
  -- Invariants for the subtrees
  (hInvA : Subtree.inv a)
  --(hInvB : Subtree.inv b)
  --(hInvC : Subtree.inv c)
  (hInvZ : Node.inv ⟨ z, b, c, bf_z ⟩)
  -- Invariant for the complete tree (but without the bounds on the balancing operation)
  (hInv : Node.invNoBalance ⟨ x, a, some ⟨ z, b, c, bf_z ⟩, bf_x ⟩)
  -- The tree is not balanced
  (hBfX : bf_x.val = 2)
  -- Z has a positive balance factor
  (hBfZ : 0 ≤ bf_z.val)
  :
  ∃ ntree, rotate_left T ⟨ x, a, none, bf_x ⟩ ⟨ z, b, c, bf_z ⟩ = ok ntree ∧
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
  simp [core.mem.replace]
  -- Some proofs common to both cases
  -- Elements in the left subtree are < z
  have : ∀ (y : T), (y = x ∨ y ∈ Subtree.v a) ∨ y ∈ Subtree.v b → y < z := by
    simp [inv_aux] at hInvZ
    intro y hIn
    -- TODO: automate that
    cases hIn
    . rename _ => hIn
      cases hIn
      . simp [*]
      . -- Proving: y ∈ a → y < z
        -- Using: y < x ∧ x < z
        rename _ => hIn
        have hInv1 : y < x := by tauto
        have hInv2 := hInv.right.right z
        simp at hInv2
        apply lt_trans hInv1 hInv2
    . tauto
  -- Elements in the right subtree are < z
  have : ∀ y ∈ Subtree.v c, z < y := by
    simp [inv_aux] at hInvZ
    tauto
  -- Two cases depending on whether the BF of Z is 0 or 1
  split
  . -- BF(Z) == 0
    simp at *
    simp [and_assoc, *]
    have hHeightEq : Subtree.height b = Subtree.height c := by
      simp_all [balanceFactor, Node.inv_aux]
      -- TODO: scalar_tac fails here (conversion int/nat)
      omega
    -- TODO: we shouldn't need this: scalar_tac should succeed
    have : 1 + Subtree.height c = Subtree.height a + 2 := by
      -- TODO: scalar_tac fails here (conversion int/nat)
      simp_all [balanceFactor, Node.inv_aux]
      omega
    simp_all
    split_conjs
    . -- Partial invariant for the final tree starting at z
      simp [Node.inv_aux, balanceFactor, *]
      split_conjs <;> (try omega) <;> tauto
    . -- Partial invariant for the subtree x
      simp [Node.inv_aux, balanceFactor, *]
      split_conjs <;> (try omega) <;> simp_all
    . -- The sets are the same
      apply Set.ext; simp; tauto
    . -- The height didn't change
      simp [balanceFactor] at *
      replace hInv := hInv.left
      simp_all
      scalar_tac
  . -- BF(Z) == 1
    rename _ => hNotEq
    simp at *
    simp [and_assoc, *]
    simp_all
    have : bf_z.val = 1 := by
      simp [Node.inv_aux] at hInvZ
      omega
    clear hNotEq hBfZ
    have : Subtree.height c = 1 + Subtree.height b := by
      simp [balanceFactor, Node.inv_aux] at *
      replace hInvZ := hInvZ.left.left.left
      omega
    have : max (Subtree.height c) (Subtree.height b) = Subtree.height c := by
      scalar_tac
    -- TODO: we shouldn't need this: scalar_tac should succeed
    have : Subtree.height c = 1 + Subtree.height a := by
      -- TODO: scalar_tac fails here (conversion int/nat)
      simp_all [balanceFactor, Node.inv_aux]
      omega
    have : Subtree.height a = Subtree.height b := by
      simp_all
    split_conjs
    . -- Invariant for whole tree (starting at z)
      simp [inv_aux, balanceFactor]
      split_conjs <;> (try omega) <;> tauto
    . -- Invariant for subtree x
      simp [inv_aux, balanceFactor]
      split_conjs <;> (try omega) <;> simp_all
    . -- The sets are the same
      apply Set.ext; simp; tauto
    . -- The height didn't change
      simp [balanceFactor] at *
      replace hInv := hInv.left
      simp_all
      scalar_tac

theorem Node.rotate_right_spec
  {T : Type} [LinearOrder T]
  (x : T) (a : Option (Node T)) (bf_x : I8) (z : T) (b c : Option (Node T))
  -- Invariants for the subtrees
  (hInvC : Subtree.inv c)
  --(hInvB : Subtree.inv b)
  --(hInvC : Subtree.inv c)
  (hInvZ : Node.inv ⟨ z, a, b, bf_z ⟩)
  -- Invariant for the complete tree (but without the bounds on the balancing operation)
  (hInv : Node.invNoBalance ⟨ x, some ⟨ z, a, b, bf_z ⟩, c, bf_x ⟩)
  -- The tree is not balanced
  (hBfX : bf_x.val = -2)
  -- Z has a positive balance factor
  (hBfZ : bf_z.val ≤ 0)
  :
  ∃ ntree, rotate_right T ⟨ x, none, c, bf_x ⟩ ⟨ z, a, b, bf_z ⟩ = ok ntree ∧
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
  simp [core.mem.replace]
  -- Some proofs common to both cases
  -- Elements in the right subtree are > z
  have : ∀ (y : T), (y = x ∨ y ∈ Subtree.v b) ∨ y ∈ Subtree.v c → z < y := by
    simp [inv_aux] at *
    intro y hIn
    -- TODO: automate that
    cases hIn
    . rename _ => hIn
      cases hIn
      . simp [*]
      . tauto
    . -- Proving: y ∈ c → z < y
      -- Using: z < x ∧ x < y
      have : z < x := by tauto
      have : x < y := by tauto
      apply lt_trans <;> tauto
  -- Elements in the left subtree are < z
  have : ∀ y ∈ Subtree.v a, y < z := by
    simp_all [inv_aux]
  -- Two cases depending on whether the BF of Z is 0 or 1
  split
  . -- BF(Z) == 0
    simp at *
    simp [and_assoc, *]
    have hHeightEq : Subtree.height a = Subtree.height b := by
      simp_all [balanceFactor, Node.inv_aux]
      -- TODO: scalar_tac fails here (conversion int/nat)
      omega
    -- TODO: we shouldn't need this: scalar_tac should succeed
    have : 1 + Subtree.height a = Subtree.height c + 2 := by
      -- TODO: scalar_tac fails here (conversion int/nat)
      simp_all [balanceFactor, Node.inv_aux]
      omega
    simp_all
    split_conjs
    . -- Partial invariant for the final tree starting at z
      simp [Node.inv_aux, balanceFactor, *]
      split_conjs <;> (try omega) <;> tauto
    . -- Partial invariant for the subtree x
      simp [Node.inv_aux, balanceFactor, *]
      split_conjs <;> (try omega) <;> simp_all
    . -- The sets are the same
      apply Set.ext; simp; tauto
    . -- The height didn't change
      simp [balanceFactor] at *
      replace hInv := hInv.left
      simp_all
      scalar_tac
  . -- BF(Z) == -1
    rename _ => hNotEq
    simp at *
    simp [and_assoc, *]
    simp_all
    have : bf_z.val = -1 := by
      simp [Node.inv_aux] at hInvZ
      omega
    clear hNotEq hBfZ
    have : Subtree.height a = 1 + Subtree.height b := by
      simp [balanceFactor, Node.inv_aux] at *
      replace hInvZ := hInvZ.left.left.left
      omega
    have : max (Subtree.height a) (Subtree.height b) = Subtree.height a := by
      scalar_tac
    -- TODO: we shouldn't need this: scalar_tac should succeed
    have : Subtree.height a = 1 + Subtree.height c := by
      -- TODO: scalar_tac fails here (conversion int/nat)
      simp_all [balanceFactor, Node.inv_aux]
      omega
    have : Subtree.height c = Subtree.height b := by
      simp_all
    split_conjs
    . -- Invariant for whole tree (starting at z)
      simp [inv_aux, balanceFactor]
      split_conjs <;> (try omega) <;> tauto
    . -- Invariant for subtree x
      simp [inv_aux, balanceFactor]
      split_conjs <;> (try omega) <;> simp_all
    . -- The sets are the same
      apply Set.ext; simp; tauto
    . -- The height didn't change
      simp [balanceFactor] at *
      replace hInv := hInv.left
      simp_all
      scalar_tac

end avl
