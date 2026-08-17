import Aeneas.SLPoC.Step

/-!
# Dardinier's magic-wand automation examples

This module ports the examples used in Dardinier et al., *Sound Automation of
Magic Wands* (CAV 2022), and in Chapter 4 of Dardinier's thesis, *Formal
Foundations for Automated Deductive Verifiers* (2025).

The main example is `leftLeaf`, the paper's running binary-tree traversal. Its
loop invariant separates ownership of the current subtree from a magic wand
that restores ownership of the original tree. Here the loop is represented by
fuel-recursion, and the pure model is restricted to full binary trees, but the
resource invariant and the `package`/`apply` proof steps are the same.

The final section ports the paper's unsound-footprint example. It shows why
packaging under two alternatives must select one footprint that works for both:
the uniform footprint owns both possible target cells, while each smaller
footprint is valid only after fixing one branch.

The paper's fractional and combinable-wand examples are intentionally omitted.
SLPoC has exclusive points-to ownership and no fractional resource model, so
their statements would not be faithful in this logic.

Sources:

- Thesis §§4.2-4.5, PDF pp. 108-125 (printed pp. 86-103).
- CAV 2022 extended version, Fig. 1 and Appendices B, I, and J.
- Artifact: <https://doi.org/10.5281/zenodo.6525310>.
-/

namespace Aeneas.SLPoC

open scoped SepLogic

namespace DardinierMagicWands

/-! ## The leftmost-leaf traversal -/

structure Node where
  value : Nat
  left : Option (Ptr Node)
  right : Option (Ptr Node)

/-- A ghost model that records the concrete pointer of every node. The paper's
predicate existentially hides this information; making it explicit keeps this
example focused on wand packaging rather than existential reconstruction. -/
inductive Tree where
  | leaf (pointer : Ptr Node) (value : Nat)
  | branch (pointer : Ptr Node) (value : Nat) (left right : Tree)

namespace Tree

def root : Tree → Ptr Node
  | .leaf pointer _ => pointer
  | .branch pointer _ _ _ => pointer

def leftmost : Tree → Tree
  | tree@(.leaf _ _) => tree
  | .branch _ _ left _ => left.leftmost

def leftDepth : Tree → Nat
  | .leaf _ _ => 0
  | .branch _ _ left _ => left.leftDepth + 1

/-- Exact ownership of the binary tree. This is the SL counterpart of the
paper's recursive `Tree(x)` predicate. -/
def owns : Tree → SLProp
  | .leaf pointer value =>
      pointer ↦ { value, left := none, right := none }
  | .branch pointer value left right =>
      iprop(
        pointer ↦ {
          value
          left := some left.root
          right := some right.root
        } ∗
        left.owns ∗
        right.owns)

@[simp] theorem root_leftmost (tree : Tree) :
    tree.leftmost.root =
      match tree with
      | .leaf pointer _ => pointer
      | .branch _ _ left _ => left.leftmost.root := by
  cases tree <;> rfl

end Tree

/-- Fuel-recursive form of the paper's `while (y.left != null)` traversal. -/
def leftLeaf : Nat → Ptr Node → St (Ptr Node)
  | 0, pointer => pure pointer
  | fuel + 1, pointer => do
      let node ← read pointer
      match node.left with
      | none => pure pointer
      | some child => leftLeaf fuel child

/-- The resources outside the selected left child package a wand that restores
the parent. This is one iteration's core `package` obligation. -/
theorem Tree.packageLeft (pointer : Ptr Node) (value : Nat)
    (left right : Tree) :
    iprop(
      pointer ↦ {
        value
        left := some left.root
        right := some right.root
      } ∗
      right.owns) ⊢
    left.owns -∗ (Tree.branch pointer value left right).owns := by
  apply hwand_intro
  simp only [Tree.owns]
  sl_frame

/-- Automatic footprint selection for one descent: keep the left subtree and
package the parent cell plus the right subtree into a wand. -/
theorem Tree.selectLeft (pointer : Ptr Node) (value : Nat)
    (left right : Tree) :
    (Tree.branch pointer value left right).owns ⊢
      iprop(left.owns ∗
        (left.owns -∗ (Tree.branch pointer value left right).owns)) := by
  simp only [Tree.owns]
  sl_frame

/-- Applying the packaged wand restores the original tree. -/
theorem Tree.applyLeft (pointer : Ptr Node) (value : Nat)
    (left right : Tree) :
    iprop(left.owns ∗
      (left.owns -∗ (Tree.branch pointer value left right).owns)) ⊢
    (Tree.branch pointer value left right).owns :=
  hwand_cancel _ _

/-- Compose the remainder of two traversal steps. -/
theorem wand_trans {A B C : SLProp} :
    (A -∗ B) ∗ (B -∗ C) ⊢ A -∗ C := by
  apply hwand_intro
  sl_xchange (hwand_cancel A B)
  sl_xchange (hwand_cancel B C)
  sl_frame

/-- Repeated packaging produces exactly the invariant used by `leftLeaf`: the
current leftmost subtree and a wand back to the complete input tree. -/
theorem Tree.packageLeftmost (tree : Tree) :
    tree.owns ⊢
      iprop(tree.leftmost.owns ∗ (tree.leftmost.owns -∗ tree.owns)) := by
  induction tree with
  | leaf pointer value =>
      simp only [Tree.leftmost]
      sl_frame
  | branch pointer value left right leftIH _ =>
      simp only [Tree.leftmost]
      sl_xchange (Tree.selectLeft pointer value left right)
      sl_xchange leftIH
      sl_xchange (wand_trans
        (A := left.leftmost.owns)
        (B := left.owns)
        (C := (Tree.branch pointer value left right).owns))
      sl_frame

/-- Direct functional proof of the executable traversal. It preserves the
complete tree and returns the concrete pointer of its leftmost leaf. -/
@[step]
theorem leftLeaf.preserves_spec (tree : Tree) :
    ⦃ tree.owns ⦄ leftLeaf (tree.leftDepth + 1) tree.root
      ⦃⇓ result => ⌜result = tree.leftmost.root⌝ ∗ tree.owns⦄ := by
  induction tree with
  | leaf pointer value =>
      simp only [Tree.owns, Tree.leftDepth, Tree.root, leftLeaf,
        Tree.leftmost]
      sl_step*
  | branch pointer value left right leftIH _ =>
      simp only [Tree.owns, Tree.leftDepth, Tree.root, Tree.leftmost]
      rw [leftLeaf]
      sl_step
      let frame : SLProp :=
        iprop(
          pointer ↦ {
            value
            left := some left.root
            right := some right.root
          } ∗
          right.owns)
      apply triple_conseq (triple_frame leftIH frame)
      · dsimp only [frame]
        sl_frame
      · intro result
        dsimp only [frame]
        change iprop(
          (⌜result = left.leftmost.root⌝ ∗ left.owns) ∗
          (pointer ↦ {
            value
            left := some left.root
            right := some right.root
          } ∗ right.owns)) ⊢
          iprop(
            ⌜result = left.leftmost.root⌝ ∗
            pointer ↦ {
              value
              left := some left.root
              right := some right.root
            } ∗
            left.owns ∗
            right.owns)
        exact himpl_of_eq (by ac_rfl)

/-- The traversal result stated in the paper's loop-invariant form. The
remaining resources have been packaged into a wand back to the input tree. -/
theorem leftLeaf.cursor_spec (tree : Tree) :
    ⦃ tree.owns ⦄ leftLeaf (tree.leftDepth + 1) tree.root
      ⦃⇓ result =>
        iprop(
          ⌜result = tree.leftmost.root⌝ ∗
          tree.leftmost.owns ∗
          (tree.leftmost.owns -∗ tree.owns))⦄ := by
  apply triple_conseq (leftLeaf.preserves_spec tree)
  · exact himpl_refl _
  · intro result
    sl_xchange tree.packageLeftmost
    sl_frame

/-- The paper's final `apply` operation consumes the current subtree and its
wand, recovering ownership of the original tree. -/
theorem leftLeaf.spec (tree : Tree) :
    ⦃ tree.owns ⦄ leftLeaf (tree.leftDepth + 1) tree.root
      ⦃⇓ result => ⌜result = tree.leftmost.root⌝ ∗ tree.owns⦄ := by
  apply triple_conseq (leftLeaf.cursor_spec tree)
  · exact himpl_refl _
  · intro result
    sl_xchange (hwand_cancel tree.leftmost.owns tree.owns)
    sl_frame

/-! ## Uniform footprints across alternatives

The paper's FIA counterexample packages a wand whose left side says that
`x.f` contains either `y` or `z`, while its right side additionally needs the
cell selected by `x.f`. The unsound algorithm chooses the `y` footprint in one
case and the `z` footprint in the other. A sound package operation must instead
choose a single footprint that covers both cases.
-/

def selected (x : Ptr (Ptr Nat)) (y z : Ptr Nat) : SLProp :=
  hexists fun chooseY : Bool =>
    x ↦ if chooseY then y else z

def selectedCell (x : Ptr (Ptr Nat)) (y z : Ptr Nat)
    (yValue zValue : Nat) : SLProp :=
  hexists fun chooseY : Bool =>
    iprop(
      x ↦ (if chooseY then y else z) ∗
      (if chooseY then y ↦ yValue else z ↦ zValue))

/-- The sound, uniform footprint contains both possible selected cells. The
unused cell is discarded once the branch is known — the logic being affine, that
needs no explicit `GC`. -/
theorem packageSelected (x : Ptr (Ptr Nat)) (y z : Ptr Nat)
    (yValue zValue : Nat) :
    y ↦ yValue ∗ z ↦ zValue ⊢
      selected x y z -∗ selectedCell x y z yValue zValue := by
  apply hwand_intro
  unfold selected selectedCell
  rw [hstar_hexists_l_eq]
  apply himpl_hexists_l
  intro chooseY
  cases chooseY
  · refine himpl_hexists_r false ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    sl_frame
  · refine himpl_hexists_r true ?_
    simp only [↓reduceIte]
    sl_frame

/-- Once the `y` branch is fixed, the smaller `y`-only footprint is valid. -/
theorem packageSelectedY (x : Ptr (Ptr Nat)) (y z : Ptr Nat)
    (yValue zValue : Nat) :
    y ↦ yValue ⊢
      x ↦ y -∗ selectedCell x y z yValue zValue := by
  apply hwand_intro
  unfold selectedCell
  refine himpl_hexists_r true ?_
  simp only [↓reduceIte]
  sl_frame

/-- Once the `z` branch is fixed, the smaller `z`-only footprint is valid.
It cannot be reused for the disjunctive `selected` precondition. -/
theorem packageSelectedZ (x : Ptr (Ptr Nat)) (y z : Ptr Nat)
    (yValue zValue : Nat) :
    z ↦ zValue ⊢
      x ↦ z -∗ selectedCell x y z yValue zValue := by
  apply hwand_intro
  unfold selectedCell
  refine himpl_hexists_r false ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  sl_frame

/-- The corresponding sound `apply` step. -/
theorem applySelected (x : Ptr (Ptr Nat)) (y z : Ptr Nat)
    (yValue zValue : Nat) :
    selected x y z ∗
      (selected x y z -∗ selectedCell x y z yValue zValue) ⊢
    selectedCell x y z yValue zValue :=
  hwand_cancel _ _

end DardinierMagicWands

end Aeneas.SLPoC
