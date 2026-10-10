import Nonnull

open Aeneas Aeneas.Std Aeneas.SepLogic Aeneas.Std.WP Result

namespace nonnull

/-- Freeing a node gives back its value. -/
theorem free_node.spec (n : NonNull Node) (node : Node) :
    ⦃ n.ptr ↦ node ∗ n.ptr.freeable ⦄ free_node n ⦃ r => ⌜r = node.value⌝ ⦄ := by
  unfold free_node
  simp only [NonNull.as_ptr_eq]
  step*

/-- Inserting a node in an empty list links the node to itself, through a mutable borrow of the
node. -/
theorem push_back_empty.spec (node : NonNull Node) (v : Std.U32) (next prev : NonNull Node) :
    ⦃ node.ptr ↦ Node.mk v next prev ⦄ push_back { head := none, len := 0#usize } node
      ⦃ list => ⌜list = { head := some node, len := 1#usize }⌝ ∗
        node.ptr ↦ Node.mk v node node ⦄ := by
  unfold push_back
  simp only [NonNull.as_ptr_eq]
  step*
  obtain ⟨n, back⟩ := x
  simp only at *
  subst_vars
  step*
  simp only [List.mk.injEq, true_and]
  scalar_tac

attribute [local step] RawPtr.eq.spec_self

/-- Removing the only node of a list: the node is borrowed (shared), and compared with the pointer
to its successor, which is itself. -/
theorem remove_singleton.spec (node : NonNull Node) (v : Std.U32) :
    ⦃ node.ptr ↦ Node.mk v node node ⦄ remove { head := some node, len := 1#usize } node
      ⦃ list => ⌜list = { head := none, len := 0#usize }⌝ ∗ node.ptr ↦ Node.mk v node node ⦄ := by
  unfold remove
  simp only [NonNull.Insts.CoreCmpPartialEq.eq]
  step*
  subst_vars
  simp only [Node.next._simpLemma_]
  step*
  subst_vars
  simp only [if_true]
  step*

/-- Two mutable borrows of the same node fail: the first one moved the node out of the heap. -/
theorem aliasing_borrows.fails (p : NonNull Node) (node : Node) :
    ifails (p.ptr ↦ node) (aliasing_borrows p) := by
  unfold aliasing_borrows
  simp only [NonNull.as_ptr_eq]
  refine ifails_bind (RawPtr.as_mut_unchecked.spec p.ptr node) fun ⟨_, _⟩ => ?_
  simp only [Std.uncurry]
  exact ifails_bind_left (ifails_mono (by iframe) (RawPtr.as_mut_unchecked.fails_borrowed p.ptr))

/-- Two boxes of a zero-sized type may have the same address: comparing them fails, although the
Lean model of the type has several values. -/
theorem compare_zero_sized.fails : ifails emp compare_zero_sized := by
  unfold compare_zero_sized
  simp only [core.mem.maybe_uninit.MaybeUninit.uninit, bind_ok]
  refine ifails_bind (alloc.boxed.Box.into_raw.spec _) fun p => ?_
  rw [← sep_emp_l_eq (p ↦ _ ∗ p.freeable)]
  refine ifails_bind (ispec_frame (alloc.boxed.Box.into_raw.spec _) _) fun q => ?_
  exact ifails_mono (by iframe) (RawPtr.eq.fails_zero_sized rfl _ _)

end nonnull
