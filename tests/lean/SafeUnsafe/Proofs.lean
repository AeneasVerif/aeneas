import SafeUnsafe.SafeUnsafe

/-! # Adequacy of the raw-pointer model

The functions of `tests/src/safe_unsafe.rs`, extracted to `SafeUnsafe.SafeUnsafe`, against what Miri
reports on them (Stacked Borrows and Tree Borrows agree on all of them). Every function is closed,
so its triple is about one execution, from the empty heap. Each Rust function falls in one case:

- `ok(n)` in Rust, and the model returns `n`: `⦃ emp ⦄ f ⦃ r => ⌜r = n⌝ ⦄`.
- UB in Rust, and the model fails: `¬ ⦃ emp ⦄ f ⦃ _ => ⌜True⌝ ⦄` (no execution of the model from
  the empty heap is safe).
- INCOMPLETE: `ok(n)` in Rust, but the model fails. Sound, but the model rejects a valid program.
- UNSOUND: UB in Rust, or a result the model cannot produce, while the model runs safely.

| Function                               | Rust (Miri) | Model      |
|----------------------------------------|-------------|------------|
| `from_mut_write_then_read`             | ok(5)       | ok(5)      |
| `from_mut_write_after_owner_write`     | UB          | fails      |
| `from_mut_read_after_owner_read`       | ok(10)      | INCOMPLETE |
| `from_mut_twice`                       | UB          | fails      |
| `from_mut_dangling`                    | UB          | fails      |
| `from_mut_escape`                      | ok(7)       | INCOMPLETE |
| `from_mut_write_in_callee`             | ok(8)       | ok(8)      |
| `as_mut_ptr_write`                     | ok(7)       | ok(7)      |
| `as_mut_ptr_one_past_end`              | ok(0)       | ok(0)      |
| `as_mut_ptr_write_one_past_end`        | UB          | fails      |
| `as_mut_ptr_add_out_of_bounds`         | UB          | fails      |
| `as_ptr_read_after_owner_write`        | UB          | fails      |
| `as_ptr_read_while_shared`             | ok(3)       | ok(3)      |
| `as_mut_ptr_twice`                     | UB          | fails      |
| `box_roundtrip`                        | ok(4)       | ok(4)      |
| `box_double_free`                      | UB          | fails      |
| `box_use_after_free`                   | UB          | fails      |
| `box_free_local`                       | UB          | fails      |
| `box_free_array_element`               | UB          | fails      |
| `box_leak`                             | ok(3)       | ok(3)      |
| `from_raw_parts_mut_write`             | ok(9)       | INCOMPLETE |
| `from_raw_parts_too_long`              | UB          | fails      |
| `from_raw_parts_write_while_shared`    | UB          | fails      |
| `from_raw_parts_read_while_shared`     | ok(2)       | INCOMPLETE |
| `from_raw_parts_mut_over_array`        | ok(5)       | INCOMPLETE |
| `ptr_read_box_double_free`             | UB          | UNSOUND    |
| `ptr_read_copy`                        | ok(2)       | ok(2)      |
| `ptr_as_mut_write` (borrow model)      | ok(6)       | INCOMPLETE |
| `ptr_as_mut_twice` (borrow model)      | UB          | fails      |
| `non_null_write`                       | ok(v)       | UNSOUND    |

The INCOMPLETE cases share one cause: the model ends the borrow behind a raw pointer when the
functional translation ends it (when the owner is used again, or at the end of the function that
created the pointer), while Rust keeps the pointer valid until a conflicting access. Ending a borrow
frees the view, or requires its cells back, so later accesses through the pointer fail.

The UNSOUND cases:
- `ptr_read_box_double_free`: `Box<T>` is `T` in the model and dropping is a no-op, so `ptr::read`
  duplicating the ownership of a `Box` (UB: double free, or aliasing violation) goes unnoticed.
  The same holds for every type which owns memory (`Vec`, `String`, ...).
- `non_null_write`: `NonNull::from(&mut x)` is an unknown function: Aeneas extracts it as an axiom
  whose backward function is not stateful, and so gives `x` back before the write through the
  pointer. Whatever the model of the axioms, the result does not depend on the written value.
-/

open Aeneas Aeneas.Std Aeneas.SepLogic Aeneas.Std.WP Aeneas.Data.Coinductive
open safe_unsafe

set_option linter.unusedSimpArgs false

namespace safe_unsafe.Proofs

unseal Result

/-! ## Executing a closed program -/

/-- A closed program is run from the empty heap. -/
theorem dwp_empty {m : Result α} {Q : α → IProp} (hTriple : ispec emp m Q) :
    DWP effectWP m (fun value h => (Q ∗+ emp) value h) ∅ :=
  (ispec_iff.mp hTriple) emp ∅ ((entails_of_eq (sep_emp_r_eq emp).symm) ∅ trivial)

set_option hygiene false in
/-- Unfolds the models of the primitives in `hSpec` down to a chain of heap effects, and computes
its pure parts (arrays, slices, lengths). -/
macro "unfold_heap" : tactic => `(tactic|
  simp (disch := scalar_tac) only [core.ptr.from_mut, core.ptr.end_from_mut, RawPtr.allocView,
    RawPtr.endView, RawPtr.read, MutRawPtr.write, RawPtr.add, RawPtr.borrow, RawPtr.endBorrow,
    RawPtr.borrowRange, RawPtr.endBorrowRange, RawPtr.readRange, RawPtr.borrowSlice, Slice.as_ptr,
    Slice.end_as_ptr, Slice.as_mut_ptr, Slice.end_as_mut_ptr, core.slice.raw.from_raw_parts,
    core.slice.raw.from_raw_parts_mut, core.slice.raw.from_raw_parts_mut.back,
    alloc.boxed.Box.into_raw, alloc.boxed.Box.from_raw, alloc.alloc.Global.allocate,
    alloc.alloc.Global.deallocate, Result.guardedModify, Result.require,
    lift, Array.to_slice_mut, Array.index_usize, Array.index_mut_usize, Slice.update,
    Slice.index_usize, Array.getElem?_Usize_eq, Slice.getElem?_Usize_eq, Array.make_val,
    Array.repeat_val, Array.val_to_slice, Slice.from_val, Slice.length, UScalar.ofNatCore_val_eq,
    List.reduceReplicate, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, getElem?_pos,
    List.getElem_cons_zero, List.getElem_cons_succ, List.set_cons_succ, List.set_cons_zero,
    dite_eq_left, Std.uncurry_apply_pair, Std.pure_tc_eq, Std.bind_tc_eq, Std.bind_tc_vis,
    Std.bind_tc_ok, Std.bind_vis, Std.bind_ok] at hSpec)

set_option hygiene false in
/-- Runs the next heap effect of `hSpec`, naming its precondition `x`. -/
macro "heap_step" x:(ppSpace colGt ident)? : tactic => do
  let x ← match x with
    | some x => pure x
    | none => pure (Lean.mkIdent `_hPre)
  `(tactic|
    (obtain ⟨$x, hSpec⟩ := DWP.vis_view hSpec
     try unfold_heap))

/-- Inversion of `DWP.bind`: the first computation reaches a state from which the rest is totally
correct. -/
theorem DWP.bind_inv {E : Effect} {θ : EffectWP E} [θ.Monotonic] {α β : Type _} {m : ITree E α}
    {k : α → ITree E β} {Q : θ.Post β} {s : θ.State}
    (hSpec : DWP θ (ITree.bind m k) Q s) : DWP θ m (fun a s' => DWP θ (k a) Q s') s := by
  have hInv := hSpec.induction
    (P := fun t s => DWP θ t Q s ∧
      ∀ m', t = ITree.bind m' k → DWP θ m' (fun a s' => DWP θ (k a) Q s') s)
    (fun value s hQ => ⟨DWP.ret_iff.mpr hQ, fun m' hEq => by
      cases m' using ITree.cases with
      | ret a =>
        rw [ITree.pure_eq_ret, itree_ret_bind] at hEq
        rw [ITree.pure_eq_ret, DWP.ret_iff, ← hEq, DWP.ret_iff]
        exact hQ
      | div => simp at hEq
      | vis e k' => simp at hEq⟩)
    (fun effect k' s hWp => ⟨DWP.vis (θ.wp_monotonic (fun _ _ h => h.1) hWp), fun m' hEq => by
      cases m' using ITree.cases with
      | ret a =>
        rw [ITree.pure_eq_ret, itree_ret_bind] at hEq
        rw [ITree.pure_eq_ret, DWP.ret_iff, ← hEq]
        exact DWP.vis (θ.wp_monotonic (fun _ _ h => h.1) hWp)
      | div => rw [itree_div_bind] at hEq; exact absurd hEq.symm not_div_vis
      | vis e k₂ =>
        rw [itree_vis_bind] at hEq
        obtain ⟨rfl, hK⟩ := vis_inj hEq
        have hK := eq_of_heq hK
        exact DWP.vis (θ.wp_monotonic (fun answer _ h => h.2 (k₂ answer) (by rw [hK])) hWp)⟩)
  exact hInv.2 m rfl

/-! ## `ptr::from_mut` -/

theorem from_mut_write_then_read.spec :
    ⦃ emp ⦄ from_mut_write_then_read ⦃ r => ⌜r = 5#u32⌝ ⦄ := by
  unfold from_mut_write_then_read
  step*
  subst_vars
  step*

theorem from_mut_write_after_owner_write.ub :
    ¬ ⦃ emp ⦄ from_mut_write_after_owner_write ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold from_mut_write_after_owner_write at hSpec
  unfold_heap
  heap_step
  heap_step
  heap_step hFree
  heap_step hValid
  exact Heap.not_isLive_freeBlock hFree rfl (Heap.isLive_of_isValid hValid)

/-- INCOMPLETE: reading `x` ends the borrow of `x`, which frees the view. -/
theorem from_mut_read_after_owner_read.incomplete :
    ¬ ⦃ emp ⦄ from_mut_read_after_owner_read ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold from_mut_read_after_owner_read at hSpec
  unfold_heap
  heap_step
  heap_step
  heap_step
  heap_step hFree
  heap_step hValid
  exact Heap.not_isLive_freeBlock hFree rfl (Heap.isLive_of_isValid hValid)

theorem from_mut_twice.ub : ¬ ⦃ emp ⦄ from_mut_twice ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold from_mut_twice at hSpec
  unfold_heap
  heap_step
  heap_step
  heap_step hFree
  heap_step
  heap_step hValidQ
  heap_step hValidP
  have hLive := Heap.isLive_of_isValid hValidP
  rw [Heap.isLive_write_iff,
    Heap.isLive_allocBlock_of_mem (Heap.mem_freeBlock hFree)] at hLive
  exact Heap.not_isLive_freeBlock hFree rfl hLive

theorem from_mut_dangling.ub : ¬ ⦃ emp ⦄ from_mut_dangling ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold from_mut_dangling ptr_to_local at hSpec
  unfold_heap
  heap_step
  heap_step
  heap_step hFree
  heap_step hValid
  exact Heap.not_isLive_freeBlock hFree rfl (Heap.isLive_of_isValid hValid)

/-- INCOMPLETE: `escape` ends the borrow of its argument when it returns, which frees the view. -/
theorem from_mut_escape.incomplete : ¬ ⦃ emp ⦄ from_mut_escape ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold from_mut_escape escape at hSpec
  unfold_heap
  heap_step
  heap_step
  heap_step hFree
  heap_step hValid
  exact Heap.not_isLive_freeBlock hFree rfl (Heap.isLive_of_isValid hValid)

@[step]
theorem write_through.spec (p : MutRawPtr U32) (old v : U32) :
    ⦃ p ↦ old ⦄ write_through p v ⦃ p ↦ v ⦄ := by
  unfold write_through
  step*

theorem from_mut_write_in_callee.spec :
    ⦃ emp ⦄ from_mut_write_in_callee ⦃ r => ⌜r = 8#u32⌝ ⦄ := by
  unfold from_mut_write_in_callee
  step*
  subst_vars
  step*

/-! ## `as_ptr`/`as_mut_ptr` -/

theorem read_head.spec (q : RawPtr T M) (values : List T) (h : 0 < values.length) :
    ⦃ q ↦* values ⦄ q.read ⦃ r => ⌜r = values[0]⌝ ∗ q ↦* values ⦄ := by
  simpa using RawPtr.read.spec_range q values 0 h

theorem as_mut_ptr_write.spec : ⦃ emp ⦄ as_mut_ptr_write ⦃ r => ⌜r = 7#u32⌝ ⦄ := by
  unfold as_mut_ptr_write
  step* 3
  subst_vars
  have hLen : s.val.length = 4 := by simp_all
  step with MutRawPtr.write.spec_range p s.val 3 7#u32 (by simp [hLen])
  step with Slice.end_as_mut_ptr.spec s p (s.val.set 3 7#u32) (by simp)
  step*
  simp_all [Array.from_slice]

theorem as_mut_ptr_one_past_end.spec :
    ⦃ emp ⦄ as_mut_ptr_one_past_end ⦃ r => ⌜r = 0#u32⌝ ⦄ := by
  unfold as_mut_ptr_one_past_end
  step* 3
  subst_vars
  step with Slice.end_as_mut_ptr.spec s p s.val rfl
  step*
  simp_all [Array.from_slice]

theorem as_mut_ptr_write_one_past_end.ub :
    ¬ ⦃ emp ⦄ as_mut_ptr_write_one_past_end ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold as_mut_ptr_write_one_past_end at hSpec
  unfold_heap
  heap_step
  heap_step
  heap_step hValid
  refine Heap.not_isLive_allocBlock_of_le (h := ∅) (i := 4) ?_
    (by convert Heap.isLive_of_isValid hValid using 2 <;> simp [Heap.allocBlock_eq])
  simp

theorem as_mut_ptr_add_out_of_bounds.ub :
    ¬ ⦃ emp ⦄ as_mut_ptr_add_out_of_bounds ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold as_mut_ptr_add_out_of_bounds at hSpec
  unfold_heap
  heap_step
  heap_step hInBounds
  refine Heap.not_isLive_allocBlock_of_le (h := ∅) (i := 4) ?_
    (by convert hInBounds 4 (by simp) using 2 <;> simp [Heap.allocBlock_eq])
  simp

theorem as_ptr_read_after_owner_write.ub :
    ¬ ⦃ emp ⦄ as_ptr_read_after_owner_write ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold as_ptr_read_after_owner_write at hSpec
  unfold_heap
  heap_step
  heap_step
  heap_step
  heap_step hFree
  heap_step
  heap_step hValid
  exact Heap.not_isLive_freeBlock hFree rfl (Heap.isLive_of_isValid hValid)

theorem as_ptr_read_while_shared.spec :
    ⦃ emp ⦄ as_ptr_read_while_shared ⦃ r => ⌜r = 3#u32⌝ ⦄ := by
  unfold as_ptr_read_while_shared
  step* 3
  subst_vars
  step with read_head.spec
  simp only [Array.val_to_slice, Array.make_val, List.getElem_cons_zero] at p1_post
  subst p1_post
  step*
  all_goals simp_all [Array.val_to_slice]
  all_goals scalar_tac

theorem as_mut_ptr_twice.ub : ¬ ⦃ emp ⦄ as_mut_ptr_twice ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold as_mut_ptr_twice at hSpec
  unfold_heap
  heap_step
  heap_step
  heap_step
  heap_step hFree
  heap_step
  heap_step
  heap_step hValid
  exact Heap.not_isLive_freeBlock hFree rfl
    ((Heap.isLive_allocBlock_of_mem (Heap.mem_freeBlock hFree)).mp
      ((Heap.isLive_write_iff _).mp (Heap.isLive_of_isValid hValid)))

/-! ## `Box::into_raw`/`Box::from_raw` -/

theorem box_roundtrip.spec : ⦃ emp ⦄ box_roundtrip ⦃ r => ⌜r = 4#u32⌝ ⦄ := by
  unfold box_roundtrip
  step*

theorem box_double_free.ub : ¬ ⦃ emp ⦄ box_double_free ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold box_double_free at hSpec
  unfold_heap
  heap_step
  heap_step
  heap_step hFree
  heap_step hValid
  exact Heap.not_isLive_freeBlock hFree rfl (Heap.isLive_of_isValid hValid)

theorem box_use_after_free.ub : ¬ ⦃ emp ⦄ box_use_after_free ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold box_use_after_free at hSpec
  unfold_heap
  heap_step
  heap_step
  heap_step hFree
  heap_step hValid
  exact Heap.not_isLive_freeBlock hFree rfl (Heap.isLive_of_isValid hValid)

/-- `from_raw` frees with the global allocator, which did not allocate the view of a local. -/
theorem box_free_local.ub : ¬ ⦃ emp ⦄ box_free_local ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold box_free_local at hSpec
  unfold_heap
  heap_step
  heap_step
  heap_step hFree
  simp only [Heap.read_snd] at hFree
  simpa using ((Heap.canDealloc_allocBlock_iff _ _ _ _ _).mp hFree).1

theorem box_free_array_element.ub : ¬ ⦃ emp ⦄ box_free_array_element ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold box_free_array_element at hSpec
  unfold_heap
  heap_step
  heap_step
  heap_step hFree
  simp only [Heap.read_snd] at hFree
  simpa using ((Heap.canDealloc_allocBlock_iff _ _ _ _ _).mp hFree).1

/-- Leaking is not undefined behaviour: the postcondition drops the allocation. -/
theorem box_leak.spec : ⦃ emp ⦄ box_leak ⦃ r => ⌜r = 3#u32⌝ ⦄ := by
  unfold box_leak
  step*

/-! ## `slice::from_raw_parts(_mut)` -/

/-- INCOMPLETE: the borrow of the slice ends at the end of the function, after `from_raw`, which
fails on the borrowed cell. Were the cell not borrowed, `from_raw` would read `1`, not `9`. -/
theorem from_raw_parts_mut_write.incomplete :
    ¬ ⦃ emp ⦄ from_raw_parts_mut_write ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold from_raw_parts_mut_write at hSpec
  unfold_heap
  heap_step
  heap_step hValid₀
  heap_step hValid
  exact Heap.not_isLive_borrow hValid₀ (Heap.isLive_of_isValid hValid)

theorem from_raw_parts_too_long.ub : ¬ ⦃ emp ⦄ from_raw_parts_too_long ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold from_raw_parts_too_long at hSpec
  unfold_heap
  heap_step
  heap_step hValid₀
  heap_step hValid₁
  have hLive := Heap.isLive_of_isLive_borrow hValid₀ (Heap.isLive_of_isValid hValid₁)
  refine Heap.not_isLive_allocBlock_of_le (h := ∅) (i := 1) ?_
    (by convert hLive using 2 <;> simp [Heap.allocBlock_eq, RawPtr.cast_const])
  simp

theorem from_raw_parts_write_while_shared.ub :
    ¬ ⦃ emp ⦄ from_raw_parts_write_while_shared ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold from_raw_parts_write_while_shared at hSpec
  unfold_heap
  heap_step
  heap_step hValid₀
  heap_step hValid
  exact Heap.not_isLive_borrow hValid₀
    ((Heap.isLive_congr rfl rfl).mp (Heap.isLive_of_isValid hValid))

/-- INCOMPLETE: the cell is borrowed by the slice, so reading it through the pointer fails. -/
theorem from_raw_parts_read_while_shared.incomplete :
    ¬ ⦃ emp ⦄ from_raw_parts_read_while_shared ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold from_raw_parts_read_while_shared at hSpec
  unfold_heap
  heap_step
  heap_step hValid₀
  heap_step hValid
  exact Heap.not_isLive_borrow hValid₀
    ((Heap.isLive_congr rfl rfl).mp (Heap.isLive_of_isValid hValid))

/-- INCOMPLETE: the borrow of the array ends (`as_mut_ptr_back`) before the borrow of the slice
(`from_raw_parts_mut_back`), whose lifetime is not related to it: ending the view reads cells which
are still borrowed by the slice. Were they not borrowed, the write `s[1] = 5` would be lost. -/
theorem from_raw_parts_mut_over_array.incomplete :
    ¬ ⦃ emp ⦄ from_raw_parts_mut_over_array ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold from_raw_parts_mut_over_array at hSpec
  unfold_heap
  heap_step
  heap_step hValid₀
  heap_step hValid₁
  heap_step hValid
  exact Heap.not_isLive_borrow hValid₀
    (Heap.isLive_of_isLive_borrow hValid₁ (Heap.isLive_of_isValid hValid))

/-! ## `ptr::read` -/

theorem ptr_read_copy.spec : ⦃ emp ⦄ ptr_read_copy ⦃ r => ⌜r = 2#u32⌝ ⦄ := by
  unfold ptr_read_copy
  step*
  subst_vars
  step*

/-- UNSOUND: Rust drops the `Box` twice, which is UB; the model returns `2`. -/
theorem ptr_read_box_double_free.unsound :
    ⦃ emp ⦄ ptr_read_box_double_free ⦃ r => ⌜r = 2#u32⌝ ⦄ := by
  unfold ptr_read_box_double_free
  step*
  subst_vars
  step*

/-! ## `<*mut T>::as_mut`

Aeneas has no model of `as_mut`: it extracts it as an axiom, with a stateful backward function
(which gives back the final value of the borrow). The proofs below assume the model of
`from_raw_parts_mut`: the cell moves into the borrow until the backward function gives it back. -/

def asMutBorrow (p : MutRawPtr U32) : Result (Option U32 × (Option U32 → Result Unit)) :=
  Std.bind (RawPtr.borrow p) fun value =>
    .ok (some value, fun final => match final with
      | some value => RawPtr.endBorrow p value
      | none => .fail .undef)

/-- INCOMPLETE: the lifetime of the `&mut` returned by `as_mut` is not related to the borrow of `x`
(the raw pointer erases it), so the extracted code ends the borrow of `x` (`from_mut_back`) first,
and gives the `&mut` back (`as_mut_back`) at the end of the function. Reading `x` then fails on the
borrowed cell. Were it not borrowed, the read would return `1`, not `6`. -/
theorem ptr_as_mut_write.incomplete
    (hModel : ∀ p, core.ptr.mut_ptr.RawPtrMutT.as_mut p = asMutBorrow p) :
    ¬ ⦃ emp ⦄ ptr_as_mut_write ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold ptr_as_mut_write at hSpec
  simp only [hModel, asMutBorrow] at hSpec
  unfold_heap
  heap_step
  heap_step hValid₀
  heap_step hValid
  exact Heap.not_isLive_borrow hValid₀ (Heap.isLive_of_isValid hValid)

theorem ptr_as_mut_twice.ub
    (hModel : ∀ p, core.ptr.mut_ptr.RawPtrMutT.as_mut p = asMutBorrow p) :
    ¬ ⦃ emp ⦄ ptr_as_mut_twice ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold ptr_as_mut_twice at hSpec
  simp only [hModel, asMutBorrow] at hSpec
  unfold_heap
  heap_step
  heap_step hValid₀
  heap_step hValid
  exact Heap.not_isLive_borrow hValid₀ (Heap.isLive_of_isValid hValid)

/-! ## `NonNull::from(&mut x)` -/

/-- The last steps of `non_null_write`: `x` was given back before the write. -/
theorem write_then_ok {p : MutRawPtr U32} {v x : U32} {Q : U32 → IProp} {h : Heap}
    (hSpec : DWP effectWP (Std.bind (MutRawPtr.write p v) fun _ => Result.ok x)
      (fun value h => (Q ∗+ emp) value h) h) : ∃ h', (Q x ∗ emp) h' := by
  simp only [MutRawPtr.write, Result.guardedModify, Std.bind_vis, Std.bind_ok] at hSpec
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  exact ⟨_, DWP.ret_iff.mp hSpec⟩

/-- UNSOUND: Rust returns the written value, while the extracted code returns `x` as given back by
the axiom `NonNull::from` before the write. Whatever the models of the axioms, the result does not
depend on the written value. -/
theorem non_null_write.unsound :
    ¬ (⦃ emp ⦄ non_null_write 2#u32 ⦃ r => ⌜r = 2#u32⌝ ⦄ ∧
      ⦃ emp ⦄ non_null_write 3#u32 ⦃ r => ⌜r = 3#u32⌝ ⦄) := by
  rintro ⟨h₂, h₃⟩
  have d₂ := dwp_empty h₂
  have d₃ := dwp_empty h₃
  unfold non_null_write at d₂ d₃
  obtain ⟨⟨p, x⟩, _, d₂, d₃⟩ :=
    DWP.exists (DWP.and_iff.mpr ⟨DWP.bind_inv d₂, DWP.bind_inv d₃⟩)
  simp only [Std.uncurry_apply_pair] at d₂ d₃
  obtain ⟨p₁, _, d₂, d₃⟩ :=
    DWP.exists (DWP.and_iff.mpr ⟨DWP.bind_inv d₂, DWP.bind_inv d₃⟩)
  obtain ⟨_, hx₂⟩ := write_then_ok d₂
  obtain ⟨_, hx₃⟩ := write_then_ok d₃
  have h₂ := ((sep_pure_l _ _ _).mp hx₂).1
  have h₃ := ((sep_pure_l _ _ _).mp hx₃).1
  simp [h₂] at h₃

end safe_unsafe.Proofs
