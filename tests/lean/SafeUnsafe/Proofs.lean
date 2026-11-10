import SafeUnsafe.Heap

/-! # Adequacy of the raw-pointer model

The functions of `tests/src/safe_unsafe.rs`, extracted to `SafeUnsafe.SafeUnsafe`, against what Miri
reports on them (Stacked Borrows and Tree Borrows agree on all of them), in the byte-heap model
(`Aeneas.Std.Heap`, with the separation logic of `Aeneas.SepLogic` and the pointer specifications
of `Aeneas.Std.RawPtrSpecs`). Every function is closed, so its triple is about the executions from
the empty heap. Each Rust function falls in one case:

- `ok(n)` in Rust, and the model returns `n`: `⦃ emp ⦄ f ⦃ r => ⌜r = n⌝ ⦄`.
- UB in Rust, and the model fails: `¬ ⦃ emp ⦄ f ⦃ _ => ⌜True⌝ ⦄`.
- INCOMPLETE: `ok(n)` in Rust, but the model fails (same statement). Sound, but the model rejects a
  valid program.

Running out of memory (`oom`) satisfies every specification, as the allocations of the model choose
an encoding and a placement nondeterministically. A refutation `¬ ⦃ emp ⦄ f ⦃ _ => ⌜True⌝ ⦄` thus
exhibits one run, with explicit placements for the allocations (see `SafeUnsafe.Heap`), which reaches
an undefined operation (a checked operation with no successor).

The functions which expose safe places as raw memory (`from_mut`, `as_ptr`, `as_mut_ptr`) take a
placement: the addresses of their exposures (see `Aeneas.Std.Placement`). Their specifications hold
for every placement; their refutations are for the placement `SafeUnsafe.Heap.distinct`, which puts
the exposures of a function at distinct addresses (`8`, `16`, ...).

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
| `ptr_read_owner_double_free`           | UB          | fails      |
| `ptr_read_copy`                        | ok(2)       | ok(2)      |
| `ptr_as_mut_write` (borrow model)      | ok(6)       | INCOMPLETE |
| `ptr_as_mut_twice` (borrow model)      | UB          | fails      |
| `reborrow_write_while_shared`          | UB          | fails      |
| `reborrow_read_while_shared`           | ok(2)       | INCOMPLETE |
| `reborrow_then_write`                  | ok(2)       | INCOMPLETE |
| `handle_write`                         | ok(4)       | ok(4)      |

The verdicts are the same as in the previous (first-order) heap model; the reason of
`from_raw_parts_read_while_shared` changed (see its docstring). The model has no unsound case.

The model has no representation of a `Box` in raw memory (a `Box<T>` is its contents, without an
allocation), so that a program which reads or writes a `Box` through a raw pointer (such as
`ptr::read` duplicating a `Box`) is not expressible. `ptr_read_owner_double_free` duplicates the
owner of an allocation made by `Box::into_raw` instead.

A shared reference made from a raw pointer (`&*p`) shares the cell until its lifetime ends, so that
writing the cell while the reference is live fails (`reborrow_write_while_shared`).

The INCOMPLETE cases share one cause: the model ends the borrow behind a raw pointer when the
functional translation ends it (when the owner is used again, or at the end of the function that
created the pointer, or in the order of the backward functions), while Rust keeps the pointer valid
until a conflicting access. Ending the borrow of a safe place retires its exposure (later accesses
through the pointer fail), and requires its cells back (it fails while they are still borrowed or
shared by a slice built from the pointer).
-/

open Aeneas Aeneas.Std Aeneas.SepLogic Aeneas.Std.WP Aeneas.Data.Coinductive
open safe_unsafe safe_unsafe.Heap

set_option linter.unusedSimpArgs false

namespace safe_unsafe.Proofs

unseal Result

/-! ## `ptr::from_mut` -/

theorem from_mut_write_then_read.spec (placement : Placement) :
    ⦃ emp ⦄ from_mut_write_then_read placement ⦃ r => ⌜r = 5#u32⌝ ⦄ := by
  unfold from_mut_write_then_read
  step*
  subst_vars
  step*

theorem from_mut_write_after_owner_write.ub :
    ¬ ⦃ emp ⦄ from_mut_write_after_owner_write distinct ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold from_mut_write_after_owner_write at hSpec
  heap_norm
  set b : Usize := distinct [0]
  have hb : b.val = 8 := distinct_val [0] (by decide)
  have hSpec := hSpec.heap_exposeAt (by omega) rfl (by heap_check [hb])
  heap_norm
  heap_checked
  obtain rfl := read_eq hx
  heap_checked
  obtain rfl := removeExposure_eq hx
  refine hSpec.heap_stuck (fun h => by simp [Result.fail] at h; exact h.heap_fail) ?_
  rintro ⟨_, _, _, _, hw⟩
  simp [Heap.write, Heap.modify, Heap.retire, add, update, Heap.live, Heap.empty] at hw

theorem from_mut_read_after_owner_read.incomplete :
    ¬ ⦃ emp ⦄ from_mut_read_after_owner_read distinct ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold from_mut_read_after_owner_read at hSpec
  heap_norm
  set b : Usize := distinct [0]
  have hb : b.val = 8 := distinct_val [0] (by decide)
  have hSpec := hSpec.heap_exposeAt (by omega) rfl (by heap_check [hb])
  heap_norm
  heap_checked
  obtain ⟨bytes, rfl⟩ := write_eq hx
  heap_checked
  obtain rfl := read_eq hx
  heap_checked
  obtain rfl := removeExposure_eq hx
  heap_stuck
  obtain ⟨hr, -⟩ := hx
  simp [Heap.read, Heap.retire, Heap.storeRepr, add, update, Heap.live, Heap.empty] at hr

theorem from_mut_twice.ub : ¬ ⦃ emp ⦄ from_mut_twice distinct ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold from_mut_twice at hSpec
  heap_norm
  set b : Usize := distinct [0]
  have hb : b.val = 8 := distinct_val [0] (by decide)
  have hSpec := hSpec.heap_exposeAt (by omega) rfl (by heap_check [hb])
  heap_norm
  heap_checked
  obtain rfl := read_eq hx
  heap_checked
  obtain rfl := removeExposure_eq hx
  set c : Usize := distinct [1]
  have hc : c.val = 16 := distinct_val [1] (by decide)
  have hSpec := hSpec.heap_exposeAt (by omega) (by simp [add, update, Heap.retire, Heap.empty])
    (by heap_check [hb, hc, Heap.retire])
  heap_norm
  heap_checked
  obtain ⟨bytes, rfl⟩ := write_eq hx
  heap_stuck
  obtain ⟨_, hw⟩ := hx
  simp [Heap.write, Heap.modify, Heap.retire, Heap.storeRepr, add, update, Heap.live,
    Heap.empty] at hw

theorem from_mut_dangling.ub : ¬ ⦃ emp ⦄ from_mut_dangling distinct ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold from_mut_dangling ptr_to_local at hSpec
  heap_norm
  set b : Usize := distinct [0, 0]
  have hb : b.val = 8 := distinct_val [0, 0] (by decide)
  have hSpec := hSpec.heap_exposeAt (by omega) rfl (by heap_check [hb])
  heap_norm
  heap_checked
  obtain rfl := read_eq hx
  heap_checked
  obtain rfl := removeExposure_eq hx
  heap_stuck
  obtain ⟨hr, -⟩ := hx
  simp [Heap.read, Heap.retire, add, update, Heap.live, Heap.empty] at hr

theorem from_mut_escape.incomplete : ¬ ⦃ emp ⦄ from_mut_escape distinct ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold from_mut_escape escape at hSpec
  heap_norm
  set b : Usize := distinct [0, 0]
  have hb : b.val = 8 := distinct_val [0, 0] (by decide)
  have hSpec := hSpec.heap_exposeAt (by omega) rfl (by heap_check [hb])
  heap_norm
  heap_checked
  obtain rfl := read_eq hx
  heap_checked
  obtain rfl := removeExposure_eq hx
  heap_stuck
  obtain ⟨_, hw⟩ := hx
  simp [Heap.write, Heap.modify, Heap.retire, add, update, Heap.live, Heap.empty] at hw

theorem from_mut_write_in_callee.spec (placement : Placement) :
    ⦃ emp ⦄ from_mut_write_in_callee placement ⦃ r => ⌜r = 8#u32⌝ ⦄ := by
  unfold from_mut_write_in_callee write_through
  step*
  subst_vars
  step*

/-! ## `as_ptr`/`as_mut_ptr` -/

theorem as_mut_ptr_write.spec (placement : Placement) : ⦃ emp ⦄ as_mut_ptr_write placement ⦃ r => ⌜r = 7#u32⌝ ⦄ := by
  unfold as_mut_ptr_write
  step* 2
  have hs : s.val.val = [0#u32, 0#u32, 0#u32, 0#u32] := by simp [s_post, Array.repeat]
  step with RawPtr.add.spec p s.val.val 3#usize (by simp [hs]) (by simp [hs])
  subst_vars
  step with MutRawPtr.write.spec_range p s.val.val 3 7#u32 (by simp [hs])
  step with Slice.end_as_mut_ptr.spec s.val p (s.val.val.set 3 7#u32) (by simp [Slice.length]) (by simp [hs])
  step*
  simp_all [Array.from_slice]

theorem as_mut_ptr_one_past_end.spec (placement : Placement) :
    ⦃ emp ⦄ as_mut_ptr_one_past_end placement ⦃ r => ⌜r = 0#u32⌝ ⦄ := by
  unfold as_mut_ptr_one_past_end
  step* 2
  have hs : s.val.val = [0#u32, 0#u32, 0#u32, 0#u32] := by simp [s_post, Array.repeat]
  step with RawPtr.add.spec p s.val.val 4#usize (by simp [hs]) (by simp [hs])
  subst_vars
  step with Slice.end_as_mut_ptr.spec s.val p s.val.val (by simp [Slice.length]) (by simp [hs])
  step*
  simp_all [Array.from_slice]

theorem as_mut_ptr_write_one_past_end.ub :
    ¬ ⦃ emp ⦄ as_mut_ptr_write_one_past_end distinct ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold as_mut_ptr_write_one_past_end at hSpec
  heap_norm
  have hv : ((Array.repeat 4#usize 0#u32).to_slice : List U32) = [0#u32, 0#u32, 0#u32, 0#u32] := by
    simp [Array.val_to_slice, Array.repeat_val]
  rw [hv] at hSpec
  set b : Usize := distinct [0]
  have hb : b.val = 8 := distinct_val [0] (by decide)
  have hSpec := hSpec.heap_exposeAt (by omega) rfl (by heap_check [hb])
  heap_norm
  heap_checked
  obtain ⟨hq, rfl⟩ := hx
  have := pow_numBits_gt
  simp [Heap.liveOffset, Heap.ptrLive, Heap.live, Heap.offset, add, block, update, Heap.empty, Heap.allocationAlive, hb, size_u32,
    UScalarTy.numBits] at hq
  obtain ⟨-, -, rfl⟩ := hq
  heap_stuck
  obtain ⟨_, _, hw⟩ := hx
  simp [Heap.write, Heap.modify, add, block, update, Heap.live, Heap.empty, hb, RawPtr.offsetFrom,
    Std.Repr.write, usize_mk_val, align_u32] at hw
  split at hw
  · next h => simp [size_u32] at h
  · simp at hw

theorem as_mut_ptr_add_out_of_bounds.ub :
    ¬ ⦃ emp ⦄ as_mut_ptr_add_out_of_bounds distinct ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold as_mut_ptr_add_out_of_bounds at hSpec
  heap_norm
  have hv : ((Array.repeat 4#usize 0#u32).to_slice : List U32) = [0#u32, 0#u32, 0#u32, 0#u32] := by
    simp [Array.val_to_slice, Array.repeat_val]
  rw [hv] at hSpec
  set b : Usize := distinct [0]
  have hb : b.val = 8 := distinct_val [0] (by decide)
  have hSpec := hSpec.heap_exposeAt (by omega) rfl (by heap_check [hb])
  heap_norm
  heap_stuck
  obtain ⟨hq, -⟩ := hx
  simp [Heap.liveOffset, Heap.ptrLive, Heap.live, Heap.offset, add, block, update, Heap.empty, Heap.allocationAlive, hb,
    create_enc_length] at hq
  obtain ⟨h, -⟩ := hq
  simp [size_u32] at h

theorem as_ptr_read_after_owner_write.ub :
    ¬ ⦃ emp ⦄ as_ptr_read_after_owner_write distinct ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold as_ptr_read_after_owner_write at hSpec
  heap_norm
  have hv : ∀ h, ((Array.make 2#usize [1#u32, 2#u32] h).to_slice : List U32) = [1#u32, 2#u32] := by
    simp [Array.val_to_slice, Array.make_val]
  rw [hv] at hSpec
  set b : Usize := distinct [0]
  have hb : b.val = 8 := distinct_val [0] (by decide)
  have hSpec := hSpec.heap_sharedExposeAt (by omega) rfl (by heap_check [hb])
  heap_norm
  heap_checked
  obtain rfl := endSharedExposure_eq hx
  simp only [List.getElem?_cons_zero, bind_ok, bind_tc_ok] at hSpec
  heap_stuck
  obtain ⟨hr, -⟩ := hx
  simp [Heap.read, Heap.retire, add, update, Heap.live, Heap.empty] at hr

theorem as_ptr_read_while_shared.spec (placement : Placement) : ⦃ emp ⦄ as_ptr_read_while_shared placement ⦃ r => ⌜r = 3#u32⌝ ⦄ := by
  unfold as_ptr_read_while_shared
  step* 2
  · subst s_post; simp [Array.as_slice, Array.make, Slice.length]
  have hs : s.val.val = [1#u32, 2#u32] := by simp [s_post, Array.make, Array.as_slice]
  step
  step with RawPtr.read.spec_readable_head p 1 s.val.val (by simp [hs])
  have hx : x.val = 2#u32 := by rw [x_post]; simp [hs]
  have hp1 : p1 = 1#u32 := by simp [p1_post, hs]
  step
  subst as_ptr_back_post
  step with Slice.end_as_ptr.spec s.val p (by simp [Slice.length, hs])
  step*

theorem as_mut_ptr_twice.ub : ¬ ⦃ emp ⦄ as_mut_ptr_twice distinct ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold as_mut_ptr_twice at hSpec
  heap_norm
  have hv : ((Array.repeat 2#usize 0#u32).to_slice : List U32) = [0#u32, 0#u32] := by
    simp [Array.val_to_slice, Array.repeat_val]
  rw [hv] at hSpec
  set b : Usize := distinct [0]
  have hb : b.val = 8 := distinct_val [0] (by decide)
  have hSpec := hSpec.heap_exposeAt (by omega) rfl (by heap_check [hb])
  heap_norm
  heap_checked
  obtain ⟨hr, rfl⟩ := hx
  simp [Heap.readRange, add, block, update, Heap.empty, Heap.live, hb, align_u32, List.range_succ,
    List.mapM_cons, Option.bind_eq_some_iff] at hr
  obtain ⟨-, -, a, -, a1, -, rfl⟩ := hr
  heap_checked
  obtain rfl := removeExposure_eq hx
  simp only [List.length_cons, List.length_nil] at hSpec
  simp only [show 0 + 1 + 1 ≤ Usize.max from by scalar_tac, _root_.dite_true, bind_ok] at hSpec
  set c : Usize := distinct [1]
  have hc : c.val = 16 := distinct_val [1] (by decide)
  have hSpec := hSpec.heap_exposeAt (by omega) (by simp [add, update, Heap.retire, Heap.empty])
    (by heap_check [hb, hc, Heap.retire])
  heap_norm
  heap_checked
  obtain ⟨bytes, rfl⟩ := write_eq hx
  heap_stuck
  obtain ⟨_, hw⟩ := hx
  simp [Heap.write, Heap.modify, Heap.retire, Heap.storeRepr, add, update, Heap.live,
    Heap.empty] at hw

/-! ## `Box::into_raw`/`Box::from_raw` -/

theorem box_roundtrip.spec : ⦃ emp ⦄ box_roundtrip ⦃ r => ⌜r = 4#u32⌝ ⦄ := by
  unfold box_roundtrip
  step*

theorem box_double_free.ub : ¬ ⦃ emp ⦄ box_double_free ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold box_double_free at hSpec
  heap_norm
  obtain ⟨b, hb⟩ : ∃ b : Usize, b.val = 8 := ⟨8#usize, by simp⟩
  have hSpec := hSpec.heap_newBlock b (by omega) rfl (by heap_check [hb])
  heap_norm
  heap_checked
  obtain rfl := read_eq hx
  heap_checked
  obtain ⟨_, hblk, rfl⟩ := dealloc_eq hx
  simp [add, block, update, Heap.empty] at hblk
  subst hblk
  heap_stuck
  obtain ⟨hr, -⟩ := hx
  simp [Heap.read, Heap.retire, Heap.killRoot, add, update, Heap.live, Heap.empty] at hr

theorem box_use_after_free.ub : ¬ ⦃ emp ⦄ box_use_after_free ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold box_use_after_free at hSpec
  heap_norm
  obtain ⟨b, hb⟩ : ∃ b : Usize, b.val = 8 := ⟨8#usize, by simp⟩
  have hSpec := hSpec.heap_newBlock b (by omega) rfl (by heap_check [hb])
  heap_norm
  heap_checked
  obtain rfl := read_eq hx
  heap_checked
  obtain ⟨_, hblk, rfl⟩ := dealloc_eq hx
  simp [add, block, update, Heap.empty] at hblk
  subst hblk
  heap_stuck
  obtain ⟨hr, -⟩ := hx
  simp [Heap.read, Heap.retire, Heap.killRoot, add, update, Heap.live, Heap.empty] at hr

theorem box_free_local.ub : ¬ ⦃ emp ⦄ box_free_local distinct ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold box_free_local at hSpec
  heap_norm
  set b : Usize := distinct [0]
  have hb : b.val = 8 := distinct_val [0] (by decide)
  have hSpec := hSpec.heap_exposeAt (by omega) rfl (by heap_check [hb])
  heap_norm
  heap_checked
  obtain rfl := read_eq hx
  heap_stuck
  simp [State.dealloc, Heap.dealloc, Heap.returnOwned, add, block, update, Heap.empty] at hx

theorem box_free_array_element.ub : ¬ ⦃ emp ⦄ box_free_array_element distinct ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold box_free_array_element at hSpec
  heap_norm
  have hv : ∀ h, ((Array.make 2#usize [1#u32, 2#u32] h).to_slice : List U32) = [1#u32, 2#u32] := by
    simp [Array.val_to_slice, Array.make_val]
  rw [hv] at hSpec
  set b : Usize := distinct [0]
  have hb : b.val = 8 := distinct_val [0] (by decide)
  have hSpec := hSpec.heap_exposeAt (by omega) rfl (by heap_check [hb])
  heap_norm
  heap_checked
  obtain rfl := read_eq hx
  heap_stuck
  simp [State.dealloc, Heap.dealloc, Heap.returnOwned, add, block, update, Heap.empty] at hx

/-- Leaking is not undefined behaviour: the postcondition drops the allocation. -/
theorem box_leak.spec : ⦃ emp ⦄ box_leak ⦃ r => ⌜r = 3#u32⌝ ⦄ := by
  unfold box_leak
  step*

/-! ## `slice::from_raw_parts(_mut)` -/

/-- INCOMPLETE: the borrow of the slice ends at the end of the function, after `from_raw`, which
reads the cell while it is still borrowed by the slice. -/
theorem from_raw_parts_mut_write.incomplete :
    ¬ ⦃ emp ⦄ from_raw_parts_mut_write ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold from_raw_parts_mut_write at hSpec
  heap_norm
  obtain ⟨b, hb⟩ : ∃ b : Usize, b.val = 8 := ⟨8#usize, by simp⟩
  have hSpec := hSpec.heap_newBlock b (by omega) rfl (by heap_check [hb])
  heap_norm
  heap_checked
  obtain ⟨hr, -, hx⟩ := hx
  simp [Heap.readRange, add, block, update, Heap.empty, Heap.live, hb, align_u32, List.range_succ,
    RawPtr.offsetFrom, List.mapM_cons, Option.bind_eq_some_iff] at hr
  obtain ⟨-, -, a, -, rfl⟩ := hr
  simp only [List.length_cons, List.length_nil] at hSpec
  simp only [show 0 + 1 ≤ Usize.max from by scalar_tac, _root_.dite_true, bind_ok] at hSpec
  simp [Heap.borrowRange, Heap.modifyRange, Heap.modify, add, block, update, Heap.empty, Heap.live,
    hb, align_u32, RawPtr.offsetFrom] at hx
  obtain ⟨out, hout, hc⟩ := Option.bind_eq_some_iff.mp hx
  split at hout
  case isFalse => simp at hout
  have hout := borrow_at (pre := []) (post := []) (data := enc 1#u32)
    (by simp [Block.bytes, Std.Repr.create]; rfl) rfl hout
  obtain ⟨rfl, -⟩ := Heap.commit_success _ _ hc
  rw [hout] at hSpec
  simp only [List.nil_append, List.append_nil] at hSpec
  simp only [Std.uncurry_apply_pair] at hSpec
  simp only [Slice.update, Slice.from_val, show (0#usize).val = 0 from rfl,
    List.getElem?_cons_zero, bind_ok] at hSpec
  heap_stuck
  obtain ⟨hy, -⟩ := hx
  simp [Heap.read, Heap.storeRepr, update, Heap.live, hb, align_u32, RawPtr.offsetFrom,
    Heap.empty] at hy
  rw [read_borrowed] at hy
  · simp at hy
  · simp [Block.bytes, show 0 < (Pointee.repr (T := U32)).size by decide]

theorem from_raw_parts_too_long.ub : ¬ ⦃ emp ⦄ from_raw_parts_too_long ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold from_raw_parts_too_long at hSpec
  heap_norm
  obtain ⟨b, hb⟩ : ∃ b : Usize, b.val = 8 := ⟨8#usize, by simp⟩
  have hSpec := hSpec.heap_newBlock b (by omega) rfl (by heap_check [hb])
  heap_norm
  heap_stuck
  obtain ⟨hr, -⟩ := hx
  simp [Heap.readRange, add, block, update, Heap.empty, Heap.live, hb, align_u32] at hr
  obtain ⟨-, h, -⟩ := hr
  simp [size_u32] at h

/-- The cells are shared by the slice: writing through the pointer fails. -/
theorem from_raw_parts_write_while_shared.ub :
    ¬ ⦃ emp ⦄ from_raw_parts_write_while_shared distinct ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold from_raw_parts_write_while_shared at hSpec
  heap_norm
  set b : Usize := distinct [0]
  have hb : b.val = 8 := distinct_val [0] (by decide)
  have hSpec := hSpec.heap_exposeAt (by omega) rfl (by heap_check [hb])
  heap_norm
  heap_checked
  obtain ⟨hr, hx⟩ := hx
  simp [Heap.readRange, add, block, update, Heap.empty, Heap.live, hb, align_u32, List.range_succ,
    List.mapM_cons, Option.bind_eq_some_iff] at hr
  obtain ⟨-, -, a, -, rfl⟩ := hr
  simp only [List.length_cons, List.length_nil] at hSpec
  simp only [show 0 + 1 ≤ Usize.max from by scalar_tac, _root_.dite_true, bind_ok] at hSpec
  simp [Heap.shareRange, Heap.modifyRange, Heap.modify, add, block, update, Heap.empty, Heap.live,
    hb, align_u32, RawPtr.offsetFrom] at hx
  obtain ⟨out, hout, hc⟩ := Option.bind_eq_some_iff.mp hx
  split at hout
  case isFalse => simp at hout
  have hout := share_at (pre := []) (post := []) (data := enc 1#u32) (by simp [Block.bytes, Std.Repr.create]; rfl) rfl hout
  obtain ⟨rfl, -⟩ := Heap.commit_success _ _ hc
  rw [hout] at hSpec
  simp only [List.nil_append, List.append_nil] at hSpec
  heap_stuck
  obtain ⟨_, _, hw⟩ := hx
  simp [Heap.write, Heap.modify, update, Heap.live, Heap.empty, hb, RawPtr.offsetFrom,
    Heap.storeRepr] at hw
  obtain ⟨-, hw⟩ := hw
  rw [write_unwritable (c := Cell.shared 1 ((enc 1#u32)[0]'(by decide))) ?_ (fun _ => rfl)] at hw
  · simp at hw
  · show (List.map (Cell.shared 1) (enc 1#u32).toList)[0]? = _
    simp [Vector.getElem?_eq_getElem (show 0 < (Pointee.repr (T := U32)).size by decide)]

/-- INCOMPLETE: reading through the pointer succeeds (shared cells are readable, which differs
from the previous model, where the read failed), but the borrow of `x` ends (`from_mut_back`)
before the one of the slice (`from_raw_parts_back`), whose lifetime is not related to it: retiring
the exposure of `x` requires its cells back, while they are still shared by the slice. -/
theorem from_raw_parts_read_while_shared.incomplete :
    ¬ ⦃ emp ⦄ from_raw_parts_read_while_shared distinct ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold from_raw_parts_read_while_shared at hSpec
  heap_norm
  set b : Usize := distinct [0]
  have hb : b.val = 8 := distinct_val [0] (by decide)
  have hSpec := hSpec.heap_exposeAt (by omega) rfl (by heap_check [hb])
  heap_norm
  heap_checked
  obtain ⟨hr, hx⟩ := hx
  simp [Heap.readRange, add, block, update, Heap.empty, Heap.live, hb, align_u32, List.range_succ, RawPtr.offsetFrom,
    List.mapM_cons, Option.bind_eq_some_iff] at hr
  obtain ⟨-, -, a, ha, rfl⟩ := hr
  rw [read_at (i := 0) (pre := []) (post := []) (data := enc 1#u32) (by simp [Block.bytes, Std.Repr.create]; rfl) rfl (encode_enc _) (by decide)] at ha
  cases ha
  simp only [List.length_cons, List.length_nil] at hSpec
  simp only [show 0 + 1 ≤ Usize.max from by scalar_tac, _root_.dite_true, bind_ok] at hSpec
  simp [Heap.shareRange, Heap.modifyRange, Heap.modify, add, block, update, Heap.empty, Heap.live,
    hb, align_u32, RawPtr.offsetFrom] at hx
  obtain ⟨out, hout, hc⟩ := Option.bind_eq_some_iff.mp hx
  split at hout
  case isFalse => simp at hout
  have hout := share_at (pre := []) (post := []) (data := enc 1#u32)
    (by simp [Block.bytes, Std.Repr.create]; rfl) rfl hout
  obtain ⟨rfl, -⟩ := Heap.commit_success _ _ hc
  rw [hout] at hSpec
  simp only [List.nil_append, List.append_nil] at hSpec
  heap_checked
  obtain ⟨hy, rfl⟩ := hx
  simp [Heap.read, Heap.storeRepr, update, Heap.live, hb, align_u32, RawPtr.offsetFrom,
    Heap.empty] at hy
  rw [read_at (i := 0) (pre := []) (post := []) (d := 1) (data := enc 1#u32) (by simp [Block.bytes]) rfl
    (encode_enc _) (by decide)] at hy
  cases hy
  simp only [Slice.index_usize, show ∀ h, (Slice.from [1#u32] h)[0#usize]? = some 1#u32 from
    fun _ => rfl, bind_ok] at hSpec
  simp only [show (1#u32 + 1#u32 : Result U32) = .ok 2#u32 from rfl, bind_ok] at hSpec
  heap_checked
  obtain ⟨-, rfl⟩ := hx
  heap_stuck
  simp [State.removeExposure, Heap.endExposureAt, Heap.storeRepr, update, Heap.live, Heap.empty] at hx
  exact hx.2.1 _ (Vector.getElem_mem (i := 0) (by decide))

/-- INCOMPLETE: the borrow of the array ends (`as_mut_ptr_back`) before the borrow of the slice
(`from_raw_parts_mut_back`), whose lifetime is not related to it: ending the exposure reads cells
which are still borrowed by the slice. -/
theorem from_raw_parts_mut_over_array.incomplete :
    ¬ ⦃ emp ⦄ from_raw_parts_mut_over_array distinct ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold from_raw_parts_mut_over_array at hSpec
  heap_norm
  have hv : ((Array.repeat 2#usize 0#u32).to_slice : List U32) = [0#u32, 0#u32] := by
    simp [Array.val_to_slice, Array.repeat_val]
  rw [hv] at hSpec
  set b : Usize := distinct [0]
  have hb : b.val = 8 := distinct_val [0] (by decide)
  have hSpec := hSpec.heap_exposeAt (by omega) rfl (by heap_check [hb])
  heap_norm
  heap_checked
  obtain ⟨hr, -, hx⟩ := hx
  simp [Heap.readRange, add, block, update, Heap.empty, Heap.live, hb, align_u32, List.range_succ,
    RawPtr.offsetFrom, List.mapM_cons, Option.bind_eq_some_iff] at hr
  obtain ⟨-, -, a, -, a1, -, rfl⟩ := hr
  simp only [List.length_cons, List.length_nil] at hSpec
  simp only [show 0 + 1 + 1 ≤ Usize.max from by scalar_tac, _root_.dite_true, bind_ok,
    Std.uncurry_apply_pair] at hSpec
  simp [Heap.borrowRange, Heap.modifyRange, Heap.modify, add, block, update, Heap.empty, Heap.live,
    hb, align_u32, RawPtr.offsetFrom, List.range_succ] at hx
  obtain ⟨out, hout, hc⟩ := Option.bind_eq_some_iff.mp hx
  split at hout
  case isFalse => simp at hout
  obtain ⟨out1, hout1, hout⟩ := Option.bind_eq_some_iff.mp hout
  have hout1 := borrow_at (pre := []) (post := (enc 0#u32).toList.map (Cell.shared 0))
    (data := enc 0#u32) (by simp [Block.bytes, Std.Repr.create]; rfl) rfl hout1
  have hout := borrow_at (pre := (enc 0#u32).toList.map fun _ => Cell.borrowed) (post := [])
    (data := enc 0#u32) (by simpa using hout1) (by simp) hout
  obtain ⟨rfl, -⟩ := Heap.commit_success _ _ hc
  rw [hout] at hSpec
  simp only [List.nil_append, List.append_nil] at hSpec
  simp only [Slice.update, Slice.from_val, show (1#usize).val = 1 from rfl,
    List.getElem?_cons_succ, List.getElem?_cons_zero, bind_ok] at hSpec
  heap_stuck
  obtain ⟨hy, -⟩ := hx
  simp [Heap.readRange, Heap.storeRepr, update, Heap.live, hb, align_u32, RawPtr.offsetFrom,
    Heap.empty, List.range_succ, List.mapM_cons] at hy
  obtain ⟨-, -, hy⟩ := hy
  rw [read_borrowed] at hy
  · simp at hy
  · simp [Block.bytes, show 0 < (Pointee.repr (T := U32)).size by decide]

/-! ## `ptr::read` -/

theorem ptr_read_copy.spec (placement : Placement) : ⦃ emp ⦄ ptr_read_copy placement ⦃ r => ⌜r = 2#u32⌝ ⦄ := by
  unfold ptr_read_copy
  step*
  subst_vars
  step*

/-- The two owners free the allocation: the second `from_raw` reads a deallocated block. -/
theorem ptr_read_owner_double_free.ub :
    ¬ ⦃ emp ⦄ ptr_read_owner_double_free distinct ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold ptr_read_owner_double_free at hSpec
  heap_norm
  obtain ⟨b, hb⟩ : ∃ b : Usize, b.val = 4 := ⟨4#usize, by simp⟩
  have hSpec := hSpec.heap_newBlock b (by omega) rfl (by heap_check [hb])
  heap_norm
  set c : Usize := distinct [0]
  have hc : c.val = 8 := distinct_val [0] (by decide)
  have hEnc : (Pointee.repr (T := RawPtr U32)).encode ⟨Heap.empty.next, b⟩
      (Std.Repr.pointerEncoding (⟨Heap.empty.next, b⟩ : RawPtr U32)) := rfl
  have hSpec := hSpec.heap_exposeAt_data
    [Std.Repr.pointerEncoding (⟨Heap.empty.next, b⟩ : RawPtr U32)]
    ⟨exposes_of_encode hEnc _ _, trivial⟩
    (by show 8 ∣ c.val; omega) (by simp [add, update, Heap.empty]) (by
      have := pow_numBits_gt
      simp [Heap.check, Heap.validBlock, Heap.bounded, Heap.empty, update, UScalarTy.numBits,
        Heap.validByte, Std.Repr.create, add, block, Heap.compatible, Heap.overlaps, List.all_eq_true,
        List.range_succ, List.map_cons, List.map_nil, List.forall_mem_cons, List.flatMap_cons,
        List.flatMap_nil, hb, hc, Std.Repr.pointerEncoding, RawPtr.cast]
      have hs8 : (Pointee.repr (T := RawPtr U32)).size = 8 := rfl
      have hs4 : (Pointee.repr (T := U32)).size = 4 := rfl
      repeat' apply And.intro
      all_goals first
        | omega
        | (simp [hs8, hs4]; omega)
        | (show 8 + 1 * 8 < _; omega)
        | (intro _ _ h₁ _ _ h₂
           have := (List.mem_zipIdx h₁).2.1
           have := (List.mem_zipIdx h₂).2.1
           simp [hs8] at *
           left; omega)
        | (intro x hx i hi
           have hi' : i < 8 := hi
           cases hx with
           | tail _ h => cases h
           | head =>
           erw [Vector.getElem_ofFn]
           simp
           omega))
  heap_norm
  heap_checked
  obtain ⟨hr, rfl⟩ := hx
  simp [Heap.read, add, update, Heap.live, Heap.empty, hb, hc, RawPtr.offsetFrom] at hr
  rw [read_at (i := 0) (d := 0) (pre := []) (post := []) (data := Std.Repr.pointerEncoding
      (⟨0, b⟩ : RawPtr U32)) (by simp [Block.bytes, Std.Repr.create]; exact List.append_nil _) rfl hEnc (by decide)] at hr
  cases hr.2
  heap_norm
  heap_checked
  obtain rfl := read_eq hx
  heap_checked
  obtain ⟨_, hblk, rfl⟩ := dealloc_eq hx
  simp [add, block, update, Heap.empty] at hblk
  subst hblk
  heap_checked
  obtain ⟨hr, rfl⟩ := hx
  simp [Heap.read, Heap.retire, Heap.killRoot, add, update, Heap.live, Heap.empty, hb, hc, RawPtr.offsetFrom] at hr
  rw [read_at (i := 0) (d := 0) (pre := []) (post := []) (data := Std.Repr.pointerEncoding
      (⟨0, b⟩ : RawPtr U32)) (by simp [Block.bytes, Std.Repr.create]; exact List.append_nil _) rfl hEnc (by decide)] at hr
  cases hr.2
  heap_checked
  obtain rfl := removeExposure_eq hx
  heap_stuck
  obtain ⟨hr, -⟩ := hx
  simp [Heap.read, Heap.retire, Heap.killRoot, add, update, Heap.live, Heap.empty] at hr

/-! ## `<*mut T>::as_mut`

Aeneas has no model of `as_mut`: it extracts it as an axiom, with a stateful backward function
(which gives back the final value of the borrow). The proofs below assume the model of
`from_raw_parts_mut`: the cells move into the borrow until the backward function gives them back. -/

def asMutBorrow (p : MutRawPtr U32) :
    Result (Option (MutBorrow U32) × (Option (MutBorrow U32) → Result Unit)) :=
  Std.bind (RawPtr.borrow Pointee.repr p) fun value =>
    .ok (some ⟨value⟩, fun final => match final with
      | some b => RawPtr.endBorrow Pointee.repr p b.val
      | none => .fail .undef)

/-- INCOMPLETE: the lifetime of the `&mut` returned by `as_mut` is not related to the borrow of `x`
(the raw pointer erases it), so the extracted code ends the borrow of `x` (`from_mut_back`) first,
and gives the `&mut` back (`as_mut_back`) at the end of the function. Reading `x` then fails on the
borrowed cells. -/
theorem ptr_as_mut_write.incomplete
    (hModel : ∀ p, core.ptr.mut_ptr.RawPtrMutT.as_mut p = asMutBorrow p) :
    ¬ ⦃ emp ⦄ ptr_as_mut_write distinct ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold ptr_as_mut_write at hSpec
  simp only [hModel, asMutBorrow, RawPtr.borrow] at hSpec
  heap_norm
  set b : Usize := distinct [0]
  have hb : b.val = 8 := distinct_val [0] (by decide)
  have hSpec := hSpec.heap_exposeAt (by omega) rfl (by heap_check [hb])
  heap_norm
  heap_checked
  obtain ⟨hr, -, hx⟩ := hx
  simp [Heap.readRange, add, block, update, Heap.empty, Heap.live, hb, align_u32, List.range_succ,
    RawPtr.offsetFrom, List.mapM_cons, Option.bind_eq_some_iff] at hr
  obtain ⟨-, -, a, -, rfl⟩ := hr
  simp [Heap.borrowRange, Heap.modifyRange, Heap.modify, add, block, update, Heap.empty, Heap.live,
    hb, align_u32, RawPtr.offsetFrom] at hx
  obtain ⟨out, hout, hc⟩ := Option.bind_eq_some_iff.mp hx
  split at hout
  case isFalse => simp at hout
  have hout := borrow_at (pre := []) (post := []) (data := enc 1#u32)
    (by simp [Block.bytes, Std.Repr.create]; rfl) rfl hout
  obtain ⟨rfl, -⟩ := Heap.commit_success _ _ hc
  rw [hout] at hSpec
  simp only [List.nil_append, List.append_nil, bind_ok, Std.uncurry_apply_pair] at hSpec
  heap_stuck
  obtain ⟨hy, -⟩ := hx
  simp [Heap.read, Heap.storeRepr, update, Heap.live, hb, align_u32, RawPtr.offsetFrom,
    Heap.empty] at hy
  rw [read_borrowed] at hy
  · simp at hy
  · simp [Block.bytes, show 0 < (Pointee.repr (T := U32)).size by decide]

/-- The second `as_mut` borrows cells which are already borrowed by the first one. -/
theorem ptr_as_mut_twice.ub
    (hModel : ∀ p, core.ptr.mut_ptr.RawPtrMutT.as_mut p = asMutBorrow p) :
    ¬ ⦃ emp ⦄ ptr_as_mut_twice distinct ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold ptr_as_mut_twice at hSpec
  simp only [hModel, asMutBorrow, RawPtr.borrow] at hSpec
  heap_norm
  set b : Usize := distinct [0]
  have hb : b.val = 8 := distinct_val [0] (by decide)
  have hSpec := hSpec.heap_exposeAt (by omega) rfl (by heap_check [hb])
  heap_norm
  heap_checked
  obtain ⟨hr, -, hx⟩ := hx
  simp [Heap.readRange, add, block, update, Heap.empty, Heap.live, hb, align_u32, List.range_succ,
    RawPtr.offsetFrom, List.mapM_cons, Option.bind_eq_some_iff] at hr
  obtain ⟨-, -, a, -, rfl⟩ := hr
  simp [Heap.borrowRange, Heap.modifyRange, Heap.modify, add, block, update, Heap.empty, Heap.live,
    hb, align_u32, RawPtr.offsetFrom] at hx
  obtain ⟨out, hout, hc⟩ := Option.bind_eq_some_iff.mp hx
  split at hout
  case isFalse => simp at hout
  have hout := borrow_at (pre := []) (post := []) (data := enc 1#u32)
    (by simp [Block.bytes, Std.Repr.create]; rfl) rfl hout
  obtain ⟨rfl, -⟩ := Heap.commit_success _ _ hc
  rw [hout] at hSpec
  simp only [List.nil_append, List.append_nil, bind_ok, Std.uncurry_apply_pair] at hSpec
  heap_stuck
  obtain ⟨hy, -, -⟩ := hx
  simp [Heap.readRange, List.range_succ, List.mapM_cons, Heap.storeRepr, update, Heap.live, hb, align_u32, RawPtr.offsetFrom,
    Heap.empty] at hy
  rw [read_borrowed] at hy
  · simp at hy
  · simp [Block.bytes, show 0 < (Pointee.repr (T := U32)).size by decide]

/-! ## A raw pointer hidden in a type which keeps the borrow alive -/

/-- The backward function of `Handle::new` ends the borrow of `x` with the backward function of
`from_mut`, which reads the value written through the hidden pointer. -/
theorem handle_write.spec (placement : Placement) :
    ⦃ emp ⦄ handle_write placement ⦃ r => ⌜r = 4#u32⌝ ⦄ := by
  unfold handle_write Handle.new Handle.as_ptr
  step as ⟨r, hBack⟩
  obtain ⟨p, back⟩ := r
  simp only at hBack ⊢
  subst hBack
  step*

/-! ## `&*p`: a shared reference made from a raw pointer -/

/-- The cell is shared by the reference: writing through the pointer fails. -/
theorem reborrow_write_while_shared.ub :
    ¬ ⦃ emp ⦄ reborrow_write_while_shared distinct ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold reborrow_write_while_shared at hSpec
  heap_norm
  set b : Usize := distinct [0]
  have hb : b.val = 8 := distinct_val [0] (by decide)
  have hSpec := hSpec.heap_exposeAt (by omega) rfl (by heap_check [hb])
  heap_norm
  heap_checked
  obtain ⟨hr, hx⟩ := hx
  simp [Heap.readRange, add, block, update, Heap.empty, Heap.live, hb, align_u32, List.range_succ,
    List.mapM_cons, Option.bind_eq_some_iff] at hr
  obtain ⟨-, -, a, -, rfl⟩ := hr
  simp [Heap.shareRange, Heap.modifyRange, Heap.modify, add, block, update, Heap.empty, Heap.live,
    hb, align_u32, RawPtr.offsetFrom] at hx
  obtain ⟨out, hout, hc⟩ := Option.bind_eq_some_iff.mp hx
  split at hout
  case isFalse => simp at hout
  have hout := share_at (pre := []) (post := []) (data := enc 1#u32) (by simp [Block.bytes, Std.Repr.create]; rfl) rfl hout
  obtain ⟨rfl, -⟩ := Heap.commit_success _ _ hc
  rw [hout] at hSpec
  simp only [List.nil_append, List.append_nil, bind_ok, Std.uncurry_apply_pair] at hSpec
  heap_stuck
  obtain ⟨_, _, hw⟩ := hx
  simp [Heap.write, Heap.modify, update, Heap.live, Heap.empty, hb, RawPtr.offsetFrom,
    Heap.storeRepr] at hw
  obtain ⟨-, hw⟩ := hw
  rw [write_unwritable (c := Cell.shared 1 ((enc 1#u32)[0]'(by decide))) ?_ (fun _ => rfl)] at hw
  · simp at hw
  · show (List.map (Cell.shared 1) (enc 1#u32).toList)[0]? = _
    simp [Vector.getElem?_eq_getElem (show 0 < (Pointee.repr (T := U32)).size by decide)]

/-- INCOMPLETE: the borrow of the local ends (`from_mut_back`) before the lifetime of the
reference (`as_ref_unchecked_back`): ending the exposure requires its cells back, and they are
still shared by the reference. -/
theorem reborrow_read_while_shared.incomplete :
    ¬ ⦃ emp ⦄ reborrow_read_while_shared distinct ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold reborrow_read_while_shared at hSpec
  heap_norm
  set b : Usize := distinct [0]
  have hb : b.val = 8 := distinct_val [0] (by decide)
  have hSpec := hSpec.heap_exposeAt (by omega) rfl (by heap_check [hb])
  heap_norm
  heap_checked
  obtain ⟨hr, hx⟩ := hx
  simp [Heap.readRange, add, block, update, Heap.empty, Heap.live, hb, align_u32, List.range_succ, RawPtr.offsetFrom,
    List.mapM_cons, Option.bind_eq_some_iff] at hr
  obtain ⟨-, -, a, ha, rfl⟩ := hr
  rw [read_at (i := 0) (pre := []) (post := []) (data := enc 1#u32) (by simp [Block.bytes, Std.Repr.create]; rfl) rfl (encode_enc _) (by decide)] at ha
  cases ha
  simp [Heap.shareRange, Heap.modifyRange, Heap.modify, add, block, update, Heap.empty, Heap.live,
    hb, align_u32, RawPtr.offsetFrom] at hx
  obtain ⟨out, hout, hc⟩ := Option.bind_eq_some_iff.mp hx
  split at hout
  case isFalse => simp at hout
  have hout := share_at (pre := []) (post := []) (data := enc 1#u32)
    (by simp [Block.bytes, Std.Repr.create]; rfl) rfl hout
  obtain ⟨rfl, -⟩ := Heap.commit_success _ _ hc
  rw [hout] at hSpec
  simp only [List.nil_append, List.append_nil, bind_ok, Std.uncurry_apply_pair] at hSpec
  heap_checked
  obtain ⟨hy, rfl⟩ := hx
  simp [Heap.read, Heap.storeRepr, update, Heap.live, hb, align_u32, RawPtr.offsetFrom,
    Heap.empty] at hy
  rw [read_at (i := 0) (pre := []) (post := []) (d := 1) (data := enc 1#u32) (by simp [Block.bytes]) rfl
    (encode_enc _) (by decide)] at hy
  cases hy
  simp only [show (1#u32 + 1#u32 : Result U32) = .ok 2#u32 from rfl, bind_ok] at hSpec
  heap_checked
  obtain ⟨-, rfl⟩ := hx
  heap_stuck
  simp [State.removeExposure, Heap.endExposureAt, Heap.storeRepr, update, Heap.live, Heap.empty] at hx
  exact hx.2.1 _ (Vector.getElem_mem (i := 0) (by decide))

/-- INCOMPLETE: the lifetime of the reference ends at the end of the function (when the
functional translation ends it), not where the reference is dead: the write through the pointer,
which Rust accepts after the last use of the reference, fails while the cell is still shared. -/
theorem reborrow_then_write.incomplete :
    ¬ ⦃ emp ⦄ reborrow_then_write distinct ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := dwp_empty hTriple
  unfold reborrow_then_write at hSpec
  heap_norm
  set b : Usize := distinct [0]
  have hb : b.val = 8 := distinct_val [0] (by decide)
  have hSpec := hSpec.heap_exposeAt (by omega) rfl (by heap_check [hb])
  heap_norm
  heap_checked
  obtain ⟨hr, hx⟩ := hx
  simp [Heap.readRange, add, block, update, Heap.empty, Heap.live, hb, align_u32, List.range_succ,
    List.mapM_cons, Option.bind_eq_some_iff] at hr
  obtain ⟨-, -, a, -, rfl⟩ := hr
  simp [Heap.shareRange, Heap.modifyRange, Heap.modify, add, block, update, Heap.empty, Heap.live,
    hb, align_u32, RawPtr.offsetFrom] at hx
  obtain ⟨out, hout, hc⟩ := Option.bind_eq_some_iff.mp hx
  split at hout
  case isFalse => simp at hout
  have hout := share_at (pre := []) (post := []) (data := enc 1#u32) (by simp [Block.bytes, Std.Repr.create]; rfl) rfl hout
  obtain ⟨rfl, -⟩ := Heap.commit_success _ _ hc
  rw [hout] at hSpec
  simp only [List.nil_append, List.append_nil, bind_ok, Std.uncurry_apply_pair] at hSpec
  heap_stuck
  obtain ⟨_, _, hw⟩ := hx
  simp [Heap.write, Heap.modify, update, Heap.live, Heap.empty, hb, RawPtr.offsetFrom,
    Heap.storeRepr] at hw
  obtain ⟨-, hw⟩ := hw
  rw [write_unwritable (c := Cell.shared 1 ((enc 1#u32)[0]'(by decide))) ?_ (fun _ => rfl)] at hw
  · simp at hw
  · show (List.map (Cell.shared 1) (enc 1#u32).toList)[0]? = _
    simp [Vector.getElem?_eq_getElem (show 0 < (Pointee.repr (T := U32)).size by decide)]

end safe_unsafe.Proofs
