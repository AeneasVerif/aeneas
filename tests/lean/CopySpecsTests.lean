import Aeneas

/-! Regression tests for the specifications of the copies and of `write_bytes`
(`Aeneas/Std/CopySpecs.lean`), on small programs written directly in Lean which mimic Ryu and
Zmij. -/

open Aeneas Aeneas.Std Aeneas.SepLogic Aeneas.Std.WP Result core.mem.maybe_uninit

namespace copy_specs_tests

theorem take_two_drop {α : Type} (l : List α) (j : Nat) (h : j + 2 ≤ l.length) :
    (l.drop j).take 2 = [l[j], l[j + 1]] := by
  have h₁ : j < l.length := by omega
  have h₂ : j + 1 < l.length := by omega
  rw [List.drop_eq_getElem_cons h₁, List.drop_eq_getElem_cons h₂]
  rfl

theorem fits (n : Usize) (h : n.val ≤ 16) :
    ((n.val * (Pointee.repr (T := U8)).size : Nat) : Int) ≤ IScalar.cMax .Isize := by
  have : (Pointee.repr (T := U8)).size = 1 := rfl
  rw [this, show IScalar.cMax .Isize = 2147483647 from rfl]
  omega

/-! ## Ryu: digit pairs from a readable table, written backwards -/

/-- As Ryu's `write_mantissa`/`write_exponent`: from the end of the output, moves back with `sub`
and copies two digit pairs of a table (for instance `DIGIT_TABLE.as_ptr()`, exposed at depth `1`). -/
def write_pairs (table : ConstRawPtr U8) (out : MutRawPtr U8) (a b : Usize) : Result Unit := do
  let p₁ ← RawPtr.sub (out.elem 4) 2#usize
  let d₁ ← RawPtr.add table a
  core.ptr.copy_nonoverlapping d₁ p₁ 2#usize
  let p₂ ← RawPtr.sub p₁ 2#usize
  let d₂ ← RawPtr.add table b
  core.ptr.copy_nonoverlapping d₂ p₂ 2#usize

theorem write_pairs.spec (table : ConstRawPtr U8) (out : MutRawPtr U8) (tbl : List U8)
    (a b : Usize) (ha : a.val + 2 ≤ tbl.length) (hb : b.val + 2 ≤ tbl.length) :
    ⦃ table.readable 1 tbl ∗ out ↦?* List.replicate 4 ⟨none⟩ ⦄ write_pairs table out a b
    ⦃ table.readable 1 tbl ∗ out ↦?* [⟨some tbl[b.val]⟩, ⟨some tbl[b.val + 1]⟩,
        ⟨some tbl[a.val]⟩, ⟨some tbl[a.val + 1]⟩] ⦄ := by
  unfold write_pairs
  step with RawPtr.sub.spec_uninit out (List.replicate 4 ⟨none⟩) 4 2#usize (by simp) (by simp)
    (by simp)
  subst p₁_post
  have hd := RawPtr.add.spec_readable_elem table 1 tbl 0 a (by omega) (by omega)
  simp only [RawPtr.elem_zero, Nat.zero_add] at hd
  step with hd
  subst d₁_post
  have hc := core.ptr.copy_nonoverlapping.spec_readable table out 1 tbl (List.replicate 4 ⟨none⟩)
    a.val (4 - 2#usize.val) 2#usize (by scalar_tac) (by simp) (by omega) (by simp)
    (fits 2#usize (by scalar_tac))
  simp [take_two_drop tbl a.val ha] at hc
  step with hc
  step with RawPtr.sub.spec_uninit out [⟨none⟩, ⟨none⟩, ⟨some tbl[a.val]⟩, ⟨some tbl[a.val + 1]⟩]
    2 2#usize (by simp) (by simp) (by simp)
  subst p₂_post
  have hd' := RawPtr.add.spec_readable_elem table 1 tbl 0 b (by omega) (by omega)
  simp only [RawPtr.elem_zero, Nat.zero_add] at hd'
  step with hd'
  subst d₂_post
  have hc' := core.ptr.copy_nonoverlapping.spec_readable table out 1 tbl
    [⟨none⟩, ⟨none⟩, ⟨some tbl[a.val]⟩, ⟨some tbl[a.val + 1]⟩] b.val (2 - 2#usize.val) 2#usize
    (by scalar_tac) (by simp) (by omega) (by simp) (fits 2#usize (by scalar_tac))
  simp [take_two_drop tbl b.val hb] at hc'
  simp only [Nat.sub_self, RawPtr.elem_zero]
  refine ispec_conseq hc' ?_ (fun _ => entails_refl _)
  rintro h ⟨_, hh⟩
  exact hh

/-! ## Zmij: the tail of `write` -/

/-- As the tail of Zmij's `write`: shifts digits left within the buffer with
`copy(buffer.add(1), buffer, len)`, pads with `write_bytes` of `'0'`, and copies 4 bytes of a `u64`
(exposed by `from_ref`, at depth `1`) through its `u8` view. -/
def zmij_tail (buf : MutRawPtr U8) (xp : ConstRawPtr U64) : Result Unit := do
  let s ← RawPtr.add buf 1#usize
  core.ptr.copy s buf 3#usize
  let z ← RawPtr.add buf 3#usize
  core.ptr.write_bytes z 48#u8 2#usize
  let xb ← RawPtr.ptr_cast U8 xp
  let d ← RawPtr.add buf 5#usize
  core.ptr.copy_nonoverlapping xb d 4#usize

theorem zmij_tail.spec (buf : MutRawPtr U8) (xp : ConstRawPtr U64) (x : U64) (c₁ c₂ c₃ : U8) :
    ⦃ buf ↦?* [⟨none⟩, ⟨some c₁⟩, ⟨some c₂⟩, ⟨some c₃⟩, ⟨none⟩, ⟨none⟩, ⟨none⟩, ⟨none⟩, ⟨none⟩] ∗
        xp.readable 1 [x] ⦄
      zmij_tail buf xp
    ⦃ buf ↦?* ([⟨some c₁⟩, ⟨some c₂⟩, ⟨some c₃⟩, ⟨some 48#u8⟩, ⟨some 48#u8⟩] ++
          ((x.bv.toLEBytes.map (UScalar.mk (ty := .U8))).take 4).map (fun v => ⟨some v⟩)) ∗
        (xp.cast U8).readable 1 (x.bv.toLEBytes.map (UScalar.mk (ty := .U8))) ⦄ := by
  -- The `u64` exposure, viewed as its bytes
  refine ispec_conseq (P' := buf ↦?* _ ∗
      (xp.cast U8).readable 1 (x.bv.toLEBytes.map (UScalar.mk (ty := .U8)))) ?_
    (sep_mono (entails_refl _) (RawPtr.readable_uscalar_toLEBytes xp 1 x)) (fun _ => entails_refl _)
  unfold zmij_tail
  have hlen : (x.bv.toLEBytes.map (UScalar.mk (ty := .U8))).length = 8 := by
    simp [BitVec.toLEBytes_length]
  -- `copy(buffer.add(1), buffer, 3)`
  have ha := RawPtr.add.spec_uninit buf
    [⟨none⟩, ⟨some c₁⟩, ⟨some c₂⟩, ⟨some c₃⟩, ⟨none⟩, ⟨none⟩, ⟨none⟩, ⟨none⟩, ⟨none⟩] 0 1#usize
    (by simp) (by simp)
  simp only [RawPtr.elem_zero] at ha
  step with ha
  subst s_post
  have hc := core.ptr.copy.spec_uninit_within buf
    [⟨none⟩, ⟨some c₁⟩, ⟨some c₂⟩, ⟨some c₃⟩, ⟨none⟩, ⟨none⟩, ⟨none⟩, ⟨none⟩, ⟨none⟩] (0 + 1) 0
    3#usize (by simp) (by simp) (by simp) (fits 3#usize (by scalar_tac))
  simp only [RawPtr.elem_zero] at hc
  simp at hc
  step with hc
  -- `write_bytes(buffer.add(3), b'0', 2)`
  have hz := RawPtr.add.spec_uninit buf
    [⟨some c₁⟩, ⟨some c₂⟩, ⟨some c₃⟩, ⟨some c₃⟩, ⟨none⟩, ⟨none⟩, ⟨none⟩, ⟨none⟩, ⟨none⟩] 0 3#usize
    (by simp) (by simp)
  simp only [RawPtr.elem_zero] at hz
  step with hz
  subst z_post
  have hw := core.ptr.write_bytes.spec_uninit buf
    [⟨some c₁⟩, ⟨some c₂⟩, ⟨some c₃⟩, ⟨some c₃⟩, ⟨none⟩, ⟨none⟩, ⟨none⟩, ⟨none⟩, ⟨none⟩]
    (0 + 3#usize.val) 48#u8 2#usize (by simp) (by rw [show IScalar.cMax .Isize = 2147483647 from rfl]; simp)
  simp at hw
  step with hw
  -- `copy_nonoverlapping(from_ref(&x).cast::<u8>(), buffer.add(5), 4)`
  step
  subst xb_post
  have hd := RawPtr.add.spec_uninit buf
    [⟨some c₁⟩, ⟨some c₂⟩, ⟨some c₃⟩, ⟨some 48#u8⟩, ⟨some 48#u8⟩, ⟨none⟩, ⟨none⟩, ⟨none⟩, ⟨none⟩]
    0 5#usize (by simp) (by simp)
  simp only [RawPtr.elem_zero] at hd
  step with hd
  subst d_post
  have hcp := core.ptr.copy_nonoverlapping.spec_readable (xp.cast U8) buf 1
    (x.bv.toLEBytes.map (UScalar.mk (ty := .U8)))
    [⟨some c₁⟩, ⟨some c₂⟩, ⟨some c₃⟩, ⟨some 48#u8⟩, ⟨some 48#u8⟩, ⟨none⟩, ⟨none⟩, ⟨none⟩, ⟨none⟩]
    0 (0 + 5#usize.val) 4#usize (by simp [hlen]) (by simp) (by simp [hlen]) (by simp)
    (fits 4#usize (by scalar_tac))
  simp only [RawPtr.elem_zero] at hcp
  simp at hcp
  refine ispec_conseq hcp ?_ (fun _ => ?_)
  · rintro h ⟨bp, hh⟩
    simp only at hh
    rw [sep_comm_eq] at hh
    refine sep_mono ?_ (entails_refl _) h hh
    exact fun _ hr => ⟨bp, hr⟩
  · refine entails_trans (entails_of_eq (sep_comm_eq _ _)) (entails_of_eq ?_)
    simp

/-! ## `n = 0`, and `step` -/

/-- Copying nothing (the ranges must be non-empty, the count may be `0`). -/
example (src dst : RawPtr U8) (a : U8) :
    ⦃ src.readable 1 [a] ∗ dst ↦?* [⟨none⟩] ⦄
      core.ptr.copy_nonoverlapping (src.elem 0) (dst.elem 1) 0#usize
    ⦃ src.readable 1 [a] ∗ dst ↦?* [⟨none⟩] ⦄ := by
  have h := core.ptr.copy_nonoverlapping.spec_readable src dst 1 [a] [⟨none⟩] 0 1 0#usize
    (by simp) (by simp) (by simp) (by simp) (fits 0#usize (by scalar_tac))
  simpa using h

/-- `step` finds the specification of `write_bytes`; the one of `copy` within a range is given
its side condition on the size. -/
example (p : MutRawPtr U8) (b : U8) :
    ⦃ p ↦?* [⟨none⟩, ⟨none⟩, ⟨none⟩] ⦄
      (do core.ptr.write_bytes (p.elem 1) b 2#usize
          core.ptr.copy (p.elem 2) (p.elem 0) 1#usize)
    ⦃ p ↦?* [⟨some b⟩, ⟨some b⟩, ⟨some b⟩] ⦄ := by
  step
  step with core.ptr.copy.spec_uninit_within p [⟨none⟩, ⟨some b⟩, ⟨some b⟩] 2 0 1#usize (by simp) (by simp) (by simp)
    (fits 1#usize (by scalar_tac))

/-- At the start of the ranges, `step` finds `write_bytes.spec_uninit_head`,
`copy.spec_uninit_within_src_head`/`_dst_head` and `copy_nonoverlapping.spec_readable_head`. -/
example (p : MutRawPtr U8) (c : U8) :
    ⦃ p ↦?* [⟨none⟩, ⟨none⟩, ⟨none⟩] ⦄
      (do core.ptr.write_bytes p c 1#usize
          core.ptr.copy p (p.elem 1) 1#usize
          core.ptr.copy (p.elem 2) p 1#usize)
    ⦃ p ↦?* [⟨none⟩, ⟨some c⟩, ⟨none⟩] ⦄ := by
  step
  step
  step

example (p : MutRawPtr U8) (src : RawPtr U8) (a b : U8) :
    ⦃ src.readable 1 [a, b] ∗ p ↦?* [⟨none⟩, ⟨none⟩, ⟨none⟩] ⦄
      core.ptr.copy_nonoverlapping src p 2#usize
    ⦃ src.readable 1 [a, b] ∗ p ↦?* [⟨some a⟩, ⟨some b⟩, ⟨none⟩] ⦄ := by
  step

#print axioms write_pairs.spec
#print axioms zmij_tail.spec
#print axioms core.ptr.copy_nonoverlapping.spec_readable
#print axioms core.ptr.copy_nonoverlapping.spec_range
#print axioms core.ptr.copy_nonoverlapping.spec_uninit
#print axioms core.ptr.copy.spec_readable
#print axioms core.ptr.copy.spec_uninit_within
#print axioms core.ptr.write_bytes.spec_uninit
#print axioms RawPtr.readable_uscalar_toLEBytes

end copy_specs_tests
