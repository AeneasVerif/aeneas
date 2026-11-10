import RawZmijMwe

/-! # The formatter of the Zmij MWE

The proof of `DecimalBuffer.format.spec` of fournet/wip-memory-model
(`tests/lean/RawZmijMwe/Formatter.lean` there), for the extracted `DecimalBuffer.format`
(`RawZmijMwe`, from `tests/src/raw_zmij_mwe.rs`), whose three exposures of the buffer are at the
addresses `placement.addr 0/1/2`.

`write_decimal` and the end of the function are proved in separation logic. The measure of the
written prefix, `end.offset_from(self.bytes.as_ptr())`, is proved on the heap (`DWP`): `end` points
into the first exposure (`as_mut_ptr`), which has been retired, and the distance is defined because
the second exposure (`as_ptr`), at the same address, overlaps it in a live allocation, so that both
have the same root (`Heap.Inv.same_root_of_overlap`). -/

open Aeneas Aeneas.Std Aeneas.SepLogic Aeneas.Std.WP Aeneas.Data.Coinductive

unseal Result

namespace raw_zmij_mwe

/-! ## Decimal digits (from fournet/wip-memory-model) -/

def ascii (n : Nat) : U8 := ⟨BitVec.ofNat 8 (48 + n)⟩

theorem ascii_val (n : Nat) (bound : n < 10) : (ascii n).val = 48 + n := by
  change (48 + n) % 256 = 48 + n
  apply Nat.mod_eq_of_lt
  omega

def decimalDigits (value : U8) : List U8 :=
  if 100 ≤ value.val then
    [ascii (value.val / 100), ascii (value.val % 100 / 10), ascii (value.val % 10)]
  else if 10 ≤ value.val then
    [ascii (value.val / 10), ascii (value.val % 10)]
  else [ascii value.val]

theorem decimalDigits_length (value : U8) :
    0 < (decimalDigits value).length ∧ (decimalDigits value).length ≤ 3 := by
  unfold decimalDigits
  split
  · simp
  · split
    · simp
    · simp

/-- `write_decimal` writes the decimal digits of `value` from `p` on, and returns the pointer
after them. -/
theorem write_decimal.spec (p : MutRawPtr U8) (value : U8) (vs : List U8) (hlen : vs.length = 4) :
    ⦃ p ↦* vs ⦄ write_decimal p value
      ⦃ fin => ⌜fin = p.elem (decimalDigits value).length⌝ ∗
        p ↦* (decimalDigits value ++ vs.drop (decimalDigits value).length) ⦄ := by
  unfold write_decimal
  by_cases h100 : value ≥ 100#u8
  · have h10 : value ≥ 10#u8 := by scalar_tac
    simp only [h100, h10, ↓reduceIte]
    step as ⟨q, hq⟩
    step as ⟨d, hd⟩
    step with MutRawPtr.write.spec_head p vs d (by omega)
    step with RawPtr.add.spec p (vs.set 0 d) 1#usize (by simp [hlen]) (by simp [hlen]) as ⟨o, ho⟩
    subst ho
    step as ⟨r, hr⟩
    step as ⟨q', hq'⟩
    step as ⟨d', hd'⟩
    step with MutRawPtr.write.spec_range p (vs.set 0 d) 1 d' (by simp [hlen])
    step with RawPtr.add.spec_elem p ((vs.set 0 d).set 1 d') 1 1#usize (by simp [hlen])
      (by simp [hlen]) as ⟨o, ho⟩
    subst ho
    step as ⟨r', hr'⟩
    step as ⟨d'', hd''⟩
    step with MutRawPtr.write.spec_range p ((vs.set 0 d).set 1 d') 2 d'' (by simp [hlen])
    step with RawPtr.add.spec_elem p (((vs.set 0 d).set 1 d').set 2 d'') 2 1#usize (by simp [hlen])
      (by simp [hlen])
    have hv : 100 ≤ value.val := by scalar_tac
    have hdig : decimalDigits value = [d, d', d''] := by
      simp only [decimalDigits, hv, ↓reduceIte, List.cons.injEq, and_true]
      refine ⟨?_, ?_, ?_⟩ <;> apply UScalar.eq_of_val_eq <;> rw [ascii_val _ (by scalar_tac)] <;>
        scalar_tac
    obtain ⟨a, b, c, e, rfl⟩ : ∃ a b c e, vs = [a, b, c, e] := by
      match vs, hlen with
      | [a, b, c, e], _ => exact ⟨a, b, c, e, rfl⟩
    rw [hdig, fin_post]
    exact pure_sep_intro _ rfl
  · obtain ⟨a, b, c, e, rfl⟩ : ∃ a b c e, vs = [a, b, c, e] := by
      match vs, hlen with
      | [a, b, c, e], _ => exact ⟨a, b, c, e, rfl⟩
    have hv : ¬ 100 ≤ value.val := by scalar_tac
    by_cases h10 : value ≥ 10#u8
    · have hv' : 10 ≤ value.val := by scalar_tac
      simp only [h100, h10, ↓reduceIte, bind_ok]
      step as ⟨q', hq'⟩
      step as ⟨d', hd'⟩
      step with MutRawPtr.write.spec_head p [a, b, c, e] d' (by simp)
      step with RawPtr.add.spec p ([a, b, c, e].set 0 d') 1#usize (by simp) (by simp) as ⟨o, ho⟩
      subst ho
      step as ⟨r', hr'⟩
      step as ⟨d'', hd''⟩
      step with MutRawPtr.write.spec_range p ([a, b, c, e].set 0 d') 1 d'' (by simp)
      step with RawPtr.add.spec_elem p (([a, b, c, e].set 0 d').set 1 d'') 1 1#usize (by simp)
        (by simp)
      have hdig : decimalDigits value = [d', d''] := by
        simp only [decimalDigits, hv, hv', ↓reduceIte, List.cons.injEq, and_true]
        refine ⟨?_, ?_⟩ <;> apply UScalar.eq_of_val_eq <;> rw [ascii_val _ (by scalar_tac)] <;>
          scalar_tac
      rw [hdig, fin_post]
      exact pure_sep_intro _ rfl
    · have hv' : ¬ 10 ≤ value.val := by scalar_tac
      simp only [h100, h10, ↓reduceIte, bind_ok]
      step as ⟨d'', hd''⟩
      step with MutRawPtr.write.spec_head p [a, b, c, e] d'' (by simp)
      step with RawPtr.add.spec p ([a, b, c, e].set 0 d'') 1#usize (by simp) (by simp)
      have hdig : decimalDigits value = [d''] := by
        simp only [decimalDigits, hv, hv', ↓reduceIte, List.cons.injEq, and_true]
        apply UScalar.eq_of_val_eq; rw [ascii_val _ (by scalar_tac)]; scalar_tac
      rw [hdig, fin_post]
      exact pure_sep_intro _ rfl

/-! ## The formatter -/

/-- The buffer after formatting `value`. -/
def formatted (bytes : List U8) (value : U8) : List U8 :=
  decimalDigits value ++ bytes.drop (decimalDigits value).length

/-- `DecimalBuffer.format` in separation logic: the slice is the decimal digits of `value`, and the
backward computation, from the resources which remain, returns the formatted buffer. -/
theorem DecimalBuffer.format.sl_spec (placement : Placement)
    (sameAddress : placement.addr 0 = placement.addr 1)
    (self : MutBorrow DecimalBuffer) (value : U8) :
    ⦃ emp ⦄ DecimalBuffer.format placement self value
      ⦃ (slice, back) => ⌜slice.val.val = decimalDigits value⌝ ∗
        iexists fun H : IProp => H ∗
          ⌜ispec H back
            (fun updated => ⌜updated.bytes.val = formatted self.val.bytes.val value⌝)⌝ ⦄ := by
  unfold DecimalBuffer.format
  step
  have hlen : s.val.val.length = 4 := by rw [s_post]; simp
  step with Slice.as_mut_ptr.spec_at (placement.addr 0) s (by simp [Slice.length, hlen])
  have hslen : s.val.length = 4 := by simp [Slice.length, hlen]
  rw [hslen]
  step with write_decimal.spec p value s.val.val hlen as ⟨fin, hfin⟩
  subst as_mut_ptr_back_post
  have bounds := decimalDigits_length value
  set k := (decimalDigits value).length with hk
  set new := decimalDigits value ++ s.val.val.drop k with hnew
  have hnewlen : new.length = 4 := by simp [hnew, hlen]; omega
  -- From here on, the heap: the first exposure is retained after its end.
  rw [ispec_iff]
  intro F s₀ hR
  have hR' : Realizes (p.exposure 4 ∗ (p ↦* new ∗ F)) s₀ :=
    Realizes.mono (by iframe) hR
  obtain ⟨blk, hl, hblen, hlive, hbptr, -⟩ := Realizes.exposure_block hR'
  have hfit := Realizes.exposure_fit hR'
  have hsz : (Pointee.repr (T := U8)).size = 1 := rfl
  rw [hsz] at hblen hfit
  have hret : Heap.Retained s₀ p.provenance (placement.addr 0) 4 :=
    ⟨blk, hl, hbptr.trans p_post, by simpa using hblen, Heap.allocationAlive_of_live _ _ hlive⟩
  unfold Slice.end_as_mut_ptr
  have e : s.val.length = new.length := by rw [hslen, hnewlen]
  rw [e]
  simp only [bind_tc_eq, Std.bind_assoc]
  refine DWP.bind_ispec_checked (RawPtr.readRange.spec p new (by omega))
    (Realizes.mono (by iframe) hR) ?_
  rintro values s₁ hR₁ ⟨-, rfl⟩
  rw [Realizes.pure_sep] at hR₁
  obtain ⟨rfl, hR₁⟩ := hR₁
  rw [show (4 : Nat) = new.length from hnewlen.symm] at hR₁
  refine DWP.bind_ispec_checked (RawPtr.endExposure.spec p new (by omega))
    (Realizes.mono (by iframe) hR₁) ?_
  rintro _ s₂ hR₂ hrun
  have hret₂ : Heap.Retained s₂ p.provenance (placement.addr 0) 4 := by
    rw [Heap.endExposureAt_run hrun]; exact hret.retire
  have hmax : new.length ≤ Usize.max := by rw [hnewlen]; scalar_tac
  simp only [hmax, _root_.dite_true, lift]
  -- The second exposure, at the same address
  have hs2 : (Array.as_slice ⟨as_mut_slice_back (Slice.from new hmax)⟩).val.val = new := by
    simp [as_mut_slice_back_post, Array.as_slice, Array.from_slice, Slice.from_val, hnewlen]
  unfold Slice.as_ptr
  simp only [Std.bind_assoc, bind_ok, Std.uncurry_apply_pair]
  rw [hs2]
  refine DWP.bind_ispec_allocating (RawPtr.allocSharedExposure.spec new (placement.addr 1)
    (by omega)) hR₂ ?_
  rintro p1 s₃ hR₃ hx
  have hp1 := State.sharedExposeAt_address hx
  have hret₃ := hret₂.of_extends (State.sharedExposeAt_allocations hx)
  -- The distance from the second exposure to the end of the digits written in the first one
  obtain ⟨a, ha, habptr, halen, haalive⟩ := hret₃
  have hR₃' : Realizes (p1.exposure new.length ∗ (p1.readable 1 new ∗ F)) s₃ :=
    Realizes.mono (entails_of_eq (sep_assoc_eq _ _ _)) hR₃
  obtain ⟨b, hb, hblen, hblive, hbbptr, -⟩ := Realizes.exposure_block hR₃'
  rw [hsz, hnewlen] at hblen
  have hfinaddr : fin.address.val = a.bptr.val + k := by
    rw [hfin, RawPtr.elem_address p k (by rw [hsz]; omega), habptr, ← p_post, hsz,
      Nat.mul_one]
  refine DWP.bind (offset_from_reexposed (count := k) hR₃.1 (by rw [hfin]; exact ha) hb haalive
    hblive hbbptr.symm
    (by rw [habptr, hbbptr, hp1, sameAddress]) (by omega) (by omega) hfinaddr (by omega)
    (by scalar_tac)
    (Q := fun r s' => r.val = k ∧ s' = s₃) (fun r hr => ⟨hr, rfl⟩)) ?_
  rintro i s₄ ⟨hi, rfl⟩
  -- The rest is in separation logic
  refine ispec_iff.mp ?_ F s₄ hR₃
  have hlenv : (IScalar.hcast .Usize i).val = k := by
    have h2 : (4 : Int) ≤ 2 ^ UScalarTy.Usize.numBits := by
      rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.Usize_numBits_eq, h]
    rw [IScalar.hcast_val_eq, hi, Int.emod_eq_of_lt (by omega) (by omega)]
    simp
  step with RawPtr.allocSharedExposure.spec new (placement.addr 2) (by omega) as ⟨p2⟩
  refine ispec_exposure_fit (p := p2) (n := new.length) (by iframe) fun hfit₂ => ?_
  simp only [← hk, ← hnew, hnewlen]
  have hsplit : new = decimalDigits value ++ s.val.val.drop k := hnew
  refine ispec_conseq (P' := p2.readable2 1 1 (decimalDigits value) (s.val.val.drop k) ∗
      (p2.exposure 4 ∗ p1.exposure 4 ∗ p1.readable 1 new)) ?_ ?_ (fun _ => entails_refl _)
  rotate_left
  · refine entails_trans ?_ (sep_mono (RawPtr.readable_split p2 1 _ _
      (by rw [hsz] at hfit₂ ⊢; omega)) (entails_refl _))
    rw [← hsplit]
    iframe
  step with core.slice.raw.from_raw_parts.spec_readable2 p2 (IScalar.hcast .Usize i) 1 1
    (decimalDigits value) (s.val.val.drop k) hlenv bounds.1
  simp only [← hk]
  obtain ⟨S, hSeq⟩ : ∃ S, (Array.as_slice ⟨as_mut_slice_back (Slice.from new hmax)⟩).val = S :=
    ⟨_, rfl⟩
  have hSval : S.val = new := by rw [← hSeq]; exact hs2
  have hSlen : S.length = 4 := by simp [Slice.length, hSval, hnewlen]
  rw [hSeq]
  -- The backward computation
  have hB : ⦃ p2.readable2 (1 + 1) 1 (decimalDigits value) (s.val.val.drop k) ∗
      p2.exposure 4 ∗ p1.exposure 4 ∗ p1.readable 1 new ⦄
      (do
        from_raw_parts_back
        Slice.end_as_ptr Pointee.repr S p2
        Slice.end_as_ptr Pointee.repr S p1
        Result.ok ({ bytes := as_mut_slice_back (Slice.from new hmax) } : DecimalBuffer))
      ⦃ updated => ⌜updated.bytes.val = formatted self.val.bytes.val value⌝ ⦄ := by
    subst from_raw_parts_back_post
    step with RawPtr.endShareRange.spec_readable2 p2 1 1 (decimalDigits value) (s.val.val.drop k)
      (by omega) bounds.1
    refine ispec_conseq (P' := p2.readable 1 new ∗ (p2.exposure 4 ∗ p1.exposure 4 ∗
        p1.readable 1 new)) ?_ ?_ (fun _ => entails_refl _)
    rotate_left
    · rw [hsplit]
      refine entails_trans ?_ (sep_mono (RawPtr.readable2_merge p2 1 _ _) (entails_refl _))
      iframe
    have h₂ := Slice.end_as_ptr.spec S p2 (by omega)
    rw [hSval, hSlen] at h₂
    step with h₂
    have h₁ := Slice.end_as_ptr.spec S p1 (by omega)
    rw [hSval, hSlen] at h₁
    refine ispec_bind h₁ (F := emp) (by iframe) fun _ => ?_
    apply ispec_ok
    intro _ _
    have h4 := decimalDigits_length value
    have h4' : (decimalDigits value).length + (4 - (decimalDigits value).length) = 4 := by omega
    simp [as_mut_slice_back_post, Array.from_slice, Slice.from_val, hnew, formatted,
      s_post, hk, h4']
  apply ispec_ok
  simp only [Std.uncurry_apply_pair]
  apply entails_exists_r (p2.readable2 (1 + 1) 1 (decimalDigits value) (s.val.val.drop k) ∗
      p2.exposure 4 ∗ p1.exposure 4 ∗ p1.readable 1 new)
  refine entails_trans ?_ (entails_trans (entails_trans (pure_sep_intro _ hB)
    (entails_of_eq (sep_comm_eq _ _))) (pure_sep_intro _ s4_post))
  iframe

/-- **Spec theorem for `raw_zmij_mwe::DecimalBuffer::format`** (the statement of
`DecimalBuffer.format.spec` of fournet/wip-memory-model). Conditional on the first two exposures
of the buffer being at the same address, the returned slice is exactly the decimal digits of
`value`, and the backward computation returns the buffer with the digits written at its start,
preserving every frame. -/
theorem DecimalBuffer.format.spec (placement : Placement)
    (sameAddress : placement.addr 0 = placement.addr 1)
    (self : MutBorrow DecimalBuffer) (value : U8) (F : IProp) (s₀ : Heap) (h₀ : Realizes F s₀) :
    DWP effectWP (DecimalBuffer.format placement self value)
      (fun result s₁ => result.1.val.val = decimalDigits value ∧
        DWP effectWP result.2 (fun updated s₂ =>
          updated.bytes.val =
            decimalDigits value ++ self.val.bytes.val.drop (decimalDigits value).length ∧
          Realizes F s₂) s₁) s₀ := by
  have h := ispec_iff.mp (DecimalBuffer.format.sl_spec placement sameAddress self value) F s₀
    (Realizes.mono (entails_of_eq (sep_emp_l_eq F).symm) h₀)
  refine h.mono ?_
  rintro ⟨slice, back⟩ s₁ hR
  simp only [postSep, Std.uncurry_apply_pair] at hR
  obtain ⟨hslice, hR⟩ := Realizes.pure_sep.mp hR
  rw [sep_exists_l_eq] at hR
  obtain ⟨hi, h, ⟨H, hH⟩, hm, ha⟩ := hR
  have hRH : Realizes ((⌜_⌝ ∗ H) ∗ F) s₁ := ⟨hi, h, by rw [sep_comm_eq ⌜_⌝ H]; exact hH, hm, ha⟩
  obtain ⟨hB, hRH⟩ := Realizes.pure_sep.mp hRH
  refine ⟨hslice, (ispec_iff.mp hB F s₁ hRH).mono ?_⟩
  intro updated s₂ hR₂
  exact Realizes.pure_frame hR₂

/-- `DecimalBuffer.format_twice` in separation logic. -/
theorem DecimalBuffer.format_twice.sl_spec (placement : Placement)
    (sameAddress₀ : (placement.sub 0).addr 0 = (placement.sub 0).addr 1)
    (sameAddress₁ : (placement.sub 1).addr 0 = (placement.sub 1).addr 1)
    (buffer : MutBorrow DecimalBuffer) (first second : U8) :
    ⦃ emp ⦄ DecimalBuffer.format_twice placement buffer first second
      ⦃ result => ⌜result.1.1.slice.val = decimalDigits first ∧
        result.1.2.slice.val = decimalDigits second ∧
        result.2.bytes.val = formatted (formatted buffer.val.bytes.val first) second⌝ ⦄ := by
  have hclone : ∀ (l : List U8), ∀ x ∈ l, core.clone.CloneU8.clone (.mk x) = .ok x :=
    fun _ _ _ => rfl
  unfold DecimalBuffer.format_twice
  step with DecimalBuffer.format.sl_spec (placement.sub 0) sameAddress₀ buffer first
    as ⟨s, back, hs, H, hB⟩
  step with alloc.slice.Slice.to_vec_spec _ s (hclone _) as ⟨a, ha⟩
  step with hB as ⟨buffer1, hbuffer1⟩
  step with DecimalBuffer.format.sl_spec (placement.sub 1) sameAddress₁ ⟨buffer1⟩ second
    as ⟨s', back', hs', H', hB'⟩
  step with alloc.slice.Slice.to_vec_spec _ s' (hclone _) as ⟨b, hb⟩
  step with hB' as ⟨buffer2, hbuffer2⟩
  apply ispec_ok
  intro _ _
  simp only [formatted] at hbuffer1 hbuffer2 ⊢
  refine ⟨by rw [← ha, hs], by rw [← hb, hs'], by rw [hbuffer2, hbuffer1]⟩

/-- **Spec theorem for `raw_zmij_mwe::DecimalBuffer::format_twice`** (after
`DecimalBuffer.format_and_return.spec` of fournet/wip-memory-model): formatting twice in the same
buffer, each time with the first two exposures at the same address, returns the two decimal
strings, copied before the buffer is reused, and the buffer, preserving every frame. -/
theorem DecimalBuffer.format_twice.spec (placement : Placement)
    (sameAddress₀ : (placement.sub 0).addr 0 = (placement.sub 0).addr 1)
    (sameAddress₁ : (placement.sub 1).addr 0 = (placement.sub 1).addr 1)
    (buffer : MutBorrow DecimalBuffer) (first second : U8) (F : IProp) (s₀ : Heap)
    (h₀ : Realizes F s₀) :
    DWP effectWP (DecimalBuffer.format_twice placement buffer first second)
      (fun result s₁ => result.1.1.slice.val = decimalDigits first ∧
        result.1.2.slice.val = decimalDigits second ∧
        result.2.bytes.val = formatted (formatted buffer.val.bytes.val first) second ∧
        Realizes F s₁) s₀ := by
  refine (ispec_iff.mp (DecimalBuffer.format_twice.sl_spec placement sameAddress₀ sameAddress₁
    buffer first second) F s₀ (Realizes.mono (entails_of_eq (sep_emp_l_eq F).symm) h₀)).mono ?_
  intro result s₁ h
  obtain ⟨⟨h₁, h₂, h₃⟩, hF⟩ := Realizes.pure_frame h
  exact ⟨h₁, h₂, h₃, hF⟩

end raw_zmij_mwe
