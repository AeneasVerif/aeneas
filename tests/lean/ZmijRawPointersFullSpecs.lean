import ZmijRawPointersFull

open Aeneas Aeneas.Std Aeneas.SepLogic Aeneas.Std.WP Result

namespace zmij_raw_pointers_full

/-- The little-endian bytes of an integer. -/
abbrev le {ty : UScalarTy} (v : UScalar ty) : List U8 := v.bv.toLEBytes.map UScalar.mk

theorem flatMap_toCells_u8 (bs : List U8) : bs.flatMap Pointee.toCells = bs.map some := by
  induction bs with
  | nil => rfl
  | cons b bs ih => rw [List.flatMap_cons, Pointee.toCells_u8, ih]; rfl

/-- An integer stored in byte cells is the range of its little-endian bytes. -/
theorem pointsTo_cast_eq {M : Mutability} {ty : UScalarTy} (q : RawPtr U8 M) (v : UScalar ty) :
    (q.cast (UScalar ty) ↦ v) = (q ↦* le v) := by
  rw [RawPtr.pointsTo_eq, RawPtr.pointsToRange_eq_cells, RawPtr.pointsToCells_eq_array,
    RawPtr.pointsToCells_eq_array]
  simp [flatMap_toCells_u8]

/-- A range of bytes, seen as the cells of an integer. -/
theorem pointsToRange_eq_cast_cells {M : Mutability} {ty : UScalarTy} (q : RawPtr U8 M)
    (bs : List U8) : (q ↦* bs) = (q.cast (UScalar ty) ↦# bs.map some) := by
  rw [RawPtr.pointsToRange_eq_cells, RawPtr.pointsToCells_eq_array,
    RawPtr.pointsToCells_eq_array]
  simp [flatMap_toCells_u8]

/-- `write_digits` stores the 8 bytes of `digits` at offset `o` (`1` if `has_extra_digit`) and
the digit character `c = '0' + last_digit` at offset `o + 16`. -/
theorem write_digits.spec (buffer : MutRawPtr U8) (b : Bool) (digits : U64) (d c : U8)
    (vs : List U8) (hc : c.val = 48 + d.val) (hlen : b.toNat + 17 ≤ vs.length) :
    ⦃ buffer ↦* vs ⦄ write_digits buffer b digits d
      ⦃ buffer ↦* ((vs.take b.toNat ++ le digits ++ vs.drop (b.toNat + 8)).set
        (b.toNat + 16) c) ⦄ := by
  have hi : (core.convert.num.FromUsizeBool.from b).val = b.toNat := by cases b <;> rfl
  have hd : (le digits).length = 8 := by simp
  have hW : (buffer ↦* (vs.take b.toNat ++ le digits ++ vs.drop (b.toNat + 8))) =
      iprop(buffer ↦* vs.take b.toNat ∗ (buffer.shift b.toNat).cast U64 ↦ digits ∗
        buffer.shift (b.toNat + 8) ↦* vs.drop (b.toNat + 8)) := by
    rw [List.append_assoc, RawPtr.pointsToRange_append, RawPtr.pointsToRange_append,
      pointsTo_cast_eq, RawPtr.shift_shift, hd]
    simp only [List.length_take]
    rw [show min b.toNat vs.length = b.toNat by omega]
  have hV : (buffer ↦* vs) =
      iprop(buffer ↦* vs.take b.toNat ∗ (buffer.shift b.toNat).cast U64 ↦# 
        ((vs.drop b.toNat).take 8).map some ∗
        buffer.shift (b.toNat + 8) ↦* vs.drop (b.toNat + 8)) := by
    rw [RawPtr.pointsToRange_split buffer vs b.toNat,
      RawPtr.pointsToRange_split _ (vs.drop b.toNat) 8, RawPtr.shift_shift, List.drop_drop]
    simp only [List.length_take, List.length_drop]
    rw [show min b.toNat vs.length = b.toNat by omega, show min 8 (vs.length - b.toNat) = 8 by omega,
      pointsToRange_eq_cast_cells (ty := .U64) (buffer.shift b.toNat)]
  unfold write_digits
  simp only [lift]
  step with RawPtr.add.spec buffer vs (core.convert.num.FromUsizeBool.from b) (by omega)
  rw [hV]
  rw [i_post, hi]
  apply WP.ispec_bind (MutRawPtr.write_unaligned.spec_cells ((buffer.shift b.toNat).cast U64)
    (((vs.drop b.toNat).take 8).map some) digits
    (by show (((vs.drop b.toNat).take 8).map some : List (Option U8)).length = 8; simp; omega)
    (by simp))
  · iframe
  · intro _
    apply WP.ispec_mono (Pm := buffer ↦* (vs.take b.toNat ++ le digits ++ vs.drop (b.toNat + 8)))
      (F := emp) ?_ (by rw [hW]; iframe) (by iframe)
    have hwl : (vs.take b.toNat ++ le digits ++ vs.drop (b.toNat + 8)).length = vs.length := by
      simp; omega
    generalize vs.take b.toNat ++ le digits ++ vs.drop (b.toNat + 8) = ws at *
    clear hW hV
    step* 3
    all_goals try scalar_tac
    have : i3 = c := by scalar_tac
    subst this p2_post
    rw [i2_post, hi]
    step with MutRawPtr.write.spec_range buffer ws (b.toNat + 16) i3 (by omega) (by simp)

/-- An integer is the range of its little-endian bytes. -/
theorem pointsTo_eq_bytes {M : Mutability} {ty : UScalarTy} (q : RawPtr (UScalar ty) M)
    (v : UScalar ty) : (q ↦ v) = (q.cast U8 ↦* le v) := by
  rw [← pointsTo_cast_eq]
  rfl

/-- Copying the first `n` bytes of `src` to `dst`. -/
theorem copy_prefix.spec (src : ConstRawPtr U8) (dst : MutRawPtr U8)
    (svs dvs : List U8) (n : Usize) (hn : 0 < n.val) (hs : n.val ≤ svs.length)
    (hd : n.val ≤ dvs.length) :
    ⦃ src ↦* svs ∗ dst ↦* dvs ⦄ core.ptr.copy_nonoverlapping src dst n
      ⦃ src ↦* svs ∗ dst ↦* (svs.take n.val ++ dvs.drop n.val) ⦄ := by
  have h1 : (svs.take n.val).length = n.val := by simp; omega
  have h2 : (dvs.take n.val).length = n.val := by simp; omega
  rw [RawPtr.pointsToRange_split src svs n.val, RawPtr.pointsToRange_split dst dvs n.val,
    RawPtr.pointsToRange_append, h1, h2]
  apply ispec_mono (core.ptr.copy_nonoverlapping.spec src dst (svs.take n.val)
    (dvs.take n.val) n h1 h2 (by simp) (by simp) (by simp; omega) (by simp; omega)) <;> iframe

/-- `write_exponent_data` copies the low 5 bytes of `exp_data` and returns the pointer advanced by
the length stored in the high 16 bits. -/
theorem write_exponent_data.spec (buffer : MutRawPtr U8) (exp_data : U64) (vs : List U8)
    (h5 : 5 ≤ vs.length) (hlen : exp_data.val >>> 48 ≤ vs.length) :
    ⦃ buffer ↦* vs ⦄ write_exponent_data buffer exp_data
      ⦃ r => ⌜r = buffer.shift (exp_data.val >>> 48)⌝ ∗
        buffer ↦* ((le exp_data).take 5 ++ vs.drop 5) ⦄ := by
  unfold write_exponent_data
  step* 3
  rw [pointsTo_eq_bytes]
  step with copy_prefix.spec (p.cast U8) buffer (le exp_data) vs 5#usize (by simp) (by simp)
    (by simpa using h5)
  have hb : exp_data.val >>> 48 < 2 ^ 16 := by rw [Nat.shiftRight_eq_div_pow]; scalar_tac
  have hl : len.val = exp_data.val >>> 48 := by
    simp only [len_post, UScalar.cast_val_eq, i_post]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h] <;> omega
  have hc : len.val ≤ ((le exp_data).take 5 ++ vs.drop 5).length := by simp; omega
  step with RawPtr.add.spec buffer _ len hc
  rw [← pointsTo_eq_bytes]
  subst from_ref_back_post
  step*

/-- `add` from inside a range. -/
theorem add.spec_range {T : Type} [Pointee T] [Pointee.Lawful T] {M : Mutability}
    (q : RawPtr T M) (vs : List T) (i : Nat) (count : Usize) (h : i + count.val ≤ vs.length) :
    ⦃ q ↦* vs ⦄ (q.shift i).add count
      ⦃ r => ⌜r = q.shift (i + count.val)⌝ ∗ q ↦* vs ⦄ := by
  have hi : (vs.take i).length = i := by simp; omega
  rw [RawPtr.pointsToRange_split q vs i, hi]
  apply ispec_mono (RawPtr.add.spec (q.shift i) (vs.drop i) count (by simp; omega))
  · iframe
  · apply postWand_intro
    intro r
    iintro hr
    subst hr
    rw [RawPtr.shift_shift]
    iframe

theorem Pow10SignificandTable.COMPRESS_eq : Pow10SignificandTable.COMPRESS = false := by
  unfold Pow10SignificandTable.COMPRESS; rfl

theorem Pow10SignificandTable.SPLIT_TABLES_eq : Pow10SignificandTable.SPLIT_TABLES = false := by
  unfold Pow10SignificandTable.SPLIT_TABLES; simp

/-- `get_unchecked` reads the two consecutive table entries of index `dec_exp + 293`. -/
theorem Pow10SignificandTable.get_unchecked.spec (self : Pow10SignificandTable) (dec_exp : I32)
    (h1 : -293 ≤ dec_exp.val) (h2 : dec_exp.val ≤ 324) :
    ⦃ emp ⦄ Pow10SignificandTable.get_unchecked self dec_exp
      ⦃ r => ⌜r = { hi := self.data.val[2 * (dec_exp.val + 293).toNat]'(by scalar_tac),
                    lo := self.data.val[2 * (dec_exp.val + 293).toNat + 1]'(by scalar_tac) }⌝ ⦄ := by
  unfold Pow10SignificandTable.get_unchecked
  simp only [Pow10SignificandTable.COMPRESS_eq, Pow10SignificandTable.SPLIT_TABLES_eq,
    Pow10SignificandTable.get_unchecked.DEC_EXP_MIN]
  step* 6
  have hk : i2.val = 2 * (dec_exp.val + 293).toNat := by
    rw [i2_post, IScalar.hcast_val_eq]
    rw [Int.emod_eq_of_lt (by scalar_tac) (by
      rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h] <;> scalar_tac)]
    scalar_tac
  have hl : (self.data.to_slice.val).length = 1236 := by simp
  subst s_post
  step with RawPtr.add.spec p self.data.to_slice.val i2 (by omega)
  subst p1_post
  step with RawPtr.read.spec_range p self.data.to_slice.val i2.val (by omega) p_post
  step with add.spec_range p self.data.to_slice.val i2.val 1#usize (by simp; omega)
  subst p3_post
  step with RawPtr.read.spec_range p self.data.to_slice.val (i2.val + 1) (by simp; omega) p_post
  subst as_ptr_back_post
  step*
  simp only [p2_post, i3_post, hk, Std.Array.to_slice]
  simp

@[step]
theorem umul128_hi64.spec (a b : U64) :
    ⦃ emp ⦄ umul128_hi64 a b ⦃ r => ⌜r.val = a.val * b.val / 2 ^ 64⌝ ⦄ := by
  unfold umul128_hi64 umul128
  have hab : a.val * b.val < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' (by scalar_tac) (by scalar_tac)
  step as ⟨ a', ha ⟩
  step as ⟨ b', hb ⟩
  have ha' : a'.val = a.val := by simp [ha, UScalar.cast_val_eq]; scalar_tac
  have hb' : b'.val = b.val := by simp [hb, UScalar.cast_val_eq]; scalar_tac
  step*

@[step]
theorem Pow10SignificandTable.compute.STRIDE.spec :
    ⦃ emp ⦄ Pow10SignificandTable.compute.STRIDE ⦃ r => ⌜r.val = 28⌝ ⦄ := by
  unfold Pow10SignificandTable.compute.STRIDE
  step*

theorem cast_usize_val (x : U32) : (UScalar.cast .Usize x).val = x.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h] <;> scalar_tac

/-- Normalizes a 192-bit product to the 128 bits below its leading bit (which is bit 190 or 191). -/
def normalize (P : Nat) : Nat := if 2 ^ 191 ≤ P then P / 2 ^ 64 else P / 2 ^ 63

theorem shiftLeft_one_or (a b : Nat) (hb : b < 2) :
    (a <<< 1) % 2 ^ 64 ||| b = (a <<< 1) % 2 ^ 64 + b := by
  have : (a <<< 1) % 2 ^ 64 = (a % 2 ^ 63) <<< 1 := by simp only [Nat.shiftLeft_eq]; omega
  rw [this, Nat.shiftLeft_add_eq_or_of_lt (by omega)]

/-- The 64-bit limb arithmetic of `compute` normalizes the 192-bit product `B * 2^64 + A`. -/
theorem normalize_limbs (A B : Nat) (hA : A ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (hB : B ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (c1 c2 : Nat)
    (hc1 : c1 = (A / 2 ^ 64 + B % 2 ^ 64) % 2 ^ 64)
    (hc2 : c2 = (if c1 < A / 2 ^ 64 then 1 else 0) + B / 2 ^ 64) :
    (c2 >>> 63 ≠ 0 → c2 = normalize (B * 2 ^ 64 + A) / 2 ^ 64 ∧
      c1 = normalize (B * 2 ^ 64 + A) % 2 ^ 64) ∧
    (c2 >>> 63 = 0 →
      ((c2 <<< 1) % 2 ^ 64 ||| c1 >>> 63) = normalize (B * 2 ^ 64 + A) / 2 ^ 64 ∧
      ((c1 <<< 1) % 2 ^ 64 ||| (A % 2 ^ 64) >>> 63) = normalize (B * 2 ^ 64 + A) % 2 ^ 64) := by
  simp only [Nat.shiftRight_eq_div_pow]
  rw [shiftLeft_one_or _ _ (by omega), shiftLeft_one_or _ _ (by omega)]
  simp only [Nat.shiftLeft_eq, normalize]
  split_ifs at hc2 ⊢ <;> omega

/-- `compute i` multiplies the `POW10_MAJOR` and `POW10_MINOR` entries `h` and `m` (read through
raw pointers), normalizes the product and subtracts the fixup bit `i` of `POW10_FIXUPS`. -/
theorem Pow10SignificandTable.compute.spec (i : U32) (hi : i.val < 618) (mn : U64) (mj : uint128)
    (fx : U32) (hm : mn = POW10_MINOR.val[(i.val + 10) % 28]'(by scalar_tac))
    (hh : mj = POW10_MAJOR.val[(i.val + 10) / 28]'(by scalar_tac))
    (hf : fx = POW10_FIXUPS.val[i.val / 32]'(by scalar_tac))
    (hbit : fx.val / 2 ^ (i.val % 32) % 2 ≤ normalize ((mj.hi.val * 2 ^ 64 + mj.lo.val) * mn.val) % 2 ^ 64) :
    ⦃ emp ⦄ Pow10SignificandTable.compute i
      ⦃ r => ⌜r.hi.val = normalize ((mj.hi.val * 2 ^ 64 + mj.lo.val) * mn.val) / 2 ^ 64 ∧
        r.lo.val = normalize ((mj.hi.val * 2 ^ 64 + mj.lo.val) * mn.val) % 2 ^ 64 -
          fx.val / 2 ^ (i.val % 32) % 2⌝ ⦄ := by
  unfold Pow10SignificandTable.compute
  step* 7
  have hl : POW10_MINOR.to_slice.val.length = 28 := by simp
  have hk : i4.val = (i.val + 10) % 28 := by rw [i4_post, cast_usize_val]; scalar_tac
  subst m_post
  subst s_post
  step with RawPtr.read.spec_range p POW10_MINOR.to_slice.val i4.val (by omega) p_post
  step* 5
  subst s1_post
  have hl1 : POW10_MAJOR.to_slice.val.length = 23 := by simp
  have hk1 : i7.val = (i.val + 10) / 28 := by rw [i7_post, cast_usize_val]; scalar_tac
  step with RawPtr.add.spec p1 POW10_MAJOR.to_slice.val i7 (by omega) as ⟨ q, q_post ⟩
  subst q_post
  step with RawPtr.read.spec_range p1 POW10_MAJOR.to_slice.val i7.val (by omega) p1_post
  have hm1 : m1 = mn := by simp [m1_post, hm, hk, Std.Array.to_slice]
  have hh1 : h1 = mj := by simp [h1_post, hh, hk1, Std.Array.to_slice]
  subst hm1 hh1
  have hA : h1.lo.val * m1.val ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by scalar_tac) (by scalar_tac)
  have hB : h1.hi.val * m1.val ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by scalar_tac) (by scalar_tac)
  rw [show (h1.hi.val * 2 ^ 64 + h1.lo.val) * m1.val = h1.hi.val * m1.val * 2 ^ 64 +
    h1.lo.val * m1.val by ring] at hbit ⊢
  step* 7
  case hmax =>
    have := Bool.toNat_le (decide (c1 < h11))
    scalar_tac
  step as ⟨ i11, i11_post ⟩
  have hL := normalize_limbs _ _ hA hB c1.val c2.val
    (by simp [c1_post, i8_post, h11_post, U64.size, U64.numBits])
    (by
      rw [c2_post, i9_post, i10_post, ← h11_post]
      by_cases hc : c1.val < h11.val <;> simp [hc, UScalar.lt_equiv])
  subst as_ptr_back_post as_ptr_back1_post
  apply WP.ispec_bind (F := emp) (Qm := fun (r : U64 × U64) =>
      iprop(⌜r.1.val = normalize (h1.hi.val * m1.val * 2 ^ 64 + h1.lo.val * m1.val) / 2 ^ 64 ∧
        r.2.val = normalize (h1.hi.val * m1.val * 2 ^ 64 + h1.lo.val * m1.val) % 2 ^ 64⌝))
    (Pm := iprop(p1 ↦* POW10_MAJOR.to_slice.val ∗
      RawPtr.freeable p1 POW10_MAJOR.to_slice.length AllocKind.view ∗
      p ↦* POW10_MINOR.to_slice.val ∗
      RawPtr.freeable p POW10_MINOR.to_slice.length AllocKind.view)) ?_ (by iframe)
  · rintro ⟨i12, i13⟩
    rw [WP.ispec_ipure]
    rintro ⟨h12, h13⟩
    step* 4
    subst s2_post
    have hl2 : POW10_FIXUPS.to_slice.val.length = 20 := by simp
    have hk2 : i15.val = i.val / 32 := by
      rw [i15_post, cast_usize_val, i14_post, Nat.shiftRight_eq_div_pow]
    step with RawPtr.add.spec p2 POW10_FIXUPS.to_slice.val i15 (by omega)
    subst p3_post
    apply WP.ispec_bind (RawPtr.read.spec_range p2 POW10_FIXUPS.to_slice.val i15.val (by omega) p2_post)
    · iframe
    intro i16
    rw [sep_assoc_eq, WP.ispec_ipure]
    intro hi16
    have hf1 : i16 = fx := by simp [hi16, hf, hk2, Std.Array.to_slice]
    subst hf1
    have hbit' : (i16.val >>> (i.val &&& 31)) &&& 1 ≤ i13.val := by
      rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow,
        show (31 : Nat) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, h13]
      exact hbit
    subst as_ptr_back2_post
    step*
    · rw [i17_post, UScalar.val_and]
      exact Nat.lt_of_le_of_lt Nat.and_le_right (by simp)
    · have h17 : i17.val = i.val % 32 := by
        rw [i17_post, UScalar.val_and, show (31#u32).val = 2 ^ 5 - 1 from rfl,
          Nat.and_two_pow_sub_one_eq_mod]
      have h20 : i20.val = i16.val / 2 ^ (i.val % 32) % 2 := by
        rw [i20_post, UScalar.cast_val_eq, i19_post, UScalar.val_and, show (1#u32).val = 1 from rfl,
          Nat.and_one_is_mod, i18_post, Nat.shiftRight_eq_div_pow, h17]
        apply Nat.mod_eq_of_lt
        simp [UScalarTy.numBits]
        omega
      exact ⟨h12, by rw [i21_post, h20, h13]⟩
  · split
    · step*
    · step*
      have hc0 : c0.val = h1.lo.val * m1.val % 2 ^ 64 := by simp [c0_post, U64.size, U64.numBits]
      simp only [i16_post, i19_post, UScalar.val_or, i14_post, i15_post, i17_post, i18_post, hc0,
        U64.size, U64.numBits]
      apply hL.2
      simp_all
end zmij_raw_pointers_full
