import RyuRawPointersFull

open Aeneas Aeneas.Std Aeneas.SepLogic Aeneas.Std.WP Result

namespace ryu_raw_pointers_full

/-- The ASCII digit `'0' + d % 10`. -/
def digit (d : Nat) : U8 := UScalar.ofNatCore (48 + d % 10) (by simp; omega)

@[simp] theorem digit_val (d : Nat) : (digit d).val = 48 + d % 10 := rfl

theorem digit_eq {m n : Nat} (h : m % 10 = n % 10) : digit m = digit n :=
  UScalar.eq_of_val_eq (by simp [h])

theorem aligned_u8 {M} (q : RawPtr U8 M) : q.Aligned := by simp

set_option maxRecDepth 100000 in
theorem DIGIT_TABLE_spec (d : Nat) (hd : d < 100) :
    (digit_table.DIGIT_TABLE.to_slice.val)[2 * d]'(by simp; omega) = digit (d / 10) ∧
      (digit_table.DIGIT_TABLE.to_slice.val)[2 * d + 1]'(by simp; omega) = digit d := by
  unfold digit_table.DIGIT_TABLE
  revert d
  simp only [Array.to_slice, Array.make]
  decide +kernel

/-- Copying two bytes from `src[j..j+2]` to `dst[i..i+2]`. -/
theorem copy2.spec (src : ConstRawPtr U8) (dst : MutRawPtr U8) (svs dvs : List U8) (j i : Nat)
    (hj : j + 2 ≤ svs.length) (hi : i + 2 ≤ dvs.length) :
    ⦃ src ↦* svs ∗ dst ↦* dvs ⦄ core.ptr.copy_nonoverlapping (src.shift j) (dst.shift i) 2#usize
      ⦃ src ↦* svs ∗ dst ↦* ((dvs.set i svs[j]).set (i + 1) svs[j + 1]) ⦄ := by
  have hs := RawPtr.pointsToRange_split src svs j
  have hs2 := RawPtr.pointsToRange_split (src.shift (svs.take j).length) (svs.drop j) 2
  have hd := RawPtr.pointsToRange_split dst dvs i
  have hd2 := RawPtr.pointsToRange_split (dst.shift (dvs.take i).length) (dvs.drop i) 2
  have hd' := RawPtr.pointsToRange_split dst ((dvs.set i svs[j]).set (i + 1) svs[j + 1]) i
  have hd2' := RawPtr.pointsToRange_split (dst.shift (dvs.take i).length)
    (((dvs.set i svs[j]).set (i + 1) svs[j + 1]).drop i) 2
  simp only [List.length_take, List.length_drop, RawPtr.shift_shift, List.length_set] at *
  rw [show min j svs.length = j by omega, show min 2 (svs.length - j) = 2 by omega] at *
  rw [show min i dvs.length = i by omega, show min 2 (dvs.length - i) = 2 by omega] at *
  rw [hs, hs2, hd, hd2, hd', hd2']
  apply ispec_mono (core.ptr.copy_nonoverlapping.spec (src.shift j) (dst.shift i)
    ((svs.drop j).take 2) ((dvs.drop i).take 2) 2#usize (by simp; omega) (by simp; omega)
    (aligned_u8 _) (aligned_u8 _) (by simp) (by simp))
  · iframe
  · have h1 : ((dvs.set i svs[j]).set (i + 1) svs[j + 1]).take i = dvs.take i := by
      rw [List.take_set_of_le (by omega), List.take_set_of_le (by omega)]
    have h2 : ((((dvs.set i svs[j]).set (i + 1) svs[j + 1]).drop i).take 2) =
        (svs.drop j).take 2 := by
      apply List.ext_getElem
      · simp; omega
      · intro n h1 h2; simp at h1; simp [List.getElem_set]
        rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
        · simp
        · simp
    have h3 : ((((dvs.set i svs[j]).set (i + 1) svs[j + 1]).drop i).drop 2) =
        (dvs.drop i).drop 2 := by
      rw [List.drop_drop, List.drop_set_of_lt (by omega), List.drop_set_of_lt (by omega),
        List.drop_drop]
    rw [h1, h2, h3]
    iframe

theorem hcast_usize_val (x : Isize) (h : 0 ≤ x.val) :
    (IScalar.hcast .Usize x).val = x.val.toNat := by
  have hx : x.val ≤ Isize.max := by scalar_tac
  rw [IScalar.hcast_val_eq, Int.emod_eq_of_lt h]
  rw [Isize.max] at hx
  simp only [Isize.numBits, UScalarTy.Usize_numBits_eq] at *
  cases System.Platform.numBits_eq <;> simp_all <;> omega

theorem isize_max_usize_max : 2 * Isize.max + 1 = Usize.max := by
  rw [Isize.max, Usize.max]
  simp only [Isize.numBits, Usize.numBits, UScalarTy.Usize_numBits_eq]
  cases System.Platform.numBits_eq <;> simp_all

theorem offset0.spec {M} (q : RawPtr U8 M) (vs : List U8) (c : Isize) (h0 : 0 ≤ c.val)
    (h : c.val ≤ vs.length) :
    ⦃ q ↦* vs ⦄ q.offsetBy c ⦃ r => ⌜r = q.shift c.val.toNat⌝ ∗ q ↦* vs ⦄ := by
  have := RawPtr.offset.spec q vs 0 c (by simp) (by simpa) (by simpa)
  simpa only [RawPtr.shift_zero, Nat.cast_zero, Int.zero_add] using this

/-- Copying all of `svs` to `dst[i..i+count]`. -/
theorem copy_into.spec (src : ConstRawPtr U8) (dst : MutRawPtr U8) (svs dvs : List U8) (i : Nat)
    (count : Usize) (hc : svs.length = count.val) (hpos : 0 < count.val)
    (hi : i + count.val ≤ dvs.length) :
    ⦃ src ↦* svs ∗ dst ↦* dvs ⦄ core.ptr.copy_nonoverlapping src (dst.shift i) count
      ⦃ src ↦* svs ∗ dst ↦* (dvs.take i ++ svs ++ dvs.drop (i + count.val)) ⦄ := by
  have hd := RawPtr.pointsToRange_split dst dvs i
  have hd2 := RawPtr.pointsToRange_split (dst.shift (dvs.take i).length) (dvs.drop i) count.val
  simp only [List.length_take, List.length_drop, RawPtr.shift_shift, List.drop_drop] at hd hd2
  simp only [show min i dvs.length = i by omega,
    show min count.val (dvs.length - i) = count.val by omega] at hd hd2
  rw [hd, hd2, RawPtr.pointsToRange_append, RawPtr.pointsToRange_append]
  apply ispec_mono (core.ptr.copy_nonoverlapping.spec src (dst.shift i) svs
    ((dvs.drop i).take count.val) count hc (by simp; omega) (aligned_u8 _) (aligned_u8 _)
    (by simp; omega) (by simp; omega))
  · iframe
  · simp only [List.length_append, List.length_take, hc]
    rw [show min i dvs.length = i by omega]
    iframe

/-- Copying the two digits of `d < 100` from `DIGIT_TABLE` (at index `j = 2 * d`) to `dst[i..i+2]`. -/
theorem copy_digits.spec (p : ConstRawPtr U8) (dst : MutRawPtr U8) (vs : List U8) (j d i : Nat)
    (hj : j = 2 * d) (hd : d < 100) (hi : i + 2 ≤ vs.length) :
    ⦃ p ↦* digit_table.DIGIT_TABLE.to_slice.val ∗ dst ↦* vs ⦄
      core.ptr.copy_nonoverlapping (p.shift j) (dst.shift i) 2#usize
      ⦃ p ↦* digit_table.DIGIT_TABLE.to_slice.val ∗
        dst ↦* ((vs.set i (digit (d / 10))).set (i + 1) (digit d)) ⦄ := by
  subst hj
  obtain ⟨h0, h1⟩ := DIGIT_TABLE_spec d hd
  rw [← h0, ← h1]
  exact copy2.spec p dst _ vs (2 * d) i (by simp; omega) hi

theorem add_shift.spec {M} (q : RawPtr U8 M) (vs : List U8) (i : Nat) (c : Usize)
    (h : i + c.val ≤ vs.length) :
    ⦃ q ↦* vs ⦄ (q.shift i).add c ⦃ r => ⌜r = q.shift (i + c.val)⌝ ∗ q ↦* vs ⦄ := by
  have hSplit := RawPtr.pointsToRange_split q vs i
  rw [show (vs.take i).length = i by simp; omega] at hSplit
  rw [hSplit]
  apply ispec_mono (RawPtr.add.spec (q.shift i) (vs.drop i) c (by simp; omega))
  · iframe
  · rw [RawPtr.shift_shift]; iframe

/-- The decimal digits of `n < 1000`. -/
def digits (n : Nat) : List U8 :=
  if 100 ≤ n then [digit (n / 100), digit (n / 10), digit n]
  else if 10 ≤ n then [digit (n / 10), digit n] else [digit n]

/-- The sign written for the exponent `k`. -/
def sign (k : Int) : List U8 := if k < 0 then [45#u8] else []

/-- The bytes written for the exponent `k`: an optional `'-'` followed by the digits of `|k|`. -/
def expBytes (k : Int) : List U8 := sign k ++ digits k.natAbs

/-- The sign prefix shared by `write_exponent3`/`write_exponent2`. -/
theorem expBytes_length_le (k : Int) : (expBytes k).length ≤ 4 := by
  simp only [expBytes, sign, digits]; split_ifs <;> simp

theorem write_sign.spec (k : Isize) (result : MutRawPtr U8) (vs : List U8)
    (hk : -1000 < k.val) (hlen : 1 ≤ vs.length) :
    ⦃ result ↦* vs ⦄
      (if k < 0#isize then do
        MutRawPtr.write result 45#u8
        let result2 ← RawPtr.add result 1#usize
        let k2 ← -. k
        ok (k2, result2)
      else ok (k, result) : Result (Isize × MutRawPtr U8))
      ⦃ r => ⌜r.1.val = k.val.natAbs ∧ r.2 = result.shift (sign k.val).length⌝ ∗
        result ↦* (sign k.val ++ vs.drop (sign k.val).length) ⦄ := by
  split
  · step with MutRawPtr.write.spec_head result vs 45#u8 (by omega) (aligned_u8 _)
    step*
    have hs : sign k.val = [45#u8] := by simp [sign]; scalar_tac
    rw [hs]
    obtain _ | ⟨a, rest⟩ := vs
    · simp at hlen
    exact pure_sep_intro _ ⟨by scalar_tac, result2_post⟩
  · step*
    have hs : sign k.val = [] := by simp [sign]; scalar_tac
    rw [hs]
    exact pure_sep_intro _ ⟨by scalar_tac, rfl⟩

theorem sign_length_le (k : Int) : (sign k).length ≤ 1 := by simp [sign]; split <;> simp

/-- The tail shared by `write_exponent3`/`write_exponent2`: writes `|k| < 100` after the sign. -/
theorem write_digits_lt100.spec (k k1 : Isize) (result : MutRawPtr U8) (vs : List U8)
    (hk1 : k1.val = k.val.natAbs) (hk : k.val.natAbs < 100) (hlen : 3 ≤ vs.length) :
    ⦃ result ↦* (sign k.val ++ vs.drop (sign k.val).length) ⦄
      (if k1 >= 10#isize then do
        let s ← lift (Array.to_slice digit_table.DIGIT_TABLE)
        let (p, as_ptr_back) ← Slice.as_ptr s
        let i ← k1 * 2#isize
        let d ← RawPtr.offsetBy p i
        core.ptr.copy_nonoverlapping d (result.shift (sign k.val).length) 2#usize
        let i1 ← lift (UScalar.cast_fromBool .Usize (k < 0#isize))
        let i2 ← i1 + 2#usize
        as_ptr_back
        ok i2
      else do
        let i ← lift (IScalar.hcast .U8 k1)
        let i1 ← 48#u8 + i
        MutRawPtr.write (result.shift (sign k.val).length) i1
        let i2 ← lift (UScalar.cast_fromBool .Usize (k < 0#isize))
        i2 + 1#usize)
      ⦃ n => ⌜n.val = (expBytes k.val).length⌝ ∗ result ↦* (expBytes k.val ++ vs.drop (expBytes k.val).length) ⦄ := by
  obtain ⟨a, b, c, rest, rfl⟩ : ∃ a b c rest, vs = a :: b :: c :: rest := by
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
      first | exact ⟨_, _, _, _, rfl⟩ | simp at hlen
  have hs := sign_length_le k.val
  have hlt : k < 0#isize ↔ k.val < 0 := by scalar_tac
  have h100 : ¬ 100 ≤ k.val.natAbs := by omega
  split
  · step* 3
    subst s_post
    step with offset0.spec p digit_table.DIGIT_TABLE.to_slice.val i (by scalar_tac)
      (by simp; scalar_tac)
    subst d_post
    step with copy_digits.spec p result (sign k.val ++ (a :: b :: c :: rest).drop (sign k.val).length)
      i.val.toNat k.val.natAbs
      (sign k.val).length (by scalar_tac) hk (by simp; omega)
    step* 1
    have hi1 : i1.val ≤ 1 := by rw [i1_post]; exact Bool.toNat_le _
    subst as_ptr_back_post
    step*
    have h10 : 10 ≤ k.val.natAbs := by scalar_tac
    by_cases hneg : k.val < 0 <;> simp [expBytes, sign, digits, hneg, h10, h100, hlt] at i1_post ⊢ <;>
      exact pure_sep_intro _ (by omega)
  · have h10 : ¬ 10 ≤ k.val.natAbs := by scalar_tac
    step* 1
    have hi : i.val = k.val.natAbs := by
      rw [i_post, IScalar.hcast_val_eq]; simp [UScalarTy.numBits]; scalar_tac
    step* 1
    step with MutRawPtr.write.spec_range result (sign k.val ++ (a :: b :: c :: rest).drop (sign k.val).length)
      (sign k.val).length i1 (by simp; omega)
      (aligned_u8 _)
    step* 1
    have hi2 : i2.val ≤ 1 := by rw [i2_post]; exact Bool.toNat_le _
    step*
    have hi1 : i1 = digit k.val.natAbs := UScalar.eq_of_val_eq (by simp; omega)
    rw [hi1]
    by_cases hneg : k.val < 0 <;> simp [expBytes, sign, digits, hneg, h10, h100, hlt] at i2_post ⊢ <;>
      exact pure_sep_intro _ (by omega)

theorem write_exponent3.spec (k : Isize) (result : MutRawPtr U8) (vs : List U8)
    (hk : -1000 < k.val ∧ k.val < 1000) (hlen : 4 ≤ vs.length) :
    ⦃ result ↦* vs ⦄ pretty.exponent.write_exponent3 k result
      ⦃ n => ⌜n.val = (expBytes k.val).length⌝ ∗ result ↦* (expBytes k.val ++ vs.drop (expBytes k.val).length) ⦄ := by
  unfold pretty.exponent.write_exponent3
  step with write_sign.spec k result vs hk.1 (by omega)
  subst result1_post
  have : k1 < 1000#isize := by scalar_tac
  step* 1
  split
  · obtain ⟨a, b, c, d, rest, rfl⟩ : ∃ a b c d rest, vs = a :: b :: c :: d :: rest := by
      rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
        first | exact ⟨_, _, _, _, _, rfl⟩ | simp at hlen
    have hs := sign_length_le k.val
    have hlt : k < 0#isize ↔ k.val < 0 := by scalar_tac
    have h100 : 100 ≤ k.val.natAbs := by scalar_tac
    generalize hws : sign k.val ++ (a :: b :: c :: d :: rest).drop (sign k.val).length = ws
    have hlen' : ws.length = 4 + rest.length := by
      rw [← hws]; simp [sign]; split <;> simp <;> omega
    have hk1' : 0 ≤ k1.val := by scalar_tac
    step* 2
    rw [Int.tdiv_eq_ediv_of_nonneg hk1'] at i_post
    have hi1 : i1.val = k.val.natAbs / 100 := by
      rw [i1_post, IScalar.hcast_val_eq]; simp [UScalarTy.numBits]; omega
    step* 1
    step with MutRawPtr.write.spec_range result ws (sign k.val).length i2 (by omega) (aligned_u8 _)
    step* 4
    rw [Int.tmod_eq_emod_of_nonneg hk1'] at k2_post
    subst s_post
    step with offset0.spec p digit_table.DIGIT_TABLE.to_slice.val i3 (by scalar_tac)
      (by simp; scalar_tac)
    step with add_shift.spec result (ws.set (sign k.val).length i2) (sign k.val).length 1#usize
      (by simp; omega)
    subst d_post p1_post
    step with copy_digits.spec p result (ws.set (sign k.val).length i2)
      i3.val.toNat (k.val.natAbs % 100) ((sign k.val).length + 1)
      (by scalar_tac) (by omega) (by simp; omega)
    step* 1
    have hi4 : i4.val ≤ 1 := by rw [i4_post]; exact Bool.toNat_le _
    subst as_ptr_back_post
    step*
    have hi2 : i2 = digit (k.val.natAbs / 100) := UScalar.eq_of_val_eq (by simp; omega)
    rw [hi2, digit_eq (m := k.val.natAbs % 100 / 10) (n := k.val.natAbs / 10) (by omega),
      digit_eq (m := k.val.natAbs % 100) (n := k.val.natAbs) (by omega)]
    subst hws
    by_cases hneg : k.val < 0 <;> simp [expBytes, sign, digits, hneg, h100, hlt] at i4_post ⊢ <;>
      exact pure_sep_intro _ (by omega)
  · exact write_digits_lt100.spec k k1 result vs k1_post (by scalar_tac) (by omega)

/-- `write_exponent3` at offset `j` of a range. -/
theorem write_exponent3.spec_at (k : Isize) (result : MutRawPtr U8) (vs : List U8) (j : Nat)
    (hk : -1000 < k.val ∧ k.val < 1000) (hlen : j + 4 ≤ vs.length) :
    ⦃ result ↦* vs ⦄ pretty.exponent.write_exponent3 k (result.shift j)
      ⦃ n => ⌜n.val = (expBytes k.val).length⌝ ∗
        result ↦* (vs.take j ++ expBytes k.val ++ vs.drop (j + (expBytes k.val).length)) ⦄ := by
  have hd := RawPtr.pointsToRange_split result vs j
  simp only [List.length_take, show min j vs.length = j by omega] at hd
  rw [hd]
  apply ispec_mono (write_exponent3.spec k (result.shift j) (vs.drop j) hk (by simp; omega))
  · iframe
  · rw [List.drop_drop]
    simp only [List.append_assoc, RawPtr.pointsToRange_append, List.length_take,
      show min j vs.length = j by omega, RawPtr.shift_shift]
    iframe

theorem write_exponent2.spec (k : Isize) (result : MutRawPtr U8) (vs : List U8)
    (hk : -100 < k.val ∧ k.val < 100) (hlen : 3 ≤ vs.length) :
    ⦃ result ↦* vs ⦄ pretty.exponent.write_exponent2 k result
      ⦃ n => ⌜n.val = (expBytes k.val).length⌝ ∗ result ↦* (expBytes k.val ++ vs.drop (expBytes k.val).length) ⦄ := by
  unfold pretty.exponent.write_exponent2
  step with write_sign.spec k result vs (by omega) (by omega)
  subst result1_post
  have : k1 < 100#isize := by scalar_tac
  step* 1
  exact write_digits_lt100.spec k k1 result vs k1_post (by scalar_tac) hlen

theorem format64_zero.spec (sign : Bool) (result : MutRawPtr U8) (vs : List U8)
    (hlen : 4 ≤ vs.length) :
    ⦃ result ↦* vs ⦄ pretty.format64_zero sign result
      ⦃ n => ⌜n.val = sign.toNat + 3⌝ ∗
        result ↦* ((if sign then [45#u8] else []) ++ [48#u8, 46#u8, 48#u8] ++
          vs.drop (sign.toNat + 3)) ⦄ := by
  obtain ⟨a, b, c, d, rest, rfl⟩ : ∃ a b c d rest, vs = a :: b :: c :: d :: rest := by
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
      first | exact ⟨_, _, _, _, _, rfl⟩ | simp at hlen
  unfold pretty.format64_zero
  cases sign <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · step* 2
    step with offset0.spec result (a :: b :: c :: d :: rest) 0#isize (by simp) (by simp; omega)
    subst p1_post
    step with copy_into.spec p result s.val (a :: b :: c :: d :: rest) 0 3#usize (by simp [s_post]) (by simp) (by simp)
    subst as_ptr_back_post s_post
    step*
  · step with MutRawPtr.write.spec_head result (a :: b :: c :: d :: rest) 45#u8 (by simp)
      (aligned_u8 _)
    step* 3
    step with offset0.spec result ((a :: b :: c :: d :: rest).set 0 45#u8) index (by scalar_tac)
      (by simp; scalar_tac)
    subst p1_post
    step with copy_into.spec p result s.val ((a :: b :: c :: d :: rest).set 0 45#u8)
      index.val.toNat 3#usize (by simp [s_post]) (by simp)
      (by simp; scalar_tac)
    subst as_ptr_back_post s_post
    step*
    rw [show (↑index : Int).toNat = 1 by scalar_tac]
    simp
    exact pure_sep_intro _ (by simp at i_post; omega)

/-- `format64_exp` moves the first digit (at `ix + 1`) to `ix`, writes `'.'` after it, `'e'` after
the `len` digits, then the exponent `kk - 1`. -/
theorem format64_exp.spec (result : MutRawPtr U8) (index length kk : Isize) (vs : List U8)
    (ix len : Nat) (hix : index.val = ix) (hlen : length.val = len)
    (hb : ix + len + 2 ≤ Isize.max) (hk : -1000 < kk.val - 1 ∧ kk.val - 1 < 1000)
    (hvs : ix + len + 6 ≤ vs.length) :
    ⦃ result ↦* vs ⦄ pretty.format64_exp result index length kk
      ⦃ n => ⌜n.val = ix + len + 2 + (expBytes (kk.val - 1)).length⌝ ∗
        result ↦* (let ws := ((vs.set ix vs[ix + 1]).set (ix + 1) 46#u8).set (ix + len + 1) 101#u8
          ws.take (ix + len + 2) ++ expBytes (kk.val - 1) ++
            ws.drop (ix + len + 2 + (expBytes (kk.val - 1)).length)) ⦄ := by
  unfold pretty.format64_exp
  have h0 : 0 ≤ index.val := by omega
  have h1 : 0 ≤ length.val := by omega
  step* 1
  case hmin => scalar_tac
  step with offset0.spec result vs i (by scalar_tac) (by scalar_tac)
  rw [show i.val.toNat = ix + 1 by scalar_tac] at p_post
  subst p_post
  step with RawPtr.read.spec_range result vs (ix + 1) (by omega) (aligned_u8 _)
  step with offset0.spec result vs index (by scalar_tac) (by scalar_tac)
  rw [show index.val.toNat = ix by scalar_tac] at p1_post
  subst p1_post i1_post
  step with MutRawPtr.write.spec_range result vs ix _ (by omega) (aligned_u8 _)
  step with offset0.spec result (vs.set ix vs[ix + 1]) i (by scalar_tac) (by simp; scalar_tac)
  rw [show i.val.toNat = ix + 1 by scalar_tac] at p2_post
  subst p2_post
  step with MutRawPtr.write.spec_range result (vs.set ix vs[ix + 1]) (ix + 1) 46#u8
    (by simp; omega) (aligned_u8 _)
  step* 2
  case hmin => scalar_tac
  case hmin => scalar_tac
  step with offset0.spec result ((vs.set ix vs[ix + 1]).set (ix + 1) 46#u8) i3 (by scalar_tac)
    (by simp; scalar_tac)
  rw [show i3.val.toNat = ix + len + 1 by scalar_tac] at p3_post
  subst p3_post
  step with MutRawPtr.write.spec_range result ((vs.set ix vs[ix + 1]).set (ix + 1) 46#u8)
    (ix + len + 1) 101#u8 (by simp; omega) (aligned_u8 _)
  step* 2
  have hi4 := hcast_usize_val index h0
  have hi5 := hcast_usize_val length h1
  have hmx := isize_max_usize_max
  subst i4_post i5_post
  step* 4
  case hmax => scalar_tac
  case hmax => scalar_tac
  all_goals try (case hmin => scalar_tac)
  step with offset0.spec result
    (((vs.set ix vs[ix + 1]).set (ix + 1) 46#u8).set (ix + len + 1) 101#u8) i9 (by scalar_tac)
    (by simp; scalar_tac)
  rw [show i9.val.toNat = ix + len + 2 by scalar_tac] at p4_post
  subst p4_post
  step with write_exponent3.spec_at i8 result
    (((vs.set ix vs[ix + 1]).set (ix + 1) 46#u8).set (ix + len + 1) 101#u8) (ix + len + 2)
    (by scalar_tac) (by simp; omega)
  have hE := expBytes_length_le (kk.val - 1)
  rw [i8_post] at i10_post ⊢
  step*
  all_goals scalar_tac

end ryu_raw_pointers_full
