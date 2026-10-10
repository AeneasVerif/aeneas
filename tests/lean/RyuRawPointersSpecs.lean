import RyuRawPointers

open Aeneas Aeneas.Std Aeneas.SepLogic Aeneas.Std.WP Result

namespace ryu_raw_pointers

/-- Write through the pointer to the first slot of a range. -/
theorem write_head.spec {T : Type} [Pointee T] [Pointee.Sized T] [Pointee.NoPointers T]
    (q : MutRawPtr T) (values : List T) (v : T) (h : 0 < values.length) :
    ⦃ q ↦* values ⦄ MutRawPtr.write q v ⦃ q ↦* values.set 0 v ⦄ := by
  simpa using MutRawPtr.write.spec_range q values 0 v h

/-- Negative exponent: writes `'-'` then the digit `c = '0' - k`. -/
theorem write_exponent.spec_neg (k : Isize) (result : MutRawPtr U8) (vs : List U8) (c : U8)
    (hk : -10 < k.val) (hneg : k.val < 0) (hc : c.val = 48 + (-k.val).toNat)
    (hlen : 2 ≤ vs.length) :
    ⦃ result ↦* vs ⦄ write_exponent k result
      ⦃ n => ⌜n = 2#usize⌝ ∗ result ↦* ((vs.set 0 45#u8).set 1 c) ⦄ := by
  unfold write_exponent
  have hc' : k < 0#isize := by scalar_tac
  simp only [hc', ↓reduceIte]
  step with write_head.spec result vs 45#u8 (by scalar_tac)
  step with RawPtr.add.spec result (vs.set 0 45#u8) 1#usize (by simp; scalar_tac)
    (by simp; scalar_tac)
  step* 1
  subst_vars
  step* 1
  have hi : i.val = (-k.val).toNat := by
    rw [i_post, IScalar.hcast_val_eq, x_post, Int.emod_eq_of_lt (by omega) (by simp; omega)]
  step* 1
  have : i1 = c := by scalar_tac
  subst this
  step with MutRawPtr.write.spec_range result (vs.set 0 45#u8) 1 i1 (by simp; scalar_tac)
  step*

/-- Nonnegative exponent: writes the digit `c = '0' + k`. -/
theorem write_exponent.spec_nonneg (k : Isize) (result : MutRawPtr U8) (vs : List U8) (c : U8)
    (hk0 : 0 ≤ k.val) (hk : k.val < 10) (hc : c.val = 48 + k.val.toNat)
    (hlen : 1 ≤ vs.length) :
    ⦃ result ↦* vs ⦄ write_exponent k result
      ⦃ n => ⌜n = 1#usize⌝ ∗ result ↦* vs.set 0 c ⦄ := by
  unfold write_exponent
  have hc' : ¬ k < 0#isize := by scalar_tac
  simp only [hc', ↓reduceIte]
  step* 2
  have hi : i.val = k.val.toNat := by
    rw [i_post, IScalar.hcast_val_eq, Int.emod_eq_of_lt (by omega) (by simp; omega)]
  have : i1 = c := by scalar_tac
  subst this
  step with write_head.spec result vs i1 (by scalar_tac)
  step*

/-- The bytes `write_exponent k` writes, where `c` is the digit `'0' + |k|`. -/
def expBytes (k : Isize) (c : U8) : List U8 := if k.val < 0 then [45#u8, c] else [c]

@[step]
theorem write_exponent.spec (k : Isize) (result : MutRawPtr U8) (vs : List U8) (c : U8)
    (hk : -10 < k.val ∧ k.val < 10) (hc : c.val = 48 + k.val.natAbs) (hlen : 2 ≤ vs.length) :
    ⦃ result ↦* vs ⦄ write_exponent k result
      ⦃ n => ⌜n.val = (expBytes k c).length⌝ ∗
        result ↦* (expBytes k c ++ vs.drop (expBytes k c).length) ⦄ := by
  obtain _ | ⟨a, _ | ⟨b, rest⟩⟩ := vs
  · simp at hlen
  · simp at hlen
  by_cases hneg : k.val < 0
  · apply ispec_mono (write_exponent.spec_neg k result _ c (by omega) hneg (by omega) hlen)
    · iframe
    · simp [expBytes, hneg]; iframe
  · apply ispec_mono (write_exponent.spec_nonneg k result (a :: b :: rest) c (by omega) (by omega)
      (by omega) (by simp))
    · iframe
    · simp [expBytes, hneg]; iframe

@[step]
theorem Buffer.new.spec : ⦃ emp ⦄ Buffer.new ⦃ b => ⌜b.bytes.val = List.replicate 24 0#u8⌝ ⦄ := by
  unfold Buffer.new
  step*
  simp

/- Not specified, for lack of pointer specifications in `Aeneas.Std.RawPtrSpecs`:
- `write_two_digits` reads `DIGIT_TABLE` through `d.add 1`, where `d = p.elem i` points into the
  middle of the readable range of `p` (from `as_ptr`): `RawPtr.add.spec_readable` only offsets the
  start `p` of the range, and there is no rule to split a readable range at `i`.
- `Buffer.format_exponent` (and thus `first_char_of_exponent`) builds a slice with
  `from_raw_parts p1 n` over a prefix of the cells exposed read-only by `as_ptr`: the specification
  of `from_raw_parts` needs an owned range `p1.range depth vs` of exactly `n` values, while
  `as_ptr` gives the readable range `p1.readable 1 vs` of all the values; there is neither a rule to
  split a range into a prefix and a suffix, nor a `from_raw_parts`/`endShareRange` on readable
  ranges. -/

end ryu_raw_pointers
