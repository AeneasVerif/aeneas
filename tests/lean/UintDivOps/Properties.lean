module
public import Aeneas
public import UintDivOps.UintDivOps
public section

open Aeneas Aeneas.Std Result

/-! Proofs about the extracted `tests/src/uint-div-ops.rs`, using the specification theorems of the
model of `div_ceil` (one `@[step]` theorem per unsigned width) through `step`. -/

namespace uint_div_ops

/-- The example of the documentation of `div_ceil`: `7.div_ceil(4) = 2`. -/
theorem ceil_u8_doc : ceil_u8 7#u8 4#u8 ⦃ z => z.val = 2 ⦄ := by
  unfold ceil_u8
  step*

theorem ceil_u8_spec (x y : U8) (hy : y.val ≠ 0) :
    ceil_u8 x y ⦃ z => x.val ≤ z.val * y.val ∧ z.val * y.val < x.val + y.val ⦄ := by
  unfold ceil_u8
  step*

theorem ceil_u16_spec (x y : U16) (hy : y.val ≠ 0) :
    ceil_u16 x y ⦃ z => x.val ≤ z.val * y.val ∧ z.val * y.val < x.val + y.val ⦄ := by
  unfold ceil_u16
  step*

theorem ceil_u32_spec (x y : U32) (hy : y.val ≠ 0) :
    ceil_u32 x y ⦃ z => x.val ≤ z.val * y.val ∧ z.val * y.val < x.val + y.val ⦄ := by
  unfold ceil_u32
  step*

theorem ceil_u64_spec (x y : U64) (hy : y.val ≠ 0) :
    ceil_u64 x y ⦃ z => x.val ≤ z.val * y.val ∧ z.val * y.val < x.val + y.val ⦄ := by
  unfold ceil_u64
  step*

theorem ceil_u128_spec (x y : U128) (hy : y.val ≠ 0) :
    ceil_u128 x y ⦃ z => x.val ≤ z.val * y.val ∧ z.val * y.val < x.val + y.val ⦄ := by
  unfold ceil_u128
  step*

theorem ceil_usize_spec (x y : Usize) (hy : y.val ≠ 0) :
    ceil_usize x y ⦃ z => x.val ≤ z.val * y.val ∧ z.val * y.val < x.val + y.val ⦄ := by
  unfold ceil_usize
  step*

/-- `num_chunks len chunk` chunks hold the `len` elements, and one chunk fewer wouldn't. -/
theorem num_chunks_spec (len chunk : Usize) (h : chunk.val ≠ 0) :
    num_chunks len chunk ⦃ n => len.val ≤ n.val * chunk.val ∧
      n.val * chunk.val < len.val + chunk.val ⦄ := by
  unfold num_chunks
  step*

end uint_div_ops
