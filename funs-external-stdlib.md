# Aeneas stdlib model coverage tracker

Tracks the Lean models we're adding for Rust `core`/`alloc` stdlib items that
currently appear as `axiom`s in downstream `FunsExternal.lean` files.

## Conventions

- **Docs** column links to `doc.rust-lang.org/...`.
- **Source** column links to `github.com/rust-lang/rust/blob/1.85.0/...`. The
  Rust version pinned for the source links is `1.85.0` — a stable release near
  Charon's current target (`nightly-2026-02-07`, see
  [charon-pin](charon-pin)). These functions are stable and unchanged across
  recent Rust versions.
- **Status**:
  - ⬜ pending
  - 🟡 model written; test/proof incomplete
  - ✅ complete (model + `@[step]` spec + verbatim-docs `#[verify::test]` + proof)
  - ⏸ deferred
- **Deps** lists other stdlib items whose models are needed so the docs example
  translates — added alongside the target function when not already present.

## Verification chain per function

For each ✅ row, a reviewer can chase the links:

1. **Docs** → Rust's English description of the function.
2. **Source** → the Rust implementation at the pinned commit.
3. **Lean file** → our model, with docstring re-linking to Docs + Source.
4. **Test file** (`tests/src/...`) → the verbatim docs example as a `#[verify::test]`.
5. **Proof** (`tests/lean/...Proofs.lean`) → machine-checked proof that the
   example evaluates correctly under our model.

---

## Summary

| Group | Count | Done |
|---|---:|---:|
| Foundation (cascade deps for other entries) | 3 | 1 |
| Option methods | 5 | 5 |
| Result methods | 5 | 5 |
| Vec methods | 8 | 0 |
| VecDeque (new type + methods) | 3 | 0 |
| Slice methods | 6 | 0 |
| Range (RangeFull index, RangeFrom bounds, Range Iterator) | 7 | 0 |
| Iterator adapters/collect/defaults | 8 | 1 |
| Array (from_fn, PartialEq) | 2 | 0 |
| i32 Iter::Step trait | 3 | 0 |
| Cmp/Eq/Borrow traits | 3 | 0 |
| Misc (black_box, TryFrom, to_owned) | 3 | 0 |
| Deferred (fmt) | 2 | — |
| **Total** | **58** | **11** |

---

## Foundation layer

Items discovered during the dep survey that are not in the original list but
are required so that verbatim docs examples of other items translate.

| Rust item | Lean name | Docs | Source | Status | Needed by | Lean file | Test file | Proof |
|---|---|---|---|---|---|---|---|---|
| `char` (primitive) + `PartialEq<char> for char::eq` | `Char` + `Char.Insts.CoreCmpPartialEqChar.eq` | [docs](https://doc.rust-lang.org/core/primitive.char.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/cmp.rs) | ⬜ | `Iterator::enumerate` docs example | — | — | — |
| `core::array::iter::IntoIter<T, N>` + `Array::into_iter` + `Iterator for IntoIter` | `core.array.iter.IntoIter` + `Array::into_iter` + trait impl | [docs](https://doc.rust-lang.org/core/array/iter/struct.IntoIter.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/array/iter.rs) | ⬜ | `Iterator::enumerate` docs example | — | — | — |
| `PartialEq<Option<T>> for Option<T>::eq` | `core.option.Option.Insts.CoreCmpPartialEqOption.eq` | [docs](https://doc.rust-lang.org/core/option/enum.Option.html#impl-PartialEq-for-Option%3CT%3E) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/option.rs) | ✅ | — | [Core/Core.lean](backends/lean/Aeneas/Std/Core/Core.lean) | [tests/src/option_methods.rs](tests/src/option_methods.rs) | — |

---

## Option methods

| Rust item | Lean name | Docs | Source | Status | Deps | Lean file | Test file | Proof |
|---|---|---|---|---|---|---|---|---|
| `Option::as_ref` | `core.option.Option.as_ref` | [docs](https://doc.rust-lang.org/core/option/enum.Option.html#method.as_ref) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/option.rs) | ✅ | — | [Core/Core.lean](backends/lean/Aeneas/Std/Core/Core.lean) | [tests/src/option_methods.rs](tests/src/option_methods.rs) | — |
| `Option::ok_or` | `core.option.Option.ok_or` | [docs](https://doc.rust-lang.org/core/option/enum.Option.html#method.ok_or) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/option.rs) | ✅ | — | [Core/Core.lean](backends/lean/Aeneas/Std/Core/Core.lean) | [tests/src/option_methods.rs](tests/src/option_methods.rs) | — |
| `Clone for Option<T>::clone` | `core.option.Option.Insts.CoreCloneClone.clone` | [docs](https://doc.rust-lang.org/core/option/enum.Option.html#impl-Clone-for-Option%3CT%3E) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/option.rs) | ✅ | — | [Core/Core.lean](backends/lean/Aeneas/Std/Core/Core.lean) | [tests/src/option_methods.rs](tests/src/option_methods.rs) | — |
| `Default for Option<T>::default` | `core.option.Option.Insts.CoreDefaultDefault.default` | [docs](https://doc.rust-lang.org/core/option/enum.Option.html#impl-Default-for-Option%3CT%3E) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/option.rs) | ✅ | — | [Core/Core.lean](backends/lean/Aeneas/Std/Core/Core.lean) | [tests/src/option_methods.rs](tests/src/option_methods.rs) | — |
| `PartialEq for Option<T>::eq` | `core.option.Option.Insts.CoreCmpPartialEqOption.eq` | [docs](https://doc.rust-lang.org/core/option/enum.Option.html#impl-PartialEq-for-Option%3CT%3E) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/option.rs) | ✅ | — | [Core/Core.lean](backends/lean/Aeneas/Std/Core/Core.lean) | [tests/src/option_methods.rs](tests/src/option_methods.rs) | — |

---

## Result methods

| Rust item | Lean name | Docs | Source | Status | Deps | Lean file | Test file | Proof |
|---|---|---|---|---|---|---|---|---|
| `Result::is_ok` | `core.result.Result.is_ok` | [docs](https://doc.rust-lang.org/core/result/enum.Result.html#method.is_ok) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/result.rs) | ✅ | — | [Core/Result.lean](backends/lean/Aeneas/Std/Core/Result.lean) | [tests/src/result_methods.rs](tests/src/result_methods.rs) | — |
| `Result::map` | `core.result.Result.map` | [docs](https://doc.rust-lang.org/core/result/enum.Result.html#method.map) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/result.rs) | ✅ | FnOnce | [Core/Result.lean](backends/lean/Aeneas/Std/Core/Result.lean) | [tests/src/result_methods.rs](tests/src/result_methods.rs) | — |
| `Result::map_err` | `core.result.Result.map_err` | [docs](https://doc.rust-lang.org/core/result/enum.Result.html#method.map_err) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/result.rs) | ✅ | FnOnce | [Core/Result.lean](backends/lean/Aeneas/Std/Core/Result.lean) | [tests/src/result_methods.rs](tests/src/result_methods.rs) | — |
| `Result::unwrap_or` | `core.result.Result.unwrap_or` | [docs](https://doc.rust-lang.org/core/result/enum.Result.html#method.unwrap_or) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/result.rs) | ✅ | — | [Core/Result.lean](backends/lean/Aeneas/Std/Core/Result.lean) | [tests/src/result_methods.rs](tests/src/result_methods.rs) | — |
| `Try<T, Result<Infallible, E>> for Result<T, E>::branch` | `core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch` | [docs](https://doc.rust-lang.org/std/ops/trait.Try.html#tymethod.branch) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/result.rs) | ✅ | ControlFlow, Infallible, FromResidual, From | [Core/Convert.lean](backends/lean/Aeneas/Std/Core/Convert.lean) | [tests/src/result_methods.rs](tests/src/result_methods.rs) | — |

---

## Vec methods

All `Vec` methods take `keepParams := [true, false]` to erase the allocator type parameter.

| Rust item | Lean name | Docs | Source | Status | Deps | Lean file | Test file | Proof |
|---|---|---|---|---|---|---|---|---|
| `Vec::truncate` | `alloc.vec.Vec.truncate` | [docs](https://doc.rust-lang.org/alloc/vec/struct.Vec.html#method.truncate) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/vec/mod.rs) | ⬜ | — | — | — | — |
| `Vec::as_slice` | `alloc.vec.Vec.as_slice` | [docs](https://doc.rust-lang.org/alloc/vec/struct.Vec.html#method.as_slice) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/vec/mod.rs) | ⬜ | — | — | — | — |
| `Vec::remove` | `alloc.vec.Vec.remove` | [docs](https://doc.rust-lang.org/alloc/vec/struct.Vec.html#method.remove) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/vec/mod.rs) | ⬜ | — | — | — | — |
| `Vec::append` | `alloc.vec.Vec.append` | [docs](https://doc.rust-lang.org/alloc/vec/struct.Vec.html#method.append) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/vec/mod.rs) | ⬜ | — | — | — | — |
| `Vec::clear` | `alloc.vec.Vec.clear` | [docs](https://doc.rust-lang.org/alloc/vec/struct.Vec.html#method.clear) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/vec/mod.rs) | ⬜ | — | — | — | — |
| `Vec::is_empty` | `alloc.vec.Vec.is_empty` | [docs](https://doc.rust-lang.org/alloc/vec/struct.Vec.html#method.is_empty) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/vec/mod.rs) | ⬜ | — | — | — | — |
| `Vec::split_off` | `alloc.vec.Vec.split_off` | [docs](https://doc.rust-lang.org/alloc/vec/struct.Vec.html#method.split_off) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/vec/mod.rs) | ⬜ | — | — | — | — |
| `Default for Vec<T>::default` | `alloc.vec.Vec.Insts.CoreDefaultDefault.default` | [docs](https://doc.rust-lang.org/alloc/vec/struct.Vec.html#impl-Default-for-Vec%3CT%3E) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/vec/mod.rs) | ⬜ | — | — | — | — |

---

## VecDeque (new type + methods)

| Rust item | Lean name | Docs | Source | Status | Deps | Lean file | Test file | Proof |
|---|---|---|---|---|---|---|---|---|
| `VecDeque<T>` (type) | `alloc.collections.vec_deque.VecDeque` | [docs](https://doc.rust-lang.org/alloc/collections/vec_deque/struct.VecDeque.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/collections/vec_deque/mod.rs) | ⬜ | — | — | — | — |
| `VecDeque::len` | `alloc.collections.vec_deque.VecDeque.len` | [docs](https://doc.rust-lang.org/alloc/collections/vec_deque/struct.VecDeque.html#method.len) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/collections/vec_deque/mod.rs) | ⬜ | VecDeque | — | — | — |
| `VecDeque::pop_front` | `alloc.collections.vec_deque.VecDeque.pop_front` | [docs](https://doc.rust-lang.org/alloc/collections/vec_deque/struct.VecDeque.html#method.pop_front) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/collections/vec_deque/mod.rs) | ⬜ | VecDeque | — | — | — |
| `VecDeque::push_back` | `alloc.collections.vec_deque.VecDeque.push_back` | [docs](https://doc.rust-lang.org/alloc/collections/vec_deque/struct.VecDeque.html#method.push_back) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/collections/vec_deque/mod.rs) | ⬜ | VecDeque | — | — | — |

---

## Slice methods

| Rust item | Lean name | Docs | Source | Status | Deps | Lean file | Test file | Proof |
|---|---|---|---|---|---|---|---|---|
| `[T]::clone_from_slice` | `core.slice.Slice.clone_from_slice` | [docs](https://doc.rust-lang.org/core/primitive.slice.html#method.clone_from_slice) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/slice/mod.rs) | ⬜ | — | — | — | — |
| `[T]::copy_within` | `core.slice.Slice.copy_within` | [docs](https://doc.rust-lang.org/core/primitive.slice.html#method.copy_within) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/slice/mod.rs) | ⬜ | — | — | — | — |
| `Ord for [T]::cmp` | `Slice.Insts.CoreCmpOrd.cmp` | [docs](https://doc.rust-lang.org/core/primitive.slice.html#impl-Ord-for-%5BT%5D) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/slice/cmp.rs) | ⬜ | — | — | — | — |
| `[T]::concat` (alloc slice) | `alloc.slice.Slice.concat` | [docs](https://doc.rust-lang.org/alloc/slice/trait.Concat.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/slice.rs) | ⬜ | `Concat for [V]::concat` | — | — | — |
| `Concat<T, Vec<T>> for [V]::concat` | `Slice.Insts.AllocSliceConcatTVec.concat` | [docs](https://doc.rust-lang.org/alloc/slice/trait.Concat.html#tymethod.concat) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/slice.rs) | ⬜ | — | — | — | — |
| `PartialEq<[U; N]> for [T]::eq` | `Slice.Insts.CoreCmpPartialEqArray.eq` | [docs](https://doc.rust-lang.org/core/primitive.slice.html#impl-PartialEq-for-%5BT%5D) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/array/equality.rs) | ⬜ | — | — | — | — |

---

## Range (RangeFull slice indexing, RangeFrom bounds, Range Iterator)

| Rust item | Lean name | Docs | Source | Status | Deps | Lean file | Test file | Proof |
|---|---|---|---|---|---|---|---|---|
| `SliceIndex<[T], [T]> for RangeFull::index` | `core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index` | [docs](https://doc.rust-lang.org/core/slice/trait.SliceIndex.html#tymethod.index) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/slice/index.rs) | ⬜ | — | — | — | — |
| `SliceIndex for RangeFull::get` | `core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get` | [docs](https://doc.rust-lang.org/core/slice/trait.SliceIndex.html#tymethod.get) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/slice/index.rs) | ⬜ | — | — | — | — |
| `SliceIndex for RangeFull::get_mut` | `core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut` | [docs](https://doc.rust-lang.org/core/slice/trait.SliceIndex.html#tymethod.get_mut) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/slice/index.rs) | ⬜ | — | — | — | — |
| `RangeBounds<T> for RangeFrom<T>::start_bound` | `core.ops.range.RangeFrom.Insts.CoreOpsRangeRangeBounds.start_bound` | [docs](https://doc.rust-lang.org/core/ops/trait.RangeBounds.html#tymethod.start_bound) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/ops/range.rs) | ⬜ | `Bound<T>` type | — | — | — |
| `RangeBounds<T> for RangeFrom<T>::end_bound` | `core.ops.range.RangeFrom.Insts.CoreOpsRangeRangeBounds.end_bound` | [docs](https://doc.rust-lang.org/core/ops/trait.RangeBounds.html#tymethod.end_bound) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/ops/range.rs) | ⬜ | `Bound<T>` type | — | — | — |
| `Iterator for Range<A>::collect` | `core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.collect` | [docs](https://doc.rust-lang.org/core/iter/trait.Iterator.html#method.collect) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/iter/range.rs) | ⬜ | — | — | — | — |
| `Iterator for Range<A>::map` | `core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.map` | [docs](https://doc.rust-lang.org/core/iter/trait.Iterator.html#method.map) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/iter/range.rs) | ⬜ | — | — | — | — |

---

## Iterator adapters / `collect` / trait defaults

| Rust item | Lean name | Docs | Source | Status | Deps | Lean file | Test file | Proof |
|---|---|---|---|---|---|---|---|---|
| `Iterator::enumerate` (default) | `core.iter.traits.iterator.Iterator.enumerate.default` | [docs](https://doc.rust-lang.org/core/iter/trait.Iterator.html#method.enumerate) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/iter/traits/iterator.rs) | ✅ | char, Array::into_iter, Option::PartialEq::eq (test adapted while deps pending) | [Core/Iter.lean](backends/lean/Aeneas/Std/Core/Iter.lean) | [tests/src/enumerate.rs](tests/src/enumerate.rs) | [tests/lean/EnumerateProofs.lean](tests/lean/EnumerateProofs.lean) |
| `Iterator::map` (default) | `core.iter.traits.iterator.Iterator.map.default` | [docs](https://doc.rust-lang.org/core/iter/trait.Iterator.html#method.map) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/iter/traits/iterator.rs) | ⬜ | — | — | — | — |
| `Iterator<&T> for Iter<T>::collect` | `core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.collect` | [docs](https://doc.rust-lang.org/core/slice/struct.Iter.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/slice/iter/macros.rs) | ⬜ | — | — | — | — |
| `Iterator<&T> for Iter<T>::map` | `core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.map` | [docs](https://doc.rust-lang.org/core/slice/struct.Iter.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/slice/iter/macros.rs) | ⬜ | — | — | — | — |
| `Iterator<B> for Map<I, F>::collect` | `core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect` | [docs](https://doc.rust-lang.org/core/iter/struct.Map.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/iter/adapters/map.rs) | ⬜ | — | — | — | — |
| `Iterator<T> for IntoIter<T, A>::collect` | `alloc.vec.into_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.collect` | [docs](https://doc.rust-lang.org/alloc/vec/struct.IntoIter.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/vec/into_iter.rs) | ⬜ | — | — | — | — |

---

## Array

| Rust item | Lean name | Docs | Source | Status | Deps | Lean file | Test file | Proof |
|---|---|---|---|---|---|---|---|---|
| `array::from_fn` | `core.array.from_fn` | [docs](https://doc.rust-lang.org/core/array/fn.from_fn.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/array/mod.rs) | ⬜ | — | — | — | — |

---

## i32 Iter::Step trait

| Rust item | Lean name | Docs | Source | Status | Deps | Lean file | Test file | Proof |
|---|---|---|---|---|---|---|---|---|
| `Step for i32::forward_checked` | `I32.Insts.CoreIterRangeStep.forward_checked` | [docs](https://doc.rust-lang.org/core/iter/trait.Step.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/iter/range.rs) | ⬜ | — | — | — | — |
| `Step for i32::backward_checked` | `I32.Insts.CoreIterRangeStep.backward_checked` | [docs](https://doc.rust-lang.org/core/iter/trait.Step.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/iter/range.rs) | ⬜ | — | — | — | — |
| `Step for i32::steps_between` | `I32.Insts.CoreIterRangeStep.steps_between` | [docs](https://doc.rust-lang.org/core/iter/trait.Step.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/iter/range.rs) | ⬜ | — | — | — | — |

---

## Cmp/Eq/Borrow traits

| Rust item | Lean name | Docs | Source | Status | Deps | Lean file | Test file | Proof |
|---|---|---|---|---|---|---|---|---|
| `Borrow<T> for &T::borrow` | `Shared0T.Insts.CoreBorrowBorrow.borrow` | [docs](https://doc.rust-lang.org/core/borrow/trait.Borrow.html#tymethod.borrow) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/borrow.rs) | ⬜ | — | — | — | — |
| `Eq for u8::assert_receiver_is_total_eq` | `U8.Insts.CoreCmpEq.assert_receiver_is_total_eq` | [docs](https://doc.rust-lang.org/core/cmp/trait.Eq.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/cmp.rs) | ⬜ | — | — | — | — |
| `Eq for usize::assert_receiver_is_total_eq` | `Usize.Insts.CoreCmpEq.assert_receiver_is_total_eq` | [docs](https://doc.rust-lang.org/core/cmp/trait.Eq.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/cmp.rs) | ⬜ | — | — | — | — |

---

## Misc

| Rust item | Lean name | Docs | Source | Status | Deps | Lean file | Test file | Proof |
|---|---|---|---|---|---|---|---|---|
| `hint::black_box` | `core.hint.black_box` | [docs](https://doc.rust-lang.org/core/hint/fn.black_box.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/hint.rs) | ⬜ | — | — | — | — |
| `TryFrom<u64, TryFromIntError> for u32::try_from` | `U32.Insts.CoreConvertTryFromU64TryFromIntError.try_from` | [docs](https://doc.rust-lang.org/core/convert/trait.TryFrom.html#tymethod.try_from) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/convert/num.rs) | ⬜ | `TryFromIntError` | — | — | — |
| `ToOwned<String> for str::to_owned` | `Str.Insts.AllocBorrowToOwnedString.to_owned` | [docs](https://doc.rust-lang.org/core/borrow/trait.ToOwned.html#tymethod.to_owned) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/str.rs) | ⬜ | `String` | — | — | — |

---

## Deferred — `fmt` functions

Pure model story unclear for formatting (impure in Rust, produces side-effect
output to a `Formatter` sink). Keep as axioms until a downstream project
(e.g. libsignal) demonstrates a proof needs `fmt` semantics.

| Rust item | Lean name | Notes |
|---|---|---|
| `Formatter::debug_struct_field2_finish` | `core.fmt.Formatter.debug_struct_field2_finish` | ⏸ Requires impure-effect story. |
| `Display for &T::fmt` | `Shared0T.Insts.CoreFmtDisplay.fmt` | ⏸ Requires impure-effect story. |
