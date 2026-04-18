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
| Foundation (cascade deps for other entries) | 3 | 3 |
| Option methods | 5 | 5 |
| Result methods | 6 | 6 |
| Vec methods | 8 | 8 |
| VecDeque (new type + methods) | 4 | 4 |
| Slice methods | 6 | 6 |
| Range (RangeFull index, RangeFrom bounds, Range Iterator) | 7 | 7 |
| Iterator adapters/collect/defaults | 8 | 6 |
| Array (from_fn, PartialEq) | 2 | 1 |
| i32 Iter::Step trait | 3 | 3 |
| Cmp/Eq/Borrow traits | 3 | 3 |
| Misc (black_box, TryFrom, TryFromIntError, to_owned) | 4 | 4 |
| Deferred (fmt) | 2 | — |
| **Total** | **60** | **55** |

---

## Foundation layer

Items discovered during the dep survey that are not in the original list but
are required so that verbatim docs examples of other items translate.

| Rust item | Lean name | Docs | Source | Status | Needed by | Lean file | Test file | Proof |
|---|---|---|---|---|---|---|---|---|
| `char` (primitive) + `PartialEq<char> for char::eq` | Lean native `Char` | [docs](https://doc.rust-lang.org/core/primitive.char.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/cmp.rs) | ✅ | — | built into Lean backend ([ExtractBase.ml](src/extract/ExtractBase.ml)) | [tests/src/char_methods.rs](tests/src/char_methods.rs) | — |
| `core::array::iter::IntoIter<T, N>` + `Array::into_iter` + `Iterator for IntoIter` | `core.array.iter.IntoIter` + `core.array.Array.into_iter` + `core.array.iter.IteratorIntoIter.next` | [docs](https://doc.rust-lang.org/core/array/iter/struct.IntoIter.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/array/iter.rs) | ✅ | — | [Array/Array.lean](backends/lean/Aeneas/Std/Array/Array.lean) | — | — |
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
| `Result::is_err` | `core.result.Result.is_err` | [docs](https://doc.rust-lang.org/core/result/enum.Result.html#method.is_err) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/result.rs) | ✅ | — | [Core/Result.lean](backends/lean/Aeneas/Std/Core/Result.lean) | [tests/src/convert_tryfrom.rs](tests/src/convert_tryfrom.rs) | — |
| `Result::map` | `core.result.Result.map` | [docs](https://doc.rust-lang.org/core/result/enum.Result.html#method.map) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/result.rs) | ✅ | FnOnce | [Core/Result.lean](backends/lean/Aeneas/Std/Core/Result.lean) | [tests/src/result_methods.rs](tests/src/result_methods.rs) | — |
| `Result::map_err` | `core.result.Result.map_err` | [docs](https://doc.rust-lang.org/core/result/enum.Result.html#method.map_err) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/result.rs) | ✅ | FnOnce | [Core/Result.lean](backends/lean/Aeneas/Std/Core/Result.lean) | [tests/src/result_methods.rs](tests/src/result_methods.rs) | — |
| `Result::unwrap_or` | `core.result.Result.unwrap_or` | [docs](https://doc.rust-lang.org/core/result/enum.Result.html#method.unwrap_or) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/result.rs) | ✅ | — | [Core/Result.lean](backends/lean/Aeneas/Std/Core/Result.lean) | [tests/src/result_methods.rs](tests/src/result_methods.rs) | — |
| `Try<T, Result<Infallible, E>> for Result<T, E>::branch` | `core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch` | [docs](https://doc.rust-lang.org/std/ops/trait.Try.html#tymethod.branch) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/result.rs) | ✅ | ControlFlow, Infallible, FromResidual, From | [Core/Convert.lean](backends/lean/Aeneas/Std/Core/Convert.lean) | [tests/src/result_methods.rs](tests/src/result_methods.rs) | — |

---

## Vec methods

All `Vec` methods take `keepParams := [true, false]` to erase the allocator type parameter.

| Rust item | Lean name | Docs | Source | Status | Deps | Lean file | Test file | Proof |
|---|---|---|---|---|---|---|---|---|
| `Vec::truncate` | `alloc.vec.Vec.truncate` | [docs](https://doc.rust-lang.org/alloc/vec/struct.Vec.html#method.truncate) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/vec/mod.rs) | ✅ | — | [Vec.lean](backends/lean/Aeneas/Std/Vec.lean) | [tests/src/vec_methods.rs](tests/src/vec_methods.rs) | — |
| `Vec::as_slice` | `alloc.vec.Vec.as_slice` | [docs](https://doc.rust-lang.org/alloc/vec/struct.Vec.html#method.as_slice) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/vec/mod.rs) | ✅ | — | [Vec.lean](backends/lean/Aeneas/Std/Vec.lean) | [tests/src/vec_methods.rs](tests/src/vec_methods.rs) | — |
| `Vec::remove` | `alloc.vec.Vec.remove` | [docs](https://doc.rust-lang.org/alloc/vec/struct.Vec.html#method.remove) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/vec/mod.rs) | ✅ | — | [Vec.lean](backends/lean/Aeneas/Std/Vec.lean) | [tests/src/vec_methods.rs](tests/src/vec_methods.rs) | — |
| `Vec::append` | `alloc.vec.Vec.append` | [docs](https://doc.rust-lang.org/alloc/vec/struct.Vec.html#method.append) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/vec/mod.rs) | ✅ | — | [Vec.lean](backends/lean/Aeneas/Std/Vec.lean) | [tests/src/vec_methods.rs](tests/src/vec_methods.rs) | — |
| `Vec::clear` | `alloc.vec.Vec.clear` | [docs](https://doc.rust-lang.org/alloc/vec/struct.Vec.html#method.clear) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/vec/mod.rs) | ✅ | — | [Vec.lean](backends/lean/Aeneas/Std/Vec.lean) | [tests/src/vec_methods.rs](tests/src/vec_methods.rs) | — |
| `Vec::is_empty` | `alloc.vec.Vec.is_empty` | [docs](https://doc.rust-lang.org/alloc/vec/struct.Vec.html#method.is_empty) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/vec/mod.rs) | ✅ | — | [Vec.lean](backends/lean/Aeneas/Std/Vec.lean) | [tests/src/vec_methods.rs](tests/src/vec_methods.rs) | — |
| `Vec::split_off` | `alloc.vec.Vec.split_off` | [docs](https://doc.rust-lang.org/alloc/vec/struct.Vec.html#method.split_off) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/vec/mod.rs) | ✅ | — | [Vec.lean](backends/lean/Aeneas/Std/Vec.lean) | [tests/src/vec_methods.rs](tests/src/vec_methods.rs) | — |
| `Default for Vec<T>::default` | `alloc.vec.Vec.Insts.CoreDefaultDefault.default` | [docs](https://doc.rust-lang.org/alloc/vec/struct.Vec.html#impl-Default-for-Vec%3CT%3E) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/vec/mod.rs) | ✅ | — | [Vec.lean](backends/lean/Aeneas/Std/Vec.lean) | [tests/src/vec_methods.rs](tests/src/vec_methods.rs) | — |

---

## VecDeque (new type + methods)

| Rust item | Lean name | Docs | Source | Status | Deps | Lean file | Test file | Proof |
|---|---|---|---|---|---|---|---|---|
| `VecDeque<T>` (type) | `alloc.collections.vec_deque.VecDeque` | [docs](https://doc.rust-lang.org/alloc/collections/vec_deque/struct.VecDeque.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/collections/vec_deque/mod.rs) | ✅ | — | [Vec.lean](backends/lean/Aeneas/Std/Vec.lean) | [tests/src/vec_deque_methods.rs](tests/src/vec_deque_methods.rs) | — |
| `VecDeque::len` | `alloc.collections.vec_deque.VecDeque.len` | [docs](https://doc.rust-lang.org/alloc/collections/vec_deque/struct.VecDeque.html#method.len) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/collections/vec_deque/mod.rs) | ✅ | VecDeque | [Vec.lean](backends/lean/Aeneas/Std/Vec.lean) | [tests/src/vec_deque_methods.rs](tests/src/vec_deque_methods.rs) | — |
| `VecDeque::pop_front` | `alloc.collections.vec_deque.VecDeque.pop_front` | [docs](https://doc.rust-lang.org/alloc/collections/vec_deque/struct.VecDeque.html#method.pop_front) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/collections/vec_deque/mod.rs) | ✅ | VecDeque | [Vec.lean](backends/lean/Aeneas/Std/Vec.lean) | [tests/src/vec_deque_methods.rs](tests/src/vec_deque_methods.rs) | — |
| `VecDeque::push_back` | `alloc.collections.vec_deque.VecDeque.push_back` | [docs](https://doc.rust-lang.org/alloc/collections/vec_deque/struct.VecDeque.html#method.push_back) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/collections/vec_deque/mod.rs) | ✅ | VecDeque | [Vec.lean](backends/lean/Aeneas/Std/Vec.lean) | [tests/src/vec_deque_methods.rs](tests/src/vec_deque_methods.rs) | — |

---

## Slice methods

| Rust item | Lean name | Docs | Source | Status | Deps | Lean file | Test file | Proof |
|---|---|---|---|---|---|---|---|---|
| `[T]::clone_from_slice` | `core.slice.Slice.clone_from_slice` | [docs](https://doc.rust-lang.org/core/primitive.slice.html#method.clone_from_slice) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/slice/mod.rs) | ✅ | — | [Slice.lean](backends/lean/Aeneas/Std/Slice.lean) | [tests/src/slice_methods.rs](tests/src/slice_methods.rs) | — |
| `[T]::copy_within` | `core.slice.Slice.copy_within` | [docs](https://doc.rust-lang.org/core/primitive.slice.html#method.copy_within) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/slice/mod.rs) | ✅ | `RangeBounds`, `Bound<T>` | [Slice.lean](backends/lean/Aeneas/Std/Slice.lean) | [tests/src/slice_methods.rs](tests/src/slice_methods.rs) | — |
| `Ord for [T]::cmp` | `core.slice.cmp.OrdSlice.cmp` | [docs](https://doc.rust-lang.org/core/primitive.slice.html#impl-Ord-for-%5BT%5D) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/slice/cmp.rs) | ✅ | — | [Array/ArraySlice.lean](backends/lean/Aeneas/Std/Array/ArraySlice.lean) | — | — |
| `[T]::concat` (alloc slice) | `alloc.slice.Slice.concat` | [docs](https://doc.rust-lang.org/alloc/slice/trait.Concat.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/slice.rs) | ✅ | Concat trait, Borrow<Vec<T>,[T]> | [Vec.lean](backends/lean/Aeneas/Std/Vec.lean) | [tests/src/slice_concat.rs](tests/src/slice_concat.rs) | — |
| `Concat<T, Vec<T>> for [V]::concat` | `alloc.slice.Insts.AllocSliceConcatTVec.concat` | [docs](https://doc.rust-lang.org/alloc/slice/trait.Concat.html#tymethod.concat) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/slice.rs) | ✅ | Clone, Borrow | [Vec.lean](backends/lean/Aeneas/Std/Vec.lean) | [tests/src/slice_concat.rs](tests/src/slice_concat.rs) | — |
| `PartialEq<[U; N]> for [T]::eq` | `core.array.equality.PartialEqSliceArray.eq` | [docs](https://doc.rust-lang.org/core/primitive.slice.html#impl-PartialEq-for-%5BT%5D) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/array/equality.rs) | ✅ | `SliceIndex<RangeFull, [T], [T]>` | [Array/ArraySlice.lean](backends/lean/Aeneas/Std/Array/ArraySlice.lean) | [tests/src/slice_methods.rs](tests/src/slice_methods.rs) | — |

---

## Range (RangeFull slice indexing, RangeFrom bounds, Range Iterator)

| Rust item | Lean name | Docs | Source | Status | Deps | Lean file | Test file | Proof |
|---|---|---|---|---|---|---|---|---|
| `SliceIndex<[T], [T]> for RangeFull::index` | `core.slice.index.SliceIndexRangeFullSlice.index` | [docs](https://doc.rust-lang.org/core/slice/trait.SliceIndex.html#tymethod.index) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/slice/index.rs) | ✅ | `RangeFull` type | [Slice.lean](backends/lean/Aeneas/Std/Slice.lean) | [tests/src/slice_methods.rs](tests/src/slice_methods.rs) | — |
| `SliceIndex for RangeFull::get` | `core.slice.index.SliceIndexRangeFullSlice.get` | [docs](https://doc.rust-lang.org/core/slice/trait.SliceIndex.html#tymethod.get) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/slice/index.rs) | ✅ | `RangeFull` type | [Slice.lean](backends/lean/Aeneas/Std/Slice.lean) | — | — |
| `SliceIndex for RangeFull::get_mut` | `core.slice.index.SliceIndexRangeFullSlice.get_mut` | [docs](https://doc.rust-lang.org/core/slice/trait.SliceIndex.html#tymethod.get_mut) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/slice/index.rs) | ✅ | `RangeFull` type | [Slice.lean](backends/lean/Aeneas/Std/Slice.lean) | — | — |
| `RangeBounds<T> for RangeFrom<T>::start_bound` | `core.ops.range.RangeFrom.RangeBounds.start_bound` | [docs](https://doc.rust-lang.org/core/ops/trait.RangeBounds.html#tymethod.start_bound) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/ops/range.rs) | ✅ | `Bound<T>` type | [Slice.lean](backends/lean/Aeneas/Std/Slice.lean) | — | — |
| `RangeBounds<T> for RangeFrom<T>::end_bound` | `core.ops.range.RangeFrom.RangeBounds.end_bound` | [docs](https://doc.rust-lang.org/core/ops/trait.RangeBounds.html#tymethod.end_bound) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/ops/range.rs) | ✅ | `Bound<T>` type | [Slice.lean](backends/lean/Aeneas/Std/Slice.lean) | — | — |
| `Iterator for Range<A>::collect` | `core.ops.range.Range.IteratorRange.collect` | [docs](https://doc.rust-lang.org/core/iter/trait.Iterator.html#method.collect) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/iter/range.rs) | ✅ | FromIterator | [Core/Iter.lean](backends/lean/Aeneas/Std/Core/Iter.lean) | [tests/src/iterator_collect.rs](tests/src/iterator_collect.rs) | — |
| `Iterator for Range<A>::map` | `core.ops.range.Range.IteratorRange.map` | [docs](https://doc.rust-lang.org/core/iter/trait.Iterator.html#method.map) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/iter/range.rs) | ✅ | Map struct, FnMut | [Core/Iter.lean](backends/lean/Aeneas/Std/Core/Iter.lean) | — | — |

---

## Iterator adapters / `collect` / trait defaults

| Rust item | Lean name | Docs | Source | Status | Deps | Lean file | Test file | Proof |
|---|---|---|---|---|---|---|---|---|
| `Iterator::enumerate` (default) | `core.iter.traits.iterator.Iterator.enumerate.default` | [docs](https://doc.rust-lang.org/core/iter/trait.Iterator.html#method.enumerate) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/iter/traits/iterator.rs) | ✅ | — | [Core/Iter.lean](backends/lean/Aeneas/Std/Core/Iter.lean) | [tests/src/enumerate.rs](tests/src/enumerate.rs) | [tests/lean/EnumerateProofs.lean](tests/lean/EnumerateProofs.lean) |
| `Iterator::map` (default) + `Iterator for Map<I,F>::next` | `core.iter.traits.iterator.Iterator.map.default`, `core.iter.adapters.map.IteratorMap.next` | [docs](https://doc.rust-lang.org/core/iter/trait.Iterator.html#method.map) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/iter/adapters/map.rs) | ✅ | Map struct, FnMut | [Core/Iter.lean](backends/lean/Aeneas/Std/Core/Iter.lean) | — | — |
| `Iterator<&T> for Iter<T>::collect` | `core.slice.iter.IteratorSliceIter.collect` | [docs](https://doc.rust-lang.org/core/slice/struct.Iter.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/slice/iter/macros.rs) | ✅ | FromIterator, collect.default | [SliceIter.lean](backends/lean/Aeneas/Std/SliceIter.lean) | — | — |
| `Iterator<&T> for Iter<T>::map` | `core.slice.iter.IteratorSliceIter.map` | [docs](https://doc.rust-lang.org/core/slice/struct.Iter.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/slice/iter/macros.rs) | ✅ | Map struct, map.default | [SliceIter.lean](backends/lean/Aeneas/Std/SliceIter.lean) | — | — |
| `Iterator<B> for Map<I, F>::collect` | `core.iter.adapters.map.IteratorMap.collect` | [docs](https://doc.rust-lang.org/core/iter/struct.Map.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/iter/adapters/map.rs) | ✅ | FromIterator | [Core/Iter.lean](backends/lean/Aeneas/Std/Core/Iter.lean) | — | — |
| `Iterator<T> for IntoIter<T, A>::collect` | `alloc.vec.into_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.collect` | [docs](https://doc.rust-lang.org/alloc/vec/struct.IntoIter.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/vec/into_iter.rs) | ✅ | FromIterator | [VecIter.lean](backends/lean/Aeneas/Std/VecIter.lean) | — | — |

---

## Array

| Rust item | Lean name | Docs | Source | Status | Deps | Lean file | Test file | Proof |
|---|---|---|---|---|---|---|---|---|
| `array::from_fn` | `core.array.from_fn` | [docs](https://doc.rust-lang.org/core/array/fn.from_fn.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/array/mod.rs) | ✅ | FnMut | [Array/Array.lean](backends/lean/Aeneas/Std/Array/Array.lean) | [tests/src/array_from_fn.rs](tests/src/array_from_fn.rs) | — |

---

## i32 Iter::Step trait

| Rust item | Lean name | Docs | Source | Status | Deps | Lean file | Test file | Proof |
|---|---|---|---|---|---|---|---|---|
| `Step for i32::forward_checked` | `core.iter.range.StepI32.forward_checked` | [docs](https://doc.rust-lang.org/core/iter/trait.Step.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/iter/range.rs) | ✅ | — | [Core/Iter.lean](backends/lean/Aeneas/Std/Core/Iter.lean) | [tests/src/step_i32.rs](tests/src/step_i32.rs) | — |
| `Step for i32::backward_checked` | `core.iter.range.StepI32.backward_checked` | [docs](https://doc.rust-lang.org/core/iter/trait.Step.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/iter/range.rs) | ✅ | — | [Core/Iter.lean](backends/lean/Aeneas/Std/Core/Iter.lean) | [tests/src/step_i32.rs](tests/src/step_i32.rs) | — |
| `Step for i32::steps_between` | `core.iter.range.StepI32.steps_between` | [docs](https://doc.rust-lang.org/core/iter/trait.Step.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/iter/range.rs) | ✅ | — | [Core/Iter.lean](backends/lean/Aeneas/Std/Core/Iter.lean) | [tests/src/step_i32.rs](tests/src/step_i32.rs) | — |

---

## Cmp/Eq/Borrow traits

| Rust item | Lean name | Docs | Source | Status | Deps | Lean file | Test file | Proof |
|---|---|---|---|---|---|---|---|---|
| `Borrow<T> for T::borrow` (identity blanket, subsumes `for &T`) | `core.borrow.Borrow.Blanket.borrow` | [docs](https://doc.rust-lang.org/core/borrow/trait.Borrow.html#tymethod.borrow) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/borrow.rs) | ✅ | — | [Core/Core.lean](backends/lean/Aeneas/Std/Core/Core.lean) | [tests/src/core_misc.rs](tests/src/core_misc.rs) | — |
| `Eq for u8::assert_receiver_is_total_eq` | via `core.cmp.Eq.assert_receiver_is_total_eq.default` (trait default) | [docs](https://doc.rust-lang.org/core/cmp/trait.Eq.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/cmp.rs) | ✅ | — | [Core/Cmp.lean](backends/lean/Aeneas/Std/Core/Cmp.lean) | [tests/src/core_misc.rs](tests/src/core_misc.rs) | — |
| `Eq for usize::assert_receiver_is_total_eq` | via `core.cmp.Eq.assert_receiver_is_total_eq.default` (trait default) | [docs](https://doc.rust-lang.org/core/cmp/trait.Eq.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/cmp.rs) | ✅ | — | [Core/Cmp.lean](backends/lean/Aeneas/Std/Core/Cmp.lean) | [tests/src/core_misc.rs](tests/src/core_misc.rs) | — |

---

## Misc

| Rust item | Lean name | Docs | Source | Status | Deps | Lean file | Test file | Proof |
|---|---|---|---|---|---|---|---|---|
| `hint::black_box` | `core.hint.black_box` | [docs](https://doc.rust-lang.org/core/hint/fn.black_box.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/hint.rs) | ✅ | — | [Core/Core.lean](backends/lean/Aeneas/Std/Core/Core.lean) | [tests/src/core_misc.rs](tests/src/core_misc.rs) | — |
| `TryFrom<u64, TryFromIntError> for u32::try_from` | `U32.Insts.CoreConvertTryFromU64TryFromIntError.try_from` | [docs](https://doc.rust-lang.org/core/convert/trait.TryFrom.html#tymethod.try_from) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/convert/num.rs) | ✅ | `TryFromIntError`, `Result::is_err` | [Scalar/CoreConvertNum.lean](backends/lean/Aeneas/Std/Scalar/CoreConvertNum.lean) | [tests/src/convert_tryfrom.rs](tests/src/convert_tryfrom.rs) | — |
| `core::num::error::TryFromIntError` (type) | `core.num.error.TryFromIntError` | [docs](https://doc.rust-lang.org/core/num/struct.TryFromIntError.html) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/num/error.rs) | ✅ | — | [Core/Convert.lean](backends/lean/Aeneas/Std/Core/Convert.lean) | [tests/src/convert_tryfrom.rs](tests/src/convert_tryfrom.rs) | — |
| `ToOwned<String> for str::to_owned` | `Str.Insts.AllocBorrowToOwnedString.to_owned` | [docs](https://doc.rust-lang.org/core/borrow/trait.ToOwned.html#tymethod.to_owned) | [source](https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/str.rs) | ✅ | `Str := Slice U8`, native `String` | [String.lean](backends/lean/Aeneas/Std/String.lean) | [tests/src/str_to_owned.rs](tests/src/str_to_owned.rs) | — |

---

## Deferred

### `fmt` functions

Pure model story unclear for formatting (impure in Rust, produces side-effect
output to a `Formatter` sink). Keep as axioms until a downstream project
(e.g. libsignal) demonstrates a proof needs `fmt` semantics.

| Rust item | Lean name | Notes |
|---|---|---|
| `Formatter::debug_struct_field2_finish` | `core.fmt.Formatter.debug_struct_field2_finish` | ⏸ Requires impure-effect story. |
| `Display for &T::fmt` | `Shared0T.Insts.CoreFmtDisplay.fmt` | ⏸ Requires impure-effect story. |

### Known-bad test pattern (not a stdlib gap)

A function that returns a string literal directly, like
`fn make_str() -> &'static str { "hello" }`, triggers a "There should be
no bottoms in the value" error in `interp/InterpExpressions.ml:55`
(`read_place_check`) when the return value is moved at `pop_frame`.
Workaround: bind the literal to a top-level `const HELLO: &str = "hello"`
and return that. This is unrelated to `str::to_owned` itself — once
the helper is rewritten with a `const`, the `to_owned` call translates
and runs against the model above.
