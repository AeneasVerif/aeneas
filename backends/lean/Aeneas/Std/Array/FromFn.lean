module
public import Aeneas.Std.Array.Array
public import Aeneas.Std.Core.Ops
public section

/-! # `core::array::from_fn`

Rust (<https://doc.rust-lang.org/std/array/fn.from_fn.html>, `library/core/src/array/mod.rs`):
```rust
pub fn from_fn<T, const N: usize, F>(cb: F) -> [T; N] where F: FnMut(usize) -> T
```
creates the array `[cb(0), cb(1), ..., cb(N - 1)]`. -/

namespace Aeneas.Std

open Result WP

/-- Rust fills the array with a `while` loop which calls the closure on the indices `0, 1, …, N - 1`
    and pushes each result into a buffer (`try_from_fn_erased`). -/
@[expose, rust_fun "core::array::from_fn"]
def core.array.from_fn {T F : Type u} (N : Usize) (inst : core.ops.function.FnMut F Usize T)
    (f : F) : Result (Array T N) := do
  let (v, _) ← StateT.run (Vector.ofFnM (m := StateT F Result) (n := N.val) fun i g =>
    inst.call_mut g (UScalar.ofNatCore i.val (by scalar_tac))) f
  ok (Array.from v.toList (by simp))

/-- Specification of `Vector.ofFnM` in the state monad, for an invariant `inv` on the state. -/
private theorem core.array.from_fn.ofFnM_spec {T F : Type u} {n : Nat}
    (fm : Fin n → StateT F Result T) {post : Nat → T → Prop} (inv : Nat → F → Prop)
    (h : ∀ (i : Fin n) g, inv i.val g →
      (fm i).run g ⦃ (v : T) (g' : F) => post i.val v ∧ inv (i.val + 1) g' ⦄)
    (g : F) (hinv : inv 0 g) :
    (Vector.ofFnM fm).run g ⦃ (vs, g') => (∀ j (hj : j < n), post j vs[j]) ∧ inv n g' ⦄ := by
  induction n generalizing g with
  | zero => simpa [pure_tc_eq, spec_ok] using hinv
  | succ n ih =>
    simp only [Vector.ofFnM_succ, StateT.run_bind, bind_tc_eq]
    apply spec_bind (ih (fun i => fm i.castSucc) (fun i => h i.castSucc) g hinv)
    rintro ⟨vs, g1⟩ ⟨hvs, hg1⟩
    apply spec_bind (h (Fin.last n) g1 hg1)
    rintro ⟨v, g2⟩ ⟨hv, hg2⟩
    simp only [StateT.run_pure, pure_tc_eq, spec_ok]
    refine ⟨fun j hj => ?_, hg2⟩
    rw [Vector.getElem_push]
    split
    · exact hvs j _
    · obtain rfl : j = n := by agrind
      exact hv

/-- Spec theorem for `core::array::from_fn`, for a closure with state: if every call `cb(i)`
    (for `i < N`), starting from a state satisfying `inv i`, returns a value satisfying `post i` and
    a state satisfying `inv (i + 1)`, then the `i`-th element of the array satisfies `post i`. -/
theorem core.array.from_fn.spec {T F : Type u} (N : Usize)
    (inst : core.ops.function.FnMut F Usize T) (f : F) (inv : Nat → F → Prop)
    (post : Nat → T → Prop) (hinv : inv 0 f)
    (h : ∀ (i : Usize) (g : F), i.val < N.val → inv i.val g →
      inst.call_mut g i ⦃ (v : T) (g' : F) => post i.val v ∧ inv (i.val + 1) g' ⦄) :
    core.array.from_fn N inst f ⦃ (a : Array T N) =>
      ∀ j (hj : j < a.val.length), post j a.val[j] ⦄ := by
  simp only [core.array.from_fn, bind_tc_eq]
  apply spec_bind (core.array.from_fn.ofFnM_spec _ inv (fun i g hg => by
    have hi : i.val < 2 ^ UScalarTy.Usize.numBits := by scalar_tac
    simpa [StateT.run] using h (UScalar.ofNatCore i.val hi) g (by simp) (by simpa using hg)) f hinv)
  rintro ⟨v, g'⟩ ⟨hv, _⟩
  simpa using hv

/-- Spec theorem for `core::array::from_fn`, as `core.array.from_fn.spec` but with the
    elements read with `a[j]!`. -/
theorem core.array.from_fn.spec_getElem! {T F : Type u} [Inhabited T] (N : Usize)
    (inst : core.ops.function.FnMut F Usize T) (f : F)
    (inv : Nat → F → Prop) (post : Nat → T → Prop) (hinv : inv 0 f)
    (h : ∀ (i : Usize) (g : F), i.val < N.val → inv i.val g →
      inst.call_mut g i ⦃ (v : T) (g' : F) => post i.val v ∧ inv (i.val + 1) g' ⦄) :
    core.array.from_fn N inst f ⦃ (a : Array T N) => ∀ j < N.val, post j a[j]! ⦄ := by
  apply spec_mono (core.array.from_fn.spec N inst f inv post hinv h)
  intro a ha j hj
  simpa [Array.getElem!_Nat_eq, getElem!_pos, hj] using ha j (by simpa using hj)

/-- Spec theorem for `core::array::from_fn`, for closures whose `call_mut` returns the closure
    state unchanged, with the elements read with `a[j]!`: no invariant is needed, only the
    postcondition `post` of each call. -/
theorem core.array.from_fn.spec_stateless_getElem! {T F : Type u} [Inhabited T] (N : Usize)
    (inst : core.ops.function.FnMut F Usize T) (f : F) (post : Nat → T → Prop)
    (h : ∀ (i : Usize), i.val < N.val →
      inst.call_mut f i ⦃ (v : T) (g : F) => post i.val v ∧ g = f ⦄) :
    core.array.from_fn N inst f ⦃ (a : Array T N) => ∀ j < N.val, post j a[j]! ⦄ :=
  core.array.from_fn.spec_getElem! N inst f (fun _ g => g = f) post rfl
    (by rintro i g hi rfl; exact h i hi)

/-- Spec theorem for `core::array::from_fn`, for closures whose `call_mut` returns the closure
    state unchanged (this is the case for closures which don't mutate their captured state). For
    closures which update their state, use `core.array.from_fn.spec` with an invariant.

    This is the `@[step]` theorem, used by `step* +inferPost`, which infers `post` from the body
    of the closure. This only works for a body with exactly one call (it fails for `|i| i`, and
    stops after the first call of a longer body), and the postcondition is on `a.val[j]`.
    Otherwise, use `core.array.from_fn.spec_stateless_getElem!` through `step with`. -/
@[step]
theorem core.array.from_fn.spec_stateless {T F : Type u} (N : Usize)
    (inst : core.ops.function.FnMut F Usize T) (f : F) {post : Nat → T × F → Prop}
    (h : ∀ (i : Usize), i.val < N.val → inst.call_mut f i ⦃ post i.val ⦄)
    (hstate : ∀ i r, post i r → r.2 = f) :
    core.array.from_fn N inst f ⦃ (a : Array T N) =>
      ∀ j (hj : j < a.val.length), post j (a.val[j], f) ⦄ :=
  core.array.from_fn.spec N inst f (fun _ g => g = f) (fun j v => post j (v, f)) rfl (by
    rintro i g hi rfl
    apply spec_mono (h i hi)
    rintro ⟨v, g'⟩ hp
    obtain rfl : g' = g := hstate _ _ hp
    exact ⟨hp, rfl⟩)

end Aeneas.Std
