module
public import Aeneas.Std.Array.Array
public import Aeneas.Std.Core.Ops
public section

/-! # `core::array::from_fn`

Rust (<https://doc.rust-lang.org/std/array/fn.from_fn.html>, `library/core/src/array/mod.rs`):
```rust
pub fn from_fn<T, const N: usize, F>(cb: F) -> [T; N] where F: FnMut(usize) -> T
```
creates the array `[cb(0), cb(1), ..., cb(N - 1)]`. The implementation (`try_from_fn_erased`)
calls `cb` exactly `N` times, **in increasing order of the index** (and never if `N = 0`). Because
`cb` is `FnMut`, every call may update the closure state, which is threaded from one call to the
next; the final state is dropped. If a call panics, `from_fn` panics: in the model, a failing call
makes `from_fn` fail. -/

namespace Aeneas.Std

open Result WP

/-- Model of `core::array::from_fn`.

    Rust fills the array with a `while` loop which calls the closure on the indices `0, 1, …, N - 1`
    and pushes each result into a buffer (`try_from_fn_erased`). `Vector.ofFnM` has the same
    structure: a counter going up from `0` and an accumulator which is pushed to. The closure state
    is threaded through the calls by running `ofFnM` in the state monad `StateT F Result`, where a
    call to `call_mut` is exactly a stateful computation. The final closure state is dropped. -/
@[expose, rust_fun "core::array::from_fn"]
def core.array.from_fn {T F : Type u} (N : Usize) (inst : core.ops.function.FnMut F Usize T)
    (f : F) : Result (Array T N) := do
  let (v, _) ← StateT.run (Vector.ofFnM (m := StateT F Result) (n := N.val) fun i g =>
    inst.call_mut g (UScalar.ofNatCore i.val (by have := N.hBounds; omega))) f
  ok (Array.from v.toList (by simp))

/-- Specification of `Vector.ofFnM` in the state monad, for an invariant `inv` on the state. -/
theorem core.array.from_fn.ofFnM_spec {T F : Type u} {n : Nat} (fm : Fin n → StateT F Result T)
    {post : Nat → T → Prop} (inv : Nat → F → Prop)
    (h : ∀ (i : Fin n) g, inv i.val g →
      (fm i).run g ⦃ (v : T) (g' : F) => post i.val v ∧ inv (i.val + 1) g' ⦄)
    (g : F) (hinv : inv 0 g) :
    (Vector.ofFnM fm).run g ⦃ (vs, g') => (∀ j (hj : j < n), post j vs[j]) ∧ inv n g' ⦄ := by
  induction n generalizing g with
  | zero =>
    simp only [Vector.ofFnM_zero, StateT.run_pure, pure_tc_eq, spec_ok, Nat.not_lt_zero,
      IsEmpty.forall_iff, implies_true, true_and]
    exact hinv
  | succ n ih =>
    rw [Vector.ofFnM_succ]
    simp only [StateT.run_bind, bind_tc_eq]
    apply spec_bind (ih (fun i => fm i.castSucc) (fun i g hg => h i.castSucc g hg) g hinv)
    rintro ⟨vs, g1⟩ ⟨hvs, hg1⟩
    apply spec_bind (h (Fin.last n) g1 hg1)
    rintro ⟨v, g2⟩ ⟨hv, hg2⟩
    simp only [StateT.run_pure, pure_tc_eq, spec_ok]
    refine ⟨fun j hj => ?_, hg2⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · simpa only [Vector.getElem_push_lt hj] using hvs j hj
    · simpa only [Vector.getElem_push_eq, Fin.val_last] using hv

/-- **Spec theorem for `core::array::from_fn`**, for a closure with state: if every call `cb(i)`
    (for `i < N`), starting from a state satisfying `inv i`, returns a value satisfying `post i` and
    a state satisfying `inv (i + 1)`, then the `i`-th element of the array satisfies `post i`. -/
theorem core.array.from_fn.spec {T F : Type u} (N : Usize)
    (inst : core.ops.function.FnMut F Usize T) (f : F)
    (inv : Nat → F → Prop) (post : Nat → T → Prop) (hinv : inv 0 f)
    (h : ∀ (i : Usize) (g : F), i.val < N.val → inv i.val g →
      inst.call_mut g i ⦃ (v : T) (g' : F) => post i.val v ∧ inv (i.val + 1) g' ⦄) :
    core.array.from_fn N inst f ⦃ (a : Array T N) =>
      ∀ j (hj : j < a.val.length), post j a.val[j] ⦄ := by
  simp only [core.array.from_fn, bind_tc_eq]
  apply spec_bind (core.array.from_fn.ofFnM_spec _ inv (fun i g hg => by
    have hi : i.val < 2 ^ UScalarTy.Usize.numBits := by have := N.hBounds; omega
    simpa only [StateT.run, UScalar.ofNatCore_val_eq] using
      h (UScalar.ofNatCore i.val hi) g (by simp only [UScalar.ofNatCore_val_eq]; omega)
        (by simpa only [UScalar.ofNatCore_val_eq] using hg)) f hinv)
  rintro ⟨v, g'⟩ ⟨hv, _⟩
  simp only [spec_ok, Array.from_val]
  intro j hj
  simpa only [Vector.getElem_toList] using hv j (by simpa using hj)

/-- **Spec theorem for `core::array::from_fn`**, as `core.array.from_fn.spec` but with the
    elements read with `a[j]!`. -/
theorem core.array.from_fn.spec_getElem! {T F : Type u} [Inhabited T] (N : Usize)
    (inst : core.ops.function.FnMut F Usize T) (f : F)
    (inv : Nat → F → Prop) (post : Nat → T → Prop) (hinv : inv 0 f)
    (h : ∀ (i : Usize) (g : F), i.val < N.val → inv i.val g →
      inst.call_mut g i ⦃ (v : T) (g' : F) => post i.val v ∧ inv (i.val + 1) g' ⦄) :
    core.array.from_fn N inst f ⦃ (a : Array T N) => ∀ j < N.val, post j a[j]! ⦄ := by
  apply spec_mono (core.array.from_fn.spec N inst f inv post hinv h)
  intro a ha j hj
  have hj' : j < a.val.length := by simpa using hj
  rw [Array.getElem!_Nat_eq, getElem!_pos a.val j hj']
  exact ha j hj'

/-- **Spec theorem for `core::array::from_fn`**, for closures whose `call_mut` returns the closure
    state unchanged (this is the case for closures which don't mutate their captured state). For
    closures which update their state, use `core.array.from_fn.spec` with an invariant.

    `post i` is the postcondition of the call on index `i`, on the pair (output, new state): it is
    stated on the whole pair so that `step +inferPost` can infer it from the closure body, and
    `hstate` then checks that the state is unchanged. -/
@[step]
theorem core.array.from_fn.spec_stateless {T F : Type u} (N : Usize)
    (inst : core.ops.function.FnMut F Usize T) (f : F) {post : Nat → T × F → Prop}
    (h : ∀ (i : Usize), i.val < N.val → inst.call_mut f i ⦃ post i.val ⦄)
    (hstate : ∀ i r, post i r → r.2 = f) :
    core.array.from_fn N inst f ⦃ (a : Array T N) =>
      ∀ j (hj : j < a.val.length), post j (a.val[j], f) ⦄ :=
  core.array.from_fn.spec N inst f (fun _ g => g = f) (fun j v => post j (v, f)) rfl (by
    intro i g hi hg
    rw [hg]
    apply spec_mono (h i hi)
    rintro ⟨v, g'⟩ hp
    have hg' : g' = f := hstate _ _ hp
    rw [hg'] at hp ⊢
    exact ⟨hp, rfl⟩)

end Aeneas.Std
