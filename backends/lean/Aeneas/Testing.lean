import Aeneas

/- example(v: Nat)(ty: UScalarTy) -/
/- : ty.numBits > 0 -/ 
/- → v <= UScalar.max ty -/
/- → ((⟨BitVec.ofFin v⟩ : UScalar ty) |>.val) = v -/
/- := by -/
/-   intro nb_ne_0 h -/
/-   simp only [UScalar.max] at h -/
/-   #check Nat.mod_eq_of_lt (lt_of_leh -/
/-   simp [h, UScalar.val, BitVec.toNat, Nat.mod_eq_of_lt h] -/
/-   simp -/ 
/-   #check UScalar.val -/
/-   simp [UScalar.val, BitVec.toNat] -/
/-   sorry -/

namespace Testing
open Aeneas Std

abbrev Rust := Result

def Rust.add(x y: U8): Result U8 := do
  if h: x.val + y.val <= U8.max then
    return ⟨x.val + y.val, by scalar_tac⟩
  else
    return ⟨x.val + y.val - U8.max, by scalar_tac⟩

@[progress]
theorem Rust.add.spec
  (x y: U8)
: x.val + y.val <= U8.max 
→ ∃ z, Rust.add x y = .ok z ∧
  z.val = x.val + y.val
:= sorry

def Rust.max(x y: U8): Result U8 := do
  if x.val > y.val then 
    return x
  else
    return y

@[progress]
theorem Rust.max.spec
  (x y: U8)
: ∃ z, Rust.max x y = .ok z ∧
  z.val = x.val ⊔ y.val
:= sorry

def Rust.program(x: U8): Rust U8 := do
  let aux₁ <- Rust.add 1#u8 2#u8
  let aux₂ <- Rust.max 1#u8 aux₁
  let res <- Rust.add aux₂ aux₂
  if res < x then
    return res
  else
    let res₂ <- Rust.add res x
    return res₂

theorem Rust.program.spec (x: U8)
: x > 10#u8
→ ∃ z, program x = .ok z ∧ z.val = 6
:= by
  intro x_big
  unfold Rust.program
  -- This is suggested by using `progress*`
  progress with Rust.add.spec as ⟨x₁, x₁_post⟩

  progress with Rust.max.spec as ⟨x₂, x₂_post⟩
  simp only [x₁_post] at x₂_post

  progress with Rust.add.spec as ⟨x₃, x₃_post⟩
  simp only [x₂_post] at x₃_post

  if h: x₃ < x then
    simp only [h, reduceIte]

    simp [pure]
    sorry
  else
    simp only [h, reduceIte]
    progress with Rust.add.spec as ⟨x₄, x₄_post⟩

    simp [pure]
    sorry
    

set_option linter.unusedTactic false in
example
: ∃ z, (do
    let aux₁ <- Rust.add 1#u8 2#u8
    let aux₂ <- Rust.max 1#u8 aux₁
    return <- Rust.add aux₂ aux₂
  ) = .ok z ∧
  z.val = 6
:= by
  progress as ⟨aux₁, expr⟩

  have h := expr; clear expr
  progress with Rust.max.spec as ⟨aux₂, expr⟩
  simp [h] at expr

  have h := expr; clear expr
  progress as ⟨res, expr⟩
  simp [h] at expr

  simp [pure, instPureResult, expr]

open Lean Elab Tactic Meta Elab in
elab "uut" stx:term : tactic => do
  let e <- elabTerm stx none
  withRef stx <|
    logInfo s!"{repr e.getAppFn}"

