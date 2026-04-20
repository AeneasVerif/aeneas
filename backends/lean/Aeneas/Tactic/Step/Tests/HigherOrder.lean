import Aeneas.Std.Slice
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result ControlFlow Error

namespace higher_order

def applyF (f : U32 → Result U32) (x : U32) : Result U32 := f x

@[step]
theorem applyF_spec (f : U32 → Result U32) (x : U32)
    (post : U32 → Prop)
    (hf : f x ⦃ post ⦄) :
    applyF f x ⦃ post ⦄ := by
  simp [applyF]; exact hf

/--
info: Try this:

  [apply]     let* ⟨ y, y_post ⟩ ← [ +inferPost ] applyF_spec
    case hf => let* ⟨ ⟩ ← [ +inferPost ] U32.add_spec
    agrind
-/
#guard_msgs in
example (a : U32) (h : a.toNat + 1 ≤ U32.max) :
    applyF (fun x => x +? 1#u32) a ⦃ y => y.toNat = a.toNat + 1 ⦄ := by
  step*? +inferPost

-- Higher-order in 2 functions, operates on a pair of inputs/outputs
def callPair (f : U32 → Result U32) (g : U32 → Result U32) (xy : U32 × U32) : Result (U32 × U32) := do
  let a ← f xy.1
  let b ← g xy.2
  return (a, b)

@[step]
theorem callPair_spec (f g : U32 → Result U32) (xy : U32 × U32)
    (postF : U32 → Prop) (postG : U32 → Prop)
    (hf : f xy.1 ⦃ postF ⦄) (hg : g xy.2 ⦃ postG ⦄) :
    callPair f g xy ⦃ fun p => postF p.1 ∧ postG p.2 ⦄ := by
  unfold callPair
  step*

/--
info: Try this:

  [apply]     let* ⟨ ab, ab_post1, ab_post2 ⟩ ← [ +inferPost ] callPair_spec
    case hf => let* ⟨ ⟩ ← [ +inferPost ] U32.add_spec
    case hg => let* ⟨ ⟩ ← [ +inferPost ] U32.add_spec
    agrind
-/
#guard_msgs in
example (x y : U32) (hx : x.toNat + 1 ≤ U32.max) (hy : y.toNat + 2 ≤ U32.max) :
    callPair (fun a => a +? 1#u32) (fun b => b +? 2#u32) (x, y) ⦃ ab => ab.1.toNat = x.toNat + 1 ∧ ab.2.toNat = y.toNat + 2 ⦄ := by
  step*? +inferPost

-- Calls f then g in sequence
def callFThenG (f g : U32 → Result U32) (x : U32) : Result U32 := do
  let y ← f x
  g y

@[step]
theorem callFThenG_spec (f g : U32 → Result U32) (x : U32)
    (mid post : U32 → Prop)
    (hf : f x ⦃ mid ⦄)
    (hg : ∀ y, mid y → g y ⦃ post ⦄) :
    callFThenG f g x ⦃ post ⦄ := by
  unfold callFThenG
  step*

/--
info: Try this:

  [apply]     let* ⟨ y, y_post ⟩ ← [ +inferPost ] callFThenG_spec
    case hf => let* ⟨ ⟩ ← [ +inferPost ] U32.add_spec
    case hg =>
      intros y a✝
      let* ⟨ ⟩ ← [ +inferPost ] U32.add_spec
    agrind
-/
#guard_msgs in
example (x : U32) (h1 : x.toNat + 1 ≤ U32.max) (h2 : x.toNat + 2 ≤ U32.max) :
    callFThenG (fun a => a +? 1#u32) (fun b => b +? 1#u32) x ⦃ y => y.toNat = x.toNat + 2 ⦄ := by
  step*? +inferPost

def callSlicemapM (x : Slice U32) : Result (Slice U32) := do
  let y ← x.mapM (fun x => x +? 1#u32)
  return y

/--
info: Try this:

  [apply]     let* ⟨ y, y_post1, y_post2 ⟩ ← [ +inferPost ] Slice.mapM_spec
    case hf =>
      intros i hi
      let* ⟨ ⟩ ← [ +inferPost ] U32.add_spec
    agrind
-/
#guard_msgs in
example (s : Slice U32) (h : ∀ i (hi : i < s.len), s[i] < U32.max) :
  callSlicemapM s ⦃ s' =>
    s'.len = s.len ∧
    ∀ i (hi₁ : i < s.len) (hi₂ : i < s'.len), s'[i].toNat = s[i].toNat + 1
    ⦄ := by
  unfold callSlicemapM
  step*? +inferPost

def callSlicemapMTwice (x : Slice U32) : Result (Slice U32) := do
  let y ← x.mapM (fun x => x +? 1#u32)
  let z ← y.mapM (fun x => x *? x)
  return z

/--
info: Try this:

  [apply]     let* ⟨ y, y_post1, y_post2 ⟩ ← [ +inferPost ] Slice.mapM_spec
    case hf =>
      intros i hi
      let* ⟨ ⟩ ← [ +inferPost ] U32.add_spec
    let* ⟨ z, z_post1, z_post2 ⟩ ← [ +inferPost ] Slice.mapM_spec
    case hf =>
      intros i hi
      let* ⟨ ⟩ ← [ +inferPost ] U32.mul_spec
    agrind
-/
#guard_msgs in
example (s : Slice U32) (h : ∀ i (hi : i < s.len), (s[i] + 1) * (s[i] + 1) ≤ U32.max) :
  callSlicemapMTwice s ⦃ s' =>
    s'.len = s.len ∧
    ∀ i (hi₁ : i < s.len) (hi₂ : i < s'.len), s'[i].toNat = (s[i].toNat + 1) * (s[i].toNat + 1)
    ⦄ := by
  unfold callSlicemapMTwice
  step*? +inferPost

end higher_order
