import Aeneas

open Aeneas Aeneas.Std Result ControlFlow Error

namespace higher_order

def applyF (f : U32 → Result U32) (x : U32) : Result U32 := f x

theorem applyF_spec (f : U32 → Result U32) (x : U32)
    (post : U32 → Prop)
    (hf : f x ⦃ post ⦄) :
    applyF f x ⦃ post ⦄ := by
  simp [applyF]; exact hf

example (a : U32) (h : a.val + 1 ≤ U32.max) :
    applyF (fun x => x + 1#u32) a ⦃ y => y.val = a.val + 1 ⦄ := by
  progress with applyF_spec
  case hf => progress +inferPost as ⟨ b, hb ⟩
  grind

-- Higher-order in 2 functions, operates on a pair of inputs/outputs
def callPair (f : U32 → Result U32) (g : U32 → Result U32) (xy : U32 × U32) : Result (U32 × U32) := do
  let a ← f xy.1
  let b ← g xy.2
  return (a, b)

theorem callPair_spec (f g : U32 → Result U32) (xy : U32 × U32)
    (postF : U32 → Prop) (postG : U32 → Prop)
    (hf : f xy.1 ⦃ postF ⦄) (hg : g xy.2 ⦃ postG ⦄) :
    callPair f g xy ⦃ fun p => postF p.1 ∧ postG p.2 ⦄ := by
  simp only [callPair]
  apply WP.spec_bind hf
  intro a ha
  apply WP.spec_bind hg
  intro b hb
  simp [WP.spec, WP.theta, WP.wp_return]
  exact ⟨ha, hb⟩

example (x y : U32) (hx : x.val + 1 ≤ U32.max) (hy : y.val + 2 ≤ U32.max) :
    callPair (fun a => a + 1#u32) (fun b => b + 2#u32) (x, y) ⦃ ab => ab.1.val = x.val + 1 ∧ ab.2.val = y.val + 2 ⦄ := by
  progress with callPair_spec
  case hf => progress +inferPost as ⟨ a, ha ⟩
  case hg => progress +inferPost as ⟨ b, hb ⟩
  grind

-- Calls f then g in sequence
def callFThenG (f g : U32 → Result U32) (x : U32) : Result U32 := do
  let y ← f x
  g y

theorem callFThenG_spec (f g : U32 → Result U32) (x : U32)
    (mid post : U32 → Prop)
    (hf : f x ⦃ mid ⦄)
    (hg : ∀ y, mid y → g y ⦃ post ⦄) :
    callFThenG f g x ⦃ post ⦄ := by
  simp only [callFThenG]
  apply WP.spec_bind hf
  intro y hy
  exact hg y hy

example (x : U32) (h1 : x.val + 1 ≤ U32.max) (h2 : x.val + 2 ≤ U32.max) :
    callFThenG (fun a => a + 1#u32) (fun b => b + 1#u32) x ⦃ y => y.val = x.val + 2 ⦄ := by
  progress with callFThenG_spec
  case hf => progress +inferPost as ⟨ a, ha ⟩
  case hg =>
    intro y hy
    progress +inferPost as ⟨ b, hb ⟩
  grind

def _root_.Aeneas.Std.Slice.mapM  {α β} (f : α → Result β) (x : Slice α) : Result (Slice β) :=
  match h : x.val.mapM f with
  | ok xs  => ok ⟨xs, List.mapM_Result_length h ▸ x.prop⟩
  | fail e => fail e
  | div    => div

theorem _root_.Aeneas.Std.Slice.mapM_spec {α β} {f : α → Result β} {s : Slice α} {post : Nat → β → Prop}
    (hf : ∀ i (hi : i < s.len), f s[i] ⦃ post i ⦄) :
    s.mapM f ⦃ s' => s'.len = s.len ∧ ∀ i (hi : i < s'.len), post i s'[i] ⦄ := by
  -- NOTE: We don't need to prove this, we just want the statement for the example below
  sorry

def callSlicemapM (x : Slice U32) : Result (Slice U32) := do
  let y ← x.mapM (fun x => x + 1#u32)
  return y

example (s : Slice U32) (h : ∀ i (hi : i < s.len), s[i] < U32.max) :
  callSlicemapM s ⦃ s' =>
    s'.len = s.len ∧
    ∀ i (hi₁ : i < s.len) (hi₂ : i < s'.len), s'[i].val = s[i].val + 1
    ⦄ := by
  unfold callSlicemapM
  progress with Slice.mapM_spec
  case hf =>
    intros t ht
    progress +inferPost as ⟨u, hu⟩
  grind

end higher_order
