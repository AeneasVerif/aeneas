import Aeneas.Tactic.Step.Step

/-!
# Step Array Spec

This file defines a convenient notation to generate a `step` theorem for
accesses to global arrays. For instance, given:
```
def const_array : Array U32 8#usize := Array.make 8#usize [
  0#u32, 1#u32, 2#u32, 3#u32, 4#u32, 5#u32, 6#u32, 7#u32,
]
```

One might want to prove the following theorem:
```
@[step]
theorem const_array_spec (i : Usize) (hi : i < 8) :
  ∃ x, Array.index_usize const_array i = ok x ∧ x.toNat = i.toNat
```

It is possible to do so by using the following notation:
```
step_array_spec (name := const_array_spec) const_array[i]!
  { x => x.toNat = i.toNat }
  by decide +kernel -- The tactic to prove the proof obligation (expressed in terms of `Array.allIdx`)
```

Note that it is possible to prefix `step_array_spec` with a prefix:
- `local`: the theorem will be marked as `private` with attribute `local step`
- `scoped`: the theorem will be marked with attribute `scoped step`
-/

namespace Aeneas

namespace Std

open Result WP

def Array.allIdx (f : Usize → α → Bool) (ls : List α) (i : Nat := 0) : Bool :=
  match ls with
  | [] => True
  | hd :: tl =>
     -- We avoid manipulating `Usize.max` as it is an axiom
    if h: i ≤ U32.max then
      f i#usize hd ∧ allIdx f tl (i + 1)
    else
      false

/-- Specification about constant arrays -/
theorem Array.index_usize_const_spec {α} [Inhabited α]
  (p : Usize → α → Bool) (p' : Usize → α → Prop)
  (a : Std.Array α n)
  (hp : ∀ i x, p i x ↔ p' i x)
  (hPred : Std.Array.allIdx p a.val)
  (i : Usize) (h : i.toNat < n.toNat) (hn : n.toNat ≤ U32.max) :
  Array.index_usize a i ⦃ v => p' i v ⦄ := by
  let rec aux (l : List α) (i : Nat) (hi : i + l.length = n)
    (hl : ∀ j, l[j]! = a[i + j]!)
    (h : Std.Array.allIdx p l i)
    (j : Nat) (hj : i + j < n) (hij : i + j < U32.max) :
    p' (Usize.ofNat (i + j) (by scalar_tac)) a[i + j]!
    := by
    match l with
    | [] =>
      -- Contradiction
      grind
    | hd :: l =>
      simp [Std.Array.allIdx] at h
      have : i ≤ U32.max := by scalar_tac
      simp [this] at h
      if hj: j = 0 then
        have hl' := hl 0; simp at hl'
        simp [hl'] at h
        have hp' := hp (Usize.ofNat i (by scalar_tac)) a[i]!
        simp [h] at hp'
        simp [hp', hj]
      else
        have hind := aux l (i + 1) (by scalar_tac)
          (by intro j
              replace hl := hl (j + 1)
              simp at hl
              have : i + 1 + j = i + (j + 1) := by omega
              simp only [List.getElem!_eq_getElem?_getD, getElem!_Nat_eq]
              rw [this]
              apply hl)
          (by simp [h]) (j - 1) (by omega) (by omega)
        have : i + 1 + (j - 1) = i + j := by omega
        simp [this] at hind
        simp [hind]
  have hi := aux a.val 0 (by scalar_tac) (by simp) hPred i (by scalar_tac) (by scalar_tac)
  simp at hi
  step as ⟨ x, hx ⟩
  grind

end Std

namespace StepArraySpec

open Lean Lean.Elab Lean.Parser.Command in
syntax (name := stepArraySpec)
  ("local" <|> "scoped")? "step_array_spec" "(" "name" " := " ident ")" ident "[" ident "]" noWs "!"
    " { " ident " => " term " } " " by " tacticSeq : command

open Lean Lean.Elab Lean.Parser.Command Lean.Elab.Command in
def parseStepArraySpec
: TSyntax ``stepArraySpec -> CommandElabM Unit := fun stx => do
  match stx with
  | `($[$vis]? step_array_spec (name := $thm_name:ident) $array:ident [ $i:ident ]! { $x:ident => $pred:term } by $tac:tacticSeq) => do
    -- Compute the visibility of the `step` theorem
    let vis : TSyntax `declModifiers ← do
      match vis with
      | none => `(declModifiers|@[step])
      | some vis =>
        if vis.raw.isOfKind `token.local then
          `(declModifiers| @[local step] private)
        else if vis.raw.isOfKind `token.scoped then
          `(declModifiers| @[scoped step])
        else
          throwUnsupportedSyntax
    -- Elaborate the full theorem
    elabCommand
      (← `(command| $vis:declModifiers theorem $thm_name:ident $i (_ : Aeneas.Std.UScalar.toNat $i < Aeneas.Std.Array.length $array) :
            Aeneas.Std.WP.spec (Aeneas.Std.Array.index_usize $array $i) (fun $x:ident => $pred) :=
            Aeneas.Std.Array.index_usize_const_spec (fun $i:ident $x:ident => $pred) (fun $i:ident $x:ident => $pred)
            $array (by simp) (by $tac) $i (by scalar_tac) (by scalar_tac)))
  | _ => throwUnsupportedSyntax

elab tk:stepArraySpec : command => do
  parseStepArraySpec tk

namespace Tests

open Std

def const_array : Array U32 8#usize := Array.make 8#usize [
  0#u32, 1#u32, 2#u32, 3#u32, 4#u32, 5#u32, 6#u32, 7#u32,
]

step_array_spec (name := const_array_spec) const_array[i]!
  { x => x.toNat = i.toNat }
  by native_decide -- The tactic to prove the proof obligation (expressed in terms of `Array.allIdx`)

end Tests

end StepArraySpec

end Aeneas
