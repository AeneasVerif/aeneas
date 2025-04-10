import Aeneas.Progress.Progress

/-!
# Progress Array Spec

This file defines a convenient notation to generate a `progress` theorem for
accesses to global arrays. For instance, given:
```
def const_array : Array U32 8#usize := Array.make 8#usize [
  0#u32, 1#u32, 2#u32, 3#u32, 4#u32, 5#u32, 6#u32, 7#u32,
]
```

One might want to prove the following theorem:
```
@[progress]
theorem const_array_spec (i : Usize) (hi : i < 8) :
  ∃ x, Array.index_usize const_array i = ok x ∧ x.val = i.val
```

It is possible to do so by using the following notation:
```
progress_array_spec (name := const_array_spec) const_array[i]!
  { x => x.val = i.val }
  by decide +kernel -- The tactic to prove the proof obligation (expressed in terms of `Array.allIdx`)
```

Note that it is possible to prefix `progress_array_spec` with a prefix:
- `local`: the theorem will be marked as `private` with attribute `local progress`
- `scoped`: the theorem will be marked with attribute `scoped progress`
-/

namespace Aeneas

namespace Std

open Result

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
  (i : Usize) (h : i.val < n.val) (hn : n.val ≤ U32.max) :
  ∃ v, Array.index_usize a i = ok v ∧ p' i v := by
  let rec aux (l : List α) (i : Nat) (hi : i + l.length = n)
    (hl : ∀ j, l[j]! = a[i + j]!)
    (h : Std.Array.allIdx p l i)
    (j : Nat) (hj : i + j < n) (hij : i + j < U32.max) :
    p' (Usize.ofNat (i + j) (by scalar_tac)) a[i + j]!
    := by
    match l with
    | [] =>
      -- Contradiction
      fsimp at hi
      have : i = n := by omega
      omega
    | hd :: l =>
      fsimp [Std.Array.allIdx] at h
      have : i ≤ U32.max := by scalar_tac
      fsimp [this] at h
      if hj: j = 0 then
        have hl' := hl 0; fsimp at hl'
        fsimp [hl'] at h
        have hp' := hp (Usize.ofNat i (by scalar_tac)) a[i]!
        fsimp [h] at hp'
        fsimp [hp', hj]
      else
        have hind := aux l (i + 1) (by scalar_tac)
          (by intro j
              replace hl := hl (j + 1)
              fsimp at hl
              have : i + 1 + j = i + (j + 1) := by omega
              simp only [List.getElem!_eq_getElem?_getD, getElem!_Nat_eq]
              rw [this]
              apply hl)
          (by fsimp [h]) (j - 1) (by omega) (by omega)
        have : i + 1 + (j - 1) = i + j := by omega
        fsimp [this] at hind
        fsimp [hind]
  have hi := aux a.val 0 (by scalar_tac) (by fsimp) hPred i (by scalar_tac) (by scalar_tac)
  fsimp at hi
  progress as ⟨ x, hx ⟩
  fsimp [hi, hx]

end Std

namespace ProgressArraySpec

open Lean Lean.Elab Lean.Parser.Command in
syntax (name := progressArraySpec)
  ("local" <|> "scoped")? "progress_array_spec" "(" "name" " := " ident ")" ident "[" ident "]" noWs "!"
    " { " ident " => " term " } " " by " tacticSeq : command

open Lean Lean.Elab Lean.Parser.Command Lean.Elab.Command in
def parseProgressArraySpec
: TSyntax ``progressArraySpec -> CommandElabM Unit := fun stx => do
  match stx with
  | `($[$vis]? progress_array_spec (name := $thm_name:ident) $array:ident [ $i:ident ]! { $x:ident => $pred:term } by $tac:tacticSeq) => do
    -- Compute the visibility of the `progress` theorem
    let vis : TSyntax `declModifiers ← do
      match vis with
      | none => `(declModifiers|@[progress])
      | some vis =>
        if vis.raw.isOfKind `token.local then
          `(declModifiers| @[local progress] private)
        else if vis.raw.isOfKind `token.scoped then
          `(declModifiers| @[scoped progress])
        else
          throwUnsupportedSyntax
    -- Elaborate the full theorem
    elabCommand
      (← `(command| $vis:declModifiers theorem $thm_name:ident $i (_ : Aeneas.Std.UScalar.val $i < Aeneas.Std.Array.length $array) :
            ∃ $x:ident, Aeneas.Std.Array.index_usize $array $i = Aeneas.Std.Result.ok $x ∧ $pred :=
            Aeneas.Std.Array.index_usize_const_spec (fun $i:ident $x:ident => $pred) (fun $i:ident $x:ident => $pred)
            $array (by simp) (by $tac) $i (by scalar_tac) (by scalar_tac)))
  | _ => throwUnsupportedSyntax

elab tk:progressArraySpec : command => do
  parseProgressArraySpec tk

namespace Tests

open Std

def const_array : Array U32 8#usize := Array.make 8#usize [
  0#u32, 1#u32, 2#u32, 3#u32, 4#u32, 5#u32, 6#u32, 7#u32,
]

progress_array_spec (name := const_array_spec) const_array[i]!
  { x => x.val = i.val }
  by native_decide -- The tactic to prove the proof obligation (expressed in terms of `Array.allIdx`)

end Tests

end ProgressArraySpec

end Aeneas
