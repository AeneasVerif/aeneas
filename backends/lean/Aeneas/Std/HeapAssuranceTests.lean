module

import all Aeneas.Std.HeapTests
import Aeneas.Std.Heap.ScopedView
import Aeneas.Std.Heap.Execution
import all Aeneas.Std.Heap.Repr
import all Aeneas.Std.Heap.Model
import Aeneas.Std.Scalar.Notations

open Aeneas

namespace Aeneas.Std.HeapTests

/- The transition tests deliberately include rejected operations. Their Rust
   counterparts execute only valid paths, never the rejected/UB alternatives. -/
def siblingScopes : Option (List U8 × U8) := do
  let (parent, s₀) ← Heap.newBlock Repr.u8 (enc [byte 1, byte 2, byte 3, byte 4])
    true (addr 256) none Heap.empty
  let (other, s₁) ← Heap.newBlock Repr.u8 (enc [byte 5]) true (addr 512) none s₀
  let s₂ ← Heap.borrowRange Repr.u8 parent 4 s₁
  let (left, s₃) ← Heap.newBlock Repr.u8 (enc [byte 1, byte 2])
    false (addr 256) (some parent.provenance) s₂
  let (right, s₄) ← Heap.newBlock Repr.u8 (enc [byte 3, byte 4])
    false (addr 258) (some parent.provenance) s₃
  let s₅ ← Heap.shareRange Repr.u8 left 2 s₄
  let (child, s₆) ← Heap.newSharedExposure Repr.u8 (enc [byte 1, byte 2])
    (addr 256) (some parent.provenance) s₅
  require ((Heap.endShareRange Repr.u8 left 2 s₆).isNone)
  let s₇ ← Heap.endSharedExposure Repr.u8 child 2 s₆
  require ((Heap.endSharedExposure Repr.u8 child 2 s₇).isNone)
  let s₈ ← Heap.endShareRange Repr.u8 left 2 s₇
  let s₉ ← Heap.shareRange Repr.u8 right 0 s₈
  let s₁₀ ← Heap.endShareRange Repr.u8 right 0 s₉
  let s₁₁ ← put left (byte 10) s₁₀
  let s₁₂ ← put (shift right 1) (byte 20) s₁₁
  let s₁₃ ← put other (byte 99) s₁₂
  let a ← Heap.readRange Repr.u8 left 2 s₁₃
  let b ← Heap.readRange Repr.u8 right 2 s₁₃
  let s₁₄ ← Heap.endExposureAt Repr.u8 left 2 0 s₁₃
  require ((Heap.dealloc Repr.u8 parent 4 s₁₄).isNone &&
    (Heap.endExposureAt Repr.u8 left 2 0 s₁₄).isNone)
  let s₁₅ ← Heap.endExposureAt Repr.u8 right 2 0 s₁₄
  require (s₁₅.noAliases parent.provenance parent.provenance)
  let s₁₆ ← Heap.endBorrowRange Repr.u8 parent (enc (a ++ b)) s₁₅
  require ((Heap.endBorrowRange Repr.u8 parent (enc (a ++ b)) s₁₆).isNone)
  let result ← Heap.readRange Repr.u8 parent 4 s₁₆
  let framed ← Heap.read Repr.u8 other s₁₆
  let s₁₇ ← Heap.dealloc Repr.u8 parent 4 s₁₆
  require (Heap.read Repr.u8 other s₁₇ == some framed)
  some (result, framed)

example : siblingScopes = some ([10, 2, 3, 20].map byte, byte 99) := by native_decide

def boolRepr : Repr Bool where
  size := 1
  align := ⟨1, 0, rfl⟩
  aligned := by decide
  decode bytes := do
    let b ← bytes[0].numeric
    if b = 0#u8 then some false else if b = 1#u8 then some true else none
  encode value bytes := bytes = #v[.data (if value then 1#u8 else 0#u8)]
  encode_complete value := ⟨_, rfl⟩
  encode_decode := by
    intro value bytes h
    subst bytes
    cases value
    · rfl
    · rfl
  decode_mono := by
    intro bytes bytes' value decoded agree
    have initialized : bytes[0] ≠ .uninit := by
      intro eq
      simp [eq, Byte.numeric] at decoded
    rw [agree ⟨0, by decide⟩ initialized]
    exact decoded
  encode_valid := by
    intro value bytes i h
    subst bytes
    simp

def zstRepr : Repr Unit where
  size := 0
  align := ⟨1, 0, rfl⟩
  aligned := by decide
  decode _ := some ()
  encode _ _ := True
  encode_complete _ := ⟨#v[], trivial⟩
  encode_decode := by intros; rfl
  decode_mono := by intros; rfl
  encode_valid _ _ i := Fin.elim0 i

def paddingAndValidity : Option Unit := do
  let (p, s₀) ← Heap.alloc padded 1 (addr 256) Heap.empty
  require ((Heap.read padded p s₀).isNone)
  let s₁ ← put p (byte 7) s₀
  require (Heap.read padded p s₁ == some (byte 7) &&
    (Heap.read Repr.u8 (shift p 1) s₁).isNone)
  let (copy, s₂) ← Heap.alloc padded 1 (addr 258) s₁
  let s₃ ← Heap.copyBytes p copy 2 s₂
  require (Heap.read padded copy s₃ == some (byte 7) &&
    (Heap.read Repr.u8 (shift copy 1) s₃).isNone)
  let (b, s₄) ← Heap.newBlock Repr.u8 (enc [byte 2]) true (addr 512) none s₃
  require ((Heap.read boolRepr (b.cast Bool) s₄).isNone)
  let s₅ ← put b (byte 1) s₄
  require (Heap.read boolRepr (b.cast Bool) s₅ == some true)
  let (z, s₆) ← Heap.alloc zstRepr 1 (addr 768) s₅
  require ((Heap.read zstRepr z s₆).isNone)
  let s₇ ← Heap.borrowRange zstRepr z 0 s₆
  let s₈ ← Heap.endBorrowRange zstRepr z [] s₇
  let _ ← Heap.dealloc zstRepr z 1 s₈
  some ()

example : paddingAndValidity = some () := by native_decide

/- Explore every numeric byte, including all 254 invalid Bool encodings.
   The test goes through permission-aware reading, not only the decoder. -/
example : (List.range 256).all (fun n =>
    boolRepr.read #v[Cell.shared 0 (.data (byte n))] 0 ==
      (if n = 0 then some false else if n = 1 then some true else none)) = true := by
  native_decide

example : (List.range 256).all (fun n =>
    padded.read #v[Cell.shared 0 (.data (byte 7)), Cell.shared 0 (.data (byte n))] 0 ==
      some (byte 7)) = true := by native_decide

/-- Exact initialization observation cannot satisfy the descriptor's padding
    monotonicity law. Raw snapshots, not a fictional MaybeUninit codec, are used. -/
theorem no_exact_uninit_decoder (repr : Repr (Option U8))
    (decodeUninit : repr.decode (Vector.replicate repr.size .uninit) = some none)
    (decodeValue : repr.decode (Vector.replicate repr.size (.data 7#u8)) = some (some 7#u8)) :
    False := by
  have monotone := repr.decode_mono _ (Vector.replicate repr.size (.data 7#u8))
    none decodeUninit (by intro i impossible; simp at impossible)
  rw [decodeValue] at monotone
  cases monotone

/-- Bounded, exhaustive lane corruption exploration already covers all pointer
    byte positions, not just one hand-picked damaged representation. -/
example : laneCoherence = some () := by native_decide

/-- info: 'Aeneas.Std.SepLogic.RootReturn.after_closed_views' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SepLogic.RootReturn.after_closed_views

end Aeneas.Std.HeapTests
