module

public import RawScale.Types
public import RawBoxProofs
import all RawBoxProofs

@[expose] public section

open Aeneas Aeneas.Std

namespace raw_scale

local macro_rules
  | `(tactic| get_elem_tactic) => `(tactic| agrind)

def rowWords (row : Row13) : Vector U32 16 :=
  Vector.ofFn fun i => row.val[i.val]

def rowOfWords (words : Vector U32 16) : Row13 :=
  Array.from words.toList (by simp)

theorem rowOfWords_rowWords (row : Row13) : rowOfWords (rowWords row) = row := by
  apply Aeneas.Std.Array.ext
  apply List.ext_getElem
  · simp [rowOfWords]
  · intro i hi hi'
    simp [rowOfWords, rowWords]

theorem rowWords_rowOfWords (words : Vector U32 16) : rowWords (rowOfWords words) = words := by
  apply Vector.ext
  intro i hi
  simp [rowWords, rowOfWords]

def rowBytes (words : Vector U32 16) : Vector U8 64 :=
  words.flatMap raw_box.u32Bytes

def decodeRowWords (bytes : Vector U8 64) : Vector U32 16 :=
  Vector.ofFn fun i =>
    ⟨bytes[4 * i.val + 3].bv ++ bytes[4 * i.val + 2].bv ++
      bytes[4 * i.val + 1].bv ++ bytes[4 * i.val].bv⟩

theorem decodeRowWords_rowBytes (words : Vector U32 16) :
    decodeRowWords (rowBytes words) = words := by
  apply Vector.ext
  intro i hi
  simp only [decodeRowWords, Vector.getElem_ofFn, rowBytes]
  rw [Vector.getElem_flatMap, Vector.getElem_flatMap, Vector.getElem_flatMap,
    Vector.getElem_flatMap]
  simp only [Nat.mul_add_div (by decide : 0 < 4), Nat.add_mod,
    Nat.mul_mod_right, Nat.zero_add, Nat.reduceMod, Nat.reduceDiv, Nat.add_zero,
    Nat.mul_div_right i (by decide : 0 < 4)]
  exact congrArg (UScalar.mk (ty := .U32)) (raw_box.u32Bytes_roundtrip words[i].bv)

/-- Sixteen initialized little-endian words, aligned to 32 bytes.
    The logical thirteen-element prefix does not change the physical stride. -/
def rowRepr : Aeneas.Std.Repr Row13 where
  size := 64
  align := ⟨32, 5, rfl⟩
  aligned := by decide
  decode bytes := do
    let bytes ← bytes.mapM Aeneas.Std.Byte.numeric
    pure (rowOfWords (decodeRowWords bytes))
  encode row bytes := bytes = (rowBytes (rowWords row)).map Aeneas.Std.Byte.data
  encode_complete row := ⟨_, rfl⟩
  encode_decode row bytes encoded := by
    subst bytes
    rw [raw_box.dataBytes_numeric]
    simp [decodeRowWords_rowBytes, rowOfWords_rowWords]
  decode_mono bytes bytes' row decoded agree := by
    cases hn : bytes.mapM Aeneas.Std.Byte.numeric
    · simp [hn] at decoded
    · rename_i values
      have same := raw_box.numericBytes_eq bytes bytes' values hn agree
      simpa only [same] using decoded
  encode_valid row bytes i encoded := by
    subst bytes
    simp

end raw_scale
