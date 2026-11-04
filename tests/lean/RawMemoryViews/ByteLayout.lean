module

public import RawBoxProofs
public import Aeneas.Std.Heap.Ranges
import all Aeneas.Std.Heap.Repr
import all Aeneas.Std.Heap.Resources
import all RawBoxProofs

@[expose] public section

open Aeneas Aeneas.Std

namespace raw_memory_views

local macro_rules
  | `(tactic| get_elem_tactic) => `(tactic| agrind)

abbrev Words := Aeneas.Std.Array U16 8#usize

def wordVector (words : Words) : Vector U16 8 :=
  ⟨words.val.toArray, by simp⟩

def ofWordVector (words : Vector U16 8) : Words :=
  .from words.toList (by simp)

@[simp] theorem wordVector_ofWordVector (words : Vector U16 8) :
    wordVector (ofWordVector words) = words := by
  apply Vector.toList_inj.mp
  simp [wordVector, ofWordVector]

@[simp] theorem ofWordVector_wordVector (words : Words) :
    ofWordVector (wordVector words) = words := by
  apply Aeneas.Std.Array.ext
  simp [wordVector, ofWordVector]

def u16Bytes (word : U16) : Vector U8 2 :=
  #v[⟨word.bv.extractLsb' 0 8⟩, ⟨word.bv.extractLsb' 8 8⟩]

def wordBytes (words : Vector U16 8) : Vector U8 16 :=
  words.flatMap u16Bytes

def decodeWords (bytes : Vector U8 16) : Vector U16 8 :=
  Vector.ofFn fun i => ⟨bytes[2 * i.val + 1].bv ++ bytes[2 * i.val].bv⟩

theorem u16Bytes_roundtrip (word : U16) :
    (u16Bytes word)[1].bv ++ (u16Bytes word)[0].bv = word.bv := by
  change word.bv.extractLsb' 8 8 ++ word.bv.extractLsb' 0 8 = word.bv
  bv_tac 16

theorem decodeWords_wordBytes (words : Vector U16 8) :
    decodeWords (wordBytes words) = words := by
  apply Vector.ext
  intro i hi
  simp only [decodeWords, Vector.getElem_ofFn, wordBytes]
  rw [Vector.getElem_flatMap, Vector.getElem_flatMap]
  simp only [Nat.mul_add_div (by decide : 0 < 2), Nat.add_mod,
    Nat.mul_mod_right, Nat.zero_add, Nat.reduceMod, Nat.reduceDiv, Nat.add_zero,
    Nat.mul_div_right i (by decide : 0 < 2)]
  exact congrArg (UScalar.mk (ty := .U16)) (u16Bytes_roundtrip words[i])

private theorem bytes_word (a b : U8) :
    u16Bytes ⟨b.bv ++ a.bv⟩ = #v[a, b] := by
  apply Vector.ext
  intro i hi
  have cases : i = 0 ∨ i = 1 := by agrind
  rcases cases with rfl | rfl
  · simp [u16Bytes]
    bv_tac 16
  · simp [u16Bytes]
    bv_tac 16

theorem wordBytes_decodeWords (bytes : Vector U8 16) :
    wordBytes (decodeWords bytes) = bytes := by
  apply Vector.ext
  intro i hi
  rw [wordBytes, Vector.getElem_flatMap]
  simp only [decodeWords, Vector.getElem_ofFn, bytes_word]
  have he : 2 * (i / 2) + i % 2 = i := by agrind
  have cases : i % 2 = 0 ∨ i % 2 = 1 := by agrind
  rcases cases with h | h
  · simp [h] at he ⊢
    agrind
  · simp [h] at he ⊢
    agrind

/-- Concrete little-endian `[u16; 8]`: sixteen initialized bytes, alignment two. -/
def wordsRepr : Aeneas.Std.Repr Words where
  size := 16
  align := ⟨2, 1, rfl⟩
  aligned := by decide
  decode bytes := do
    let values ← bytes.mapM Aeneas.Std.Byte.numeric
    pure (ofWordVector (decodeWords values))
  encode words bytes := bytes = (wordBytes (wordVector words)).map Aeneas.Std.Byte.data
  encode_complete words := ⟨_, rfl⟩
  encode_decode words bytes encoded := by
    subst bytes
    rw [raw_box.dataBytes_numeric]
    simp [decodeWords_wordBytes]
  decode_mono bytes bytes' words decoded agree := by
    cases hn : bytes.mapM Aeneas.Std.Byte.numeric
    · simp [hn] at decoded
    · rename_i values
      have same := raw_box.numericBytes_eq bytes bytes' values hn agree
      simpa only [same] using decoded
  encode_valid words bytes i encoded := by
    subst bytes
    simp

theorem wordsRepr_noPointers (words : Words) (p : RawPtr Unit) :
    ¬ wordsRepr.Carries words p := by
  rintro ⟨bytes, encoded, i, lane, hp⟩
  change bytes = (wordBytes (wordVector words)).map Aeneas.Std.Byte.data at encoded
  subst bytes
  have impossible := (Vector.getElem_map Aeneas.Std.Byte.data
    (xs := wordBytes (wordVector words)) i.isLt).symm.trans hp
  cases impossible

theorem wordsRepr_calibrated (words : Words) (bytes : Vector Aeneas.Std.Byte 16)
    (decoded : wordsRepr.decode bytes = some words)
    (carried : ∀ i : Fin 16, ∀ q lane,
      bytes[i.val] = .pointer q lane → wordsRepr.Carries words q) :
    wordsRepr.encode words bytes := by
  change ((bytes.mapM Aeneas.Std.Byte.numeric).bind
    (fun values => some (ofWordVector (decodeWords values)))) = some words at decoded
  cases hn : bytes.mapM Aeneas.Std.Byte.numeric
  · simp [hn] at decoded
  · rename_i values
    have data : ∀ i : Fin 16, ∃ value, bytes[i.val] = Aeneas.Std.Byte.data value := by
      intro i
      obtain ⟨value, hv⟩ := vector_mapM_enabled hn i.val i.isLt
      cases hb : bytes[i.val]
      · simp [hb, Aeneas.Std.Byte.numeric] at hv
      · exact ⟨_, rfl⟩
      · rename_i q lane
        exact (wordsRepr_noPointers words q (carried i q lane hb)).elim
    classical
    let numeric := Vector.ofFn fun i => (data i).choose
    have same : bytes = numeric.map Aeneas.Std.Byte.data := by
      apply Vector.ext
      intro i hi
      simpa [numeric] using (data ⟨i, hi⟩).choose_spec
    have numeric_eq : numeric = values := by
      rw [same, raw_box.dataBytes_numeric] at hn
      exact Option.some.inj hn
    have hr : ofWordVector (decodeWords values) = words := by
      simpa [hn] using decoded
    change bytes = (wordBytes (wordVector words)).map Aeneas.Std.Byte.data
    rw [← hr, wordVector_ofWordVector, wordBytes_decodeWords]
    exact numeric_eq ▸ same

open SepLogic

private theorem byteCells (bytes : Vector U8 16) :
    ((bytes.map (fun x => #v[Aeneas.Std.Byte.data x])).flatMap
      (fun data => data.map (Cell.shared 0))) =
    (bytes.map Aeneas.Std.Byte.data).map (Cell.shared 0) := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_flatMap]
  simp

theorem words_to_bytes (p : RawPtr Words) (base : BasePtr) (words : Words) (h : Fragment)
    (hp : pointsTo wordsRepr p base words 0 h) :
    pointsToRange Aeneas.Std.Repr.u8 (p.cast U8) base
      (wordBytes (wordVector words)) 0 h := by
  obtain ⟨bytes, encoded, lower, _, cells⟩ := hp
  change bytes = (wordBytes (wordVector words)).map Aeneas.Std.Byte.data at encoded
  subst bytes
  refine ⟨(wordBytes (wordVector words)).map (fun x => #v[Aeneas.Std.Byte.data x]), ?_,
    lower, by simp [Aeneas.Std.Repr.u8], ?_⟩
  · intro i
    simp [Aeneas.Std.Repr.u8]
  · change h = cellsHeap base p.provenance (p.offsetFrom base)
      (((wordBytes (wordVector words)).map (fun x => #v[Aeneas.Std.Byte.data x])).flatMap
        (fun data : Vector Aeneas.Std.Byte 1 => data.map (Cell.shared 0))).toList
    rw [byteCells]
    exact cells

theorem bytes_to_words (p : RawPtr Words) (base : BasePtr) (bytes : Vector U8 16)
    (h : Fragment) (aligned : 2 ∣ p.address.val)
    (hp : pointsToRange Aeneas.Std.Repr.u8 (p.cast U8) base bytes 0 h) :
    pointsTo wordsRepr p base (ofWordVector (decodeWords bytes)) 0 h := by
  obtain ⟨data, encoded, lower, _, cells⟩ := hp
  have he : data = bytes.map (fun x => #v[Aeneas.Std.Byte.data x]) := by
    apply Vector.ext
    intro i hi
    simpa [Aeneas.Std.Repr.u8] using encoded ⟨i, hi⟩
  subst data
  refine ⟨bytes.map Aeneas.Std.Byte.data, ?_, lower, aligned, ?_⟩
  · change _ = (wordBytes (wordVector (ofWordVector (decodeWords bytes)))).map _
    rw [wordVector_ofWordVector, wordBytes_decodeWords]
    rfl
  · change h = cellsHeap base p.provenance (p.offsetFrom base)
      ((bytes.map (fun x => #v[Aeneas.Std.Byte.data x])).flatMap
        (fun data => data.map (Cell.shared 0))).toList at cells
    rw [byteCells] at cells
    exact cells

end raw_memory_views
