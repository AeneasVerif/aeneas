module

public import RawMatrixView.Types
public import RawBoxProofs
public import Aeneas.Std.Heap.Ranges
import all Aeneas.Std.Heap.Resources
import all RawBoxProofs

@[expose] public section

open Aeneas Aeneas.Std

namespace raw_matrix_view

local macro_rules
  | `(tactic| get_elem_tactic) => `(tactic| agrind)

def words (m : Matrix) : Vector U32 32 :=
  Vector.ofFn fun i => m.val[i.val / 16]!.val[i.val % 16]!

def ofWords (v : Vector U32 32) : Matrix :=
  Array.from (List.ofFn fun r : Fin 2 =>
    Array.from (List.ofFn fun c : Fin 16 => v[r.val * 16 + c.val]) (by simp)) (by simp)

theorem ofWords_words (m : Matrix) : ofWords (words m) = m := by
  apply Aeneas.Std.Array.ext
  apply List.ext_getElem
  · simp [ofWords]
  · intro r hr hr'
    have hr2 : r < 2 := by simpa using hr'
    simp only [ofWords, Array.from_val, List.getElem_ofFn]
    apply Aeneas.Std.Array.ext
    apply List.ext_getElem
    · simp
    · intro c hc hc'
      have hc16 : c < 16 := by simpa using hc'
      simp only [Array.from_val, List.getElem_ofFn, words, Vector.getElem_ofFn]
      have hd : (r * 16 + c) / 16 = r := by agrind
      have hm : (r * 16 + c) % 16 = c := by agrind
      simp [hd, hm, hr2, hc16]

theorem words_ofWords (v : Vector U32 32) : words (ofWords v) = v := by
  apply Vector.ext
  intro i hi
  have hr : i / 16 < 2 := by agrind
  have hc : i % 16 < 16 := by agrind
  simp only [words, Vector.getElem_ofFn, ofWords, Array.from_val]
  rw [List.getElem!_ofFn _ _ hr, Array.from_val, List.getElem!_ofFn _ _ hc]
  have he : i / 16 * 16 + i % 16 = i := by agrind
  simp [he]

def wordBytes (v : Vector U32 32) : Vector U8 128 :=
  v.flatMap raw_box.u32Bytes

def decodeWords (bytes : Vector U8 128) : Vector U32 32 :=
  Vector.ofFn fun i =>
    ⟨bytes[4 * i.val + 3].bv ++ bytes[4 * i.val + 2].bv ++
      bytes[4 * i.val + 1].bv ++ bytes[4 * i.val].bv⟩

theorem decodeWords_wordBytes (v : Vector U32 32) :
    decodeWords (wordBytes v) = v := by
  apply Vector.ext
  intro i hi
  simp only [decodeWords, Vector.getElem_ofFn, wordBytes]
  rw [Vector.getElem_flatMap, Vector.getElem_flatMap, Vector.getElem_flatMap,
    Vector.getElem_flatMap]
  simp only [Nat.mul_add_div (by decide : 0 < 4), Nat.add_mod,
    Nat.mul_mod_right, Nat.zero_add, Nat.reduceMod, Nat.reduceDiv, Nat.add_zero,
    Nat.mul_div_right i (by decide : 0 < 4)]
  exact congrArg (UScalar.mk (ty := .U32)) (raw_box.u32Bytes_roundtrip v[i].bv)

/-- Two contiguous sixteen-word rows, little endian, with 32-byte alignment.
    All 128 bytes are data; none is compiler-inserted padding. -/
def matrixRepr : Aeneas.Std.Repr Matrix where
  size := 128
  align := ⟨32, 5, rfl⟩
  aligned := by decide
  decode bytes := do
    let bytes ← bytes.mapM Aeneas.Std.Byte.numeric
    pure (ofWords (decodeWords bytes))
  encode m bytes := bytes = (wordBytes (words m)).map Aeneas.Std.Byte.data
  encode_complete m := ⟨_, rfl⟩
  encode_decode m bytes encoded := by
    subst bytes
    rw [raw_box.dataBytes_numeric]
    simp [decodeWords_wordBytes, ofWords_words]
  decode_mono bytes bytes' m decoded agree := by
    cases hn : bytes.mapM Aeneas.Std.Byte.numeric
    · simp [hn] at decoded
    · rename_i values
      have same := raw_box.numericBytes_eq bytes bytes' values hn agree
      simpa only [same] using decoded
  encode_valid m bytes i encoded := by
    subst bytes
    simp

theorem matrixRepr_noPointers (m : Matrix) (p : RawPtr Unit) :
    ¬ matrixRepr.Carries m p := by
  rintro ⟨bytes, encoded, i, lane, hp⟩
  change bytes = (wordBytes (words m)).map Aeneas.Std.Byte.data at encoded
  subst bytes
  have impossible := (Vector.getElem_map Aeneas.Std.Byte.data
    (xs := wordBytes (words m)) i.isLt).symm.trans hp
  cases impossible

private theorem bytes_word (a b c d : U8) :
    raw_box.u32Bytes ⟨d.bv ++ c.bv ++ b.bv ++ a.bv⟩ = #v[a, b, c, d] := by
  apply Vector.ext
  intro i hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by agrind
  rcases cases with rfl | rfl | rfl | rfl
  · simp [raw_box.u32Bytes]
    bv_tac 32
  · simp [raw_box.u32Bytes]
    bv_tac 32
  · simp [raw_box.u32Bytes]
    bv_tac 32
  · simp [raw_box.u32Bytes]
    bv_tac 32

theorem wordBytes_decodeWords (bytes : Vector U8 128) :
    wordBytes (decodeWords bytes) = bytes := by
  apply Vector.ext
  intro i hi
  change ((decodeWords bytes).flatMap raw_box.u32Bytes)[i] = bytes[i]
  rw [Vector.getElem_flatMap]
  simp only [decodeWords, Vector.getElem_ofFn, bytes_word]
  have hm : i % 4 < 4 := Nat.mod_lt _ (by decide)
  have he : 4 * (i / 4) + i % 4 = i := by agrind
  have cases : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by agrind
  rcases cases with h | h | h | h
  · simp [h] at he ⊢
    agrind
  · simp [h] at he ⊢
    agrind
  · simp [h] at he ⊢
    agrind
  · simp [h] at he ⊢
    agrind

theorem matrixRepr_calibrated (m : Matrix) (bytes : Vector Aeneas.Std.Byte 128)
    (decoded : matrixRepr.decode bytes = some m)
    (carried : ∀ i : Fin 128, ∀ q lane,
      bytes[i.val] = .pointer q lane → matrixRepr.Carries m q) :
    matrixRepr.encode m bytes := by
  change ((bytes.mapM Aeneas.Std.Byte.numeric).bind
    (fun values => some (ofWords (decodeWords values)))) = some m at decoded
  cases hn : bytes.mapM Aeneas.Std.Byte.numeric
  · simp [hn] at decoded
  · rename_i values
    have data : ∀ i : Fin 128, ∃ value, bytes[i.val] = Aeneas.Std.Byte.data value := by
      intro i
      obtain ⟨value, hv⟩ := vector_mapM_enabled hn i.val i.isLt
      cases hb : bytes[i.val]
      · simp [hb, Aeneas.Std.Byte.numeric] at hv
      · exact ⟨_, rfl⟩
      · rename_i q lane
        exact (matrixRepr_noPointers m q (carried i q lane hb)).elim
    classical
    let numeric := Vector.ofFn fun i => (data i).choose
    have same : bytes = numeric.map Aeneas.Std.Byte.data := by
      apply Vector.ext
      intro i hi
      simpa [numeric] using (data ⟨i, hi⟩).choose_spec
    have numeric_eq : numeric = values := by
      rw [same, raw_box.dataBytes_numeric] at hn
      exact Option.some.inj hn
    have hr : ofWords (decodeWords values) = m := by
      simpa [hn] using decoded
    change bytes = (wordBytes (words m)).map Aeneas.Std.Byte.data
    rw [← hr, words_ofWords, wordBytes_decodeWords]
    exact numeric_eq ▸ same

open SepLogic

private theorem wordCells (v : Vector U32 32) :
    ((v.map (fun x => (raw_box.u32Bytes x).map Aeneas.Std.Byte.data)).flatMap
      (fun bytes => bytes.map (Cell.shared 0))) =
    ((wordBytes v).map Aeneas.Std.Byte.data).map (Cell.shared 0) := by
  unfold wordBytes
  rw [Vector.flatMap_map, Vector.map_flatMap, Vector.map_flatMap]

theorem matrix_to_words (p : RawPtr Matrix) (base : BasePtr) (m : Matrix) (h : Fragment)
    (hp : pointsTo matrixRepr p base m 0 h) :
    pointsToRange raw_box.u32Repr (p.cast U32) base (words m) 0 h := by
  obtain ⟨bytes, encoded, lower, aligned, cells⟩ := hp
  change bytes = (wordBytes (words m)).map Aeneas.Std.Byte.data at encoded
  subst bytes
  refine ⟨(words m).map (fun x => (raw_box.u32Bytes x).map Aeneas.Std.Byte.data), ?_,
    lower, Nat.dvd_trans (by decide : 4 ∣ 32) aligned, ?_⟩
  · intro i
    simp [raw_box.u32Repr]
  · change h = cellsHeap base p.provenance (p.offsetFrom base)
      (((words m).map (fun x => (raw_box.u32Bytes x).map Aeneas.Std.Byte.data)).flatMap
        (fun bytes => bytes.map (Cell.shared 0))).toList
    rw [wordCells]
    exact cells

theorem words_to_matrix (p : RawPtr Matrix) (base : BasePtr) (v : Vector U32 32)
    (h : Fragment) (aligned : 32 ∣ p.address.val)
    (hp : pointsToRange raw_box.u32Repr (p.cast U32) base v 0 h) :
    pointsTo matrixRepr p base (ofWords v) 0 h := by
  obtain ⟨data, encoded, lower, _, cells⟩ := hp
  have he : data = v.map (fun x => (raw_box.u32Bytes x).map Aeneas.Std.Byte.data) := by
    apply Vector.ext
    intro i hi
    simpa [raw_box.u32Repr] using encoded ⟨i, hi⟩
  subst data
  refine ⟨(wordBytes v).map Aeneas.Std.Byte.data, ?_, lower, aligned, ?_⟩
  · change _ = (wordBytes (words (ofWords v))).map Aeneas.Std.Byte.data
    rw [words_ofWords]
    rfl
  · change h = cellsHeap base p.provenance (p.offsetFrom base)
      ((v.map (fun x => (raw_box.u32Bytes x).map Aeneas.Std.Byte.data)).flatMap
        (fun bytes => bytes.map (Cell.shared 0))).toList at cells
    rw [wordCells] at cells
    exact cells

end raw_matrix_view
