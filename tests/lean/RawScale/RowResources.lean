module

public import RawScale.Kernel
public import Mathlib.Data.List.Forall2
import all Aeneas.Std.Heap.Resources
import all RawBoxProofs

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic

namespace raw_scale

local macro_rules
  | `(tactic| get_elem_tactic) => `(tactic| agrind)

private theorem rowCells (v : Vector U32 16) (depth : Nat) :
    ((v.map (fun x => (raw_box.u32Bytes x).map Aeneas.Std.Byte.data)).flatMap
      (fun bytes => bytes.map (Cell.shared depth))) =
    ((rowBytes v).map Aeneas.Std.Byte.data).map (Cell.shared depth) := by
  unfold rowBytes
  rw [Vector.flatMap_map, Vector.map_flatMap, Vector.map_flatMap]

theorem row_to_words (p : RawPtr Row15) (base : BasePtr) (row : Row15)
    (depth : Nat) (h : Fragment) (hp : pointsTo rowRepr p base row depth h) :
    pointsToRange raw_box.u32Repr (p.cast U32) base (rowWords row) depth h := by
  obtain ⟨bytes, encoded, lower, aligned, cells⟩ := hp
  change bytes = (rowBytes (rowWords row)).map Aeneas.Std.Byte.data at encoded
  subst bytes
  refine ⟨(rowWords row).map (fun x => (raw_box.u32Bytes x).map Aeneas.Std.Byte.data), ?_,
    lower, Nat.dvd_trans (by decide : 4 ∣ 32) aligned, ?_⟩
  · intro i
    simp [raw_box.u32Repr]
  · change h = cellsHeap base p.provenance (p.offsetFrom base)
      (((rowWords row).map (fun x => (raw_box.u32Bytes x).map Aeneas.Std.Byte.data)).flatMap
        (fun bytes => bytes.map (Cell.shared depth))).toList
    rw [rowCells]
    exact cells

theorem words_to_row (p : RawPtr Row15) (base : BasePtr) (v : Vector U32 16)
    (depth : Nat) (h : Fragment) (aligned : 32 ∣ p.address.val)
    (hp : pointsToRange raw_box.u32Repr (p.cast U32) base v depth h) :
    pointsTo rowRepr p base (rowOfWords v) depth h := by
  obtain ⟨data, encoded, lower, _, cells⟩ := hp
  have he : data = v.map (fun x => (raw_box.u32Bytes x).map Aeneas.Std.Byte.data) := by
    apply Vector.ext
    intro i hi
    simpa [raw_box.u32Repr] using encoded ⟨i, hi⟩
  subst data
  refine ⟨(rowBytes v).map Aeneas.Std.Byte.data, ?_, lower, aligned, ?_⟩
  · change _ = (rowBytes (rowWords (rowOfWords v))).map Aeneas.Std.Byte.data
    rw [rowWords_rowOfWords]
    rfl
  · change h = cellsHeap base p.provenance (p.offsetFrom base)
      ((v.map (fun x => (raw_box.u32Bytes x).map Aeneas.Std.Byte.data)).flatMap
        (fun bytes => bytes.map (Cell.shared depth))).toList at cells
    rw [rowCells] at cells
    exact cells

theorem rowRepr_noPointers (row : Row15) (p : RawPtr Unit) :
    ¬ rowRepr.Carries row p := by
  rintro ⟨bytes, encoded, i, lane, hp⟩
  change bytes = (rowBytes (rowWords row)).map Aeneas.Std.Byte.data at encoded
  subst bytes
  have impossible := (Vector.getElem_map Aeneas.Std.Byte.data
    (xs := rowBytes (rowWords row)) i.isLt).symm.trans hp
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

theorem rowBytes_decodeRowWords (bytes : Vector U8 64) :
    rowBytes (decodeRowWords bytes) = bytes := by
  apply Vector.ext
  intro i hi
  change ((decodeRowWords bytes).flatMap raw_box.u32Bytes)[i] = bytes[i]
  rw [Vector.getElem_flatMap]
  simp only [decodeRowWords, Vector.getElem_ofFn]
  simp only [bytes_word]
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

theorem rowRepr_calibrated (row : Row15) (bytes : Vector Aeneas.Std.Byte 64)
    (decoded : rowRepr.decode bytes = some row)
    (carried : ∀ i : Fin 64, ∀ q lane,
      bytes[i.val] = .pointer q lane → rowRepr.Carries row q) :
    rowRepr.encode row bytes := by
  change ((bytes.mapM Aeneas.Std.Byte.numeric).bind
    (fun values => some (rowOfWords (decodeRowWords values)))) = some row at decoded
  cases hn : bytes.mapM Aeneas.Std.Byte.numeric
  · simp [hn] at decoded
  · rename_i values
    have data : ∀ i : Fin 64, ∃ value, bytes[i.val] = Aeneas.Std.Byte.data value := by
      intro i
      obtain ⟨value, hv⟩ := vector_mapM_enabled hn i.val i.isLt
      cases hb : bytes[i.val]
      · simp [hb, Aeneas.Std.Byte.numeric] at hv
      · exact ⟨_, rfl⟩
      · rename_i q lane
        exact (rowRepr_noPointers row q (carried i q lane hb)).elim
    classical
    let numeric := Vector.ofFn fun i => (data i).choose
    have same' : bytes = numeric.map Aeneas.Std.Byte.data := by
      apply Vector.ext
      intro i hi
      simpa [numeric] using (data ⟨i, hi⟩).choose_spec
    have numeric_eq : numeric = values := by
      rw [same', raw_box.dataBytes_numeric] at hn
      exact Option.some.inj hn
    have hr : rowOfWords (decodeRowWords values) = row := by
      simpa [hn] using decoded
    change bytes = (rowBytes (rowWords row)).map Aeneas.Std.Byte.data
    rw [← hr, rowWords_rowOfWords, rowBytes_decodeRowWords]
    exact numeric_eq ▸ same'

private theorem list_mapM_iff {α β : Type} (f : α → Option β) (xs : List α) (ys : List β) :
    xs.mapM f = some ys ↔ List.Forall₂ (fun x y => f x = some y) xs ys := by
  induction xs generalizing ys
  · cases ys
    · simp
    · simp
  · rename_i x xs ih
    cases hx : f x
    · cases ys
      · simp [List.mapM_cons, hx]
      · simp [List.mapM_cons, hx]
    · rename_i y
      cases ht : xs.mapM f
      · cases ys
        · simp [List.mapM_cons, hx, ht]
        · simp [List.mapM_cons, hx, ← ih, ht]
      · rename_i tail
        cases ys
        · simp [List.mapM_cons, hx, ht]
        · simp [List.mapM_cons, hx, ← ih, ht]

private theorem vector_mapM_iff {α β : Type} (f : α → Option β)
    (xs : Vector α n) (ys : Vector β n) :
    xs.mapM f = some ys ↔ ∀ i (hi : i < n), f xs[i] = some ys[i] := by
  have hl := vector_mapM_toList (f := f) xs
  have injective : Function.Injective (Option.map (Vector.toList (α := β) (n := n))) :=
    Option.map_injective (fun _ _ h => Vector.toList_inj.mp h)
  rw [← injective.eq_iff, hl]
  simp only [Option.map_some, list_mapM_iff, List.forall₂_iff_get]
  simp

theorem readable_row_to_words (p : RawPtr Row15) (base : BasePtr) (row : Row15)
    (depth : Nat) (h : Fragment) (hp : readable rowRepr p base row depth h) :
    readableRange raw_box.u32Repr (p.cast U32) base (rowWords row) depth h := by
  obtain ⟨bytes, decoded, lower, aligned, cells⟩ := hp
  change Vector Aeneas.Std.Byte 64 at bytes
  change 32 ∣ p.address.val at aligned
  change ((bytes.mapM Aeneas.Std.Byte.numeric).bind
    (fun values => some (rowOfWords (decodeRowWords values)))) = some row at decoded
  cases hn : bytes.mapM Aeneas.Std.Byte.numeric
  · simp [hn] at decoded
  · rename_i values
    have hr : rowWords row = decodeRowWords values := by
      have he : rowOfWords (decodeRowWords values) = row := by simpa [hn] using decoded
      rw [← he, rowWords_rowOfWords]
    let data : Vector (Vector Aeneas.Std.Byte 4) 16 :=
      Vector.ofFn fun i => Vector.ofFn fun j => bytes[4 * i.val + j.val]
    have flat : data.flatMap (fun b => b.map (Cell.shared depth)) =
        bytes.map (Cell.shared depth) := by
      apply Vector.ext
      intro i hi
      rw [Vector.getElem_flatMap]
      simp only [data, Vector.getElem_ofFn, Vector.getElem_map]
      have he : 4 * (i / 4) + i % 4 = i := by agrind
      simp only [he]
    refine ⟨data, ?_, lower, Nat.dvd_trans (by decide : 4 ∣ 32) aligned, ?_⟩
    · intro i
      have group : (data[i.val]).mapM Aeneas.Std.Byte.numeric =
          some (Vector.ofFn fun j : Fin 4 => values[4 * i.val + j.val]) := by
        apply (vector_mapM_iff _ _ _).mpr
        intro j hj
        simpa [data] using
          (vector_mapM_iff _ _ _).mp hn (4 * i.val + j) (by agrind)
      change ((data[i.val].mapM Aeneas.Std.Byte.numeric).bind
        (fun v => some (⟨v[3].bv ++ v[2].bv ++ v[1].bv ++ v[0].bv⟩ : U32))) = _
      rw [group, hr]
      simp [decodeRowWords]
    · change h = cellsHeap base p.provenance (p.offsetFrom base)
        (data.flatMap (fun b => b.map (Cell.shared depth))).toList
      rw [flat]
      exact cells

end raw_scale
