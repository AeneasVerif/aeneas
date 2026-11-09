module

public import Aeneas.SepLogic.RangeAccess
public import Aeneas.SepLogic.Local
public import Aeneas.SepLogic.Local

import Aeneas.Tactic.Solver.ScalarTac

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.Bytes

namespace Aeneas.Std

open Aeneas.SepLogic

set_option maxHeartbeats 1000000

theorem cellsHeap_flatMap (base : BasePtr) (prov start : Nat)
    (data : Vector (Vector Cell size) count) (hsize : 0 < size) (r : Resource) :
    cellsHeap base prov start (data.flatMap id).toList r ↔
      ∃ i : Fin count, cellsHeap base prov (start + i.val * size) data[i.val].toList r := by
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj' : j < count * size := by simpa using hj
    have hi : j / size < count := (Nat.div_lt_iff_lt_mul hsize).mpr hj'
    have hk : j % size < size := Nat.mod_lt j hsize
    refine ⟨⟨j / size, hi⟩, j % size, by simpa using hk, ?_⟩
    have hoff : start + j = start + j / size * size + j % size := by
      have he := Nat.mod_add_div j size
      agrind
    simp [hoff]
  · rintro ⟨i, j, hj, rfl⟩
    have hj' : j < size := by simpa using hj
    have hb := range_element_bound (start := 0) (size := size) (r := count * size)
      i.isLt (by simp)
    have hij : i.val * size + j < count * size := by agrind
    refine ⟨i.val * size + j, by simpa using hij, ?_⟩
    have hdiv : (i.val * size + j) / size = i.val := by
      rw [Nat.mul_comm i.val size, Nat.mul_add_div hsize, Nat.div_eq_of_lt hj', Nat.add_zero]
    simp [hdiv, Nat.add_mod, Nat.mod_eq_of_lt hj', Nat.add_assoc]

def otherCells (base : BasePtr) (prov start : Nat)
    (data : Vector (Vector Cell size) count) (i : Fin count) : Fragment :=
  fun r => ∃ j : Fin count, j ≠ i ∧
    cellsHeap base prov (start + j.val * size) data[j.val].toList r

theorem split_cells (base : BasePtr) (prov start : Nat)
    (data : Vector (Vector Cell size) count) (hsize : 0 < size) (i : Fin count) :
    cellsHeap base prov start (data.flatMap id).toList =
      cellsHeap base prov (start + i.val * size) data[i.val].toList ∪
        otherCells base prov start data i := by
  funext r
  apply propext
  rw [cellsHeap_flatMap base prov start data hsize r]
  constructor
  · rintro ⟨j, hj⟩
    by_cases he : j = i
    · subst j
      exact Or.inl hj
    · exact Or.inr ⟨j, he, hj⟩
  · rintro (hi | ⟨j, _, hj⟩)
    · exact ⟨i, hi⟩
    · exact ⟨j, hj⟩

theorem disjoint_otherCells (base : BasePtr) (prov start : Nat)
    (data : Vector (Vector Cell size) count) (i : Fin count) :
    (cellsHeap base prov (start + i.val * size) data[i.val].toList).Disjoint
      (otherCells base prov start data i) := by
  rintro r ⟨a, ha, rfl⟩ r' ⟨j, hne, b, hb, rfl⟩
  have ha' : a < size := by simpa using ha
  have hb' : b < size := by simpa using hb
  have hne' : i.val ≠ j.val := fun he => hne (Fin.ext he.symm)
  have apart : i.val * size + size ≤ j.val * size ∨
      j.val * size + size ≤ i.val * size := by
    rcases Nat.lt_or_gt_of_ne hne' with hlt | hgt
    · left
      have hm := Nat.mul_le_mul_right size (Nat.succ_le_of_lt hlt)
      simp only [Nat.succ_mul] at hm
      exact hm
    · right
      have hm := Nat.mul_le_mul_right size (Nat.succ_le_of_lt hgt)
      simp only [Nat.succ_mul] at hm
      exact hm
  right
  intro he
  have he := Option.some.inj he
  change start + i.val * size + a = start + j.val * size + b at he
  rcases apart with hleft | hright
  · scalar_tac
  · scalar_tac

theorem otherCells_set (base : BasePtr) (prov start : Nat)
    (data : Vector (Vector Cell size) count) (i : Fin count) (bytes : Vector Cell size) :
    otherCells base prov start (data.set i.val bytes i.isLt) i =
      otherCells base prov start data i := by
  funext r
  apply propext
  apply exists_congr
  intro j
  by_cases hj : j = i
  · subst j
    simp
  · have hne : j.val ≠ i.val := fun he => hj (Fin.ext he)
    rw [Vector.getElem_set_ne i.isLt j.isLt (Ne.symm hne)]

/- The same decomposition works for admissible encodings and read-only decodings.
   The remainder retains its exact cells; only the selected element may change. -/
theorem focus_range {T : Type u} (repr : Repr T)
    (valid : T → Vector Byte repr.size → Prop)
    (p q : RawPtr T) (base : BasePtr) (values : Vector T count)
    (depth : Nat) (i : Fin count) (hsize : 0 < repr.size)
    (hprov : q.provenance = p.provenance)
    (haddr : q.address.val = p.address.val + i.val * repr.size)
    (h : Fragment)
    (hp : ∃ data : Vector (Vector Byte repr.size) count,
      (∀ j : Fin count, valid values[j.val] data[j.val]) ∧
      block repr p base (data.flatMap (fun b => b.map (Cell.shared depth))).toList h) :
    ∃ rest : (Fragment → Prop),
      sep (fun h => ∃ bytes, valid values[i.val] bytes ∧
        block repr q base (bytes.map (Cell.shared depth)).toList h) rest h ∧
      ∀ value h', sep (fun h => ∃ bytes, valid value bytes ∧
        block repr q base (bytes.map (Cell.shared depth)).toList h) rest h' →
        ∃ data : Vector (Vector Byte repr.size) count,
          (∀ j : Fin count, valid (values.set i.val value i.isLt)[j.val] data[j.val]) ∧
          block repr p base (data.flatMap (fun b => b.map (Cell.shared depth))).toList h' := by
  obtain ⟨data, encoded, hlo, aligned, cells⟩ := hp
  let old := data.map fun bytes => bytes.map (Cell.shared depth)
  let rest := otherCells base p.provenance (p.offsetFrom base) old i
  have hoff : q.offsetFrom base = p.offsetFrom base + i.val * repr.size := by
    simp only [RawPtr.offsetFrom]
    agrind
  have halign : repr.align.val ∣ q.address.val := by
    rw [haddr]
    exact Nat.dvd_add aligned (repr.aligned_stride i.val)
  refine ⟨fun h => h = rest, ?_, ?_⟩
  ·
    refine ⟨cellsHeap base p.provenance (p.offsetFrom base + i.val * repr.size)
      old[i.val].toList, rest, disjoint_otherCells _ _ _ old i, ?_, ?_, rfl⟩
    · rw [cells]
      simpa only [old, Vector.flatMap_map, Function.comp_def, id_eq] using
        split_cells base p.provenance (p.offsetFrom base) old hsize i
    · refine ⟨data[i.val], encoded i, by agrind, halign, ?_⟩
      simp only [hprov, hoff, old, Vector.getElem_map]
  · rintro value h' ⟨single, other, _, combined, hvalue, hother⟩
    subst other
    obtain ⟨bytes, newEncoded, _, _, singleEq⟩ := hvalue
    refine ⟨data.set i.val bytes i.isLt, ?_, hlo, aligned, ?_⟩
    · intro j
      by_cases he : j = i
      · subst j
        simpa only [Vector.getElem_set_self] using newEncoded
      · have hne : i.val ≠ j.val := fun he' => he (Fin.ext he'.symm)
        simp only [Vector.getElem_set_ne i.isLt j.isLt hne]
        exact encoded j
    · have grouped : (data.set i.val bytes i.isLt).map (fun b => b.map (Cell.shared depth)) =
          old.set i.val (bytes.map (Cell.shared depth)) i.isLt := by
        simp [old]
      have full := split_cells base p.provenance (p.offsetFrom base)
        (old.set i.val (bytes.map (Cell.shared depth)) i.isLt) hsize i
      simp only [Vector.getElem_set_self, otherCells_set] at full
      have joined : h' = cellsHeap base p.provenance (p.offsetFrom base)
          ((old.set i.val (bytes.map (Cell.shared depth)) i.isLt).flatMap id).toList := by
        rw [full, combined, singleEq]
        simp only [hprov, hoff]
        rfl
      simpa only [← grouped, Vector.flatMap_map, Function.comp_def, id_eq] using joined

theorem pointsToRange_focus (repr : Repr T) (p q : RawPtr T) (base : BasePtr)
    (values : Vector T count) (depth : Nat) (i : Fin count) (hsize : 0 < repr.size)
    (hprov : q.provenance = p.provenance)
    (haddr : q.address.val = p.address.val + i.val * repr.size)
    (h : Fragment) (hp : pointsToRange repr p base values depth h) :
    ∃ rest : (Fragment → Prop), sep (pointsTo repr q base values[i.val] depth) rest h ∧
      ∀ value h', sep (pointsTo repr q base value depth) rest h' →
        pointsToRange repr p base (values.set i.val value i.isLt) depth h' :=
  focus_range repr repr.encode p q base values depth i hsize hprov haddr h hp

theorem readableRange_focus (repr : Repr T) (p q : RawPtr T) (base : BasePtr)
    (values : Vector T count) (depth : Nat) (i : Fin count) (hsize : 0 < repr.size)
    (hprov : q.provenance = p.provenance)
    (haddr : q.address.val = p.address.val + i.val * repr.size)
    (h : Fragment) (hp : readableRange repr p base values depth h) :
    ∃ rest : (Fragment → Prop), sep (readable repr q base values[i.val] depth) rest h ∧
      ∀ value h', sep (readable repr q base value depth) rest h' →
        readableRange repr p base (values.set i.val value i.isLt) depth h' :=
  focus_range repr (fun v bytes => repr.decode bytes = some v)
    p q base values depth i hsize hprov haddr h hp
