module

public import DoublyLinked.RawProperties
public import RawBoxProofs
import all Aeneas.Std.Heap.Repr
import all RawBoxProofs

@[expose] public section

open Aeneas Aeneas.Std

namespace doubly_linked.concrete

set_option maxHeartbeats 1000000

local macro_rules
| `(tactic| get_elem_tactic) => `(tactic| agrind)

/- A calibrated 64-bit little-endian repr(C) layout: two eight-byte pointers,
   a four-byte value, and four genuinely ignored padding bytes. -/
def bytes (node : Node) : Vector Aeneas.Std.Byte 24 :=
  Vector.ofFn fun i =>
    if h : i.val < 8 then .pointer (node.prev.cast Unit) i.val
    else if h' : i.val < 16 then .pointer (node.next.cast Unit) (i.val - 8)
    else if h'' : i.val < 20 then .data (raw_box.u32Bytes node.value)[i.val - 16]
    else .uninit

def field (data : Vector Aeneas.Std.Byte 24) (offset n : Nat)
    (_ : offset + n ≤ 24) : Vector Aeneas.Std.Byte n :=
  Vector.ofFn fun i => data[offset + i.val]

def decode (data : Vector Aeneas.Std.Byte 24) : Option Node := do
  let prev ← (Repr.pointer Node).decode (field data 0 8 (by decide))
  let next ← (Repr.pointer Node).decode (field data 8 8 (by decide))
  let value ← raw_box.u32Repr.decode (field data 16 4 (by decide))
  pure (Node.mk prev next value)

theorem prev_field (node : Node) :
    field (bytes node) 0 8 (by decide) = Repr.pointerEncoding node.prev := by
  apply Vector.ext
  intro i hi
  simp [field, bytes, Repr.pointerEncoding]

theorem next_field (node : Node) :
    field (bytes node) 8 8 (by decide) = Repr.pointerEncoding node.next := by
  apply Vector.ext
  intro i hi
  have lt : 8 + i < 16 := by agrind
  simp [field, bytes, Repr.pointerEncoding, lt]

theorem value_field (node : Node) :
    field (bytes node) 16 4 (by decide) = (raw_box.u32Bytes node.value).map Byte.data := by
  apply Vector.ext
  intro i hi
  have lt : 16 + i < 20 := by agrind
  have ge₁ : ¬ 16 + i < 8 := by agrind
  simp [field, bytes, lt, ge₁]

theorem decode_bytes (node : Node) : decode (bytes node) = some node := by
  unfold decode
  rw [prev_field, next_field, value_field]
  rw [(Repr.pointer Node).encode_decode node.prev _ rfl,
    (Repr.pointer Node).encode_decode node.next _ rfl,
    raw_box.u32Repr.encode_decode node.value _ rfl]
  exact congrArg some (Node.mk_eta node)

theorem field_agrees (data data' : Vector Aeneas.Std.Byte 24)
    (agree : ∀ i : Fin 24, data[i.val] ≠ .uninit → data'[i.val] = data[i.val])
    (offset n : Nat) (bound : offset + n ≤ 24) :
    ∀ i : Fin n, (field data offset n bound)[i.val] ≠ .uninit →
      (field data' offset n bound)[i.val] = (field data offset n bound)[i.val] := by
  intro i h
  simpa [field] using agree ⟨offset + i.val, by agrind⟩ (by simpa [field] using h)

theorem decode_mono (data data' : Vector Aeneas.Std.Byte 24) (node : Node)
    (decoded : decode data = some node)
    (agree : ∀ i : Fin 24, data[i.val] ≠ .uninit → data'[i.val] = data[i.val]) :
    decode data' = some node := by
  obtain ⟨prev, hp, rest⟩ := Option.bind_eq_some_iff.mp decoded
  obtain ⟨next, hn, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨value, hv, result⟩ := Option.bind_eq_some_iff.mp rest
  have hp' := (Repr.pointer Node).decode_mono _ _ prev hp (field_agrees _ _ agree 0 8 _)
  have hn' := (Repr.pointer Node).decode_mono _ _ next hn (field_agrees _ _ agree 8 8 _)
  have hv' := raw_box.u32Repr.decode_mono _ _ value hv (field_agrees _ _ agree 16 4 _)
  simpa only [decode, hp', hn', hv', Bind.bind, Option.bind_some] using result

theorem bytes_valid (node : Node) (i : Fin 24) :
    match (bytes node)[i.val] with
    | .pointer _ lane => lane < pointerWidth
    | _ => True := by
  simp only [bytes, Vector.getElem_ofFn]
  by_cases h : i.val < 8
  · simpa only [dite_eq_left h] using h
  · by_cases h' : i.val < 16
    · simp only [dite_eq_right h, dite_eq_left h']
      change i.val - 8 < 8
      agrind
    · by_cases h'' : i.val < 20
      · simp only [dite_eq_right h, dite_eq_right h', dite_eq_left h'']
      · simp only [dite_eq_right h, dite_eq_right h', dite_eq_right h'']

attribute [local irreducible] bytes

def repr : Aeneas.Std.Repr Node where
  size := 24
  align := ⟨8, 3, rfl⟩
  aligned := by decide
  decode := decode
  encode node data := data = bytes node
  encode_complete node := ⟨bytes node, rfl⟩
  encode_decode node data h := h ▸ decode_bytes node
  decode_mono := decode_mono
  encode_valid node data i h := h.symm ▸ bytes_valid node i

theorem layout : NodeLayout repr where
  carries node q h := by
    obtain ⟨data, encoded, i, lane, occurrence⟩ := h
    change data = bytes node at encoded
    subst data
    change (bytes node)[i.val]'(show i.val < 24 from i.isLt) = .pointer q lane at occurrence
    simp only [bytes, Vector.getElem_ofFn] at occurrence
    split at occurrence
    · exact .inl (congrArg RawPtr.provenance (Byte.pointer.inj occurrence).1).symm
    · split at occurrence
      · exact .inr (congrArg RawPtr.provenance (Byte.pointer.inj occurrence).1).symm
      · split at occurrence
        · contradiction
        · contradiction
  links node data encoded := by
    change data = bytes node at encoded
    subst data
    constructor
    · refine ⟨⟨0, by decide⟩, 0, ?_⟩
      change (bytes node)[0] = .pointer (node.prev.cast Unit) 0
      simp [bytes]
    · refine ⟨⟨8, by decide⟩, 0, ?_⟩
      change (bytes node)[8] = .pointer (node.next.cast Unit) 0
      simp [bytes]

end doubly_linked.concrete
