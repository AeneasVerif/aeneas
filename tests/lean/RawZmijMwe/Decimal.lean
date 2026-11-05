module

public import RawRyuMwe.ByteOps

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic scalar_mwe
open scoped Aeneas.Std.HeapWP

namespace raw_zmij_mwe

set_option maxHeartbeats 1000000

local macro_rules
| `(tactic| get_elem_tactic) => `(tactic| agrind)

def ascii (n : Nat) : U8 := ⟨BitVec.ofNat 8 (48 + n)⟩

theorem ascii_val (n : Nat) (bound : n < 10) : (ascii n).val = 48 + n := by
  change (48 + n) % 256 = 48 + n
  apply Nat.mod_eq_of_lt
  agrind

def decimalDigits (value : U8) : List U8 :=
  if 100 ≤ value.val then
    [ascii (value.val / 100), ascii (value.val % 100 / 10), ascii (value.val % 10)]
  else if 10 ≤ value.val then
    [ascii (value.val / 10), ascii (value.val % 10)]
  else [ascii value.val]

def emit (out : RawPtr U8) (digit : U8) : Result (RawPtr U8) := do
  MutRawPtr.write Repr.u8 out digit
  RawPtr.add Repr.u8 out 1#usize

@[local step]
theorem emit.spec (out : RawPtr U8) (digit : U8) (start : RawPtr U8)
    (base : BasePtr) (old : Vector Aeneas.Std.Byte 4) (offset : Nat)
    (bound : offset < 3) (prov : out.provenance = start.provenance)
    (address : out.address.val = start.address.val + offset) :
    ⦃ bytesAt start base old.toList ⦄ emit out digit
    ⦃ (next : RawPtr U8) => fun h =>
      next.provenance = start.provenance ∧
      next.address.val = start.address.val + (offset + 1) ∧
      bytesAt start base (old.set offset (.data digit)).toList 0 h ⦄ := by
  unfold emit
  have write := raw_memory_views.write_byte.spec start out base old
    ⟨offset, by agrind⟩ digit prov address
  simp only [raw_memory_views.writableBytes, Vector.toList_map] at write
  apply HeapWP.Triple.bind write
  intro _
  exact advance_bytes.spec start out base (old.set offset (.data digit)) offset
    prov address (by agrind)

def digit (remaining divisor : U8) : Result U8 := do
  let q ← remaining / divisor
  48#u8 + q

@[local step]
theorem digit.spec (remaining divisor : U8) (nonzero : 0 < divisor.val)
    (bound : remaining.val / divisor.val < 10) :
    digit remaining divisor ⦃ (result : U8) =>
      result = ascii (remaining.val / divisor.val) ⦄ := by
  unfold digit
  step*
  · apply UScalar.eq_of_val_eq
    rw [ascii_val _ bound]
    agrind

def write_last (out : RawPtr U8) (remaining : U8) : Result (RawPtr U8) := do
  let d ← 48#u8 + remaining
  emit out d

@[local step]
theorem write_last.spec (out : RawPtr U8) (remaining : U8) (start : RawPtr U8)
    (base : BasePtr) (old : Vector Aeneas.Std.Byte 4) (offset : Nat)
    (bound : offset < 3) (small : remaining.val < 10)
    (prov : out.provenance = start.provenance)
    (address : out.address.val = start.address.val + offset) :
    ⦃ bytesAt start base old.toList ⦄ write_last out remaining
    ⦃ (next : RawPtr U8) => fun h =>
      next.provenance = start.provenance ∧
      next.address.val = start.address.val + (offset + 1) ∧
      bytesAt start base (old.set offset (.data (ascii remaining.val))).toList 0 h ⦄ := by
  unfold write_last
  step as ⟨d, hd⟩
  have digitEq : d = ascii remaining.val := by
    apply UScalar.eq_of_val_eq
    rw [ascii_val _ small]
    agrind
  subst d
  step with emit.spec out (ascii remaining.val) start base old offset bound prov address
  · agrind

/- The helper boundaries only group contiguous operations of the Rust writer. -/
def write_tail (out : RawPtr U8) (remaining : U8) (tens : Bool) : Result (RawPtr U8) := do
  let (out, remaining) ←
    if tens then do
      let d ← digit remaining 10#u8
      let next ← emit out d
      let r ← remaining % 10#u8
      pure (next, r)
    else pure (out, remaining)
  write_last out remaining

def tailStorage (old : Vector Aeneas.Std.Byte 4) (offset : Nat) (bound : offset < 2)
    (remaining : U8) (tens : Bool) : Vector Aeneas.Std.Byte 4 :=
  if tens then
    (old.set offset (.data (ascii (remaining.val / 10)))).set (offset + 1)
      (.data (ascii (remaining.val % 10)))
  else old.set offset (.data (ascii remaining.val))

@[local step]
theorem write_tail.spec (out : RawPtr U8) (remaining : U8) (tens : Bool)
    (start : RawPtr U8) (base : BasePtr) (old : Vector Aeneas.Std.Byte 4) (offset : Nat)
    (bound : offset < 2) (small : remaining.val < if tens then 100 else 10)
    (prov : out.provenance = start.provenance)
    (address : out.address.val = start.address.val + offset) :
    ⦃ bytesAt start base old.toList ⦄ write_tail out remaining tens
    ⦃ (next : RawPtr U8) => fun h =>
      next.provenance = start.provenance ∧
      next.address.val = start.address.val + (offset + if tens then 2 else 1) ∧
      bytesAt start base (tailStorage old offset bound remaining tens).toList 0 h ⦄ := by
  cases tens
  · simpa [write_tail, tailStorage, pure, bind_tc_ok] using
      write_last.spec out remaining start base old offset (by agrind) small prov address
  · simp only [write_tail, ↓reduceIte, tailStorage]
    step with digit.spec remaining 10#u8 (by scalar_tac) (by scalar_tac) as ⟨d⟩
    have deq : d = ascii (remaining.val / 10) := by agrind
    subst d
    step with emit.spec out (ascii (remaining.val / 10)) start base old offset
      (by agrind) prov address as ⟨next, _, nextProv, nextAddr⟩
    step as ⟨r⟩
    step with write_last.spec next r start base
      (old.set offset (.data (ascii (remaining.val / 10)))) (offset + 1)
      (by agrind) (by scalar_tac) nextProv nextAddr
    · simp [*]
      agrind

def write_decimal (out : RawPtr U8) (value : U8) : Result (RawPtr U8) := do
  let (out, remaining) ←
    if value ≥ 100#u8 then do
      let d ← digit value 100#u8
      let next ← emit out d
      let r ← value % 100#u8
      pure (next, r)
    else pure (out, value)
  write_tail out remaining (value ≥ 10#u8)

/-- **Spec theorem for `raw_zmij_mwe::write_decimal`**
    The cursor advances by the decimal length, exactly that prefix is initialized,
    and all remaining bytes (including uninitialized bytes) are unchanged. -/
@[step]
theorem write_decimal.spec (out : RawPtr U8) (value : U8) (base : BasePtr)
    (old : Vector Aeneas.Std.Byte 4) :
    ⦃ bytesAt out base old.toList ⦄ write_decimal out value
    ⦃ (finish : RawPtr U8) => fun h =>
      finish.provenance = out.provenance ∧
      finish.address.val = out.address.val + (decimalDigits value).length ∧
      bytesAt out base
        ((decimalDigits value).map Byte.data ++ old.toList.drop (decimalDigits value).length) 0 h ⦄ := by
  unfold write_decimal
  by_cases hundred : 100 ≤ value.val
  · have ten : 10 ≤ value.val := by agrind
    simp only [UScalar.le_equiv, UScalar.ofNatCore_val_eq,
      hundred, ten, ↓reduceIte, decide_true, decimalDigits]
    step with digit.spec value 100#u8 (by scalar_tac) (by scalar_tac) as ⟨d⟩
    have deq : d = ascii (value.val / 100) := by agrind
    subst d
    step with emit.spec out (ascii (value.val / 100)) out base old 0
      (by decide) rfl (by simp) as ⟨next, _, nextProv, nextAddr⟩
    step as ⟨r⟩
    step with write_tail.spec next r true out base
      (old.set 0 (.data (ascii (value.val / 100)))) 1 (by decide)
      (by scalar_tac) nextProv nextAddr
    · have modEq : value.val % 100 % 10 = value.val % 10 :=
        Nat.mod_mod_of_dvd _ (by decide)
      simp [tailStorage, Vector.toList_set,
        List.set_eq_take_append_cons_drop, *] at *
      agrind
  · simp only [UScalar.le_equiv, UScalar.ofNatCore_val_eq,
      hundred, ↓reduceIte, pure]
    step with write_tail.spec out value (decide (10 ≤ value.val)) out base old 0
      (by decide) (by split <;> scalar_tac) rfl (by simp)
    · by_cases ten : 10 ≤ value.val
      · simp [decimalDigits, hundred, ten, tailStorage, Vector.toList_set,
          List.set_eq_take_append_cons_drop] at *
        agrind
      · simp [decimalDigits, hundred, ten, tailStorage, Vector.toList_set,
          List.set_eq_take_append_cons_drop] at *
        agrind

end raw_zmij_mwe
