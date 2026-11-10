import Aeneas

/-! Regression tests for the specifications of typed accesses through casts of byte buffers
(`Aeneas/Std/CastSpecs.lean`), on small programs written directly in Lean. -/

open Aeneas Aeneas.Std Aeneas.SepLogic Aeneas.Std.WP Result core.mem.maybe_uninit

namespace cast_specs_tests

theorem toBytes_pair : toBytes (0x0201#u16) = [1#u8, 2#u8] := by
  simp [BitVec.toLEBytes]; decide

/-- Writes a `u16` unaligned at offset 1 of a byte buffer (as Zmij writes digit pairs), and reads
its second byte back as a `u8`. -/
def write_pair (buf : MutRawPtr U8) : Result U8 := do
  let b ← RawPtr.add buf 1#usize
  let q ← RawPtr.ptr_cast U16 b
  MutRawPtr.write_unaligned q 0x0201#u16
  let r ← RawPtr.add buf 2#usize
  RawPtr.read r

theorem write_pair.spec (buf : MutRawPtr U8) :
    ⦃ buf ↦?* [⟨none⟩, ⟨none⟩, ⟨none⟩] ⦄ write_pair buf
      ⦃ r => ⌜r = 2#u8⌝ ∗ buf ↦?* [⟨none⟩, ⟨some 1#u8⟩, ⟨some 2#u8⟩] ⦄ := by
  unfold write_pair
  have ha := RawPtr.add.spec_uninit buf [⟨none⟩, ⟨none⟩, ⟨none⟩] 0 1#usize (by simp) (by simp)
  simp only [RawPtr.elem_zero] at ha
  step with ha
  subst b_post
  step
  subst q_post
  have hw := MutRawPtr.write_unaligned.spec_cast (U := U16) buf [⟨none⟩, ⟨none⟩, ⟨none⟩] 1
    0x0201#u16 (by simp [Pointee.size_uscalar])
  simp only [toBytes_pair, Pointee.size_uscalar] at hw
  step with hw
  have ha := RawPtr.add.spec_uninit buf [⟨none⟩, ⟨some 1#u8⟩, ⟨some 2#u8⟩] 0 2#usize
    (by simp) (by simp)
  simp only [RawPtr.elem_zero] at ha
  step with ha
  subst r_post
  step with RawPtr.read.spec_uninit buf [⟨none⟩, ⟨some 1#u8⟩, ⟨some 2#u8⟩] (0 + 2) 2#u8
    (by simp) rfl

instance : Fact (0 < (2#usize).val) := ⟨by decide⟩

/-- Writes a `[u64; 2]` unaligned at the start of a byte buffer (as Zmij writes its decimal
digits), and reads the second element back as a `u64` and its first byte as a `u8`. -/
def write_digits (buf : MutRawPtr U8) (d : Array U64 2#usize) : Result (U64 × U8) := do
  let q ← RawPtr.ptr_cast (Array U64 2#usize) buf
  MutRawPtr.write_unaligned q d
  let b ← RawPtr.add buf 8#usize
  let r ← RawPtr.ptr_cast U64 b
  let x ← RawPtr.read_unaligned r
  let y ← RawPtr.read b
  .ok (x, y)

theorem write_digits.spec (buf : MutRawPtr U8) (d : Array U64 2#usize) (lo hi : U64)
    (hd : d.val = [lo, hi]) :
    ⦃ buf ↦?* List.replicate 16 ⟨none⟩ ⦄ write_digits buf d
      ⦃ r => ⌜r = (hi, (toBytes hi)[0]'(by simp))⌝ ∗
        buf ↦?* (toBytes lo ++ toBytes hi).map (fun x => ⟨some x⟩) ⦄ := by
  unfold write_digits
  step
  subst q_post
  have hw := MutRawPtr.write_unaligned.spec_cast (U := Array U64 2#usize) buf
    (List.replicate 16 ⟨none⟩) 0 d (by simp [Pointee.size_array, Pointee.size_uscalar])
  simp only [RawPtr.elem_zero, Pointee.toBytes_array, hd, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.take_zero, List.nil_append, Pointee.size_array,
    Pointee.size_uscalar] at hw
  simp only [List.drop_replicate] at hw
  have e : 16 - (0 + (2#usize).val * (UScalarTy.U64.numBits / 8)) = 0 := by simp
  rw [e, List.replicate_zero, List.append_nil] at hw
  step with hw
  have ha := RawPtr.add.spec_uninit buf ((toBytes lo ++ toBytes hi).map (fun x => ⟨some x⟩))
    0 8#usize (by simp) (by simp)
  simp only [RawPtr.elem_zero] at ha
  step with ha
  subst b_post
  step
  subst r_post
  step with RawPtr.read_unaligned.spec_cast (U := U64) buf
    ((toBytes lo ++ toBytes hi).map (fun x => ⟨some x⟩)) (0 + 8) hi
    (by simp [List.map_append, Pointee.size_uscalar])
  step with RawPtr.read.spec_uninit buf ((toBytes lo ++ toBytes hi).map (fun x => ⟨some x⟩))
    (0 + 8) ((toBytes hi)[0]'(by simp)) (by simp)
    (by simp [List.getElem_append_right])
  subst x_post y_post
  step*

/-- A `u64` exposed read-only (as by `ptr::from_ref`, which gives `q.readable 1 [v]`) is readable
as its little-endian bytes. -/
example (q : RawPtr U64) (v : U64) : q.readable 1 [v] ⊢ (q.cast U8).readable 1 (toBytes v) :=
  RawPtr.readable_cast_bytes q 1 v

example (q : RawPtr (Array U64 2#usize)) (v : Array U64 2#usize) :
    q.readable 1 [v] ⊢ (q.cast U8).readable 1 (v.val.flatMap toBytes) :=
  RawPtr.readable_cast_bytes q 1 v

/-- Reads the first byte of an exposed `u64`. -/
def first_byte (q : ConstRawPtr U64) : Result U8 := do
  let b ← RawPtr.ptr_cast U8 q
  RawPtr.read b

theorem first_byte.spec (q : ConstRawPtr U64) (v : U64) :
    ⦃ q.readable 1 [v] ⦄ first_byte q
      ⦃ r => ⌜r = (toBytes v)[0]'(by simp)⌝ ∗ (q.cast U8).readable 1 (toBytes v) ⦄ := by
  unfold first_byte
  step
  subst b_post
  refine ispec_conseq ?_ (RawPtr.readable_cast_bytes q 1 v) (fun _ => entails_refl _)
  have := RawPtr.read.spec_readable (q.cast U8) 1 (toBytes v) 0 (by simp)
  simpa using this

example : core.mem.size_of U32 ⦃ r => r.val = 4 ⦄ := by
  have := core.mem.size_of.spec_uscalar .U32
  simpa using this

example : core.mem.size_of (Array U64 2#usize) ⦃ r => r.val = 16 ⦄ := by
  have := core.mem.size_of.spec_array U64 2#usize
    (by simp [Pointee.size_uscalar]; apply le_usize_max_of_le; decide)
  simpa [Pointee.size_uscalar] using this

#print axioms write_pair.spec
#print axioms write_digits.spec
#print axioms first_byte.spec
#print axioms MutRawPtr.write_unaligned.spec_cast
#print axioms RawPtr.read_unaligned.spec_cast
#print axioms RawPtr.read_unaligned.spec_cast_readable
#print axioms RawPtr.readable_cast_bytes
#print axioms RawPtr.readable_bytes_cast
#print axioms RawPtr.pointsTo_cast_bytes
#print axioms RawPtr.bytes_pointsTo_cast
#print axioms core.mem.size_of.spec_array

end cast_specs_tests
