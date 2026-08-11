import Aeneas.Std.Scalar
import Aeneas.Std.Slice
import Aeneas.Std.StringDef

namespace Aeneas.Std

instance : DecidableEq Str := inferInstanceAs (DecidableEq (Slice U8))

/-- `bs.toList` has the same length as `bs`. -/
theorem ByteArray.length_toList (bs : ByteArray) :
    bs.toList.length = bs.size := by
  have loop_length :
      ∀ (i : Nat) (r : List UInt8), i ≤ bs.size →
        (ByteArray.toList.loop bs i r).length = (bs.size - i) + r.length := by
    intro i r hi
    fun_induction ByteArray.toList.loop bs i r with
    | case1 i r h ih =>
      have hi' : i + 1 ≤ bs.size := by scalar_tac
      rw [ih hi']
      simp; scalar_tac
    | case2 i r h =>
      simp; scalar_tac
  unfold ByteArray.toList
  rw [loop_length 0 [] (Nat.zero_le _)]
  simp

/-- TODO: we shouldn't use `decide +native` but it seems we can't reduce it otherwise. -/
def toStr (s : String) (h : s.toByteArray.size ≤ U32.max := by decide +native) : Str :=
  ⟨ s.toByteArray.toList.map
    (fun x => ⟨ x.toNat, by cases x; simp only [UInt8.toNat_ofBitVec, UScalarTy.U8_numBits_eq, Nat.reducePow]; omega  ⟩),
    by
      simp only [UScalarTy.U8_numBits_eq, Nat.reducePow, Fin.mk_uInt8ToNat, BitVec.ofFin_uInt8ToFin,
        List.length_map]
      rw [ByteArray.length_toList]
      exact h.trans (by scalar_tac) ⟩

example : Str := toStr "hello"

/-- Returns the compilation target as a string.

    Used by multi-target dispatch: nothing meaningful can be deduced from
    its output. -/
axiom get_target : Result Str

@[step]
axiom get_target.spec : get_target ⦃ fun _ => True ⦄

end Aeneas.Std
