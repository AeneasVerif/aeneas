import Aeneas.Std.Scalar
import Aeneas.Std.Slice

namespace Aeneas.Std

def Str := Slice U8

/-- TODO: we shouldn't use `decide +native` but it seems we can't reduce it otherwise. -/
def toStr (s : String) (h : s.toByteArray.size ≤ U32.max := by decide +native) : Str :=
  ⟨ s.toByteArray.toList.map
    (fun x => ⟨ x.toNat, by cases x; simp only [UInt8.toNat_ofBitVec, UScalarTy.U8_numBits_eq, Nat.reducePow]; omega  ⟩),
    by
      simp only [UScalarTy.U8_numBits_eq, Nat.reducePow, Fin.mk_uInt8ToNat, BitVec.ofFin_uInt8ToFin,
        List.length_map]
      -- TODO: there seems to be missing lemmas to relate `ByteArray.size` and `ByteArray.toList.size`
      sorry ⟩

example : Str := toStr "hello"

end Aeneas.Std
