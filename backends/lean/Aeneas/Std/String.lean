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

@[rust_type "core::str::iter::Chars" (body := .opaque)]
structure core.str.iter.Chars where
  iter : core.slice.iter.Iter U8

/- [core::str::iter::{core::iter::traits::iterator::Iterator<char> for core::str::iter::Chars<'a>}::collect]:
   Source: '/rustc/library/core/src/str/iter.rs', lines 35:0-35:31
   Name pattern: [core::str::iter::{core::iter::traits::iterator::Iterator<core::str::iter::Chars<'a>, char>}::collect] -/
@[rust_fun
  "core::str::iter::{core::iter::traits::iterator::Iterator<core::str::iter::Chars<'a>, char>}::collect"]
def core.str.iter.IteratorChars.collect
  {B : Type} (itertraitscollectFromIteratorBCharInst :
  core.iter.traits.collect.FromIterator B Char) :
  core.str.iter.Chars → Result B := sorry

@[rust_fun "core::str::{str}::chars"]
def core.str.Str.chars (s : Str) : Result core.str.iter.Chars := sorry

end Aeneas.Std
