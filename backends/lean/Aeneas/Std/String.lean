import Aeneas.Std.Scalar
import Aeneas.Std.Slice

namespace Aeneas.Std

open Result

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

/-- `str::to_owned` via `ToOwned<String> for str`. Takes a `Str` (modeled as
`Slice U8`) and returns an owned `String`.

- Docs: https://doc.rust-lang.org/core/borrow/trait.ToOwned.html#tymethod.to_owned
- Source: https://github.com/rust-lang/rust/blob/1.85.0/library/alloc/src/str.rs
-/
@[rust_fun "alloc::str::{alloc::borrow::ToOwned<str, alloc::string::String>}::to_owned"]
def Str.Insts.AllocBorrowToOwnedString.to_owned (s : Str) : Result String :=
  ok (String.fromUTF8!
    ⟨ (s.val.map (fun x => (UInt8.ofNat x.val))).toArray ⟩)

end Aeneas.Std
