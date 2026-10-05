module
public import Aeneas.Std.Scalar.SliceCodec
@[expose] public section

namespace Aeneas.Std.IsScalar.Tests

def bytes : Slice U8 := Slice.from [52#u8, 18#u8, 255#u8, 255#u8] (by scalar_tac)

def words : Slice U16 := Slice.from [4660#u16, 65535#u16] (by scalar_tac)

def signedWords : Slice I16 := Slice.from [4660#i16, (-1)#i16] (by scalar_tac)

example (s : Slice U8) : toBytes s = .ok s := by simp

example (s : Slice U8) : fromBytes (T := U8) s = .ok s := by simp

theorem toBytes_words : toBytes words = .ok bytes := by
  simp [toBytes, words, bytes, BitVec.toLEBytes,
    show 4 ≤ Usize.max by scalar_tac]
  rfl

example : fromBytes (T := U16) bytes = .ok words :=
  fromBytes_toBytes (UScalar.byteRepr_size_pos _) toBytes_words

theorem toBytes_signedWords : toBytes signedWords = .ok bytes := by
  simp [toBytes, signedWords, bytes, BitVec.toLEBytes,
    show 4 ≤ Usize.max by scalar_tac]
  rfl

example : fromBytes (T := I16) bytes = .ok signedWords :=
  fromBytes_toBytes (IScalar.byteRepr_size_pos _) toBytes_signedWords

example : fromBytes (T := U16) (Slice.from [1#u8] (by scalar_tac)) = .fail .undef := by
  simp only [fromBytes, Slice.from_val, List.map_cons, List.map_nil]
  rw [ByteRepr.decodeAll]
  simp [ByteRepr.decode, BitVec.decodeLE]

example : fromBytes (T := I32) (Slice.from [1#u8, 2#u8, 3#u8] (by scalar_tac)) =
    .fail .undef := by
  simp only [fromBytes, Slice.from_val, List.map_cons, List.map_nil]
  rw [ByteRepr.decodeAll]
  simp [ByteRepr.decode, BitVec.decodeLE]

example : fromBytes (T := U32) (Slice.from [] (by scalar_tac)) =
    .ok (Slice.from [] (by scalar_tac)) := by
  simp only [fromBytes, Slice.from_val, List.map_nil]
  rw [ByteRepr.decodeAll]
  simp

example : numElems U8 16 = 16 := by simp

example : numElems U32 16 = 4 := by
  rcases System.Platform.numBits_eq with h | h
  · simp [numElems, size, UScalar.val, h]
  · simp [numElems, size, UScalar.val, h]

example : numElems U64 17 = 3 := by
  rcases System.Platform.numBits_eq with h | h
  · simp [numElems, size, UScalar.val, h]
  · simp [numElems, size, UScalar.val, h]

example : numElems U128 0 = 0 := by
  rcases System.Platform.numBits_eq with h | h
  · simp [numElems, size, UScalar.val, h]
  · simp [numElems, size, UScalar.val, h]

example : (size (T := U128)).val = 16 := by
  rcases System.Platform.numBits_eq with h | h
  · simp [size, UScalar.val, h]
  · simp [size, UScalar.val, h]

example : (size (T := Isize)).val = System.Platform.numBits / 8 := by
  rcases System.Platform.numBits_eq with h | h
  · simp [size, UScalar.val, h]
  · simp [size, UScalar.val, h]

end Aeneas.Std.IsScalar.Tests
