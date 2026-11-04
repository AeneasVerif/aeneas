module

public import Aeneas

@[expose] public section

open Aeneas Aeneas.Std

namespace raw_zeroize

/-- Local heap-resident model of `&mut [MaybeUninit<T>]`. The contents stay in
    the heap, governed by writableBytes, rather than being decoded into T.
    T is a layout index; no value of T is constructed or read. -/
structure UninitSlice (T : Type) where
  ptr : RawPtr T
  len : Usize

end raw_zeroize
