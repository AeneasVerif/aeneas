(** THIS FILE WAS AUTOMATICALLY GENERATED FROM LEAN: DO NOT MODIFY DIRECTLY *)
open ExtractBuiltinCore

let lean_builtin_types = []

let lean_builtin_funs =
  [
    (* file: "Aeneas/Std/Vec.lean", line: 237 *)
    mk_fun "alloc::vec::from_elem" "alloc.vec.from_elem";
    (* file: "Aeneas/Std/Vec.lean", line: 299 *)
    mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::resize" "alloc.vec.Vec.resize"
      ~filter:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 326 *)
    mk_fun
      "alloc::vec::{core::convert::From<Box<[@T]>, alloc::vec::Vec<@T>>}::from"
      "alloc.vec.FromBoxSliceVec.from"
      ~filter:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 178 *)
    mk_fun
      "alloc::vec::{core::ops::index::Index<alloc::vec::Vec<@T>, @I, \
       @O>}::index"
      "alloc.vec.Vec.index"
      ~filter:(Some [ true; true; false; true ]);
    (* file: "Aeneas/Std/Vec.lean", line: 184 *)
    mk_fun
      "alloc::vec::{core::ops::index::IndexMut<alloc::vec::Vec<@T>, @I, \
       @O>}::index_mut"
      "alloc.vec.Vec.index_mut"
      ~filter:(Some [ true; true; false; true ]);
    (* file: "Aeneas/Std/Core.lean", line: 78 *)
    mk_fun "core::mem::replace" "core.mem.replace" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Core.lean", line: 82 *)
    mk_fun "core::mem::swap" "core.mem.swap" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Core.lean", line: 88 *)
    mk_fun "core::option::{core::option::Option<@T>}::unwrap"
      "core.option.Option.unwrap";
    (* file: "Aeneas/Std/Slice.lean", line: 221 *)
    mk_fun "core::slice::index::{core::ops::index::Index<[@T], @I, @O>}::index"
      "core.slice.index.Slice.index";
    (* file: "Aeneas/Std/Slice.lean", line: 290 *)
    mk_fun
      "core::slice::index::{core::ops::index::IndexMut<[@T], @I, \
       @O>}::index_mut"
      "core.slice.index.Slice.index_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 239 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::get"
      "core.slice.index.SliceIndexRangeUsizeSlice.get";
    (* file: "Aeneas/Std/Slice.lean", line: 246 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::get_mut"
      "core.slice.index.SliceIndexRangeUsizeSlice.get_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 260 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::get_unchecked"
      "core.slice.index.SliceIndexRangeUsizeSlice.get_unchecked";
    (* file: "Aeneas/Std/Slice.lean", line: 266 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::get_unchecked_mut"
      "core.slice.index.SliceIndexRangeUsizeSlice.get_unchecked_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 272 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::index"
      "core.slice.index.SliceIndexRangeUsizeSlice.index";
    (* file: "Aeneas/Std/Slice.lean", line: 278 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::index_mut"
      "core.slice.index.SliceIndexRangeUsizeSlice.index_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 227 *)
    mk_fun "core::slice::{[@T]}::get" "core.slice.Slice.get";
    (* file: "Aeneas/Std/Slice.lean", line: 233 *)
    mk_fun "core::slice::{[@T]}::get_mut" "core.slice.Slice.get_mut";
  ]
