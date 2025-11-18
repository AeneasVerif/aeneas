(** THIS FILE WAS AUTOMATICALLY GENERATED FROM LEAN: DO NOT MODIFY DIRECTLY *)
open ExtractBuiltinCore

let lean_builtin_types = []

let lean_builtin_funs =
  [
    (* file: "Aeneas/Std/Core.lean", line: 11 *)
    mk_fun "alloc::boxed::{core::convert::AsMut<Box<@T>, @T>}::as_mut"
      "alloc.boxed.AsMutBox.as_mut"
      ~filter:(Some [ true; false ])
      ~can_fail:false;
    (* file: "Aeneas/Std/Vec.lean", line: 237 *)
    mk_fun "alloc::vec::from_elem" "alloc.vec.from_elem";
    (* file: "Aeneas/Std/Vec.lean", line: 260 *)
    mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::extend_from_slice"
      "alloc.vec.Vec.extend_from_slice"
      ~filter:(Some [ true; false ]);
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
    (* file: "Aeneas/Std/Array/Array.lean", line: 190 *)
    mk_fun "core::array::{core::clone::Clone<[@T; @N]>}::clone"
      "core.array.CloneArray.clone";
    (* file: "Aeneas/Std/Array/Array.lean", line: 202 *)
    mk_fun "core::array::{core::clone::Clone<[@T; @N]>}::clone_from"
      "core.array.CloneArray.clone_from";
    (* file: "Aeneas/Std/Array/Array.lean", line: 268 *)
    mk_fun "core::array::{core::default::Default<[@T; 0]>}::default"
      "core.default.DefaultArrayEmpty.default";
    (* file: "Aeneas/Std/Array/Array.lean", line: 248 *)
    mk_fun "core::array::{core::default::Default<[@T; @N]>}::default"
      "core.default.DefaultArray.default";
    (* file: "Aeneas/Std/Core.lean", line: 270 *)
    mk_fun "core::cmp::Ord::clamp" "core.cmp.Ord.clamp.default";
    (* file: "Aeneas/Std/Core.lean", line: 258 *)
    mk_fun "core::cmp::Ord::max" "core.cmp.Ord.max.default";
    (* file: "Aeneas/Std/Core.lean", line: 264 *)
    mk_fun "core::cmp::Ord::min" "core.cmp.Ord.min.default";
    (* file: "Aeneas/Std/Core.lean", line: 200 *)
    mk_fun "core::cmp::PartialEq::ne" "core.cmp.PartialEq.ne.default";
    (* file: "Aeneas/Std/Core.lean", line: 240 *)
    mk_fun "core::cmp::PartialOrd::ge" "core.cmp.PartialOrd.ge.default";
    (* file: "Aeneas/Std/Core.lean", line: 232 *)
    mk_fun "core::cmp::PartialOrd::gt" "core.cmp.PartialOrd.gt.default";
    (* file: "Aeneas/Std/Core.lean", line: 224 *)
    mk_fun "core::cmp::PartialOrd::le" "core.cmp.PartialOrd.le.default";
    (* file: "Aeneas/Std/Core.lean", line: 216 *)
    mk_fun "core::cmp::PartialOrd::lt" "core.cmp.PartialOrd.lt.default";
    (* file: "Aeneas/Std/Core.lean", line: 125 *)
    mk_fun "core::convert::{core::convert::From<@T, @T>}::from"
      "core.convert.FromSame.from_" ~can_fail:false;
    (* file: "Aeneas/Std/Core.lean", line: 113 *)
    mk_fun "core::convert::{core::convert::Into<@T, @U>}::into"
      "core.convert.IntoFrom.into";
    (* file: "Aeneas/Std/Core.lean", line: 78 *)
    mk_fun "core::mem::replace" "core.mem.replace" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Core.lean", line: 82 *)
    mk_fun "core::mem::swap" "core.mem.swap" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Core.lean", line: 106 *)
    mk_fun "core::option::{core::option::Option<@T>}::is_none"
      "core.option.Option.is_none" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Core.lean", line: 103 *)
    mk_fun "core::option::{core::option::Option<@T>}::take"
      "core.option.Option.take" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Core.lean", line: 87 *)
    mk_fun "core::option::{core::option::Option<@T>}::unwrap"
      "core.option.Option.unwrap";
    (* file: "Aeneas/Std/Core.lean", line: 91 *)
    mk_fun "core::option::{core::option::Option<@T>}::unwrap_or"
      "core.option.Option.unwrap_or" ~can_fail:false;
    (* file: "Aeneas/Std/Core.lean", line: 177 *)
    mk_fun "core::result::{core::result::Result<@T, @E>}::unwrap"
      "core.result.Result.unwrap";
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
    (* file: "Aeneas/Std/Slice.lean", line: 460 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::get"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.get";
    (* file: "Aeneas/Std/Slice.lean", line: 466 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::get_mut"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.get_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 480 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::get_unchecked"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.get_unchecked";
    (* file: "Aeneas/Std/Slice.lean", line: 486 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::get_unchecked_mut"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.get_unchecked_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 492 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::index"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.index";
    (* file: "Aeneas/Std/Slice.lean", line: 499 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::index_mut"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 321 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, \
       [@T], [@T]>}::get"
      "core.slice.index.SliceIndexRangeToUsizeSlice.get";
    (* file: "Aeneas/Std/Slice.lean", line: 328 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, \
       [@T], [@T]>}::get_mut"
      "core.slice.index.SliceIndexRangeToUsizeSlice.get_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 343 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, \
       [@T], [@T]>}::get_unchecked"
      "core.slice.index.SliceIndexRangeToUsizeSlice.get_unchecked";
    (* file: "Aeneas/Std/Slice.lean", line: 349 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, \
       [@T], [@T]>}::get_unchecked_mut"
      "core.slice.index.SliceIndexRangeToUsizeSlice.get_unchecked_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 356 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, \
       [@T], [@T]>}::index"
      "core.slice.index.SliceIndexRangeToUsizeSlice.index";
    (* file: "Aeneas/Std/Slice.lean", line: 363 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, \
       [@T], [@T]>}::index_mut"
      "core.slice.index.SliceIndexRangeToUsizeSlice.index_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 454 *)
    mk_fun "core::slice::{[@T]}::copy_from_slice"
      "core.slice.Slice.copy_from_slice";
    (* file: "Aeneas/Std/Slice.lean", line: 227 *)
    mk_fun "core::slice::{[@T]}::get" "core.slice.Slice.get";
    (* file: "Aeneas/Std/Slice.lean", line: 233 *)
    mk_fun "core::slice::{[@T]}::get_mut" "core.slice.Slice.get_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 564 *)
    mk_fun "core::slice::{[@T]}::split_at" "core.slice.Slice.split_at";
    (* file: "Aeneas/Std/Slice.lean", line: 575 *)
    mk_fun "core::slice::{[@T]}::split_at_mut" "core.slice.Slice.split_at_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 593 *)
    mk_fun "core::slice::{[@T]}::swap" "core.slice.Slice.swap";
  ]
