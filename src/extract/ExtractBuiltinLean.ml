(** THIS FILE WAS AUTOMATICALLY GENERATED FROM LEAN: DO NOT MODIFY DIRECTLY *)
open ExtractBuiltinCore

let lean_builtin_types =
  [
    (* file: "Aeneas/Std/Alloc.lean", line: 13 *)
    mk_type "alloc::alloc::Global" "Global" ~kind:(KEnum [ ("Mk", Some "mk") ]);
    (* file: "Aeneas/Std/Alloc.lean", line: 10 *)
    mk_type "alloc::string::String" "String"
      ~kind:(KStruct [ ("data", Some "data") ]);
    (* file: "Aeneas/Std/Vec.lean", line: 18 *)
    mk_type "alloc::vec::Vec" "alloc.vec.Vec";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 110 *)
    mk_type "core::array::TryFromSliceError" "core.array.TryFromSliceError";
    (* file: "Aeneas/Std/Core.lean", line: 210 *)
    mk_type "core::cmp::Ordering" "Ordering"
      ~kind:
        (KEnum
           [ ("Less", Some "lt"); ("Equal", Some "eq"); ("Greater", Some "gt") ]);
    (* file: "Aeneas/Std/Core.lean", line: 141 *)
    mk_type "core::fmt::Error" "core.fmt.Error";
    (* file: "Aeneas/Std/Core.lean", line: 173 *)
    mk_type "core::fmt::Formatter" "Formatter";
    (* file: "Aeneas/Std/Range.lean", line: 14 *)
    mk_type "core::ops::range::Range" "core.ops.range.Range"
      ~kind:(KStruct [ ("start", Some "start"); ("end", Some "end_") ]);
    (* file: "Aeneas/Std/Core.lean", line: 187 *)
    mk_type "core::ops::range::RangeFrom" "core.ops.range.RangeFrom"
      ~kind:(KStruct [ ("start", Some "start") ]);
    (* file: "Aeneas/Std/Range.lean", line: 20 *)
    mk_type "core::ops::range::RangeTo" "core.ops.range.RangeTo"
      ~kind:(KStruct [ ("end", Some "end_") ]);
    (* file: "Aeneas/Std/Core.lean", line: 11 *)
    mk_type "core::option::Option" "Option" ~prefix_variant_names:false
      ~kind:(KEnum [ ("None", Some "none"); ("Some", Some "some") ]);
    (* file: "Aeneas/Std/Core.lean", line: 136 *)
    mk_type "core::result::Result" "core.result.Result"
      ~kind:(KEnum [ ("Ok", Some "Ok"); ("Err", Some "Err") ]);
  ]

let lean_builtin_consts = []

let lean_builtin_funs =
  [
    (* file: "Aeneas/Std/Core.lean", line: 13 *)
    mk_fun "alloc::boxed::{core::convert::AsMut<Box<@T>, @T>}::as_mut"
      "alloc.boxed.AsMutBox.as_mut"
      ~filter:(Some [ true; false ])
      ~can_fail:false;
    (* file: "Aeneas/Std/Alloc.lean", line: 16 *)
    mk_fun "alloc::boxed::{core::ops::deref::Deref<Box<@T>, @T>}::deref"
      "alloc.boxed.Box.deref"
      ~filter:(Some [ true; false ])
      ~can_fail:false;
    (* file: "Aeneas/Std/Alloc.lean", line: 19 *)
    mk_fun "alloc::boxed::{core::ops::deref::DerefMut<Box<@T>, @T>}::deref_mut"
      "alloc.boxed.Box.deref_mut"
      ~filter:(Some [ true; false ])
      ~can_fail:false;
    (* file: "Aeneas/Std/Vec.lean", line: 227 *)
    mk_fun "alloc::slice::{[@T]}::to_vec" "alloc.slice.Slice.to_vec";
    (* file: "Aeneas/Std/Vec.lean", line: 240 *)
    mk_fun "alloc::vec::from_elem" "alloc.vec.from_elem";
    (* file: "Aeneas/Std/Vec.lean", line: 260 *)
    mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::extend_from_slice"
      "alloc.vec.Vec.extend_from_slice"
      ~filter:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 117 *)
    mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::insert" "alloc.vec.Vec.insert"
      ~filter:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 50 *)
    mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::len" "alloc.vec.Vec.len"
      ~filter:(Some [ true; false ])
      ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Vec.lean", line: 43 *)
    mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::new" "alloc.vec.Vec.new"
      ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Vec.lean", line: 100 *)
    mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::push" "alloc.vec.Vec.push"
      ~filter:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 294 *)
    mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::resize" "alloc.vec.Vec.resize"
      ~filter:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 257 *)
    mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::with_capacity"
      "alloc.vec.Vec.with_capacity" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Vec.lean", line: 321 *)
    mk_fun
      "alloc::vec::{core::convert::From<Box<[@T]>, alloc::vec::Vec<@T>>}::from"
      "alloc.vec.FromBoxSliceVec.from"
      ~filter:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 271 *)
    mk_fun
      "alloc::vec::{core::ops::deref::Deref<alloc::vec::Vec<@T>, [@T]>}::deref"
      "alloc.vec.Vec.deref"
      ~filter:(Some [ true; false ])
      ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Vec.lean", line: 281 *)
    mk_fun
      "alloc::vec::{core::ops::deref::DerefMut<alloc::vec::Vec<@T>, \
       [@T]>}::deref_mut"
      "alloc.vec.Vec.deref_mut"
      ~filter:(Some [ true; false ])
      ~can_fail:false;
    (* file: "Aeneas/Std/Vec.lean", line: 181 *)
    mk_fun
      "alloc::vec::{core::ops::index::Index<alloc::vec::Vec<@T>, @I, \
       @O>}::index"
      "alloc.vec.Vec.index"
      ~filter:(Some [ true; true; false; true ]);
    (* file: "Aeneas/Std/Vec.lean", line: 187 *)
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
    (* file: "Aeneas/Std/Array/Array.lean", line: 261 *)
    mk_fun "core::array::{core::default::Default<[@T; 0]>}::default"
      "core.default.DefaultArrayEmpty.default";
    (* file: "Aeneas/Std/Array/Array.lean", line: 245 *)
    mk_fun "core::array::{core::default::Default<[@T; @N]>}::default"
      "core.default.DefaultArray.default";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 81 *)
    mk_fun "core::array::{core::ops::index::Index<[@T; @N], @I, @O>}::index"
      "core.array.Array.index";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 87 *)
    mk_fun
      "core::array::{core::ops::index::IndexMut<[@T; @N], @I, @O>}::index_mut"
      "core.array.Array.index_mut";
    (* file: "Aeneas/Std/Core.lean", line: 277 *)
    mk_fun "core::cmp::Ord::clamp" "core.cmp.Ord.clamp.default";
    (* file: "Aeneas/Std/Core.lean", line: 265 *)
    mk_fun "core::cmp::Ord::max" "core.cmp.Ord.max.default";
    (* file: "Aeneas/Std/Core.lean", line: 271 *)
    mk_fun "core::cmp::Ord::min" "core.cmp.Ord.min.default";
    (* file: "Aeneas/Std/Core.lean", line: 203 *)
    mk_fun "core::cmp::PartialEq::ne" "core.cmp.PartialEq.ne.default";
    (* file: "Aeneas/Std/Core.lean", line: 248 *)
    mk_fun "core::cmp::PartialOrd::ge" "core.cmp.PartialOrd.ge.default";
    (* file: "Aeneas/Std/Core.lean", line: 240 *)
    mk_fun "core::cmp::PartialOrd::gt" "core.cmp.PartialOrd.gt.default";
    (* file: "Aeneas/Std/Core.lean", line: 232 *)
    mk_fun "core::cmp::PartialOrd::le" "core.cmp.PartialOrd.le.default";
    (* file: "Aeneas/Std/Core.lean", line: 224 *)
    mk_fun "core::cmp::PartialOrd::lt" "core.cmp.PartialOrd.lt.default";
    (* file: "Aeneas/Std/Core.lean", line: 128 *)
    mk_fun "core::convert::{core::convert::From<@T, @T>}::from"
      "core.convert.FromSame.from_" ~can_fail:false;
    (* file: "Aeneas/Std/Core.lean", line: 117 *)
    mk_fun "core::convert::{core::convert::Into<@T, @U>}::into"
      "core.convert.IntoFrom.into";
    (* file: "Aeneas/Std/Core.lean", line: 82 *)
    mk_fun "core::mem::replace" "core.mem.replace" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Core.lean", line: 86 *)
    mk_fun "core::mem::swap" "core.mem.swap" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Core.lean", line: 110 *)
    mk_fun "core::option::{core::option::Option<@T>}::is_none"
      "core.option.Option.is_none" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Core.lean", line: 107 *)
    mk_fun "core::option::{core::option::Option<@T>}::take"
      "core.option.Option.take" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Core.lean", line: 91 *)
    mk_fun "core::option::{core::option::Option<@T>}::unwrap"
      "core.option.Option.unwrap";
    (* file: "Aeneas/Std/Core.lean", line: 95 *)
    mk_fun "core::option::{core::option::Option<@T>}::unwrap_or"
      "core.option.Option.unwrap_or" ~can_fail:false;
    (* file: "Aeneas/Std/Core.lean", line: 180 *)
    mk_fun "core::result::{core::result::Result<@T, @E>}::unwrap"
      "core.result.Result.unwrap";
    (* file: "Aeneas/Std/Slice.lean", line: 225 *)
    mk_fun "core::slice::index::{core::ops::index::Index<[@T], @I, @O>}::index"
      "core.slice.index.Slice.index";
    (* file: "Aeneas/Std/Slice.lean", line: 294 *)
    mk_fun
      "core::slice::index::{core::ops::index::IndexMut<[@T], @I, \
       @O>}::index_mut"
      "core.slice.index.Slice.index_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 243 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::get"
      "core.slice.index.SliceIndexRangeUsizeSlice.get";
    (* file: "Aeneas/Std/Slice.lean", line: 250 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::get_mut"
      "core.slice.index.SliceIndexRangeUsizeSlice.get_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 264 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::get_unchecked"
      "core.slice.index.SliceIndexRangeUsizeSlice.get_unchecked";
    (* file: "Aeneas/Std/Slice.lean", line: 270 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::get_unchecked_mut"
      "core.slice.index.SliceIndexRangeUsizeSlice.get_unchecked_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 276 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::index"
      "core.slice.index.SliceIndexRangeUsizeSlice.index";
    (* file: "Aeneas/Std/Slice.lean", line: 282 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::index_mut"
      "core.slice.index.SliceIndexRangeUsizeSlice.index_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 456 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::get"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.get";
    (* file: "Aeneas/Std/Slice.lean", line: 462 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::get_mut"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.get_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 476 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::get_unchecked"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.get_unchecked";
    (* file: "Aeneas/Std/Slice.lean", line: 482 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::get_unchecked_mut"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.get_unchecked_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 488 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::index"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.index";
    (* file: "Aeneas/Std/Slice.lean", line: 495 *)
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
    (* file: "Aeneas/Std/Slice.lean", line: 403 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
       @T>}::get"
      "core.slice.index.Usize.get";
    (* file: "Aeneas/Std/Slice.lean", line: 408 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
       @T>}::get_mut"
      "core.slice.index.Usize.get_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 413 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
       @T>}::get_unchecked"
      "core.slice.index.Usize.get_unchecked";
    (* file: "Aeneas/Std/Slice.lean", line: 419 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
       @T>}::get_unchecked_mut"
      "core.slice.index.Usize.get_unchecked_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 425 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
       @T>}::index"
      "core.slice.index.Usize.index";
    (* file: "Aeneas/Std/Slice.lean", line: 429 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
       @T>}::index_mut"
      "core.slice.index.Usize.index_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 450 *)
    mk_fun "core::slice::{[@T]}::copy_from_slice"
      "core.slice.Slice.copy_from_slice";
    (* file: "Aeneas/Std/Slice.lean", line: 231 *)
    mk_fun "core::slice::{[@T]}::get" "core.slice.Slice.get";
    (* file: "Aeneas/Std/Slice.lean", line: 237 *)
    mk_fun "core::slice::{[@T]}::get_mut" "core.slice.Slice.get_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 43 *)
    mk_fun "core::slice::{[@T]}::len" "Slice.len" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Slice.lean", line: 208 *)
    mk_fun "core::slice::{[@T]}::reverse" "core.slice.Slice.reverse"
      ~can_fail:false;
    (* file: "Aeneas/Std/Slice.lean", line: 558 *)
    mk_fun "core::slice::{[@T]}::split_at" "core.slice.Slice.split_at";
    (* file: "Aeneas/Std/Slice.lean", line: 569 *)
    mk_fun "core::slice::{[@T]}::split_at_mut" "core.slice.Slice.split_at_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 587 *)
    mk_fun "core::slice::{[@T]}::swap" "core.slice.Slice.swap";
  ]

let lean_builtin_trait_decls =
  [
    (* file: "Aeneas/Std/Core.lean", line: 53 *)
    mk_trait_decl "core::clone::Clone" "core.clone.Clone"
      ~methods:[ ("clone", "clone"); ("clone_from", "clone_from") ]
      ~default_methods:[ "clone_from" ];
    (* file: "Aeneas/Std/Core.lean", line: 198 *)
    mk_trait_decl "core::cmp::Eq" "core.cmp.Eq"
      ~parent_clauses:[ "partialEqInst" ];
    (* file: "Aeneas/Std/Core.lean", line: 255 *)
    mk_trait_decl "core::cmp::Ord" "core.cmp.Ord"
      ~parent_clauses:[ "eqInst"; "partialOrdInst" ]
      ~methods:
        [ ("cmp", "cmp"); ("max", "max"); ("min", "min"); ("clamp", "clamp") ];
    (* file: "Aeneas/Std/Core.lean", line: 191 *)
    mk_trait_decl "core::cmp::PartialEq" "core.cmp.PartialEq"
      ~methods:[ ("eq", "eq"); ("ne", "ne") ];
    (* file: "Aeneas/Std/Core.lean", line: 214 *)
    mk_trait_decl "core::cmp::PartialOrd" "core.cmp.PartialOrd"
      ~parent_clauses:[ "partialEqInst" ]
      ~methods:
        [
          ("partial_cmp", "partial_cmp");
          ("lt", "lt");
          ("le", "le");
          ("gt", "gt");
          ("ge", "ge");
        ];
    (* file: "Aeneas/Std/Core.lean", line: 163 *)
    mk_trait_decl "core::convert::AsMut" "core.convert.AsMut"
      ~methods:[ ("as_mut", "as_mut") ];
    (* file: "Aeneas/Std/Core.lean", line: 19 *)
    mk_trait_decl "core::convert::From" "core.convert.From"
      ~methods:[ ("from", "from_") ];
    (* file: "Aeneas/Std/Core.lean", line: 113 *)
    mk_trait_decl "core::convert::Into" "core.convert.Into"
      ~methods:[ ("into", "into") ];
    (* file: "Aeneas/Std/Core.lean", line: 144 *)
    mk_trait_decl "core::convert::TryFrom" "core.convert.TryFrom"
      ~methods:[ ("try_from", "try_from") ];
    (* file: "Aeneas/Std/Core.lean", line: 148 *)
    mk_trait_decl "core::convert::TryInto" "core.convert.TryInto"
      ~methods:[ ("try_into", "try_into") ];
    (* file: "Aeneas/Std/Default.lean", line: 5 *)
    mk_trait_decl "core::default::Default" "core.default.Default"
      ~methods:[ ("default", "default") ];
    (* file: "Aeneas/Std/Core.lean", line: 176 *)
    mk_trait_decl "core::fmt::Debug" "core.fmt.Debug"
      ~methods:[ ("fmt", "fmt") ];
    (* file: "Aeneas/Std/Core.lean", line: 73 *)
    mk_trait_decl "core::marker::Copy" "core.marker.Copy"
      ~parent_clauses:[ "cloneInst" ];
    (* file: "Aeneas/Std/Core.lean", line: 40 *)
    mk_trait_decl "core::ops::deref::Deref" "core.ops.deref.Deref"
      ~methods:[ ("deref", "deref") ];
    (* file: "Aeneas/Std/Core.lean", line: 44 *)
    mk_trait_decl "core::ops::deref::DerefMut" "core.ops.deref.DerefMut"
      ~parent_clauses:[ "derefInst" ]
      ~methods:[ ("deref_mut", "deref_mut") ];
    (* file: "Aeneas/Std/Core.lean", line: 27 *)
    mk_trait_decl "core::ops::index::Index" "core.ops.index.Index"
      ~methods:[ ("index", "index") ];
    (* file: "Aeneas/Std/Core.lean", line: 31 *)
    mk_trait_decl "core::ops::index::IndexMut" "core.ops.index.IndexMut"
      ~parent_clauses:[ "indexInst" ]
      ~methods:[ ("index_mut", "index_mut") ];
    (* file: "Aeneas/Std/Slice.lean", line: 215 *)
    mk_trait_decl "core::slice::index::SliceIndex" "core.slice.index.SliceIndex"
      ~parent_clauses:[ "sealedInst" ]
      ~methods:
        [
          ("get", "get");
          ("get_mut", "get_mut");
          ("get_unchecked", "get_unchecked");
          ("get_unchecked_mut", "get_unchecked_mut");
          ("index", "index");
          ("index_mut", "index_mut");
        ];
    (* file: "Aeneas/Std/Slice.lean", line: 212 *)
    mk_trait_decl "core::slice::index::private_slice_index::Sealed"
      "core.slice.index.private_slice_index.Sealed";
  ]

let lean_builtin_trait_impls =
  [
    (* file: "Aeneas/Std/Array/Array.lean", line: 214 *)
    mk_trait_impl "core::clone::Clone<[@T; @N]>" "core.clone.CloneArray";
    (* file: "Aeneas/Std/Core.lean", line: 67 *)
    mk_trait_impl "core::clone::Clone<bool>" "core.clone.CloneBool";
    (* file: "Aeneas/Std/Core.lean", line: 167 *)
    mk_trait_impl "core::convert::AsMut<Box<@T>, @T>" "core.convert.AsMutBox";
    (* file: "Aeneas/Std/Core.lean", line: 131 *)
    mk_trait_impl "core::convert::From<@Self, @Self>" "core.convert.FromSame";
    (* file: "Aeneas/Std/Vec.lean", line: 329 *)
    mk_trait_impl "core::convert::From<Box<[@T]>, alloc::vec::Vec<@T>>"
      "core.convert.FromBoxSliceVec"
      ~filter_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Core.lean", line: 122 *)
    mk_trait_impl "core::convert::Into<@Self, @T>" "core.convert.IntoFrom";
    (* file: "Aeneas/Std/Core.lean", line: 157 *)
    mk_trait_impl "core::convert::{core::convert::TryInto<@T, @U>}"
      "core.convert.TryIntoFrom";
    (* file: "Aeneas/Std/Array/Array.lean", line: 266 *)
    mk_trait_impl "core::default::Default<[@T; 0]>"
      "core.default.DefaultArrayEmpty";
    (* file: "Aeneas/Std/Array/Array.lean", line: 255 *)
    mk_trait_impl "core::default::Default<[@T; @N]>" "core.default.DefaultArray";
    (* file: "Aeneas/Std/Alloc.lean", line: 23 *)
    mk_trait_impl "core::ops::deref::Deref<Box<@T>, @T>"
      "core.ops.deref.DerefBoxInst";
    (* file: "Aeneas/Std/Vec.lean", line: 276 *)
    mk_trait_impl "core::ops::deref::Deref<alloc::vec::Vec<@T>, [@T]>"
      "core.ops.deref.DerefVec"
      ~filter_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Alloc.lean", line: 30 *)
    mk_trait_impl "core::ops::deref::DerefMut<Box<@T>, @T>"
      "core.ops.deref.DerefMutBoxInst";
    (* file: "Aeneas/Std/Vec.lean", line: 287 *)
    mk_trait_impl "core::ops::deref::DerefMut<alloc::vec::Vec<@T>, [@T]>"
      "core.ops.deref.DerefMutVec"
      ~filter_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 95 *)
    mk_trait_impl "core::ops::index::Index<[@T; @N], @I, @O>"
      "core.ops.index.IndexArray";
    (* file: "Aeneas/Std/Slice.lean", line: 388 *)
    mk_trait_impl "core::ops::index::Index<[@T], @I, @O>"
      "core.ops.index.IndexSlice";
    (* file: "Aeneas/Std/Vec.lean", line: 195 *)
    mk_trait_impl "core::ops::index::Index<alloc::vec::Vec<@T>, @T, @O>"
      "alloc.vec.Vec.Index"
      ~filter_params:(Some [ true; true; false; true ]);
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 102 *)
    mk_trait_impl "core::ops::index::IndexMut<[@T; @N], @I, @O>"
      "core.ops.index.IndexMutArray";
    (* file: "Aeneas/Std/Slice.lean", line: 395 *)
    mk_trait_impl "core::ops::index::IndexMut<[@T], @I, @O>"
      "core.ops.index.IndexMutSlice";
    (* file: "Aeneas/Std/Vec.lean", line: 203 *)
    mk_trait_impl "core::ops::index::IndexMut<alloc::vec::Vec<@T>, @T, @O>"
      "alloc.vec.Vec.IndexMut"
      ~filter_params:(Some [ true; true; false; true ]);
    (* file: "Aeneas/Std/Slice.lean", line: 304 *)
    mk_trait_impl
      "core::slice::index::SliceIndex<core::ops::range::Range<usize>, [@T], \
       [@T]>"
      "core.slice.index.SliceIndexRangeUsizeSlice";
    (* file: "Aeneas/Std/Slice.lean", line: 520 *)
    mk_trait_impl
      "core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>"
      "core.slice.index.SliceIndexRangeFromUsizeSlice";
    (* file: "Aeneas/Std/Slice.lean", line: 375 *)
    mk_trait_impl
      "core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, [@T], \
       [@T]>"
      "core.slice.index.SliceIndexRangeToUsizeSlice";
    (* file: "Aeneas/Std/Slice.lean", line: 438 *)
    mk_trait_impl "core::slice::index::SliceIndex<usize, [@T], @T>"
      "core.slice.index.SliceIndexUsizeSlice";
    (* file: "Aeneas/Std/Slice.lean", line: 300 *)
    mk_trait_impl
      "core::slice::index::private_slice_index::Sealed<core::ops::range::Range<usize>>"
      "core.slice.index.private_slice_index.SealedRangeUsize";
    (* file: "Aeneas/Std/Slice.lean", line: 515 *)
    mk_trait_impl
      "core::slice::index::private_slice_index::Sealed<core::ops::range::RangeFrom<usize>>"
      "core.slice.index.private_slice_index.SealedRangeFromUsize";
    (* file: "Aeneas/Std/Slice.lean", line: 316 *)
    mk_trait_impl
      "core::slice::index::private_slice_index::Sealed<core::ops::range::RangeTo<usize>>"
      "core.slice.index.private_slice_index.SealedRangeToUsize";
    (* file: "Aeneas/Std/Slice.lean", line: 434 *)
    mk_trait_impl "core::slice::index::private_slice_index::Sealed<usize>"
      "core.slice.index.private_slice_index.SealedUsize";
  ]
