(** THIS FILE WAS AUTOMATICALLY GENERATED FROM LEAN: DO NOT MODIFY DIRECTLY *)
open ExtractBuiltinCore

let lean_builtin_types =
  [
    (* file: "Aeneas/Std/Alloc.lean", line: 16 *)
    mk_type "alloc::alloc::Global" "Global" ~kind:(KEnum [ ("Mk", Some "mk") ]);
    (* file: "Aeneas/Std/Alloc.lean", line: 11 *)
    mk_type "alloc::string::String" "String"
      ~kind:(KStruct [ ("data", Some "data") ]);
    (* file: "Aeneas/Std/Vec.lean", line: 18 *)
    mk_type "alloc::vec::Vec" "alloc.vec.Vec";
    (* file: "Aeneas/Std/Core/Ptr.lean", line: 77 *)
    mk_type "core::alloc::layout::Layout" "core.alloc.layout.Layout"
      ~kind:(KStruct [ ("size", Some "size"); ("align", Some "align") ]);
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 112 *)
    mk_type "core::array::TryFromSliceError" "core.array.TryFromSliceError";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 31 *)
    mk_type "core::cmp::Ordering" "Ordering"
      ~kind:
        (KEnum
           [ ("Less", Some "lt"); ("Equal", Some "eq"); ("Greater", Some "gt") ]);
    (* file: "Aeneas/Std/Core/Convert.lean", line: 8 *)
    mk_type "core::convert::Infallible" "core.convert.Infallible"
      ~kind:(KEnum []);
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 25 *)
    mk_type "core::fmt::Arguments" "core.fmt.Arguments";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 6 *)
    mk_type "core::fmt::Error" "core.fmt.Error";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 10 *)
    mk_type "core::fmt::Formatter" "core.fmt.Formatter";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 28 *)
    mk_type "core::fmt::rt::Argument" "core.fmt.rt.Argument";
    (* file: "Aeneas/Std/Core/Ops.lean", line: 65 *)
    mk_type "core::ops::control_flow::ControlFlow"
      "core.ops.control_flow.ControlFlow"
      ~kind:(KEnum [ ("Continue", Some "Continue"); ("Break", Some "Break") ]);
    (* file: "Aeneas/Std/Range.lean", line: 14 *)
    mk_type "core::ops::range::Range" "core.ops.range.Range"
      ~kind:(KStruct [ ("start", Some "start"); ("end", Some "end_") ]);
    (* file: "Aeneas/Std/Core/Core.lean", line: 113 *)
    mk_type "core::ops::range::RangeFrom" "core.ops.range.RangeFrom"
      ~kind:(KStruct [ ("start", Some "start") ]);
    (* file: "Aeneas/Std/Range.lean", line: 20 *)
    mk_type "core::ops::range::RangeTo" "core.ops.range.RangeTo"
      ~kind:(KStruct [ ("end", Some "end_") ]);
    (* file: "Aeneas/Std/Core/Core.lean", line: 12 *)
    mk_type "core::option::Option" "Option" ~prefix_variant_names:false
      ~kind:(KEnum [ ("None", Some "none"); ("Some", Some "some") ]);
    (* file: "Aeneas/Std/Core/Panic.lean", line: 6 *)
    mk_type "core::panic::panic_info::PanicInfo"
      "core.panic.panic_info.PanicInfo";
    (* file: "Aeneas/Std/Core/Core.lean", line: 117 *)
    mk_type "core::panicking::AssertKind" "core.panicking.AssertKind"
      ~kind:
        (KEnum [ ("Eq", Some "Eq"); ("Ne", Some "Ne"); ("Match", Some "Match") ]);
    (* file: "Aeneas/Std/Core/Pin.lean", line: 6 *)
    mk_type "core::pin::Pin" "core.pin.Pin";
    (* file: "Aeneas/Std/Core/Pin.lean", line: 10 *)
    mk_type "core::pin::helper::PinHelper" "core.pin.helper.PinHelper";
    (* file: "Aeneas/Std/Core/Ptr.lean", line: 73 *)
    mk_type "core::ptr::alignment::Alignment" "core.ptr.alignment.Alignment";
    (* file: "Aeneas/Std/Core/Ptr.lean", line: 6 *)
    mk_type "core::ptr::alignment::AlignmentEnum"
      "core.ptr.alignment.AlignmentEnum"
      ~kind:
        (KEnum
           [
             ("_Align1Shl0", Some "_Align1Shl0");
             ("_Align1Shl1", Some "_Align1Shl1");
             ("_Align1Shl2", Some "_Align1Shl2");
             ("_Align1Shl3", Some "_Align1Shl3");
             ("_Align1Shl4", Some "_Align1Shl4");
             ("_Align1Shl5", Some "_Align1Shl5");
             ("_Align1Shl6", Some "_Align1Shl6");
             ("_Align1Shl7", Some "_Align1Shl7");
             ("_Align1Shl8", Some "_Align1Shl8");
             ("_Align1Shl9", Some "_Align1Shl9");
             ("_Align1Shl10", Some "_Align1Shl10");
             ("_Align1Shl11", Some "_Align1Shl11");
             ("_Align1Shl12", Some "_Align1Shl12");
             ("_Align1Shl13", Some "_Align1Shl13");
             ("_Align1Shl14", Some "_Align1Shl14");
             ("_Align1Shl15", Some "_Align1Shl15");
             ("_Align1Shl16", Some "_Align1Shl16");
             ("_Align1Shl17", Some "_Align1Shl17");
             ("_Align1Shl18", Some "_Align1Shl18");
             ("_Align1Shl19", Some "_Align1Shl19");
             ("_Align1Shl20", Some "_Align1Shl20");
             ("_Align1Shl21", Some "_Align1Shl21");
             ("_Align1Shl22", Some "_Align1Shl22");
             ("_Align1Shl23", Some "_Align1Shl23");
             ("_Align1Shl24", Some "_Align1Shl24");
             ("_Align1Shl25", Some "_Align1Shl25");
             ("_Align1Shl26", Some "_Align1Shl26");
             ("_Align1Shl27", Some "_Align1Shl27");
             ("_Align1Shl28", Some "_Align1Shl28");
             ("_Align1Shl29", Some "_Align1Shl29");
             ("_Align1Shl30", Some "_Align1Shl30");
             ("_Align1Shl31", Some "_Align1Shl31");
             ("_Align1Shl32", Some "_Align1Shl32");
             ("_Align1Shl33", Some "_Align1Shl33");
             ("_Align1Shl34", Some "_Align1Shl34");
             ("_Align1Shl35", Some "_Align1Shl35");
             ("_Align1Shl36", Some "_Align1Shl36");
             ("_Align1Shl37", Some "_Align1Shl37");
             ("_Align1Shl38", Some "_Align1Shl38");
             ("_Align1Shl39", Some "_Align1Shl39");
             ("_Align1Shl40", Some "_Align1Shl40");
             ("_Align1Shl41", Some "_Align1Shl41");
             ("_Align1Shl42", Some "_Align1Shl42");
             ("_Align1Shl43", Some "_Align1Shl43");
             ("_Align1Shl44", Some "_Align1Shl44");
             ("_Align1Shl45", Some "_Align1Shl45");
             ("_Align1Shl46", Some "_Align1Shl46");
             ("_Align1Shl47", Some "_Align1Shl47");
             ("_Align1Shl48", Some "_Align1Shl48");
             ("_Align1Shl49", Some "_Align1Shl49");
             ("_Align1Shl50", Some "_Align1Shl50");
             ("_Align1Shl51", Some "_Align1Shl51");
             ("_Align1Shl52", Some "_Align1Shl52");
             ("_Align1Shl53", Some "_Align1Shl53");
             ("_Align1Shl54", Some "_Align1Shl54");
             ("_Align1Shl55", Some "_Align1Shl55");
             ("_Align1Shl56", Some "_Align1Shl56");
             ("_Align1Shl57", Some "_Align1Shl57");
             ("_Align1Shl58", Some "_Align1Shl58");
             ("_Align1Shl59", Some "_Align1Shl59");
             ("_Align1Shl60", Some "_Align1Shl60");
             ("_Align1Shl61", Some "_Align1Shl61");
             ("_Align1Shl62", Some "_Align1Shl62");
             ("_Align1Shl63", Some "_Align1Shl63");
           ]);
    (* file: "Aeneas/Std/Core/Result.lean", line: 5 *)
    mk_type "core::result::Result" "core.result.Result"
      ~kind:(KEnum [ ("Ok", Some "Ok"); ("Err", Some "Err") ]);
    (* file: "Aeneas/Std/Slice.lean", line: 656 *)
    mk_type "core::slice::iter::Iter" "core.slice.iter.Iter"
      ~kind:(KStruct [ ("slice", Some "slice"); ("i", Some "i") ]);
    (* file: "Aeneas/Std/Slice.lean", line: 663 *)
    mk_type "core::slice::iter::IterMut" "core.slice.iter.IterMut"
      ~kind:(KStruct [ ("slice", Some "slice"); ("i", Some "i") ]);
    (* file: "Aeneas/Std/Core/Atomic.lean", line: 6 *)
    mk_type "core::sync::atomic::AtomicBool" "core.sync.atomic.AtomicBool";
    (* file: "Aeneas/Std/Core/Atomic.lean", line: 10 *)
    mk_type "core::sync::atomic::AtomicU32" "core.sync.atomic.AtomicU32";
  ]

let lean_builtin_consts = []

let lean_builtin_funs =
  [
    (* file: "Aeneas/Std/Alloc.lean", line: 25 *)
    mk_fun "alloc::alloc::{core::clone::Clone<alloc::alloc::Global>}::clone"
      "alloc.alloc.CloneGlobal.clone";
    (* file: "Aeneas/Std/Core/Core.lean", line: 48 *)
    mk_fun "alloc::boxed::{core::clone::Clone<Box<@T>>}::clone"
      "core.alloc.boxed.CloneBox.clone"
      ~keep_params:(Some [ true; false ])
      ~keep_trait_clauses:(Some [ true; false ]);
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 155 *)
    mk_fun "alloc::boxed::{core::cmp::PartialEq<Box<@T>, Box<@T>>}::eq"
      "alloc.boxed.PartialEqBox.eq"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Core/Core.lean", line: 14 *)
    mk_fun "alloc::boxed::{core::convert::AsMut<Box<@T>, @T>}::as_mut"
      "alloc.boxed.AsMutBox.as_mut"
      ~keep_params:(Some [ true; false ])
      ~can_fail:false;
    (* file: "Aeneas/Std/Alloc.lean", line: 19 *)
    mk_fun "alloc::boxed::{core::ops::deref::Deref<Box<@T>, @T>}::deref"
      "alloc.boxed.Box.deref"
      ~keep_params:(Some [ true; false ])
      ~can_fail:false;
    (* file: "Aeneas/Std/Alloc.lean", line: 22 *)
    mk_fun "alloc::boxed::{core::ops::deref::DerefMut<Box<@T>, @T>}::deref_mut"
      "alloc.boxed.Box.deref_mut"
      ~keep_params:(Some [ true; false ])
      ~can_fail:false;
    (* file: "Aeneas/Std/Vec.lean", line: 227 *)
    mk_fun "alloc::slice::{[@T]}::to_vec" "alloc.slice.Slice.to_vec";
    (* file: "Aeneas/Std/Vec.lean", line: 240 *)
    mk_fun "alloc::vec::from_elem" "alloc.vec.from_elem";
    (* file: "Aeneas/Std/Vec.lean", line: 371 *)
    mk_fun
      "alloc::vec::partial_eq::{core::cmp::PartialEq<alloc::vec::Vec<@T>, \
       alloc::vec::Vec<@U>>}::eq"
      "alloc.vec.partial_eq.PartialEqVec.eq"
      ~keep_params:(Some [ true; true; false; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 381 *)
    mk_fun
      "alloc::vec::partial_eq::{core::cmp::PartialEq<alloc::vec::Vec<@T>, \
       alloc::vec::Vec<@U>>}::ne"
      "alloc.vec.partial_eq.PartialEqVec.ne"
      ~keep_params:(Some [ true; true; false; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 260 *)
    mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::extend_from_slice"
      "alloc.vec.Vec.extend_from_slice"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 117 *)
    mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::insert" "alloc.vec.Vec.insert"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 50 *)
    mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::len" "alloc.vec.Vec.len"
      ~keep_params:(Some [ true; false ])
      ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Vec.lean", line: 43 *)
    mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::new" "alloc.vec.Vec.new"
      ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Vec.lean", line: 100 *)
    mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::push" "alloc.vec.Vec.push"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 294 *)
    mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::resize" "alloc.vec.Vec.resize"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 257 *)
    mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::with_capacity"
      "alloc.vec.Vec.with_capacity" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Vec.lean", line: 358 *)
    mk_fun "alloc::vec::{core::clone::Clone<alloc::vec::Vec<@T>>}::clone"
      "alloc.vec.CloneVec.clone"
      ~keep_params:(Some [ true; false ])
      ~keep_trait_clauses:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 321 *)
    mk_fun
      "alloc::vec::{core::convert::From<Box<[@T]>, alloc::vec::Vec<@T>>}::from"
      "alloc.vec.FromBoxSliceVec.from"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 271 *)
    mk_fun
      "alloc::vec::{core::ops::deref::Deref<alloc::vec::Vec<@T>, [@T]>}::deref"
      "alloc.vec.Vec.deref"
      ~keep_params:(Some [ true; false ])
      ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Vec.lean", line: 281 *)
    mk_fun
      "alloc::vec::{core::ops::deref::DerefMut<alloc::vec::Vec<@T>, \
       [@T]>}::deref_mut"
      "alloc.vec.Vec.deref_mut"
      ~keep_params:(Some [ true; false ])
      ~can_fail:false;
    (* file: "Aeneas/Std/Vec.lean", line: 181 *)
    mk_fun
      "alloc::vec::{core::ops::index::Index<alloc::vec::Vec<@T>, @I, \
       @O>}::index"
      "alloc.vec.Vec.index"
      ~keep_params:(Some [ true; true; false; true ]);
    (* file: "Aeneas/Std/Vec.lean", line: 187 *)
    mk_fun
      "alloc::vec::{core::ops::index::IndexMut<alloc::vec::Vec<@T>, @I, \
       @O>}::index_mut"
      "alloc.vec.Vec.index_mut"
      ~keep_params:(Some [ true; true; false; true ]);
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 124 *)
    mk_fun
      "core::array::equality::{core::cmp::PartialEq<[@T; @N], [@U; @N]>}::eq"
      "core.array.equality.PartialEqArray.eq";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 132 *)
    mk_fun
      "core::array::equality::{core::cmp::PartialEq<[@T; @N], [@U; @N]>}::ne"
      "core.array.equality.PartialEqArray.ne";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 193 *)
    mk_fun "core::array::{[@T; @N]}::as_mut_slice"
      "core.array.Array.as_mut_slice";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 189 *)
    mk_fun "core::array::{[@T; @N]}::as_slice" "core.array.Array.as_slice";
    (* file: "Aeneas/Std/Array/Array.lean", line: 190 *)
    mk_fun "core::array::{core::clone::Clone<[@T; @N]>}::clone"
      "core.array.CloneArray.clone";
    (* file: "Aeneas/Std/Array/Array.lean", line: 202 *)
    mk_fun "core::array::{core::clone::Clone<[@T; @N]>}::clone_from"
      "core.array.CloneArray.clone_from";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 159 *)
    mk_fun
      "core::array::{core::convert::TryFrom<&'a [@T; @N], &'a [@T], \
       core::array::TryFromSliceError>}::try_from"
      "core.array.TryFromSharedArraySlice.try_from";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 166 *)
    mk_fun
      "core::array::{core::convert::TryFrom<&'a mut [@T; @N], &'a mut [@T], \
       core::array::TryFromSliceError>}::try_from"
      "core.array.TryFromMutArraySlice.try_from";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 147 *)
    mk_fun
      "core::array::{core::convert::TryFrom<[@T; @N], &'0 [@T], \
       core::array::TryFromSliceError>}::try_from"
      "core.array.TryFromArrayCopySlice.try_from";
    (* file: "Aeneas/Std/Array/Array.lean", line: 261 *)
    mk_fun "core::array::{core::default::Default<[@T; 0]>}::default"
      "core.default.DefaultArrayEmpty.default";
    (* file: "Aeneas/Std/Array/Array.lean", line: 245 *)
    mk_fun "core::array::{core::default::Default<[@T; @N]>}::default"
      "core.default.DefaultArray.default";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 182 *)
    mk_fun "core::array::{core::fmt::Debug<[@T; @N]>}::fmt"
      "core.array.DebugArray.fmt";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 140 *)
    mk_fun
      "core::array::{core::fmt::Debug<core::array::TryFromSliceError>}::fmt"
      "core.array.DebugcorearrayTryFromSliceError.fmt";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 83 *)
    mk_fun "core::array::{core::ops::index::Index<[@T; @N], @I, @O>}::index"
      "core.array.Array.index";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 89 *)
    mk_fun
      "core::array::{core::ops::index::IndexMut<[@T; @N], @I, @O>}::index_mut"
      "core.array.Array.index_mut";
    (* file: "Aeneas/Std/Core/Core.lean", line: 123 *)
    mk_fun "core::clone::impls::{core::clone::Clone<&'0 @T>}::clone"
      "core.clone.impls.CloneShared.clone";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 18 *)
    mk_fun "core::cmp::Eq::assert_receiver_is_total_eq"
      "core.cmp.Eq.assert_receiver_is_total_eq.default";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 98 *)
    mk_fun "core::cmp::Ord::clamp" "core.cmp.Ord.clamp.default";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 86 *)
    mk_fun "core::cmp::Ord::max" "core.cmp.Ord.max.default";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 92 *)
    mk_fun "core::cmp::Ord::min" "core.cmp.Ord.min.default";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 24 *)
    mk_fun "core::cmp::PartialEq::ne" "core.cmp.PartialEq.ne.default";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 69 *)
    mk_fun "core::cmp::PartialOrd::ge" "core.cmp.PartialOrd.ge.default";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 61 *)
    mk_fun "core::cmp::PartialOrd::gt" "core.cmp.PartialOrd.gt.default";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 53 *)
    mk_fun "core::cmp::PartialOrd::le" "core.cmp.PartialOrd.le.default";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 45 *)
    mk_fun "core::cmp::PartialOrd::lt" "core.cmp.PartialOrd.lt.default";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 132 *)
    mk_fun "core::cmp::impls::{core::cmp::Ord<()>}::cmp"
      "core.cmp.impls.OrdUnit.cmp";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 144 *)
    mk_fun "core::cmp::impls::{core::cmp::PartialEq<&'a @A, &'b @B>}::eq"
      "core.cmp.impls.PartialEqShared.eq";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 116 *)
    mk_fun "core::cmp::impls::{core::cmp::PartialEq<(), ()>}::eq"
      "core.cmp.impls.PartialEqUnit.eq";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 119 *)
    mk_fun "core::cmp::impls::{core::cmp::PartialEq<(), ()>}::ne"
      "core.cmp.impls.PartialEqUnit.ne";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 136 *)
    mk_fun "core::cmp::impls::{core::cmp::PartialEq<bool, bool>}::eq"
      "core.cmp.impls.PartialEqBool.eq";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 128 *)
    mk_fun "core::cmp::impls::{core::cmp::PartialOrd<(), ()>}::partial_cmp"
      "core.cmp.impls.PartialOrdUnit.partial_cmp";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 111 *)
    mk_fun "core::cmp::max" "core.cmp.max";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 106 *)
    mk_fun "core::cmp::min" "core.cmp.min";
    (* file: "Aeneas/Std/Core/Convert.lean", line: 26 *)
    mk_fun "core::convert::{core::convert::From<@T, @T>}::from"
      "core.convert.FromSame.from_" ~can_fail:false;
    (* file: "Aeneas/Std/Core/Convert.lean", line: 15 *)
    mk_fun "core::convert::{core::convert::Into<@T, @U>}::into"
      "core.convert.IntoFrom.into";
    (* file: "Aeneas/Std/Core/Convert.lean", line: 38 *)
    mk_fun
      "core::convert::{core::convert::TryInto<@T, @U, \
       @Clause0_Error>}::try_into"
      "core.convert.TryInto.Blanket.try_into";
    (* file: "Aeneas/Std/Core/Default.lean", line: 9 *)
    mk_fun "core::default::{core::default::Default<bool>}::default"
      "core.default.DefaultBool.default";
    (* file: "Aeneas/Std/Scalar/Fmt.lean", line: 36 *)
    mk_fun "core::fmt::num::{core::fmt::Debug<u128>}::fmt"
      "core.fmt.num.DebugU128.fmt";
    (* file: "Aeneas/Std/Scalar/Fmt.lean", line: 18 *)
    mk_fun "core::fmt::num::{core::fmt::Debug<u16>}::fmt"
      "core.fmt.num.DebugU16.fmt";
    (* file: "Aeneas/Std/Scalar/Fmt.lean", line: 24 *)
    mk_fun "core::fmt::num::{core::fmt::Debug<u32>}::fmt"
      "core.fmt.num.DebugU32.fmt";
    (* file: "Aeneas/Std/Scalar/Fmt.lean", line: 30 *)
    mk_fun "core::fmt::num::{core::fmt::Debug<u64>}::fmt"
      "core.fmt.num.DebugU64.fmt";
    (* file: "Aeneas/Std/Scalar/Fmt.lean", line: 12 *)
    mk_fun "core::fmt::num::{core::fmt::Debug<u8>}::fmt"
      "core.fmt.num.DebugU8.fmt";
    (* file: "Aeneas/Std/Scalar/Fmt.lean", line: 42 *)
    mk_fun "core::fmt::num::{core::fmt::Debug<usize>}::fmt"
      "core.fmt.num.DebugUsize.fmt";
    (* file: "Aeneas/Std/Scalar/Fmt.lean", line: 6 *)
    mk_fun "core::fmt::num::{core::fmt::LowerHex<u16>}::fmt"
      "core.fmt.num.LowerHexU16.fmt";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 52 *)
    mk_fun "core::fmt::{core::fmt::Debug<&'0 @T>}::fmt"
      "core.fmt.DebugShared.fmt";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 64 *)
    mk_fun "core::fmt::{core::fmt::Debug<()>}::fmt" "core.fmt.DebugUnit.fmt";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 58 *)
    mk_fun "core::fmt::{core::fmt::Debug<bool>}::fmt" "core.fmt.DebugBool.fmt";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 45 *)
    mk_fun "core::fmt::{core::fmt::Formatter<'a>}::write_fmt"
      "core.fmt.Formatter.write_fmt";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 39 *)
    mk_fun "core::fmt::{core::fmt::Formatter<'a>}::write_str"
      "core.fmt.Formatter.write_str";
    (* file: "Aeneas/Std/Core/Discriminant.lean", line: 26 *)
    mk_fun "core::intrinsics::discriminant_value"
      "core.intrinsics.discriminant_value";
    (* file: "Aeneas/Std/Core/Core.lean", line: 73 *)
    mk_fun "core::mem::replace" "core.mem.replace" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Core/Core.lean", line: 77 *)
    mk_fun "core::mem::swap" "core.mem.swap" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Core/Core.lean", line: 110 *)
    mk_fun "core::option::{core::option::Option<@T>}::is_none"
      "core.option.Option.is_none" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Core/Core.lean", line: 107 *)
    mk_fun "core::option::{core::option::Option<@T>}::take"
      "core.option.Option.take" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Core/Core.lean", line: 91 *)
    mk_fun "core::option::{core::option::Option<@T>}::unwrap"
      "core.option.Option.unwrap";
    (* file: "Aeneas/Std/Core/Core.lean", line: 95 *)
    mk_fun "core::option::{core::option::Option<@T>}::unwrap_or"
      "core.option.Option.unwrap_or" ~can_fail:false;
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 18 *)
    mk_fun "core::result::{core::result::Result<@T, @E>}::unwrap"
      "core.result.Result.unwrap";
    (* file: "Aeneas/Std/Slice.lean", line: 226 *)
    mk_fun "core::slice::index::{core::ops::index::Index<[@T], @I, @O>}::index"
      "core.slice.index.Slice.index";
    (* file: "Aeneas/Std/Slice.lean", line: 295 *)
    mk_fun
      "core::slice::index::{core::ops::index::IndexMut<[@T], @I, \
       @O>}::index_mut"
      "core.slice.index.Slice.index_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 244 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::get"
      "core.slice.index.SliceIndexRangeUsizeSlice.get";
    (* file: "Aeneas/Std/Slice.lean", line: 251 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::get_mut"
      "core.slice.index.SliceIndexRangeUsizeSlice.get_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 265 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::get_unchecked"
      "core.slice.index.SliceIndexRangeUsizeSlice.get_unchecked";
    (* file: "Aeneas/Std/Slice.lean", line: 271 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::get_unchecked_mut"
      "core.slice.index.SliceIndexRangeUsizeSlice.get_unchecked_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 277 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::index"
      "core.slice.index.SliceIndexRangeUsizeSlice.index";
    (* file: "Aeneas/Std/Slice.lean", line: 283 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::index_mut"
      "core.slice.index.SliceIndexRangeUsizeSlice.index_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 457 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::get"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.get";
    (* file: "Aeneas/Std/Slice.lean", line: 463 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::get_mut"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.get_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 477 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::get_unchecked"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.get_unchecked";
    (* file: "Aeneas/Std/Slice.lean", line: 483 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::get_unchecked_mut"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.get_unchecked_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 489 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::index"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.index";
    (* file: "Aeneas/Std/Slice.lean", line: 496 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::index_mut"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 322 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, \
       [@T], [@T]>}::get"
      "core.slice.index.SliceIndexRangeToUsizeSlice.get";
    (* file: "Aeneas/Std/Slice.lean", line: 329 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, \
       [@T], [@T]>}::get_mut"
      "core.slice.index.SliceIndexRangeToUsizeSlice.get_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 344 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, \
       [@T], [@T]>}::get_unchecked"
      "core.slice.index.SliceIndexRangeToUsizeSlice.get_unchecked";
    (* file: "Aeneas/Std/Slice.lean", line: 350 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, \
       [@T], [@T]>}::get_unchecked_mut"
      "core.slice.index.SliceIndexRangeToUsizeSlice.get_unchecked_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 357 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, \
       [@T], [@T]>}::index"
      "core.slice.index.SliceIndexRangeToUsizeSlice.index";
    (* file: "Aeneas/Std/Slice.lean", line: 364 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, \
       [@T], [@T]>}::index_mut"
      "core.slice.index.SliceIndexRangeToUsizeSlice.index_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 404 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
       @T>}::get"
      "core.slice.index.Usize.get";
    (* file: "Aeneas/Std/Slice.lean", line: 409 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
       @T>}::get_mut"
      "core.slice.index.Usize.get_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 414 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
       @T>}::get_unchecked"
      "core.slice.index.Usize.get_unchecked";
    (* file: "Aeneas/Std/Slice.lean", line: 420 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
       @T>}::get_unchecked_mut"
      "core.slice.index.Usize.get_unchecked_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 426 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
       @T>}::index"
      "core.slice.index.Usize.index";
    (* file: "Aeneas/Std/Slice.lean", line: 430 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
       @T>}::index_mut"
      "core.slice.index.Usize.index_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 674 *)
    mk_fun "core::slice::{[@T]}::contains" "core.slice.Slice.contains";
    (* file: "Aeneas/Std/Slice.lean", line: 451 *)
    mk_fun "core::slice::{[@T]}::copy_from_slice"
      "core.slice.Slice.copy_from_slice";
    (* file: "Aeneas/Std/Slice.lean", line: 232 *)
    mk_fun "core::slice::{[@T]}::get" "core.slice.Slice.get";
    (* file: "Aeneas/Std/Slice.lean", line: 238 *)
    mk_fun "core::slice::{[@T]}::get_mut" "core.slice.Slice.get_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 670 *)
    mk_fun "core::slice::{[@T]}::iter" "core.slice.Slice.iter";
    (* file: "Aeneas/Std/Slice.lean", line: 44 *)
    mk_fun "core::slice::{[@T]}::len" "Slice.len" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Slice.lean", line: 209 *)
    mk_fun "core::slice::{[@T]}::reverse" "core.slice.Slice.reverse"
      ~can_fail:false;
    (* file: "Aeneas/Std/Slice.lean", line: 559 *)
    mk_fun "core::slice::{[@T]}::split_at" "core.slice.Slice.split_at";
    (* file: "Aeneas/Std/Slice.lean", line: 570 *)
    mk_fun "core::slice::{[@T]}::split_at_mut" "core.slice.Slice.split_at_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 588 *)
    mk_fun "core::slice::{[@T]}::swap" "core.slice.Slice.swap";
  ]

let lean_builtin_trait_decls =
  [
    (* file: "Aeneas/Std/Core/Ptr.lean", line: 82 *)
    mk_trait_decl "core::alloc::global::GlobalAlloc"
      "core.alloc.global.GlobalAlloc"
      ~methods:[ ("alloc", "alloc"); ("dealloc", "dealloc") ];
    (* file: "Aeneas/Std/Core/Core.lean", line: 24 *)
    mk_trait_decl "core::clone::Clone" "core.clone.Clone"
      ~methods:[ ("clone", "clone"); ("clone_from", "clone_from") ]
      ~default_methods:[ "clone_from" ];
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 13 *)
    mk_trait_decl "core::cmp::Eq" "core.cmp.Eq"
      ~parent_clauses:[ "partialEqInst" ]
      ~methods:
        [ ("assert_receiver_is_total_eq", "assert_receiver_is_total_eq") ];
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 76 *)
    mk_trait_decl "core::cmp::Ord" "core.cmp.Ord"
      ~parent_clauses:[ "eqInst"; "partialOrdInst" ]
      ~methods:
        [ ("cmp", "cmp"); ("max", "max"); ("min", "min"); ("clamp", "clamp") ];
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 8 *)
    mk_trait_decl "core::cmp::PartialEq" "core.cmp.PartialEq"
      ~methods:[ ("eq", "eq"); ("ne", "ne") ];
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 35 *)
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
    (* file: "Aeneas/Std/Core/Convert.lean", line: 59 *)
    mk_trait_decl "core::convert::AsMut" "core.convert.AsMut"
      ~methods:[ ("as_mut", "as_mut") ];
    (* file: "Aeneas/Std/Core/Core.lean", line: 20 *)
    mk_trait_decl "core::convert::From" "core.convert.From"
      ~methods:[ ("from", "from_") ];
    (* file: "Aeneas/Std/Core/Convert.lean", line: 11 *)
    mk_trait_decl "core::convert::Into" "core.convert.Into"
      ~methods:[ ("into", "into") ];
    (* file: "Aeneas/Std/Core/Convert.lean", line: 34 *)
    mk_trait_decl "core::convert::TryFrom" "core.convert.TryFrom"
      ~methods:[ ("try_from", "try_from") ];
    (* file: "Aeneas/Std/Core/Convert.lean", line: 44 *)
    mk_trait_decl "core::convert::TryInto" "core.convert.TryInto"
      ~methods:[ ("try_into", "try_into") ];
    (* file: "Aeneas/Std/Core/Default.lean", line: 5 *)
    mk_trait_decl "core::default::Default" "core.default.Default"
      ~methods:[ ("default", "default") ];
    (* file: "Aeneas/Std/Core/Error.lean", line: 5 *)
    mk_trait_decl "core::error::Error" "core.error.Error"
      ~parent_clauses:[ "fmtDebugInst"; "fmtDisplayInst" ];
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 13 *)
    mk_trait_decl "core::fmt::Debug" "core.fmt.Debug"
      ~methods:[ ("fmt", "fmt") ];
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 31 *)
    mk_trait_decl "core::fmt::Display" "core.fmt.Display"
      ~methods:[ ("fmt", "fmt") ];
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 35 *)
    mk_trait_decl "core::fmt::LowerHex" "core.fmt.LowerHex"
      ~methods:[ ("fmt", "fmt") ];
    (* file: "Aeneas/Std/Core/Hash.lean", line: 11 *)
    mk_trait_decl "core::hash::Hash" "core.hash.Hash"
      ~methods:[ ("hash", "hash") ];
    (* file: "Aeneas/Std/Core/Hash.lean", line: 6 *)
    mk_trait_decl "core::hash::Hasher" "core.hash.Hasher"
      ~methods:[ ("finish", "finish"); ("write", "write") ];
    (* file: "Aeneas/Std/Core/Core.lean", line: 59 *)
    mk_trait_decl "core::marker::Copy" "core.marker.Copy"
      ~parent_clauses:[ "cloneInst" ];
    (* file: "Aeneas/Std/Core/Discriminant.lean", line: 8 *)
    mk_trait_decl "core::marker::DiscriminantKind" "DiscriminantKind"
      ~parent_clauses:
        [
          "cloneInst";
          "copyInst";
          "debugInst";
          "partialEqInst";
          "eqInst";
          "hashInst";
        ]
      ~types:[ ("Discriminant", "Discriminant") ];
    (* file: "Aeneas/Std/Core/Marker.lean", line: 8 *)
    mk_trait_decl "core::marker::Freeze" "core.marker.Freeze";
    (* file: "Aeneas/Std/Core/Marker.lean", line: 5 *)
    mk_trait_decl "core::marker::StructuralPartialEq"
      "core.marker.StructuralPartialEq";
    (* file: "Aeneas/Std/Core/Ops.lean", line: 43 *)
    mk_trait_decl "core::ops::bit::BitAnd" "core.ops.bit.BitAnd"
      ~methods:[ ("bitand", "bitand") ];
    (* file: "Aeneas/Std/Core/Ops.lean", line: 19 *)
    mk_trait_decl "core::ops::deref::Deref" "core.ops.deref.Deref"
      ~methods:[ ("deref", "deref") ];
    (* file: "Aeneas/Std/Core/Ops.lean", line: 23 *)
    mk_trait_decl "core::ops::deref::DerefMut" "core.ops.deref.DerefMut"
      ~parent_clauses:[ "derefInst" ]
      ~methods:[ ("deref_mut", "deref_mut") ];
    (* file: "Aeneas/Std/Core/Ops.lean", line: 56 *)
    mk_trait_decl "core::ops::function::Fn" "core.ops.function.Fn"
      ~parent_clauses:[ "FnMutInst" ]
      ~methods:[ ("call", "call") ];
    (* file: "Aeneas/Std/Core/Ops.lean", line: 51 *)
    mk_trait_decl "core::ops::function::FnMut" "core.ops.function.FnMut"
      ~parent_clauses:[ "FnOnceInst" ]
      ~methods:[ ("call_mut", "call_mut") ];
    (* file: "Aeneas/Std/Core/Ops.lean", line: 47 *)
    mk_trait_decl "core::ops::function::FnOnce" "core.ops.function.FnOnce"
      ~methods:[ ("call_once", "call_once") ];
    (* file: "Aeneas/Std/Core/Ops.lean", line: 10 *)
    mk_trait_decl "core::ops::index::Index" "core.ops.index.Index"
      ~methods:[ ("index", "index") ];
    (* file: "Aeneas/Std/Core/Ops.lean", line: 14 *)
    mk_trait_decl "core::ops::index::IndexMut" "core.ops.index.IndexMut"
      ~parent_clauses:[ "indexInst" ]
      ~methods:[ ("index_mut", "index_mut") ];
    (* file: "Aeneas/Std/Core/Ops.lean", line: 61 *)
    mk_trait_decl "core::ops::try_trait::FromResidual"
      "core.ops.try_trait.FromResidual"
      ~methods:[ ("from_residual", "from_residual") ];
    (* file: "Aeneas/Std/Core/Ops.lean", line: 76 *)
    mk_trait_decl "core::ops::try_trait::Residual" "core.ops.try_trait.Residual"
      ~parent_clauses:[ "TryInst" ];
    (* file: "Aeneas/Std/Core/Ops.lean", line: 70 *)
    mk_trait_decl "core::ops::try_trait::Try" "core.ops.try_trait.Try"
      ~parent_clauses:[ "FromResidualInst" ]
      ~methods:[ ("from_output", "from_output"); ("branch", "branch") ];
    (* file: "Aeneas/Std/Slice.lean", line: 216 *)
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
    (* file: "Aeneas/Std/Slice.lean", line: 213 *)
    mk_trait_decl "core::slice::index::private_slice_index::Sealed"
      "core.slice.index.private_slice_index.Sealed";
  ]

let lean_builtin_trait_impls =
  [
    (* file: "Aeneas/Std/Core/Core.lean", line: 53 *)
    mk_trait_impl "core::clone::Clone<Box<@T>>" "core.core.clone.CloneBox"
      ~keep_params:(Some [ true; false ])
      ~keep_trait_clauses:(Some [ true; false ]);
    (* file: "Aeneas/Std/Array/Array.lean", line: 214 *)
    mk_trait_impl "core::clone::Clone<[@T; @N]>" "core.clone.CloneArray";
    (* file: "Aeneas/Std/Core/Core.lean", line: 33 *)
    mk_trait_impl "core::clone::Clone<alloc::alloc::Global>"
      "core.core.clone.CloneGlobal";
    (* file: "Aeneas/Std/Vec.lean", line: 364 *)
    mk_trait_impl "core::clone::Clone<alloc::vec::Vec<@T>>"
      "core.clone.CloneallocvecVec"
      ~keep_params:(Some [ true; false ])
      ~keep_trait_clauses:(Some [ true; false ]);
    (* file: "Aeneas/Std/Core/Core.lean", line: 42 *)
    mk_trait_impl "core::clone::Clone<bool>" "core.clone.CloneBool";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 149 *)
    mk_trait_impl "core::cmp::PartialEq<&'a @A, &'b @B>"
      "core.cmp.PartialEqShared";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 122 *)
    mk_trait_impl "core::cmp::PartialEq<(), ()>" "core.cmp.PartialEqUnit";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 160 *)
    mk_trait_impl "core::cmp::PartialEq<Box<@T>, Box<@T>>"
      "core.cmp.PartialEqBox"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 392 *)
    mk_trait_impl
      "core::cmp::PartialEq<alloc::vec::Vec<@T>, alloc::vec::Vec<@U>>"
      "core.cmp.PartialEqVec"
      ~keep_params:(Some [ true; true; false; false ]);
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 139 *)
    mk_trait_impl "core::cmp::PartialEq<bool, bool>" "core.cmp.PartialEqBool";
    (* file: "Aeneas/Std/Core/Convert.lean", line: 63 *)
    mk_trait_impl "core::convert::AsMut<Box<@T>, @T>" "core.convert.AsMutBox";
    (* file: "Aeneas/Std/Core/Convert.lean", line: 29 *)
    mk_trait_impl "core::convert::From<@Self, @Self>" "core.convert.FromSame";
    (* file: "Aeneas/Std/Vec.lean", line: 329 *)
    mk_trait_impl "core::convert::From<Box<[@T]>, alloc::vec::Vec<@T>>"
      "core.convert.FromBoxSliceVec"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Core/Convert.lean", line: 20 *)
    mk_trait_impl "core::convert::Into<@Self, @T>" "core.convert.IntoFrom";
    (* file: "Aeneas/Std/Core/Convert.lean", line: 53 *)
    mk_trait_impl "core::convert::{core::convert::TryInto<@T, @U>}"
      "core.convert.TryIntoFrom";
    (* file: "Aeneas/Std/Array/Array.lean", line: 266 *)
    mk_trait_impl "core::default::Default<[@T; 0]>"
      "core.default.DefaultArrayEmpty";
    (* file: "Aeneas/Std/Array/Array.lean", line: 255 *)
    mk_trait_impl "core::default::Default<[@T; @N]>" "core.default.DefaultArray";
    (* file: "Aeneas/Std/Core/Core.lean", line: 63 *)
    mk_trait_impl "core::marker::Copy<bool>" "core.core.marker.CopyBool";
    (* file: "Aeneas/Std/Core/Ops.lean", line: 29 *)
    mk_trait_impl "core::ops::deref::Deref<Box<@T>, @T>"
      "core.ops.deref.DerefBoxInst";
    (* file: "Aeneas/Std/Vec.lean", line: 276 *)
    mk_trait_impl "core::ops::deref::Deref<alloc::vec::Vec<@T>, [@T]>"
      "core.ops.deref.DerefVec"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Core/Ops.lean", line: 36 *)
    mk_trait_impl "core::ops::deref::DerefMut<Box<@T>, @T>"
      "core.ops.deref.DerefMutBoxInst";
    (* file: "Aeneas/Std/Vec.lean", line: 287 *)
    mk_trait_impl "core::ops::deref::DerefMut<alloc::vec::Vec<@T>, [@T]>"
      "core.ops.deref.DerefMutVec"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 97 *)
    mk_trait_impl "core::ops::index::Index<[@T; @N], @I, @O>"
      "core.ops.index.IndexArray";
    (* file: "Aeneas/Std/Slice.lean", line: 389 *)
    mk_trait_impl "core::ops::index::Index<[@T], @I, @O>"
      "core.ops.index.IndexSlice";
    (* file: "Aeneas/Std/Vec.lean", line: 195 *)
    mk_trait_impl "core::ops::index::Index<alloc::vec::Vec<@T>, @T, @O>"
      "alloc.vec.Vec.Index"
      ~keep_params:(Some [ true; true; false; true ]);
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 104 *)
    mk_trait_impl "core::ops::index::IndexMut<[@T; @N], @I, @O>"
      "core.ops.index.IndexMutArray";
    (* file: "Aeneas/Std/Slice.lean", line: 396 *)
    mk_trait_impl "core::ops::index::IndexMut<[@T], @I, @O>"
      "core.ops.index.IndexMutSlice";
    (* file: "Aeneas/Std/Vec.lean", line: 203 *)
    mk_trait_impl "core::ops::index::IndexMut<alloc::vec::Vec<@T>, @T, @O>"
      "alloc.vec.Vec.IndexMut"
      ~keep_params:(Some [ true; true; false; true ]);
    (* file: "Aeneas/Std/Slice.lean", line: 305 *)
    mk_trait_impl
      "core::slice::index::SliceIndex<core::ops::range::Range<usize>, [@T], \
       [@T]>"
      "core.slice.index.SliceIndexRangeUsizeSlice";
    (* file: "Aeneas/Std/Slice.lean", line: 521 *)
    mk_trait_impl
      "core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>"
      "core.slice.index.SliceIndexRangeFromUsizeSlice";
    (* file: "Aeneas/Std/Slice.lean", line: 376 *)
    mk_trait_impl
      "core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, [@T], \
       [@T]>"
      "core.slice.index.SliceIndexRangeToUsizeSlice";
    (* file: "Aeneas/Std/Slice.lean", line: 439 *)
    mk_trait_impl "core::slice::index::SliceIndex<usize, [@T], @T>"
      "core.slice.index.SliceIndexUsizeSlice";
    (* file: "Aeneas/Std/Slice.lean", line: 301 *)
    mk_trait_impl
      "core::slice::index::private_slice_index::Sealed<core::ops::range::Range<usize>>"
      "core.slice.index.private_slice_index.SealedRangeUsize";
    (* file: "Aeneas/Std/Slice.lean", line: 516 *)
    mk_trait_impl
      "core::slice::index::private_slice_index::Sealed<core::ops::range::RangeFrom<usize>>"
      "core.slice.index.private_slice_index.SealedRangeFromUsize";
    (* file: "Aeneas/Std/Slice.lean", line: 317 *)
    mk_trait_impl
      "core::slice::index::private_slice_index::Sealed<core::ops::range::RangeTo<usize>>"
      "core.slice.index.private_slice_index.SealedRangeToUsize";
    (* file: "Aeneas/Std/Slice.lean", line: 435 *)
    mk_trait_impl "core::slice::index::private_slice_index::Sealed<usize>"
      "core.slice.index.private_slice_index.SealedUsize";
  ]
