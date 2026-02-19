(** THIS FILE WAS AUTOMATICALLY GENERATED FROM LEAN: DO NOT MODIFY DIRECTLY *)
open ExtractBuiltinCore

let lean_builtin_types =
  [
    (* file: "Aeneas/Std/Alloc.lean", line: 16 *)
    mk_type "alloc::alloc::Global" "Global" ~kind:(KEnum [ ("Mk", Some "mk") ]);
    (* file: "Aeneas/Std/Alloc.lean", line: 11 *)
    mk_type "alloc::string::String" "String";
    (* file: "Aeneas/Std/Vec.lean", line: 18 *)
    mk_type "alloc::vec::Vec" "alloc.vec.Vec";
    (* file: "Aeneas/Std/VecIter.lean", line: 8 *)
    mk_type "alloc::vec::into_iter::IntoIter" "alloc.vec.into_iter.IntoIter"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Core/Ptr.lean", line: 78 *)
    mk_type "core::alloc::layout::Layout" "core.alloc.layout.Layout"
      ~kind:(KStruct [ ("size", Some "size"); ("align", Some "align") ]);
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 115 *)
    mk_type "core::array::TryFromSliceError" "core.array.TryFromSliceError";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 31 *)
    mk_type "core::cmp::Ordering" "Ordering"
      ~kind:
        (KEnum
           [ ("Less", Some "lt"); ("Equal", Some "eq"); ("Greater", Some "gt") ]);
    (* file: "Aeneas/Std/Core/Convert.lean", line: 8 *)
    mk_type "core::convert::Infallible" "core.convert.Infallible"
      ~kind:(KEnum []);
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 27 *)
    mk_type "core::fmt::Arguments" "core.fmt.Arguments";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 7 *)
    mk_type "core::fmt::Error" "core.fmt.Error";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 11 *)
    mk_type "core::fmt::Formatter" "core.fmt.Formatter";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 30 *)
    mk_type "core::fmt::rt::Argument" "core.fmt.rt.Argument";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 36 *)
    mk_type "core::iter::adapters::enumerate::Enumerate"
      "core.iter.adapters.enumerate.Enumerate"
      ~kind:(KStruct [ ("iter", Some "iter"); ("count", Some "count") ]);
    (* file: "Aeneas/Std/Core/Iter.lean", line: 249 *)
    mk_type "core::iter::adapters::map::Map" "core.iter.adapters.map.Map"
      ~kind:(KStruct [ ("iter", Some "iter"); ("f", Some "f") ]);
    (* file: "Aeneas/Std/Core/Iter.lean", line: 46 *)
    mk_type "core::iter::adapters::rev::Rev" "core.iter.adapters.rev.Rev"
      ~kind:(KStruct [ ("iter", Some "iter") ]);
    (* file: "Aeneas/Std/Core/Iter.lean", line: 30 *)
    mk_type "core::iter::adapters::step_by::StepBy"
      "core.iter.adapters.step_by.StepBy";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 41 *)
    mk_type "core::iter::adapters::take::Take" "core.iter.adapters.take.Take"
      ~kind:(KStruct [ ("iter", Some "iter"); ("n", Some "n") ]);
    (* file: "Aeneas/Std/Core/Ops.lean", line: 83 *)
    mk_type "core::ops::control_flow::ControlFlow"
      "core.ops.control_flow.ControlFlow"
      ~kind:(KEnum [ ("Continue", Some "Continue"); ("Break", Some "Break") ]);
    (* file: "Aeneas/Std/Range.lean", line: 14 *)
    mk_type "core::ops::range::Range" "core.ops.range.Range"
      ~kind:(KStruct [ ("start", Some "start"); ("end", Some "«end»") ]);
    (* file: "Aeneas/Std/Core/Core.lean", line: 113 *)
    mk_type "core::ops::range::RangeFrom" "core.ops.range.RangeFrom"
      ~kind:(KStruct [ ("start", Some "start") ]);
    (* file: "Aeneas/Std/Range.lean", line: 20 *)
    mk_type "core::ops::range::RangeTo" "core.ops.range.RangeTo"
      ~kind:(KStruct [ ("end", Some "«end»") ]);
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
    (* file: "Aeneas/Std/Core/Ptr.lean", line: 74 *)
    mk_type "core::ptr::alignment::Alignment" "core.ptr.alignment.Alignment";
    (* file: "Aeneas/Std/Core/Ptr.lean", line: 7 *)
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
    (* file: "Aeneas/Std/SliceIter.lean", line: 96 *)
    mk_type "core::slice::iter::ChunksExact" "core.slice.iter.ChunksExact";
    (* file: "Aeneas/Std/SliceIter.lean", line: 12 *)
    mk_type "core::slice::iter::Iter" "core.slice.iter.Iter"
      ~kind:(KStruct [ ("slice", Some "slice"); ("i", Some "i") ]);
    (* file: "Aeneas/Std/SliceIter.lean", line: 19 *)
    mk_type "core::slice::iter::IterMut" "core.slice.iter.IterMut"
      ~mut_regions:[ 0 ];
    (* file: "Aeneas/Std/StringIter.lean", line: 7 *)
    mk_type "core::str::iter::Chars" "core.str.iter.Chars";
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
    (* file: "Aeneas/Std/Vec.lean", line: 233 *)
    mk_fun "alloc::slice::{[@T]}::into_vec" "alloc.slice.Slice.into_vec"
      ~keep_params:(Some [ true; false ])
      ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Vec.lean", line: 221 *)
    mk_fun "alloc::slice::{[@T]}::to_vec" "alloc.slice.Slice.to_vec";
    (* file: "Aeneas/Std/Vec.lean", line: 237 *)
    mk_fun "alloc::vec::from_elem" "alloc.vec.from_elem";
    (* file: "Aeneas/Std/VecIter.lean", line: 27 *)
    mk_fun
      "alloc::vec::into_iter::{core::iter::traits::iterator::Iterator<alloc::vec::into_iter::IntoIter<@T, \
       @A>, @T>}::enumerate"
      "alloc.vec.into_iter.IteratorIntoIter.enumerate"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/VecIter.lean", line: 83 *)
    mk_fun
      "alloc::vec::into_iter::{core::iter::traits::iterator::Iterator<alloc::vec::into_iter::IntoIter<@T, \
       @A>, @T>}::map"
      "alloc.vec.into_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.map";
    (* file: "Aeneas/Std/VecIter.lean", line: 11 *)
    mk_fun
      "alloc::vec::into_iter::{core::iter::traits::iterator::Iterator<alloc::vec::into_iter::IntoIter<@T, \
       @A>, @T>}::next"
      "alloc.vec.into_iter.IteratorIntoIter.next"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/VecIter.lean", line: 20 *)
    mk_fun
      "alloc::vec::into_iter::{core::iter::traits::iterator::Iterator<alloc::vec::into_iter::IntoIter<@T, \
       @A>, @T>}::step_by"
      "alloc.vec.into_iter.IteratorIntoIter.step_by"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/VecIter.lean", line: 34 *)
    mk_fun
      "alloc::vec::into_iter::{core::iter::traits::iterator::Iterator<alloc::vec::into_iter::IntoIter<@T, \
       @A>, @T>}::take"
      "alloc.vec.into_iter.IteratorIntoIter.take"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 381 *)
    mk_fun
      "alloc::vec::partial_eq::{core::cmp::PartialEq<alloc::vec::Vec<@T>, \
       alloc::vec::Vec<@U>>}::eq"
      "alloc.vec.partial_eq.PartialEqVec.eq"
      ~keep_params:(Some [ true; true; false; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 391 *)
    mk_fun
      "alloc::vec::partial_eq::{core::cmp::PartialEq<alloc::vec::Vec<@T>, \
       alloc::vec::Vec<@U>>}::ne"
      "alloc.vec.partial_eq.PartialEqVec.ne"
      ~keep_params:(Some [ true; true; false; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 257 *)
    mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::extend_from_slice"
      "alloc.vec.Vec.extend_from_slice"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 115 *)
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
    (* file: "Aeneas/Std/Vec.lean", line: 291 *)
    mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::resize" "alloc.vec.Vec.resize"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 254 *)
    mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::with_capacity"
      "alloc.vec.Vec.with_capacity" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Vec.lean", line: 368 *)
    mk_fun "alloc::vec::{core::clone::Clone<alloc::vec::Vec<@T>>}::clone"
      "alloc.vec.CloneVec.clone"
      ~keep_params:(Some [ true; false ])
      ~keep_trait_clauses:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 331 *)
    mk_fun
      "alloc::vec::{core::convert::From<Box<[@T]>, alloc::vec::Vec<@T>>}::from"
      "alloc.vec.FromBoxSliceVec.from"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 317 *)
    mk_fun
      "alloc::vec::{core::convert::From<alloc::vec::Vec<@T>, [@T; @N]>}::from"
      "alloc.vec.FromVecArray.from";
    (* file: "Aeneas/Std/Vec.lean", line: 412 *)
    mk_fun "alloc::vec::{core::fmt::Debug<alloc::vec::Vec<@T>>}::fmt"
      "alloc.vec.DebugVec.fmt"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/VecIter.lean", line: 67 *)
    mk_fun
      "alloc::vec::{core::iter::traits::collect::FromIterator<alloc::vec::Vec<@T>, \
       @T>}::from_iter"
      "alloc.vec.FromIteratorVec.from_iter";
    (* file: "Aeneas/Std/VecIter.lean", line: 52 *)
    mk_fun
      "alloc::vec::{core::iter::traits::collect::IntoIterator<alloc::vec::Vec<@T>, \
       @T, alloc::vec::into_iter::IntoIter<@T, @A>>}::into_iter"
      "alloc.vec.IntoIteratorVec.into_iter"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 268 *)
    mk_fun
      "alloc::vec::{core::ops::deref::Deref<alloc::vec::Vec<@T>, [@T]>}::deref"
      "alloc.vec.Vec.deref"
      ~keep_params:(Some [ true; false ])
      ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Vec.lean", line: 278 *)
    mk_fun
      "alloc::vec::{core::ops::deref::DerefMut<alloc::vec::Vec<@T>, \
       [@T]>}::deref_mut"
      "alloc.vec.Vec.deref_mut"
      ~keep_params:(Some [ true; false ])
      ~can_fail:false;
    (* file: "Aeneas/Std/Vec.lean", line: 175 *)
    mk_fun
      "alloc::vec::{core::ops::index::Index<alloc::vec::Vec<@T>, @I, \
       @O>}::index"
      "alloc.vec.Vec.index"
      ~keep_params:(Some [ true; true; false; true ]);
    (* file: "Aeneas/Std/Vec.lean", line: 181 *)
    mk_fun
      "alloc::vec::{core::ops::index::IndexMut<alloc::vec::Vec<@T>, @I, \
       @O>}::index_mut"
      "alloc.vec.Vec.index_mut"
      ~keep_params:(Some [ true; true; false; true ]);
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 127 *)
    mk_fun
      "core::array::equality::{core::cmp::PartialEq<[@T; @N], [@U; @N]>}::eq"
      "core.array.equality.PartialEqArray.eq";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 135 *)
    mk_fun
      "core::array::equality::{core::cmp::PartialEq<[@T; @N], [@U; @N]>}::ne"
      "core.array.equality.PartialEqArray.ne";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 211 *)
    mk_fun "core::array::{[@T; @N]}::as_mut_slice"
      "core.array.Array.as_mut_slice";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 207 *)
    mk_fun "core::array::{[@T; @N]}::as_slice" "core.array.Array.as_slice";
    (* file: "Aeneas/Std/Array/Array.lean", line: 192 *)
    mk_fun "core::array::{core::clone::Clone<[@T; @N]>}::clone"
      "core.array.CloneArray.clone";
    (* file: "Aeneas/Std/Array/Array.lean", line: 205 *)
    mk_fun "core::array::{core::clone::Clone<[@T; @N]>}::clone_from"
      "core.array.CloneArray.clone_from";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 169 *)
    mk_fun
      "core::array::{core::convert::TryFrom<&'a [@T; @N], &'a [@T], \
       core::array::TryFromSliceError>}::try_from"
      "core.array.TryFromSharedArraySlice.try_from";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 184 *)
    mk_fun
      "core::array::{core::convert::TryFrom<&'a mut [@T; @N], &'a mut [@T], \
       core::array::TryFromSliceError>}::try_from"
      "core.array.TryFromMutArraySlice.try_from";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 157 *)
    mk_fun
      "core::array::{core::convert::TryFrom<[@T; @N], &'0 [@T], \
       core::array::TryFromSliceError>}::try_from"
      "core.array.TryFromArrayCopySlice.try_from";
    (* file: "Aeneas/Std/Array/Array.lean", line: 265 *)
    mk_fun "core::array::{core::default::Default<[@T; 0]>}::default"
      "core.default.DefaultArrayEmpty.default";
    (* file: "Aeneas/Std/Array/Array.lean", line: 249 *)
    mk_fun "core::array::{core::default::Default<[@T; @N]>}::default"
      "core.default.DefaultArray.default";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 200 *)
    mk_fun "core::array::{core::fmt::Debug<[@T; @N]>}::fmt"
      "core.array.DebugArray.fmt";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 143 *)
    mk_fun
      "core::array::{core::fmt::Debug<core::array::TryFromSliceError>}::fmt"
      "core.array.DebugTryFromSliceError.fmt";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 86 *)
    mk_fun "core::array::{core::ops::index::Index<[@T; @N], @I, @O>}::index"
      "core.array.Array.index";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 92 *)
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
    (* file: "Aeneas/Std/Scalar/Display.lean", line: 56 *)
    mk_fun "core::fmt::num::imp::{core::fmt::Display<i128>}::fmt"
      "core.fmt.num.imp.DisplayI128.fmt";
    (* file: "Aeneas/Std/Scalar/Display.lean", line: 41 *)
    mk_fun "core::fmt::num::imp::{core::fmt::Display<i16>}::fmt"
      "core.fmt.num.imp.DisplayI16.fmt";
    (* file: "Aeneas/Std/Scalar/Display.lean", line: 46 *)
    mk_fun "core::fmt::num::imp::{core::fmt::Display<i32>}::fmt"
      "core.fmt.num.imp.DisplayI32.fmt";
    (* file: "Aeneas/Std/Scalar/Display.lean", line: 51 *)
    mk_fun "core::fmt::num::imp::{core::fmt::Display<i64>}::fmt"
      "core.fmt.num.imp.DisplayI64.fmt";
    (* file: "Aeneas/Std/Scalar/Display.lean", line: 36 *)
    mk_fun "core::fmt::num::imp::{core::fmt::Display<i8>}::fmt"
      "core.fmt.num.imp.DisplayI8.fmt";
    (* file: "Aeneas/Std/Scalar/Display.lean", line: 61 *)
    mk_fun "core::fmt::num::imp::{core::fmt::Display<isize>}::fmt"
      "core.fmt.num.imp.DisplayIsize.fmt";
    (* file: "Aeneas/Std/Scalar/Display.lean", line: 26 *)
    mk_fun "core::fmt::num::imp::{core::fmt::Display<u128>}::fmt"
      "core.fmt.num.imp.DisplayU128.fmt";
    (* file: "Aeneas/Std/Scalar/Display.lean", line: 11 *)
    mk_fun "core::fmt::num::imp::{core::fmt::Display<u16>}::fmt"
      "core.fmt.num.imp.DisplayU16.fmt";
    (* file: "Aeneas/Std/Scalar/Display.lean", line: 16 *)
    mk_fun "core::fmt::num::imp::{core::fmt::Display<u32>}::fmt"
      "core.fmt.num.imp.DisplayU32.fmt";
    (* file: "Aeneas/Std/Scalar/Display.lean", line: 21 *)
    mk_fun "core::fmt::num::imp::{core::fmt::Display<u64>}::fmt"
      "core.fmt.num.imp.DisplayU64.fmt";
    (* file: "Aeneas/Std/Scalar/Display.lean", line: 6 *)
    mk_fun "core::fmt::num::imp::{core::fmt::Display<u8>}::fmt"
      "core.fmt.num.imp.DisplayU8.fmt";
    (* file: "Aeneas/Std/Scalar/Display.lean", line: 31 *)
    mk_fun "core::fmt::num::imp::{core::fmt::Display<usize>}::fmt"
      "core.fmt.num.imp.DisplayUsize.fmt";
    (* file: "Aeneas/Std/Scalar/Fmt.lean", line: 102 *)
    mk_fun "core::fmt::num::{core::fmt::Debug<i128>}::fmt"
      "core.fmt.num.DebugI128.fmt";
    (* file: "Aeneas/Std/Scalar/Fmt.lean", line: 84 *)
    mk_fun "core::fmt::num::{core::fmt::Debug<i16>}::fmt"
      "core.fmt.num.DebugI16.fmt";
    (* file: "Aeneas/Std/Scalar/Fmt.lean", line: 90 *)
    mk_fun "core::fmt::num::{core::fmt::Debug<i32>}::fmt"
      "core.fmt.num.DebugI32.fmt";
    (* file: "Aeneas/Std/Scalar/Fmt.lean", line: 96 *)
    mk_fun "core::fmt::num::{core::fmt::Debug<i64>}::fmt"
      "core.fmt.num.DebugI64.fmt";
    (* file: "Aeneas/Std/Scalar/Fmt.lean", line: 78 *)
    mk_fun "core::fmt::num::{core::fmt::Debug<i8>}::fmt"
      "core.fmt.num.DebugI8.fmt";
    (* file: "Aeneas/Std/Scalar/Fmt.lean", line: 108 *)
    mk_fun "core::fmt::num::{core::fmt::Debug<isize>}::fmt"
      "core.fmt.num.DebugIsize.fmt";
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
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 42 *)
    mk_fun "core::fmt::rt::{core::fmt::rt::Argument<'0>}::new_debug"
      "core.fmt.rt.Argument.new_debug";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 137 *)
    mk_fun "core::fmt::rt::{core::fmt::rt::Argument<'0>}::new_display"
      "core.fmt.rt.Argument.new_display";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 33 *)
    mk_fun "core::fmt::{core::fmt::Arguments<'a>}::from_str"
      "core.fmt.Arguments.from_str";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 36 *)
    mk_fun "core::fmt::{core::fmt::Arguments<'a>}::new" "core.fmt.Arguments.new";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 69 *)
    mk_fun "core::fmt::{core::fmt::Debug<&'0 @T>}::fmt"
      "core.fmt.DebugShared.fmt";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 81 *)
    mk_fun "core::fmt::{core::fmt::Debug<()>}::fmt" "core.fmt.DebugUnit.fmt";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 75 *)
    mk_fun "core::fmt::{core::fmt::Debug<bool>}::fmt" "core.fmt.DebugBool.fmt";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 96 *)
    mk_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field1_finish"
      "core.fmt.Formatter.debug_struct_field1_finish";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 103 *)
    mk_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field4_finish"
      "core.fmt.Formatter.debug_struct_field4_finish";
    (* file: "Aeneas/Std/Core/FmtWithSlice.lean", line: 7 *)
    mk_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_fields_finish"
      "core.fmt.Formatter.debug_struct_fields_finish";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 113 *)
    mk_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_tuple_field1_finish"
      "core.fmt.Formatter.debug_tuple_field1_finish";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 62 *)
    mk_fun "core::fmt::{core::fmt::Formatter<'a>}::write_fmt"
      "core.fmt.Formatter.write_fmt";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 56 *)
    mk_fun "core::fmt::{core::fmt::Formatter<'a>}::write_str"
      "core.fmt.Formatter.write_str";
    (* file: "Aeneas/Std/Core/Discriminant.lean", line: 26 *)
    mk_fun "core::intrinsics::discriminant_value"
      "core.intrinsics.discriminant_value";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 83 *)
    mk_fun
      "core::iter::adapters::step_by::{core::iter::traits::iterator::Iterator<core::iter::adapters::step_by::StepBy<@I>, \
       @Clause0_Item>}::enumerate"
      "core.iter.adapters.step_by.IteratorStepBy.enumerate";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 65 *)
    mk_fun
      "core::iter::adapters::step_by::{core::iter::traits::iterator::Iterator<core::iter::adapters::step_by::StepBy<@I>, \
       @Clause0_Item>}::next"
      "core.iter.adapters.step_by.IteratorStepBy.next";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 74 *)
    mk_fun
      "core::iter::adapters::step_by::{core::iter::traits::iterator::Iterator<core::iter::adapters::step_by::StepBy<@I>, \
       @Clause0_Item>}::step_by"
      "core.iter.adapters.step_by.IteratorStepBy.step_by";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 92 *)
    mk_fun
      "core::iter::adapters::step_by::{core::iter::traits::iterator::Iterator<core::iter::adapters::step_by::StepBy<@I>, \
       @Clause0_Item>}::take"
      "core.iter.adapters.step_by.IteratorStepBy.take";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 187 *)
    mk_fun
      "core::iter::range::{core::iter::range::Step<usize>}::backward_checked"
      "core.iter.range.StepUsize.backward_checked";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 181 *)
    mk_fun
      "core::iter::range::{core::iter::range::Step<usize>}::forward_checked"
      "core.iter.range.StepUsize.forward_checked";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 172 *)
    mk_fun "core::iter::range::{core::iter::range::Step<usize>}::steps_between"
      "core.iter.range.StepUsize.steps_between";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 224 *)
    mk_fun
      "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, \
       @A>}::enumerate"
      "core.iter.range.IteratorRange.enumerate";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 202 *)
    mk_fun
      "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, \
       @A>}::next"
      "core.iter.range.IteratorRange.next";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 217 *)
    mk_fun
      "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, \
       @A>}::step_by"
      "core.iter.range.IteratorRange.step_by";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 231 *)
    mk_fun
      "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, \
       @A>}::take"
      "core.iter.range.IteratorRange.take";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 140 *)
    mk_fun
      "core::iter::traits::collect::{core::iter::traits::collect::IntoIterator<@I, \
       @Item, @I>}::into_iter"
      "core.iter.traits.collect.IntoIterator.Blanket.into_iter";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 133 *)
    mk_fun "core::iter::traits::iterator::Iterator::collect"
      "core.iter.traits.iterator.Iterator.collect.default";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 60 *)
    mk_fun "core::iter::traits::iterator::Iterator::step_by"
      "core.iter.traits.iterator.Iterator.step_by.default";
    (* file: "Aeneas/Std/Core/Core.lean", line: 73 *)
    mk_fun "core::mem::replace" "core.mem.replace" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Core/Core.lean", line: 77 *)
    mk_fun "core::mem::swap" "core.mem.swap" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Scalar/Pow.lean", line: 7 *)
    mk_fun "core::num::{usize}::is_power_of_two"
      "core.num.Usize.is_power_of_two";
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
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 87 *)
    mk_fun "core::result::{core::result::Result<@T, @E>}::expect"
      "core.result.Result.expect";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 19 *)
    mk_fun "core::result::{core::result::Result<@T, @E>}::unwrap"
      "core.result.Result.unwrap";
    (* file: "Aeneas/Std/Slice.lean", line: 230 *)
    mk_fun "core::slice::index::{core::ops::index::Index<[@T], @I, @O>}::index"
      "core.slice.index.Slice.index";
    (* file: "Aeneas/Std/Slice.lean", line: 307 *)
    mk_fun
      "core::slice::index::{core::ops::index::IndexMut<[@T], @I, \
       @O>}::index_mut"
      "core.slice.index.Slice.index_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 256 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::get"
      "core.slice.index.SliceIndexRangeUsizeSlice.get";
    (* file: "Aeneas/Std/Slice.lean", line: 263 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::get_mut"
      "core.slice.index.SliceIndexRangeUsizeSlice.get_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 277 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::get_unchecked"
      "core.slice.index.SliceIndexRangeUsizeSlice.get_unchecked";
    (* file: "Aeneas/Std/Slice.lean", line: 283 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::get_unchecked_mut"
      "core.slice.index.SliceIndexRangeUsizeSlice.get_unchecked_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 289 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::index"
      "core.slice.index.SliceIndexRangeUsizeSlice.index";
    (* file: "Aeneas/Std/Slice.lean", line: 295 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::index_mut"
      "core.slice.index.SliceIndexRangeUsizeSlice.index_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 476 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::get"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.get";
    (* file: "Aeneas/Std/Slice.lean", line: 482 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::get_mut"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.get_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 496 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::get_unchecked"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.get_unchecked";
    (* file: "Aeneas/Std/Slice.lean", line: 502 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::get_unchecked_mut"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.get_unchecked_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 508 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::index"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.index";
    (* file: "Aeneas/Std/Slice.lean", line: 515 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::index_mut"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 334 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, \
       [@T], [@T]>}::get"
      "core.slice.index.SliceIndexRangeToUsizeSlice.get";
    (* file: "Aeneas/Std/Slice.lean", line: 341 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, \
       [@T], [@T]>}::get_mut"
      "core.slice.index.SliceIndexRangeToUsizeSlice.get_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 356 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, \
       [@T], [@T]>}::get_unchecked"
      "core.slice.index.SliceIndexRangeToUsizeSlice.get_unchecked";
    (* file: "Aeneas/Std/Slice.lean", line: 362 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, \
       [@T], [@T]>}::get_unchecked_mut"
      "core.slice.index.SliceIndexRangeToUsizeSlice.get_unchecked_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 369 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, \
       [@T], [@T]>}::index"
      "core.slice.index.SliceIndexRangeToUsizeSlice.index";
    (* file: "Aeneas/Std/Slice.lean", line: 376 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, \
       [@T], [@T]>}::index_mut"
      "core.slice.index.SliceIndexRangeToUsizeSlice.index_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 416 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
       @T>}::get"
      "core.slice.index.Usize.get";
    (* file: "Aeneas/Std/Slice.lean", line: 421 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
       @T>}::get_mut"
      "core.slice.index.Usize.get_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 426 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
       @T>}::get_unchecked"
      "core.slice.index.Usize.get_unchecked";
    (* file: "Aeneas/Std/Slice.lean", line: 432 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
       @T>}::get_unchecked_mut"
      "core.slice.index.Usize.get_unchecked_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 438 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
       @T>}::index"
      "core.slice.index.Usize.index";
    (* file: "Aeneas/Std/Slice.lean", line: 442 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
       @T>}::index_mut"
      "core.slice.index.Usize.index_mut";
    (* file: "Aeneas/Std/SliceIter.lean", line: 116 *)
    mk_fun
      "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, \
       @T>, &'a [@T]>}::enumerate"
      "core.slice.iter.IteratorChunksExact.enumerate";
    (* file: "Aeneas/Std/SliceIter.lean", line: 100 *)
    mk_fun
      "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, \
       @T>, &'a [@T]>}::next"
      "core.slice.iter.IteratorChunksExact.next";
    (* file: "Aeneas/Std/SliceIter.lean", line: 109 *)
    mk_fun
      "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, \
       @T>, &'a [@T]>}::step_by"
      "core.slice.iter.IteratorChunksExact.step_by";
    (* file: "Aeneas/Std/SliceIter.lean", line: 122 *)
    mk_fun
      "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, \
       @T>, &'a [@T]>}::take"
      "core.slice.iter.IteratorChunksExact.take";
    (* file: "Aeneas/Std/SliceIter.lean", line: 74 *)
    mk_fun
      "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, \
       @T>, &'a @T>}::enumerate"
      "core.slice.iter.IteratorSliceIter.enumerate";
    (* file: "Aeneas/Std/SliceIter.lean", line: 58 *)
    mk_fun
      "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, \
       @T>, &'a @T>}::next"
      "core.slice.iter.IteratorSliceIter.next";
    (* file: "Aeneas/Std/SliceIter.lean", line: 68 *)
    mk_fun
      "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, \
       @T>, &'a @T>}::step_by"
      "core.slice.iter.IteratorSliceIter.step_by";
    (* file: "Aeneas/Std/SliceIter.lean", line: 80 *)
    mk_fun
      "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, \
       @T>, &'a @T>}::take"
      "core.slice.iter.IteratorSliceIter.take";
    (* file: "Aeneas/Std/SliceIter.lean", line: 35 *)
    mk_fun
      "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::IterMut<'a, \
       @T>, &'a mut @T>}::next"
      "core.slice.iter.IteratorIterMut.next";
    (* file: "Aeneas/Std/SliceIter.lean", line: 139 *)
    mk_fun "core::slice::{[@T]}::chunks_exact" "core.slice.Slice.chunks_exact";
    (* file: "Aeneas/Std/SliceIter.lean", line: 30 *)
    mk_fun "core::slice::{[@T]}::contains" "core.slice.Slice.contains";
    (* file: "Aeneas/Std/Slice.lean", line: 470 *)
    mk_fun "core::slice::{[@T]}::copy_from_slice"
      "core.slice.Slice.copy_from_slice";
    (* file: "Aeneas/Std/Slice.lean", line: 236 *)
    mk_fun "core::slice::{[@T]}::get" "core.slice.Slice.get";
    (* file: "Aeneas/Std/Slice.lean", line: 250 *)
    mk_fun "core::slice::{[@T]}::get_mut" "core.slice.Slice.get_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 242 *)
    mk_fun "core::slice::{[@T]}::get_unchecked" "core.slice.Slice.get_unchecked";
    (* file: "Aeneas/Std/Slice.lean", line: 110 *)
    mk_fun "core::slice::{[@T]}::is_empty" "core.slice.Slice.is_empty";
    (* file: "Aeneas/Std/SliceIter.lean", line: 26 *)
    mk_fun "core::slice::{[@T]}::iter" "core.slice.Slice.iter";
    (* file: "Aeneas/Std/SliceIter.lean", line: 53 *)
    mk_fun "core::slice::{[@T]}::iter_mut" "core.slice.Slice.iter_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 45 *)
    mk_fun "core::slice::{[@T]}::len" "Slice.len" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Slice.lean", line: 213 *)
    mk_fun "core::slice::{[@T]}::reverse" "core.slice.Slice.reverse"
      ~can_fail:false;
    (* file: "Aeneas/Std/Slice.lean", line: 578 *)
    mk_fun "core::slice::{[@T]}::split_at" "core.slice.Slice.split_at";
    (* file: "Aeneas/Std/Slice.lean", line: 589 *)
    mk_fun "core::slice::{[@T]}::split_at_mut" "core.slice.Slice.split_at_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 607 *)
    mk_fun "core::slice::{[@T]}::swap" "core.slice.Slice.swap";
    (* file: "Aeneas/Std/StringIter.lean", line: 11 *)
    mk_fun
      "core::str::iter::{core::iter::traits::iterator::Iterator<core::str::iter::Chars<'a>, \
       char>}::collect"
      "core.str.iter.IteratorChars.collect";
    (* file: "Aeneas/Std/StringIter.lean", line: 18 *)
    mk_fun "core::str::{str}::chars" "core.str.Str.chars";
    (* file: "Aeneas/Std/Std/Io.lean", line: 5 *)
    mk_fun "std::io::stdio::_print" "std.io.stdio._print";
  ]

let lean_builtin_trait_decls =
  [
    (* file: "Aeneas/Std/Core/Ptr.lean", line: 83 *)
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
    (* file: "Aeneas/Std/Core/Convert.lean", line: 66 *)
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
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 14 *)
    mk_trait_decl "core::fmt::Debug" "core.fmt.Debug"
      ~methods:[ ("fmt", "fmt") ];
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 48 *)
    mk_trait_decl "core::fmt::Display" "core.fmt.Display"
      ~methods:[ ("fmt", "fmt") ];
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 52 *)
    mk_trait_decl "core::fmt::LowerHex" "core.fmt.LowerHex"
      ~methods:[ ("fmt", "fmt") ];
    (* file: "Aeneas/Std/Core/Hash.lean", line: 11 *)
    mk_trait_decl "core::hash::Hash" "core.hash.Hash"
      ~methods:[ ("hash", "hash") ];
    (* file: "Aeneas/Std/Core/Hash.lean", line: 6 *)
    mk_trait_decl "core::hash::Hasher" "core.hash.Hasher"
      ~methods:[ ("finish", "finish"); ("write", "write") ];
    (* file: "Aeneas/Std/Core/Iter.lean", line: 24 *)
    mk_trait_decl "core::iter::adapters::zip::TrustedRandomAccessNoCoerce"
      "core.iter.adapters.zip.TrustedRandomAccessNoCoerce"
      ~consts:[ ("MAY_HAVE_SIDE_EFFECT", "MAY_HAVE_SIDE_EFFECT") ];
    (* file: "Aeneas/Std/Core/Iter.lean", line: 13 *)
    mk_trait_decl "core::iter::range::Step" "core.iter.range.Step"
      ~parent_clauses:[ "cloneInst"; "partialOrdInst" ]
      ~methods:
        [
          ("steps_between", "steps_between");
          ("forward_checked", "forward_checked");
          ("backward_checked", "backward_checked");
        ];
    (* file: "Aeneas/Std/Core/Iter.lean", line: 116 *)
    mk_trait_decl "core::iter::traits::accum::Product"
      "core.iter.traits.accum.Product"
      ~methods:[ ("product", "product") ];
    (* file: "Aeneas/Std/Core/Iter.lean", line: 112 *)
    mk_trait_decl "core::iter::traits::accum::Sum" "core.iter.traits.accum.Sum"
      ~methods:[ ("sum", "sum") ];
    (* file: "Aeneas/Std/Core/Iter.lean", line: 156 *)
    mk_trait_decl "core::iter::traits::collect::Extend"
      "core.iter.traits.collect.Extend"
      ~methods:[ ("extend", "extend") ];
    (* file: "Aeneas/Std/Core/Iter.lean", line: 127 *)
    mk_trait_decl "core::iter::traits::collect::FromIterator"
      "core.iter.traits.collect.FromIterator"
      ~methods:[ ("from_iter", "from_iter") ];
    (* file: "Aeneas/Std/Core/Iter.lean", line: 120 *)
    mk_trait_decl "core::iter::traits::collect::IntoIterator"
      "core.iter.traits.collect.IntoIterator" ~parent_clauses:[ "iteratorInst" ]
      ~methods:[ ("into_iter", "into_iter") ];
    (* file: "Aeneas/Std/Core/Iter.lean", line: 161 *)
    mk_trait_decl "core::iter::traits::double_ended::DoubleEndedIterator"
      "core.iter.traits.double_ended.DoubleEndedIterator"
      ~parent_clauses:[ "iteratorInst" ]
      ~methods:[ ("next_back", "next_back") ];
    (* file: "Aeneas/Std/Core/Iter.lean", line: 167 *)
    mk_trait_decl "core::iter::traits::exact_size::ExactSizeIterator"
      "core.iter.traits.exact_size.ExactSizeIterator"
      ~parent_clauses:[ "iteratorInst" ];
    (* file: "Aeneas/Std/Core/Iter.lean", line: 50 *)
    mk_trait_decl "core::iter::traits::iterator::Iterator"
      "core.iter.traits.iterator.Iterator"
      ~methods:
        [
          ("next", "next");
          ("step_by", "step_by");
          ("enumerate", "enumerate");
          ("take", "take");
        ];
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
    (* file: "Aeneas/Std/Core/Ops.lean", line: 79 *)
    mk_trait_decl "core::ops::try_trait::FromResidual"
      "core.ops.try_trait.FromResidual"
      ~methods:[ ("from_residual", "from_residual") ];
    (* file: "Aeneas/Std/Core/Ops.lean", line: 94 *)
    mk_trait_decl "core::ops::try_trait::Residual" "core.ops.try_trait.Residual"
      ~parent_clauses:[ "TryInst" ];
    (* file: "Aeneas/Std/Core/Ops.lean", line: 88 *)
    mk_trait_decl "core::ops::try_trait::Try" "core.ops.try_trait.Try"
      ~parent_clauses:[ "FromResidualInst" ]
      ~methods:[ ("from_output", "from_output"); ("branch", "branch") ];
    (* file: "Aeneas/Std/Slice.lean", line: 220 *)
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
    (* file: "Aeneas/Std/Slice.lean", line: 217 *)
    mk_trait_decl "core::slice::index::private_slice_index::Sealed"
      "core.slice.index.private_slice_index.Sealed";
  ]

let lean_builtin_trait_impls =
  [
    (* file: "Aeneas/Std/Core/Core.lean", line: 53 *)
    mk_trait_impl "core::clone::Clone<Box<@T>>" "core.core.clone.CloneBox"
      ~keep_params:(Some [ true; false ])
      ~keep_trait_clauses:(Some [ true; false ]);
    (* file: "Aeneas/Std/Array/Array.lean", line: 218 *)
    mk_trait_impl "core::clone::Clone<[@T; @N]>" "core.clone.CloneArray";
    (* file: "Aeneas/Std/Core/Core.lean", line: 33 *)
    mk_trait_impl "core::clone::Clone<alloc::alloc::Global>"
      "core.core.clone.CloneGlobal";
    (* file: "Aeneas/Std/Vec.lean", line: 374 *)
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
    (* file: "Aeneas/Std/Vec.lean", line: 402 *)
    mk_trait_impl
      "core::cmp::PartialEq<alloc::vec::Vec<@T>, alloc::vec::Vec<@U>>"
      "core.cmp.PartialEqVec"
      ~keep_params:(Some [ true; true; false; false ]);
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 139 *)
    mk_trait_impl "core::cmp::PartialEq<bool, bool>" "core.cmp.PartialEqBool";
    (* file: "Aeneas/Std/Core/Convert.lean", line: 70 *)
    mk_trait_impl "core::convert::AsMut<Box<@T>, @T>" "core.convert.AsMutBox";
    (* file: "Aeneas/Std/Core/Convert.lean", line: 29 *)
    mk_trait_impl "core::convert::From<@Self, @Self>" "core.convert.FromSame";
    (* file: "Aeneas/Std/Vec.lean", line: 339 *)
    mk_trait_impl "core::convert::From<Box<[@T]>, alloc::vec::Vec<@T>>"
      "core.convert.FromBoxSliceVec"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 323 *)
    mk_trait_impl "core::convert::From<alloc::vec::Vec<@T>, [@T; @N]>"
      "core.convert.FromVecArray";
    (* file: "Aeneas/Std/Core/Convert.lean", line: 20 *)
    mk_trait_impl "core::convert::Into<@Self, @T>" "core.convert.IntoFrom";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 176 *)
    mk_trait_impl
      "core::convert::TryFrom<&'a [@T; @N], &'a [@T], \
       core::array::TryFromSliceError>"
      "core.convert.TryFromSharedArraySliceTryFromSliceError";
    (* file: "Aeneas/Std/Core/Convert.lean", line: 59 *)
    mk_trait_impl "core::convert::TryInto<@T, @U, @E>"
      "core.convert.TryInto.Blanket";
    (* file: "Aeneas/Std/Core/Convert.lean", line: 53 *)
    mk_trait_impl "core::convert::{core::convert::TryInto<@T, @U>}"
      "core.convert.TryIntoFrom";
    (* file: "Aeneas/Std/Array/Array.lean", line: 270 *)
    mk_trait_impl "core::default::Default<[@T; 0]>"
      "core.default.DefaultArrayEmpty";
    (* file: "Aeneas/Std/Array/Array.lean", line: 259 *)
    mk_trait_impl "core::default::Default<[@T; @N]>" "core.default.DefaultArray";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 121 *)
    mk_trait_impl "core::fmt::Debug<&'0 @T>" "core.fmt.DebugShared";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 127 *)
    mk_trait_impl "core::fmt::Debug<()>" "core.fmt.DebugUnit";
    (* file: "Aeneas/Std/Vec.lean", line: 423 *)
    mk_trait_impl "core::fmt::Debug<alloc::vec::Vec<@T>>" "core.fmt.DebugVec"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 132 *)
    mk_trait_impl "core::fmt::Debug<bool>" "core.fmt.DebugBool";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 150 *)
    mk_trait_impl "core::fmt::Debug<core::array::TryFromSliceError>"
      "core.fmt.DebugTryFromSliceError";
    (* file: "Aeneas/Std/Scalar/Fmt.lean", line: 134 *)
    mk_trait_impl "core::fmt::Debug<i128>" "core.fmt.DebugI128";
    (* file: "Aeneas/Std/Scalar/Fmt.lean", line: 119 *)
    mk_trait_impl "core::fmt::Debug<i16>" "core.fmt.DebugI16";
    (* file: "Aeneas/Std/Scalar/Fmt.lean", line: 124 *)
    mk_trait_impl "core::fmt::Debug<i32>" "core.fmt.DebugI32";
    (* file: "Aeneas/Std/Scalar/Fmt.lean", line: 129 *)
    mk_trait_impl "core::fmt::Debug<i64>" "core.fmt.DebugI64";
    (* file: "Aeneas/Std/Scalar/Fmt.lean", line: 114 *)
    mk_trait_impl "core::fmt::Debug<i8>" "core.fmt.DebugI8";
    (* file: "Aeneas/Std/Scalar/Fmt.lean", line: 139 *)
    mk_trait_impl "core::fmt::Debug<isize>" "core.fmt.DebugIsize";
    (* file: "Aeneas/Std/Scalar/Fmt.lean", line: 68 *)
    mk_trait_impl "core::fmt::Debug<u128>" "core.fmt.DebugU128";
    (* file: "Aeneas/Std/Scalar/Fmt.lean", line: 53 *)
    mk_trait_impl "core::fmt::Debug<u16>" "core.fmt.DebugU16";
    (* file: "Aeneas/Std/Scalar/Fmt.lean", line: 58 *)
    mk_trait_impl "core::fmt::Debug<u32>" "core.fmt.DebugU32";
    (* file: "Aeneas/Std/Scalar/Fmt.lean", line: 63 *)
    mk_trait_impl "core::fmt::Debug<u64>" "core.fmt.DebugU64";
    (* file: "Aeneas/Std/Scalar/Fmt.lean", line: 48 *)
    mk_trait_impl "core::fmt::Debug<u8>" "core.fmt.DebugU8";
    (* file: "Aeneas/Std/Scalar/Fmt.lean", line: 73 *)
    mk_trait_impl "core::fmt::Debug<usize>" "core.fmt.DebugUsize";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 193 *)
    mk_trait_impl "core::iter::range::Step<usize>" "core.iter.range.StepUsize";
    (* file: "Aeneas/Std/VecIter.lean", line: 74 *)
    mk_trait_impl
      "core::iter::traits::collect::FromIterator<alloc::vec::Vec<@T>, @T>"
      "core.iter.traits.collect.FromIteratorVec";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 147 *)
    mk_trait_impl "core::iter::traits::collect::IntoIterator<@I, @Item, @I>"
      "core.iter.traits.collect.IntoIterator.Blanket";
    (* file: "Aeneas/Std/VecIter.lean", line: 57 *)
    mk_trait_impl
      "core::iter::traits::collect::IntoIterator<alloc::vec::Vec<@T>, @T, \
       alloc::vec::into_iter::IntoIter<@T, @A>>"
      "core.iter.traits.collect.IntoIteratorVec"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/VecIter.lean", line: 41 *)
    mk_trait_impl
      "core::iter::traits::iterator::Iterator<alloc::vec::into_iter::IntoIter<@T, \
       @A>, @T>"
      "core.iter.traits.iterator.IteratorVecIntoIter"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Core/Iter.lean", line: 101 *)
    mk_trait_impl
      "core::iter::traits::iterator::Iterator<core::iter::adapters::step_by::StepBy<@I>, \
       @Clause0_Item>"
      "core.iter.traits.iterator.IteratorStepBy";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 238 *)
    mk_trait_impl
      "core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, @A>"
      "core.iter.traits.iterator.IteratorRange";
    (* file: "Aeneas/Std/SliceIter.lean", line: 128 *)
    mk_trait_impl
      "core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, \
       @T>, &'a [@T]>"
      "core.iter.traits.iterator.IteratorChunksExact";
    (* file: "Aeneas/Std/SliceIter.lean", line: 86 *)
    mk_trait_impl
      "core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, \
       &'a @T>"
      "core.iter.traits.iterator.IteratorSliceIter";
    (* file: "Aeneas/Std/Core/Core.lean", line: 63 *)
    mk_trait_impl "core::marker::Copy<bool>" "core.core.marker.CopyBool";
    (* file: "Aeneas/Std/Core/Ops.lean", line: 29 *)
    mk_trait_impl "core::ops::deref::Deref<Box<@T>, @T>"
      "core.ops.deref.DerefBoxInst"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 273 *)
    mk_trait_impl "core::ops::deref::Deref<alloc::vec::Vec<@T>, [@T]>"
      "core.ops.deref.DerefVec"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Core/Ops.lean", line: 36 *)
    mk_trait_impl "core::ops::deref::DerefMut<Box<@T>, @T>"
      "core.ops.deref.DerefMutBoxInst"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 284 *)
    mk_trait_impl "core::ops::deref::DerefMut<alloc::vec::Vec<@T>, [@T]>"
      "core.ops.deref.DerefMutVec"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 100 *)
    mk_trait_impl "core::ops::index::Index<[@T; @N], @I, @O>"
      "core.ops.index.IndexArray";
    (* file: "Aeneas/Std/Slice.lean", line: 401 *)
    mk_trait_impl "core::ops::index::Index<[@T], @I, @O>"
      "core.ops.index.IndexSlice";
    (* file: "Aeneas/Std/Vec.lean", line: 189 *)
    mk_trait_impl "core::ops::index::Index<alloc::vec::Vec<@T>, @T, @O>"
      "alloc.vec.Vec.Index"
      ~keep_params:(Some [ true; true; false; true ]);
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 107 *)
    mk_trait_impl "core::ops::index::IndexMut<[@T; @N], @I, @O>"
      "core.ops.index.IndexMutArray";
    (* file: "Aeneas/Std/Slice.lean", line: 408 *)
    mk_trait_impl "core::ops::index::IndexMut<[@T], @I, @O>"
      "core.ops.index.IndexMutSlice";
    (* file: "Aeneas/Std/Vec.lean", line: 197 *)
    mk_trait_impl "core::ops::index::IndexMut<alloc::vec::Vec<@T>, @T, @O>"
      "alloc.vec.Vec.IndexMut"
      ~keep_params:(Some [ true; true; false; true ]);
    (* file: "Aeneas/Std/Slice.lean", line: 317 *)
    mk_trait_impl
      "core::slice::index::SliceIndex<core::ops::range::Range<usize>, [@T], \
       [@T]>"
      "core.slice.index.SliceIndexRangeUsizeSlice";
    (* file: "Aeneas/Std/Slice.lean", line: 540 *)
    mk_trait_impl
      "core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>"
      "core.slice.index.SliceIndexRangeFromUsizeSlice";
    (* file: "Aeneas/Std/Slice.lean", line: 388 *)
    mk_trait_impl
      "core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, [@T], \
       [@T]>"
      "core.slice.index.SliceIndexRangeToUsizeSlice";
    (* file: "Aeneas/Std/Slice.lean", line: 451 *)
    mk_trait_impl "core::slice::index::SliceIndex<usize, [@T], @T>"
      "core.slice.index.SliceIndexUsizeSlice";
    (* file: "Aeneas/Std/Slice.lean", line: 313 *)
    mk_trait_impl
      "core::slice::index::private_slice_index::Sealed<core::ops::range::Range<usize>>"
      "core.slice.index.private_slice_index.SealedRangeUsize";
    (* file: "Aeneas/Std/Slice.lean", line: 535 *)
    mk_trait_impl
      "core::slice::index::private_slice_index::Sealed<core::ops::range::RangeFrom<usize>>"
      "core.slice.index.private_slice_index.SealedRangeFromUsize";
    (* file: "Aeneas/Std/Slice.lean", line: 329 *)
    mk_trait_impl
      "core::slice::index::private_slice_index::Sealed<core::ops::range::RangeTo<usize>>"
      "core.slice.index.private_slice_index.SealedRangeToUsize";
    (* file: "Aeneas/Std/Slice.lean", line: 447 *)
    mk_trait_impl "core::slice::index::private_slice_index::Sealed<usize>"
      "core.slice.index.private_slice_index.SealedUsize";
  ]
