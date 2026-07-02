(** THIS FILE WAS AUTOMATICALLY GENERATED FROM LEAN: DO NOT MODIFY DIRECTLY *)
open ExtractBuiltinCore

let lean_builtin_types =
  [
    (* file: "Aeneas/Std/Alloc.lean", line: 16 *)
    mk_type "alloc::alloc::Global" "Global" ~kind:(KEnum [ ("Mk", Some "mk") ]);
    (* file: "Aeneas/Std/Alloc.lean", line: 11 *)
    mk_type "alloc::string::String" "String";
    (* file: "Aeneas/Std/Vec.lean", line: 21 *)
    mk_type "alloc::vec::Vec" "alloc.vec.Vec";
    (* file: "Aeneas/Std/VecIter.lean", line: 8 *)
    mk_type "alloc::vec::into_iter::IntoIter" "alloc.vec.into_iter.IntoIter"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Core/Ptr.lean", line: 78 *)
    mk_type "core::alloc::layout::Layout" "core.alloc.layout.Layout"
      ~kind:(KStruct [ ("size", Some "size"); ("align", Some "align") ]);
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 123 *)
    mk_type "core::array::TryFromSliceError" "core.array.TryFromSliceError";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 31 *)
    mk_type "core::cmp::Ordering" "Ordering"
      ~kind:
        (KEnum
           [ ("Less", Some "lt"); ("Equal", Some "eq"); ("Greater", Some "gt") ]);
    (* file: "Aeneas/Std/Core/Convert.lean", line: 10 *)
    mk_type "core::convert::Infallible" "core.convert.Infallible"
      ~kind:(KEnum []);
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 47 *)
    mk_type "core::fmt::Arguments" "core.fmt.Arguments";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 8 *)
    mk_type "core::fmt::Error" "core.fmt.Error";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 12 *)
    mk_type "core::fmt::Formatter" "core.fmt.Formatter";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 50 *)
    mk_type "core::fmt::rt::Argument" "core.fmt.rt.Argument";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 36 *)
    mk_type "core::iter::adapters::enumerate::Enumerate"
      "core.iter.adapters.enumerate.Enumerate"
      ~kind:(KStruct [ ("iter", Some "iter"); ("count", Some "count") ]);
    (* file: "Aeneas/Std/Core/Iter.lean", line: 826 *)
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
    (* file: "Aeneas/Std/Core/Iter.lean", line: 54 *)
    mk_type "core::iter::adapters::zip::Zip" "core.iter.adapters.zip.Zip"
      ~kind:(KStruct [ ("fst", Some "fst"); ("snd", Some "snd") ]);
    (* file: "Aeneas/Std/Scalar/CoreConvertNum.lean", line: 803 *)
    mk_type "core::num::error::TryFromIntError" "core.num.error.TryFromIntError";
    (* file: "Aeneas/Std/Core/Ops.lean", line: 92 *)
    mk_type "core::ops::control_flow::ControlFlow"
      "core.ops.control_flow.ControlFlow"
      ~kind:(KEnum [ ("Continue", Some "Continue"); ("Break", Some "Break") ]);
    (* file: "Aeneas/Std/Range.lean", line: 14 *)
    mk_type "core::ops::range::Range" "core.ops.range.Range"
      ~kind:(KStruct [ ("start", Some "start"); ("end", Some "«end»") ]);
    (* file: "Aeneas/Std/Core/Core.lean", line: 122 *)
    mk_type "core::ops::range::RangeFrom" "core.ops.range.RangeFrom"
      ~kind:(KStruct [ ("start", Some "start") ]);
    (* file: "Aeneas/Std/Range.lean", line: 30 *)
    mk_type "core::ops::range::RangeInclusive" "core.ops.range.RangeInclusive"
      ~kind:
        (KStruct
           [
             ("start", Some "start");
             ("end", Some "«end»");
             ("exhausted", Some "exhausted");
           ]);
    (* file: "Aeneas/Std/Range.lean", line: 20 *)
    mk_type "core::ops::range::RangeTo" "core.ops.range.RangeTo"
      ~kind:(KStruct [ ("end", Some "«end»") ]);
    (* file: "Aeneas/Std/Core/Core.lean", line: 12 *)
    mk_type "core::option::Option" "Option" ~prefix_variant_names:false
      ~kind:(KEnum [ ("None", Some "none"); ("Some", Some "some") ]);
    (* file: "Aeneas/Std/Core/Panic.lean", line: 6 *)
    mk_type "core::panic::panic_info::PanicInfo"
      "core.panic.panic_info.PanicInfo";
    (* file: "Aeneas/Std/Core/Core.lean", line: 126 *)
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
    (* file: "Aeneas/Std/SliceIter.lean", line: 141 *)
    mk_type "core::slice::iter::ChunksExact" "core.slice.iter.ChunksExact";
    (* file: "Aeneas/Std/SliceIter.lean", line: 13 *)
    mk_type "core::slice::iter::Iter" "core.slice.iter.Iter"
      ~kind:(KStruct [ ("slice", Some "slice"); ("i", Some "i") ]);
    (* file: "Aeneas/Std/SliceIter.lean", line: 20 *)
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
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 198 *)
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
    (* file: "Aeneas/Std/Vec.lean", line: 328 *)
    mk_fun "alloc::slice::{[@T]}::into_vec" "alloc.slice.Slice.into_vec"
      ~keep_params:(Some [ true; false ])
      ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Vec.lean", line: 316 *)
    mk_fun "alloc::slice::{[@T]}::to_vec" "alloc.slice.Slice.to_vec";
    (* file: "Aeneas/Std/Vec.lean", line: 332 *)
    mk_fun "alloc::vec::from_elem" "alloc.vec.from_elem";
    (* file: "Aeneas/Std/VecIter.lean", line: 28 *)
    mk_fun
      "alloc::vec::into_iter::{core::iter::traits::iterator::Iterator<alloc::vec::into_iter::IntoIter<@T, \
       @A>, @T>}::enumerate"
      "alloc.vec.into_iter.IteratorIntoIter.enumerate"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/VecIter.lean", line: 100 *)
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
    (* file: "Aeneas/Std/VecIter.lean", line: 35 *)
    mk_fun
      "alloc::vec::into_iter::{core::iter::traits::iterator::Iterator<alloc::vec::into_iter::IntoIter<@T, \
       @A>, @T>}::take"
      "alloc.vec.into_iter.IteratorIntoIter.take"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 550 *)
    mk_fun
      "alloc::vec::partial_eq::{core::cmp::PartialEq<alloc::vec::Vec<@T>, \
       alloc::vec::Vec<@U>>}::eq"
      "alloc.vec.partial_eq.PartialEqVec.eq"
      ~keep_params:(Some [ true; true; false; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 560 *)
    mk_fun
      "alloc::vec::partial_eq::{core::cmp::PartialEq<alloc::vec::Vec<@T>, \
       alloc::vec::Vec<@U>>}::ne"
      "alloc.vec.partial_eq.PartialEqVec.ne"
      ~keep_params:(Some [ true; true; false; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 352 *)
    mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::extend_from_slice"
      "alloc.vec.Vec.extend_from_slice"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 135 *)
    mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::insert" "alloc.vec.Vec.insert"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 53 *)
    mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::len" "alloc.vec.Vec.len"
      ~keep_params:(Some [ true; false ])
      ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Vec.lean", line: 46 *)
    mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::new" "alloc.vec.Vec.new"
      ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Vec.lean", line: 120 *)
    mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::push" "alloc.vec.Vec.push"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 386 *)
    mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::resize" "alloc.vec.Vec.resize"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 349 *)
    mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::with_capacity"
      "alloc.vec.Vec.with_capacity" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Vec.lean", line: 537 *)
    mk_fun "alloc::vec::{core::clone::Clone<alloc::vec::Vec<@T>>}::clone"
      "alloc.vec.CloneVec.clone"
      ~keep_params:(Some [ true; false ])
      ~keep_trait_clauses:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 459 *)
    mk_fun
      "alloc::vec::{core::convert::From<Box<[@T]>, alloc::vec::Vec<@T>>}::from"
      "alloc.vec.FromBoxSliceVec.from"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 445 *)
    mk_fun
      "alloc::vec::{core::convert::From<alloc::vec::Vec<@T>, [@T; @N]>}::from"
      "alloc.vec.FromVecArray.from";
    (* file: "Aeneas/Std/Vec.lean", line: 581 *)
    mk_fun "alloc::vec::{core::fmt::Debug<alloc::vec::Vec<@T>>}::fmt"
      "alloc.vec.DebugVec.fmt"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/VecIter.lean", line: 79 *)
    mk_fun
      "alloc::vec::{core::iter::traits::collect::FromIterator<alloc::vec::Vec<@T>, \
       @T>}::from_iter"
      "alloc.vec.FromIteratorVec.from_iter";
    (* file: "Aeneas/Std/VecIter.lean", line: 53 *)
    mk_fun
      "alloc::vec::{core::iter::traits::collect::IntoIterator<alloc::vec::Vec<@T>, \
       @T, alloc::vec::into_iter::IntoIter<@T, @A>>}::into_iter"
      "alloc.vec.IntoIteratorVec.into_iter"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 363 *)
    mk_fun
      "alloc::vec::{core::ops::deref::Deref<alloc::vec::Vec<@T>, [@T]>}::deref"
      "alloc.vec.Vec.deref"
      ~keep_params:(Some [ true; false ])
      ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Vec.lean", line: 373 *)
    mk_fun
      "alloc::vec::{core::ops::deref::DerefMut<alloc::vec::Vec<@T>, \
       [@T]>}::deref_mut"
      "alloc.vec.Vec.deref_mut"
      ~keep_params:(Some [ true; false ])
      ~can_fail:false;
    (* file: "Aeneas/Std/Vec.lean", line: 195 *)
    mk_fun
      "alloc::vec::{core::ops::index::Index<alloc::vec::Vec<@T>, @I, \
       @O>}::index"
      "alloc.vec.Vec.index"
      ~keep_params:(Some [ true; true; false; true ]);
    (* file: "Aeneas/Std/Vec.lean", line: 201 *)
    mk_fun
      "alloc::vec::{core::ops::index::IndexMut<alloc::vec::Vec<@T>, @I, \
       @O>}::index_mut"
      "alloc.vec.Vec.index_mut"
      ~keep_params:(Some [ true; true; false; true ]);
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 135 *)
    mk_fun
      "core::array::equality::{core::cmp::PartialEq<[@T; @N], [@U; @N]>}::eq"
      "core.array.equality.PartialEqArray.eq";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 144 *)
    mk_fun
      "core::array::equality::{core::cmp::PartialEq<[@T; @N], [@U; @N]>}::ne"
      "core.array.equality.PartialEqArray.ne";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 365 *)
    mk_fun "core::array::{[@T; @N]}::as_mut_slice"
      "core.array.Array.as_mut_slice";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 344 *)
    mk_fun "core::array::{[@T; @N]}::as_slice" "core.array.Array.as_slice";
    (* file: "Aeneas/Std/Array/Array.lean", line: 295 *)
    mk_fun "core::array::{core::clone::Clone<[@T; @N]>}::clone"
      "core.array.CloneArray.clone";
    (* file: "Aeneas/Std/Array/Array.lean", line: 308 *)
    mk_fun "core::array::{core::clone::Clone<[@T; @N]>}::clone_from"
      "core.array.CloneArray.clone_from";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 356 *)
    mk_fun "core::array::{core::convert::AsMut<[@T; @N], [@T]>}::as_mut"
      "Array.Insts.CoreConvertAsMutSlice.as_mut";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 349 *)
    mk_fun "core::array::{core::convert::AsRef<[@T; @N], [@T]>}::as_ref"
      "Array.Insts.CoreConvertAsRefSlice.as_ref";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 313 *)
    mk_fun
      "core::array::{core::convert::TryFrom<&'a [@T; @N], &'a [@T], \
       core::array::TryFromSliceError>}::try_from"
      "core.array.TryFromSharedArraySlice.try_from";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 328 *)
    mk_fun
      "core::array::{core::convert::TryFrom<&'a mut [@T; @N], &'a mut [@T], \
       core::array::TryFromSliceError>}::try_from"
      "core.array.TryFromMutArraySlice.try_from";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 293 *)
    mk_fun
      "core::array::{core::convert::TryFrom<[@T; @N], &'0 [@T], \
       core::array::TryFromSliceError>}::try_from"
      "core.array.TryFromArrayCopySlice.try_from";
    (* file: "Aeneas/Std/Array/Array.lean", line: 402 *)
    mk_fun "core::array::{core::default::Default<[@T; 0]>}::default"
      "core.default.DefaultArrayEmpty.default";
    (* file: "Aeneas/Std/Array/Array.lean", line: 386 *)
    mk_fun "core::array::{core::default::Default<[@T; @N]>}::default"
      "core.default.DefaultArray.default";
    (* file: "Aeneas/Std/Array/ArrayDebug.lean", line: 9 *)
    mk_fun "core::array::{core::fmt::Debug<[@T; @N]>}::fmt"
      "core.array.DebugArray.fmt";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 279 *)
    mk_fun
      "core::array::{core::fmt::Debug<core::array::TryFromSliceError>}::fmt"
      "core.array.DebugTryFromSliceError.fmt";
    (* file: "Aeneas/Std/SliceIter.lean", line: 105 *)
    mk_fun
      "core::array::{core::iter::traits::collect::IntoIterator<&'a [@T; @N], \
       &'a @T, core::slice::iter::Iter<'a, @T>>}::into_iter"
      "SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 94 *)
    mk_fun "core::array::{core::ops::index::Index<[@T; @N], @I, @O>}::index"
      "core.array.Array.index";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 100 *)
    mk_fun
      "core::array::{core::ops::index::IndexMut<[@T; @N], @I, @O>}::index_mut"
      "core.array.Array.index_mut";
    (* file: "Aeneas/Std/Core/Core.lean", line: 132 *)
    mk_fun "core::clone::impls::{core::clone::Clone<&'0 @T>}::clone"
      "core.clone.impls.CloneShared.clone";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 18 *)
    mk_fun "core::cmp::Eq::assert_fields_are_eq"
      "core.cmp.Eq.assert_fields_are_eq.default";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 138 *)
    mk_fun "core::cmp::Ord::clamp" "core.cmp.Ord.clamp.default";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 126 *)
    mk_fun "core::cmp::Ord::max" "core.cmp.Ord.max.default";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 132 *)
    mk_fun "core::cmp::Ord::min" "core.cmp.Ord.min.default";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 24 *)
    mk_fun "core::cmp::PartialEq::ne" "core.cmp.PartialEq.ne.default";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 91 *)
    mk_fun "core::cmp::PartialOrd::ge" "core.cmp.PartialOrd.ge.default";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 84 *)
    mk_fun "core::cmp::PartialOrd::gt" "core.cmp.PartialOrd.gt.default";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 77 *)
    mk_fun "core::cmp::PartialOrd::le" "core.cmp.PartialOrd.le.default";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 70 *)
    mk_fun "core::cmp::PartialOrd::lt" "core.cmp.PartialOrd.lt.default";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 169 *)
    mk_fun "core::cmp::impls::{core::cmp::Ord<()>}::cmp"
      "core.cmp.impls.OrdUnit.cmp";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 181 *)
    mk_fun "core::cmp::impls::{core::cmp::PartialEq<&'a @A, &'b @B>}::eq"
      "core.cmp.impls.PartialEqShared.eq";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 186 *)
    mk_fun "core::cmp::impls::{core::cmp::PartialEq<&'a @A, &'b @B>}::ne"
      "core.cmp.impls.PartialEqShared.ne";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 153 *)
    mk_fun "core::cmp::impls::{core::cmp::PartialEq<(), ()>}::eq"
      "core.cmp.impls.PartialEqUnit.eq";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 156 *)
    mk_fun "core::cmp::impls::{core::cmp::PartialEq<(), ()>}::ne"
      "core.cmp.impls.PartialEqUnit.ne";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 173 *)
    mk_fun "core::cmp::impls::{core::cmp::PartialEq<bool, bool>}::eq"
      "core.cmp.impls.PartialEqBool.eq";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 165 *)
    mk_fun "core::cmp::impls::{core::cmp::PartialOrd<(), ()>}::partial_cmp"
      "core.cmp.impls.PartialOrdUnit.partial_cmp";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 148 *)
    mk_fun "core::cmp::max" "core.cmp.max";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 143 *)
    mk_fun "core::cmp::min" "core.cmp.min";
    (* file: "Aeneas/Std/Scalar/CoreConvertNum.lean", line: 815 *)
    mk_fun
      "core::convert::num::ptr_try_from_impls::{core::convert::TryFrom<u32, \
       usize, core::num::error::TryFromIntError>}::try_from"
      "core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from";
    (* file: "Aeneas/Std/Core/Convert.lean", line: 32 *)
    mk_fun "core::convert::{core::convert::From<@T, @T>}::from"
      "core.convert.FromSame.from" ~can_fail:false;
    (* file: "Aeneas/Std/Core/Convert.lean", line: 17 *)
    mk_fun "core::convert::{core::convert::Into<@T, @U>}::into"
      "core.convert.IntoFrom.into";
    (* file: "Aeneas/Std/Core/Convert.lean", line: 44 *)
    mk_fun "core::convert::{core::convert::TryInto<@T, @U, @Error>}::try_into"
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
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 62 *)
    mk_fun "core::fmt::rt::{core::fmt::rt::Argument<'0>}::new_debug"
      "core.fmt.rt.Argument.new_debug";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 193 *)
    mk_fun "core::fmt::rt::{core::fmt::rt::Argument<'0>}::new_display"
      "core.fmt.rt.Argument.new_display";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 76 *)
    mk_fun "core::fmt::rt::{core::fmt::rt::Argument<'0>}::new_lower_hex"
      "core.fmt.rt.Argument.new_lower_hex";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 53 *)
    mk_fun "core::fmt::{core::fmt::Arguments<'a>}::from_str"
      "core.fmt.Arguments.from_str";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 56 *)
    mk_fun "core::fmt::{core::fmt::Arguments<'a>}::new" "core.fmt.Arguments.new";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 96 *)
    mk_fun "core::fmt::{core::fmt::Debug<&'0 @T>}::fmt"
      "core.fmt.DebugShared.fmt";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 108 *)
    mk_fun "core::fmt::{core::fmt::Debug<()>}::fmt" "core.fmt.DebugUnit.fmt";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 102 *)
    mk_fun "core::fmt::{core::fmt::Debug<bool>}::fmt" "core.fmt.DebugBool.fmt";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 123 *)
    mk_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field1_finish"
      "core.fmt.Formatter.debug_struct_field1_finish";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 130 *)
    mk_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field2_finish"
      "core.fmt.Formatter.debug_struct_field2_finish";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 138 *)
    mk_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field3_finish"
      "core.fmt.Formatter.debug_struct_field3_finish";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 148 *)
    mk_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field4_finish"
      "core.fmt.Formatter.debug_struct_field4_finish";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 159 *)
    mk_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field5_finish"
      "core.fmt.Formatter.debug_struct_field5_finish";
    (* file: "Aeneas/Std/Core/FmtWithSlice.lean", line: 7 *)
    mk_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_fields_finish"
      "core.fmt.Formatter.debug_struct_fields_finish";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 169 *)
    mk_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_tuple_field1_finish"
      "core.fmt.Formatter.debug_tuple_field1_finish";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 89 *)
    mk_fun "core::fmt::{core::fmt::Formatter<'a>}::write_fmt"
      "core.fmt.Formatter.write_fmt";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 83 *)
    mk_fun "core::fmt::{core::fmt::Formatter<'a>}::write_str"
      "core.fmt.Formatter.write_str";
    (* file: "Aeneas/Std/Core/Discriminant.lean", line: 26 *)
    mk_fun "core::intrinsics::discriminant_value"
      "core.intrinsics.discriminant_value";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 457 *)
    mk_fun
      "core::iter::adapters::enumerate::{core::iter::traits::iterator::Iterator<core::iter::adapters::enumerate::Enumerate<@I>, \
       (usize, @Clause0_Item)>}::enumerate"
      "core.iter.adapters.enumerate.IteratorEnumerate.enumerate";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 433 *)
    mk_fun
      "core::iter::adapters::enumerate::{core::iter::traits::iterator::Iterator<core::iter::adapters::enumerate::Enumerate<@I>, \
       (usize, @Clause0_Item)>}::next"
      "core.iter.adapters.enumerate.IteratorEnumerate.next";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 447 *)
    mk_fun
      "core::iter::adapters::enumerate::{core::iter::traits::iterator::Iterator<core::iter::adapters::enumerate::Enumerate<@I>, \
       (usize, @Clause0_Item)>}::step_by"
      "core.iter.adapters.enumerate.IteratorEnumerate.step_by";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 466 *)
    mk_fun
      "core::iter::adapters::enumerate::{core::iter::traits::iterator::Iterator<core::iter::adapters::enumerate::Enumerate<@I>, \
       (usize, @Clause0_Item)>}::take"
      "core.iter.adapters.enumerate.IteratorEnumerate.take";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 702 *)
    mk_fun
      "core::iter::adapters::rev::{core::iter::traits::iterator::Iterator<core::iter::adapters::rev::Rev<@I>, \
       @Clause0_Clause0_Item>}::next"
      "core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 132 *)
    mk_fun
      "core::iter::adapters::step_by::{core::iter::traits::iterator::Iterator<core::iter::adapters::step_by::StepBy<@I>, \
       @Clause0_Item>}::enumerate"
      "core.iter.adapters.step_by.IteratorStepBy.enumerate";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 106 *)
    mk_fun
      "core::iter::adapters::step_by::{core::iter::traits::iterator::Iterator<core::iter::adapters::step_by::StepBy<@I>, \
       @Clause0_Item>}::next"
      "core.iter.adapters.step_by.IteratorStepBy.next";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 121 *)
    mk_fun
      "core::iter::adapters::step_by::{core::iter::traits::iterator::Iterator<core::iter::adapters::step_by::StepBy<@I>, \
       @Clause0_Item>}::step_by"
      "core.iter.adapters.step_by.IteratorStepBy.step_by";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 141 *)
    mk_fun
      "core::iter::adapters::step_by::{core::iter::traits::iterator::Iterator<core::iter::adapters::step_by::StepBy<@I>, \
       @Clause0_Item>}::take"
      "core.iter.adapters.step_by.IteratorStepBy.take";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 515 *)
    mk_fun
      "core::iter::adapters::take::{core::iter::traits::iterator::Iterator<core::iter::adapters::take::Take<@I>, \
       @Clause0_Item>}::enumerate"
      "core.iter.adapters.take.IteratorTake.enumerate";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 491 *)
    mk_fun
      "core::iter::adapters::take::{core::iter::traits::iterator::Iterator<core::iter::adapters::take::Take<@I>, \
       @Clause0_Item>}::next"
      "core.iter.adapters.take.IteratorTake.next";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 505 *)
    mk_fun
      "core::iter::adapters::take::{core::iter::traits::iterator::Iterator<core::iter::adapters::take::Take<@I>, \
       @Clause0_Item>}::step_by"
      "core.iter.adapters.take.IteratorTake.step_by";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 524 *)
    mk_fun
      "core::iter::adapters::take::{core::iter::traits::iterator::Iterator<core::iter::adapters::take::Take<@I>, \
       @Clause0_Item>}::take"
      "core.iter.adapters.take.IteratorTake.take";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 600 *)
    mk_fun
      "core::iter::adapters::zip::{core::iter::traits::iterator::Iterator<core::iter::adapters::zip::Zip<@A, \
       @B>, (@Clause0_Item, @Clause1_Item)>}::next"
      "core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 423 *)
    mk_fun
      "core::iter::range::{core::iter::range::Step<i128>}::backward_checked"
      "core.iter.range.StepI128.backward_checked";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 421 *)
    mk_fun "core::iter::range::{core::iter::range::Step<i128>}::forward_checked"
      "core.iter.range.StepI128.forward_checked";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 419 *)
    mk_fun "core::iter::range::{core::iter::range::Step<i128>}::steps_between"
      "core.iter.range.StepI128.steps_between";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 396 *)
    mk_fun "core::iter::range::{core::iter::range::Step<i16>}::backward_checked"
      "core.iter.range.StepI16.backward_checked";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 394 *)
    mk_fun "core::iter::range::{core::iter::range::Step<i16>}::forward_checked"
      "core.iter.range.StepI16.forward_checked";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 392 *)
    mk_fun "core::iter::range::{core::iter::range::Step<i16>}::steps_between"
      "core.iter.range.StepI16.steps_between";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 405 *)
    mk_fun "core::iter::range::{core::iter::range::Step<i32>}::backward_checked"
      "core.iter.range.StepI32.backward_checked";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 403 *)
    mk_fun "core::iter::range::{core::iter::range::Step<i32>}::forward_checked"
      "core.iter.range.StepI32.forward_checked";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 401 *)
    mk_fun "core::iter::range::{core::iter::range::Step<i32>}::steps_between"
      "core.iter.range.StepI32.steps_between";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 414 *)
    mk_fun "core::iter::range::{core::iter::range::Step<i64>}::backward_checked"
      "core.iter.range.StepI64.backward_checked";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 412 *)
    mk_fun "core::iter::range::{core::iter::range::Step<i64>}::forward_checked"
      "core.iter.range.StepI64.forward_checked";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 410 *)
    mk_fun "core::iter::range::{core::iter::range::Step<i64>}::steps_between"
      "core.iter.range.StepI64.steps_between";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 387 *)
    mk_fun "core::iter::range::{core::iter::range::Step<i8>}::backward_checked"
      "core.iter.range.StepI8.backward_checked";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 385 *)
    mk_fun "core::iter::range::{core::iter::range::Step<i8>}::forward_checked"
      "core.iter.range.StepI8.forward_checked";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 383 *)
    mk_fun "core::iter::range::{core::iter::range::Step<i8>}::steps_between"
      "core.iter.range.StepI8.steps_between";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 378 *)
    mk_fun
      "core::iter::range::{core::iter::range::Step<isize>}::backward_checked"
      "core.iter.range.StepIsize.backward_checked";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 376 *)
    mk_fun
      "core::iter::range::{core::iter::range::Step<isize>}::forward_checked"
      "core.iter.range.StepIsize.forward_checked";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 374 *)
    mk_fun "core::iter::range::{core::iter::range::Step<isize>}::steps_between"
      "core.iter.range.StepIsize.steps_between";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 369 *)
    mk_fun
      "core::iter::range::{core::iter::range::Step<u128>}::backward_checked"
      "core.iter.range.StepU128.backward_checked";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 367 *)
    mk_fun "core::iter::range::{core::iter::range::Step<u128>}::forward_checked"
      "core.iter.range.StepU128.forward_checked";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 365 *)
    mk_fun "core::iter::range::{core::iter::range::Step<u128>}::steps_between"
      "core.iter.range.StepU128.steps_between";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 342 *)
    mk_fun "core::iter::range::{core::iter::range::Step<u16>}::backward_checked"
      "core.iter.range.StepU16.backward_checked";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 340 *)
    mk_fun "core::iter::range::{core::iter::range::Step<u16>}::forward_checked"
      "core.iter.range.StepU16.forward_checked";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 338 *)
    mk_fun "core::iter::range::{core::iter::range::Step<u16>}::steps_between"
      "core.iter.range.StepU16.steps_between";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 351 *)
    mk_fun "core::iter::range::{core::iter::range::Step<u32>}::backward_checked"
      "core.iter.range.StepU32.backward_checked";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 349 *)
    mk_fun "core::iter::range::{core::iter::range::Step<u32>}::forward_checked"
      "core.iter.range.StepU32.forward_checked";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 347 *)
    mk_fun "core::iter::range::{core::iter::range::Step<u32>}::steps_between"
      "core.iter.range.StepU32.steps_between";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 360 *)
    mk_fun "core::iter::range::{core::iter::range::Step<u64>}::backward_checked"
      "core.iter.range.StepU64.backward_checked";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 358 *)
    mk_fun "core::iter::range::{core::iter::range::Step<u64>}::forward_checked"
      "core.iter.range.StepU64.forward_checked";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 356 *)
    mk_fun "core::iter::range::{core::iter::range::Step<u64>}::steps_between"
      "core.iter.range.StepU64.steps_between";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 333 *)
    mk_fun "core::iter::range::{core::iter::range::Step<u8>}::backward_checked"
      "core.iter.range.StepU8.backward_checked";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 331 *)
    mk_fun "core::iter::range::{core::iter::range::Step<u8>}::forward_checked"
      "core.iter.range.StepU8.forward_checked";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 329 *)
    mk_fun "core::iter::range::{core::iter::range::Step<u8>}::steps_between"
      "core.iter.range.StepU8.steps_between";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 324 *)
    mk_fun
      "core::iter::range::{core::iter::range::Step<usize>}::backward_checked"
      "core.iter.range.StepUsize.backward_checked";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 322 *)
    mk_fun
      "core::iter::range::{core::iter::range::Step<usize>}::forward_checked"
      "core.iter.range.StepUsize.forward_checked";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 320 *)
    mk_fun "core::iter::range::{core::iter::range::Step<usize>}::steps_between"
      "core.iter.range.StepUsize.steps_between";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 736 *)
    mk_fun
      "core::iter::range::{core::iter::traits::double_ended::DoubleEndedIterator<core::ops::range::Range<@A>, \
       @A>}::next_back"
      "core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 808 *)
    mk_fun
      "core::iter::range::{core::iter::traits::double_ended::DoubleEndedIterator<core::ops::range::RangeInclusive<@A>, \
       @A>}::next_back"
      "core.ops.range.RangeInclusive.Insts.CoreIterTraitsDoubleEndedIterator.next_back";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 568 *)
    mk_fun
      "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, \
       @A>}::enumerate"
      "core.iter.range.IteratorRange.enumerate";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 544 *)
    mk_fun
      "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, \
       @A>}::next"
      "core.iter.range.IteratorRange.next";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 714 *)
    mk_fun
      "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, \
       @A>}::rev"
      "core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.rev";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 559 *)
    mk_fun
      "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, \
       @A>}::step_by"
      "core.iter.range.IteratorRange.step_by";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 575 *)
    mk_fun
      "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, \
       @A>}::take"
      "core.iter.range.IteratorRange.take";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 723 *)
    mk_fun
      "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, \
       @A>}::zip"
      "core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.zip";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 771 *)
    mk_fun
      "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::RangeInclusive<@A>, \
       @A>}::enumerate"
      "core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.enumerate";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 647 *)
    mk_fun
      "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::RangeInclusive<@A>, \
       @A>}::next"
      "core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 751 *)
    mk_fun
      "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::RangeInclusive<@A>, \
       @A>}::rev"
      "core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.rev";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 780 *)
    mk_fun
      "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::RangeInclusive<@A>, \
       @A>}::step_by"
      "core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.step_by";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 762 *)
    mk_fun
      "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::RangeInclusive<@A>, \
       @A>}::take"
      "core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.take";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 666 *)
    mk_fun
      "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::RangeInclusive<@A>, \
       @A>}::zip"
      "core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.zip";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 182 *)
    mk_fun
      "core::iter::traits::collect::{core::iter::traits::collect::IntoIterator<@I, \
       @Item, @I>}::into_iter"
      "core.iter.traits.collect.IntoIterator.Blanket.into_iter";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 199 *)
    mk_fun "core::iter::traits::iterator::Iterator::collect"
      "core.iter.traits.iterator.Iterator.collect.default";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 82 *)
    mk_fun "core::iter::traits::iterator::Iterator::enumerate"
      "core.iter.traits.iterator.Iterator.enumerate.default";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 693 *)
    mk_fun "core::iter::traits::iterator::Iterator::rev"
      "core.iter.traits.iterator.Iterator.rev.default";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 75 *)
    mk_fun "core::iter::traits::iterator::Iterator::step_by"
      "core.iter.traits.iterator.Iterator.step_by.default";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 88 *)
    mk_fun "core::iter::traits::iterator::Iterator::take"
      "core.iter.traits.iterator.Iterator.take.default";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 682 *)
    mk_fun "core::iter::traits::iterator::Iterator::zip"
      "core.iter.traits.iterator.Iterator.zip.default";
    (* file: "Aeneas/Std/Core/Core.lean", line: 73 *)
    mk_fun "core::mem::replace" "core.mem.replace" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Core/Core.lean", line: 77 *)
    mk_fun "core::mem::swap" "core.mem.swap" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Scalar/CoreConvertNum.lean", line: 694 *)
    mk_fun "core::num::{i128}::cast_unsigned" "core.num.I128.cast_unsigned";
    (* file: "Aeneas/Std/Scalar/WrappingOps/Shl.lean", line: 44 *)
    mk_fun "core::num::{i128}::wrapping_shl" "core.num.I128.wrapping_shl"
      ~can_fail:false;
    (* file: "Aeneas/Std/Scalar/WrappingOps/Shr.lean", line: 45 *)
    mk_fun "core::num::{i128}::wrapping_shr" "core.num.I128.wrapping_shr"
      ~can_fail:false;
    (* file: "Aeneas/Std/Scalar/CoreConvertNum.lean", line: 676 *)
    mk_fun "core::num::{i16}::cast_unsigned" "core.num.I16.cast_unsigned";
    (* file: "Aeneas/Std/Scalar/WrappingOps/Shl.lean", line: 41 *)
    mk_fun "core::num::{i16}::wrapping_shl" "core.num.I16.wrapping_shl"
      ~can_fail:false;
    (* file: "Aeneas/Std/Scalar/WrappingOps/Shr.lean", line: 42 *)
    mk_fun "core::num::{i16}::wrapping_shr" "core.num.I16.wrapping_shr"
      ~can_fail:false;
    (* file: "Aeneas/Std/Scalar/CoreConvertNum.lean", line: 682 *)
    mk_fun "core::num::{i32}::cast_unsigned" "core.num.I32.cast_unsigned";
    (* file: "Aeneas/Std/Scalar/WrappingOps/Shl.lean", line: 42 *)
    mk_fun "core::num::{i32}::wrapping_shl" "core.num.I32.wrapping_shl"
      ~can_fail:false;
    (* file: "Aeneas/Std/Scalar/WrappingOps/Shr.lean", line: 43 *)
    mk_fun "core::num::{i32}::wrapping_shr" "core.num.I32.wrapping_shr"
      ~can_fail:false;
    (* file: "Aeneas/Std/Scalar/CoreConvertNum.lean", line: 688 *)
    mk_fun "core::num::{i64}::cast_unsigned" "core.num.I64.cast_unsigned";
    (* file: "Aeneas/Std/Scalar/WrappingOps/Shl.lean", line: 43 *)
    mk_fun "core::num::{i64}::wrapping_shl" "core.num.I64.wrapping_shl"
      ~can_fail:false;
    (* file: "Aeneas/Std/Scalar/WrappingOps/Shr.lean", line: 44 *)
    mk_fun "core::num::{i64}::wrapping_shr" "core.num.I64.wrapping_shr"
      ~can_fail:false;
    (* file: "Aeneas/Std/Scalar/CoreConvertNum.lean", line: 670 *)
    mk_fun "core::num::{i8}::cast_unsigned" "core.num.I8.cast_unsigned";
    (* file: "Aeneas/Std/Scalar/WrappingOps/Shl.lean", line: 40 *)
    mk_fun "core::num::{i8}::wrapping_shl" "core.num.I8.wrapping_shl"
      ~can_fail:false;
    (* file: "Aeneas/Std/Scalar/WrappingOps/Shr.lean", line: 41 *)
    mk_fun "core::num::{i8}::wrapping_shr" "core.num.I8.wrapping_shr"
      ~can_fail:false;
    (* file: "Aeneas/Std/Scalar/CoreConvertNum.lean", line: 700 *)
    mk_fun "core::num::{isize}::cast_unsigned" "core.num.Isize.cast_unsigned";
    (* file: "Aeneas/Std/Scalar/WrappingOps/Shl.lean", line: 45 *)
    mk_fun "core::num::{isize}::wrapping_shl" "core.num.Isize.wrapping_shl"
      ~can_fail:false;
    (* file: "Aeneas/Std/Scalar/WrappingOps/Shr.lean", line: 46 *)
    mk_fun "core::num::{isize}::wrapping_shr" "core.num.Isize.wrapping_shr"
      ~can_fail:false;
    (* file: "Aeneas/Std/Scalar/CoreConvertNum.lean", line: 691 *)
    mk_fun "core::num::{u128}::cast_signed" "core.num.U128.cast_signed";
    (* file: "Aeneas/Std/Scalar/CoreConvertNum.lean", line: 784 *)
    mk_fun "core::num::{u128}::is_multiple_of" "core.num.U128.is_multiple_of";
    (* file: "Aeneas/Std/Scalar/WrappingOps/Shl.lean", line: 38 *)
    mk_fun "core::num::{u128}::wrapping_shl" "core.num.U128.wrapping_shl"
      ~can_fail:false;
    (* file: "Aeneas/Std/Scalar/WrappingOps/Shr.lean", line: 39 *)
    mk_fun "core::num::{u128}::wrapping_shr" "core.num.U128.wrapping_shr"
      ~can_fail:false;
    (* file: "Aeneas/Std/Scalar/CoreConvertNum.lean", line: 673 *)
    mk_fun "core::num::{u16}::cast_signed" "core.num.U16.cast_signed";
    (* file: "Aeneas/Std/Scalar/CoreConvertNum.lean", line: 775 *)
    mk_fun "core::num::{u16}::is_multiple_of" "core.num.U16.is_multiple_of";
    (* file: "Aeneas/Std/Scalar/WrappingOps/Shl.lean", line: 35 *)
    mk_fun "core::num::{u16}::wrapping_shl" "core.num.U16.wrapping_shl"
      ~can_fail:false;
    (* file: "Aeneas/Std/Scalar/WrappingOps/Shr.lean", line: 36 *)
    mk_fun "core::num::{u16}::wrapping_shr" "core.num.U16.wrapping_shr"
      ~can_fail:false;
    (* file: "Aeneas/Std/Scalar/CoreConvertNum.lean", line: 679 *)
    mk_fun "core::num::{u32}::cast_signed" "core.num.U32.cast_signed";
    (* file: "Aeneas/Std/Scalar/CoreConvertNum.lean", line: 778 *)
    mk_fun "core::num::{u32}::is_multiple_of" "core.num.U32.is_multiple_of";
    (* file: "Aeneas/Std/Scalar/WrappingOps/Shl.lean", line: 36 *)
    mk_fun "core::num::{u32}::wrapping_shl" "core.num.U32.wrapping_shl"
      ~can_fail:false;
    (* file: "Aeneas/Std/Scalar/WrappingOps/Shr.lean", line: 37 *)
    mk_fun "core::num::{u32}::wrapping_shr" "core.num.U32.wrapping_shr"
      ~can_fail:false;
    (* file: "Aeneas/Std/Scalar/CoreConvertNum.lean", line: 685 *)
    mk_fun "core::num::{u64}::cast_signed" "core.num.U64.cast_signed";
    (* file: "Aeneas/Std/Scalar/CoreConvertNum.lean", line: 781 *)
    mk_fun "core::num::{u64}::is_multiple_of" "core.num.U64.is_multiple_of";
    (* file: "Aeneas/Std/Scalar/WrappingOps/Shl.lean", line: 37 *)
    mk_fun "core::num::{u64}::wrapping_shl" "core.num.U64.wrapping_shl"
      ~can_fail:false;
    (* file: "Aeneas/Std/Scalar/WrappingOps/Shr.lean", line: 38 *)
    mk_fun "core::num::{u64}::wrapping_shr" "core.num.U64.wrapping_shr"
      ~can_fail:false;
    (* file: "Aeneas/Std/Scalar/CoreConvertNum.lean", line: 667 *)
    mk_fun "core::num::{u8}::cast_signed" "core.num.U8.cast_signed";
    (* file: "Aeneas/Std/Scalar/CoreConvertNum.lean", line: 772 *)
    mk_fun "core::num::{u8}::is_multiple_of" "core.num.U8.is_multiple_of";
    (* file: "Aeneas/Std/Scalar/WrappingOps/Shl.lean", line: 34 *)
    mk_fun "core::num::{u8}::wrapping_shl" "core.num.U8.wrapping_shl"
      ~can_fail:false;
    (* file: "Aeneas/Std/Scalar/WrappingOps/Shr.lean", line: 35 *)
    mk_fun "core::num::{u8}::wrapping_shr" "core.num.U8.wrapping_shr"
      ~can_fail:false;
    (* file: "Aeneas/Std/Scalar/CoreConvertNum.lean", line: 697 *)
    mk_fun "core::num::{usize}::cast_signed" "core.num.Usize.cast_signed";
    (* file: "Aeneas/Std/Scalar/CoreConvertNum.lean", line: 787 *)
    mk_fun "core::num::{usize}::is_multiple_of" "core.num.Usize.is_multiple_of";
    (* file: "Aeneas/Std/Scalar/Pow.lean", line: 7 *)
    mk_fun "core::num::{usize}::is_power_of_two"
      "core.num.Usize.is_power_of_two";
    (* file: "Aeneas/Std/Scalar/WrappingOps/Shl.lean", line: 39 *)
    mk_fun "core::num::{usize}::wrapping_shl" "core.num.Usize.wrapping_shl"
      ~can_fail:false;
    (* file: "Aeneas/Std/Scalar/WrappingOps/Shr.lean", line: 40 *)
    mk_fun "core::num::{usize}::wrapping_shr" "core.num.Usize.wrapping_shr"
      ~can_fail:false;
    (* file: "Aeneas/Std/Core/Ops.lean", line: 51 *)
    mk_fun "core::ops::drop::Drop::drop" "core.ops.drop.Drop.drop.default";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 622 *)
    mk_fun
      "core::ops::range::{core::ops::range::RangeInclusive<@Idx>}::is_empty"
      "core.ops.range.RangeInclusive.is_empty";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 617 *)
    mk_fun "core::ops::range::{core::ops::range::RangeInclusive<@Idx>}::new"
      "core.ops.range.RangeInclusive.new";
    (* file: "Aeneas/Std/Core/CoreOption.lean", line: 8 *)
    mk_fun "core::option::{core::option::Option<@T>}::expect"
      "core.option.Option.expect";
    (* file: "Aeneas/Std/Core/Core.lean", line: 115 *)
    mk_fun "core::option::{core::option::Option<@T>}::is_none"
      "core.option.Option.is_none" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Core/Core.lean", line: 119 *)
    mk_fun "core::option::{core::option::Option<@T>}::is_some"
      "core.option.Option.is_some" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Core/Core.lean", line: 112 *)
    mk_fun "core::option::{core::option::Option<@T>}::take"
      "core.option.Option.take" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Core/Core.lean", line: 91 *)
    mk_fun "core::option::{core::option::Option<@T>}::unwrap"
      "core.option.Option.unwrap";
    (* file: "Aeneas/Std/Core/Core.lean", line: 100 *)
    mk_fun "core::option::{core::option::Option<@T>}::unwrap_or"
      "core.option.Option.unwrap_or" ~can_fail:false;
    (* file: "Aeneas/Std/Core/Convert.lean", line: 114 *)
    mk_fun
      "core::result::{core::ops::try_trait::FromResidual<core::result::Result<@T, \
       @F>, core::result::Result<core::convert::Infallible, \
       @E>>}::from_residual"
      "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual";
    (* file: "Aeneas/Std/Core/Convert.lean", line: 102 *)
    mk_fun
      "core::result::{core::ops::try_trait::Try<core::result::Result<@T, \
       @E>>}::branch"
      "core.result.Result.Insts.CoreOpsTry.branch";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 114 *)
    mk_fun "core::result::{core::result::Result<@T, @E>}::expect"
      "core.result.Result.expect";
    (* file: "Aeneas/Std/Core/Convert.lean", line: 82 *)
    mk_fun "core::result::{core::result::Result<@T, @E>}::is_ok"
      "core.result.Result.is_ok";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 20 *)
    mk_fun "core::result::{core::result::Result<@T, @E>}::unwrap"
      "core.result.Result.unwrap";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 153 *)
    mk_fun "core::slice::cmp::{core::cmp::PartialEq<[@T], [@U]>}::eq"
      "core.slice.cmp.PartialEqSlice.eq";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 221 *)
    mk_fun "core::slice::cmp::{core::cmp::PartialEq<[@T], [@U]>}::ne"
      "core.slice.cmp.PartialEqSlice.ne";
    (* file: "Aeneas/Std/Slice.lean", line: 350 *)
    mk_fun "core::slice::index::{core::ops::index::Index<[@T], @I, @O>}::index"
      "core.slice.index.Slice.index";
    (* file: "Aeneas/Std/Slice.lean", line: 428 *)
    mk_fun
      "core::slice::index::{core::ops::index::IndexMut<[@T], @I, \
       @O>}::index_mut"
      "core.slice.index.Slice.index_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 376 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::get"
      "core.slice.index.SliceIndexRangeUsizeSlice.get";
    (* file: "Aeneas/Std/Slice.lean", line: 383 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::get_mut"
      "core.slice.index.SliceIndexRangeUsizeSlice.get_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 397 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::get_unchecked"
      "core.slice.index.SliceIndexRangeUsizeSlice.get_unchecked";
    (* file: "Aeneas/Std/Slice.lean", line: 403 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::get_unchecked_mut"
      "core.slice.index.SliceIndexRangeUsizeSlice.get_unchecked_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 409 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::index"
      "core.slice.index.SliceIndexRangeUsizeSlice.index";
    (* file: "Aeneas/Std/Slice.lean", line: 415 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T], [@T]>}::index_mut"
      "core.slice.index.SliceIndexRangeUsizeSlice.index_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 598 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::get"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.get";
    (* file: "Aeneas/Std/Slice.lean", line: 604 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::get_mut"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.get_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 618 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::get_unchecked"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.get_unchecked";
    (* file: "Aeneas/Std/Slice.lean", line: 624 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::get_unchecked_mut"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.get_unchecked_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 630 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::index"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.index";
    (* file: "Aeneas/Std/Slice.lean", line: 637 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>}::index_mut"
      "core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 455 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, \
       [@T], [@T]>}::get"
      "core.slice.index.SliceIndexRangeToUsizeSlice.get";
    (* file: "Aeneas/Std/Slice.lean", line: 462 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, \
       [@T], [@T]>}::get_mut"
      "core.slice.index.SliceIndexRangeToUsizeSlice.get_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 477 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, \
       [@T], [@T]>}::get_unchecked"
      "core.slice.index.SliceIndexRangeToUsizeSlice.get_unchecked";
    (* file: "Aeneas/Std/Slice.lean", line: 483 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, \
       [@T], [@T]>}::get_unchecked_mut"
      "core.slice.index.SliceIndexRangeToUsizeSlice.get_unchecked_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 490 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, \
       [@T], [@T]>}::index"
      "core.slice.index.SliceIndexRangeToUsizeSlice.index";
    (* file: "Aeneas/Std/Slice.lean", line: 497 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, \
       [@T], [@T]>}::index_mut"
      "core.slice.index.SliceIndexRangeToUsizeSlice.index_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 538 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
       @T>}::get"
      "core.slice.index.Usize.get";
    (* file: "Aeneas/Std/Slice.lean", line: 543 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
       @T>}::get_mut"
      "core.slice.index.Usize.get_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 548 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
       @T>}::get_unchecked"
      "core.slice.index.Usize.get_unchecked";
    (* file: "Aeneas/Std/Slice.lean", line: 554 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
       @T>}::get_unchecked_mut"
      "core.slice.index.Usize.get_unchecked_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 560 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
       @T>}::index"
      "core.slice.index.Usize.index";
    (* file: "Aeneas/Std/Slice.lean", line: 564 *)
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
       @T>}::index_mut"
      "core.slice.index.Usize.index_mut";
    (* file: "Aeneas/Std/SliceIter.lean", line: 126 *)
    mk_fun
      "core::slice::iter::{core::iter::traits::collect::IntoIterator<&'a [@T], \
       &'a @T, core::slice::iter::Iter<'a, @T>>}::into_iter"
      "SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter";
    (* file: "Aeneas/Std/SliceIter.lean", line: 169 *)
    mk_fun
      "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, \
       @T>, &'a [@T]>}::enumerate"
      "core.slice.iter.IteratorChunksExact.enumerate";
    (* file: "Aeneas/Std/SliceIter.lean", line: 152 *)
    mk_fun
      "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, \
       @T>, &'a [@T]>}::next"
      "core.slice.iter.IteratorChunksExact.next";
    (* file: "Aeneas/Std/SliceIter.lean", line: 218 *)
    mk_fun
      "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, \
       @T>, &'a [@T]>}::rev"
      "core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedSlice.rev";
    (* file: "Aeneas/Std/SliceIter.lean", line: 161 *)
    mk_fun
      "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, \
       @T>, &'a [@T]>}::step_by"
      "core.slice.iter.IteratorChunksExact.step_by";
    (* file: "Aeneas/Std/SliceIter.lean", line: 175 *)
    mk_fun
      "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, \
       @T>, &'a [@T]>}::take"
      "core.slice.iter.IteratorChunksExact.take";
    (* file: "Aeneas/Std/SliceIter.lean", line: 229 *)
    mk_fun
      "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, \
       @T>, &'a [@T]>}::zip"
      "core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedSlice.zip";
    (* file: "Aeneas/Std/SliceIter.lean", line: 76 *)
    mk_fun
      "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, \
       @T>, &'a @T>}::enumerate"
      "core.slice.iter.IteratorSliceIter.enumerate";
    (* file: "Aeneas/Std/SliceIter.lean", line: 59 *)
    mk_fun
      "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, \
       @T>, &'a @T>}::next"
      "core.slice.iter.IteratorSliceIter.next";
    (* file: "Aeneas/Std/SliceIter.lean", line: 197 *)
    mk_fun
      "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, \
       @T>, &'a @T>}::rev"
      "core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorShared.rev";
    (* file: "Aeneas/Std/SliceIter.lean", line: 69 *)
    mk_fun
      "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, \
       @T>, &'a @T>}::step_by"
      "core.slice.iter.IteratorSliceIter.step_by";
    (* file: "Aeneas/Std/SliceIter.lean", line: 82 *)
    mk_fun
      "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, \
       @T>, &'a @T>}::take"
      "core.slice.iter.IteratorSliceIter.take";
    (* file: "Aeneas/Std/SliceIter.lean", line: 206 *)
    mk_fun
      "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, \
       @T>, &'a @T>}::zip"
      "core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorShared.zip";
    (* file: "Aeneas/Std/SliceIter.lean", line: 36 *)
    mk_fun
      "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::IterMut<'a, \
       @T>, &'a mut @T>}::next"
      "core.slice.iter.IteratorIterMut.next";
    (* file: "Aeneas/Std/SliceIter.lean", line: 146 *)
    mk_fun
      "core::slice::iter::{core::slice::iter::ChunksExact<'a, @T>}::remainder"
      "core.slice.iter.ChunksExact.getRemainder";
    (* file: "Aeneas/Std/SliceIter.lean", line: 278 *)
    mk_fun "core::slice::{[@T]}::chunks_exact" "core.slice.Slice.chunks_exact";
    (* file: "Aeneas/Std/SliceIter.lean", line: 31 *)
    mk_fun "core::slice::{[@T]}::contains" "core.slice.Slice.contains";
    (* file: "Aeneas/Std/Slice.lean", line: 592 *)
    mk_fun "core::slice::{[@T]}::copy_from_slice"
      "core.slice.Slice.copy_from_slice";
    (* file: "Aeneas/Std/Slice.lean", line: 1054 *)
    mk_fun "core::slice::{[@T]}::fill" "core.slice.Slice.fill";
    (* file: "Aeneas/Std/Slice.lean", line: 356 *)
    mk_fun "core::slice::{[@T]}::get" "core.slice.Slice.get";
    (* file: "Aeneas/Std/Slice.lean", line: 370 *)
    mk_fun "core::slice::{[@T]}::get_mut" "core.slice.Slice.get_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 362 *)
    mk_fun "core::slice::{[@T]}::get_unchecked" "core.slice.Slice.get_unchecked";
    (* file: "Aeneas/Std/Slice.lean", line: 123 *)
    mk_fun "core::slice::{[@T]}::is_empty" "core.slice.Slice.is_empty";
    (* file: "Aeneas/Std/SliceIter.lean", line: 27 *)
    mk_fun "core::slice::{[@T]}::iter" "core.slice.Slice.iter";
    (* file: "Aeneas/Std/SliceIter.lean", line: 54 *)
    mk_fun "core::slice::{[@T]}::iter_mut" "core.slice.Slice.iter_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 49 *)
    mk_fun "core::slice::{[@T]}::len" "Slice.len" ~can_fail:false ~lift:false;
    (* file: "Aeneas/Std/Slice.lean", line: 333 *)
    mk_fun "core::slice::{[@T]}::reverse" "core.slice.Slice.reverse"
      ~can_fail:false;
    (* file: "Aeneas/Std/Slice.lean", line: 701 *)
    mk_fun "core::slice::{[@T]}::split_at" "core.slice.Slice.split_at";
    (* file: "Aeneas/Std/Slice.lean", line: 712 *)
    mk_fun "core::slice::{[@T]}::split_at_mut" "core.slice.Slice.split_at_mut";
    (* file: "Aeneas/Std/Slice.lean", line: 772 *)
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
      ~methods:[ ("assert_fields_are_eq", "assert_fields_are_eq") ];
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 113 *)
    mk_trait_decl "core::cmp::Ord" "core.cmp.Ord"
      ~parent_clauses:[ "eqInst"; "partialOrdInst" ]
      ~methods:
        [ ("cmp", "cmp"); ("max", "max"); ("min", "min"); ("clamp", "clamp") ];
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 8 *)
    mk_trait_decl "core::cmp::PartialEq" "core.cmp.PartialEq"
      ~methods:[ ("eq", "eq"); ("ne", "ne") ];
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 60 *)
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
    (* file: "Aeneas/Std/Core/Convert.lean", line: 72 *)
    mk_trait_decl "core::convert::AsMut" "core.convert.AsMut"
      ~methods:[ ("as_mut", "as_mut") ];
    (* file: "Aeneas/Std/Core/Convert.lean", line: 28 *)
    mk_trait_decl "core::convert::AsRef" "core.convert.AsRef"
      ~methods:[ ("as_ref", "as_ref") ];
    (* file: "Aeneas/Std/Core/Core.lean", line: 20 *)
    mk_trait_decl "core::convert::From" "core.convert.From"
      ~methods:[ ("from", "«from»") ];
    (* file: "Aeneas/Std/Core/Convert.lean", line: 13 *)
    mk_trait_decl "core::convert::Into" "core.convert.Into"
      ~methods:[ ("into", "into") ];
    (* file: "Aeneas/Std/Core/Convert.lean", line: 40 *)
    mk_trait_decl "core::convert::TryFrom" "core.convert.TryFrom"
      ~methods:[ ("try_from", "try_from") ];
    (* file: "Aeneas/Std/Core/Convert.lean", line: 50 *)
    mk_trait_decl "core::convert::TryInto" "core.convert.TryInto"
      ~methods:[ ("try_into", "try_into") ];
    (* file: "Aeneas/Std/Core/Default.lean", line: 5 *)
    mk_trait_decl "core::default::Default" "core.default.Default"
      ~methods:[ ("default", "default") ];
    (* file: "Aeneas/Std/Core/Error.lean", line: 5 *)
    mk_trait_decl "core::error::Error" "core.error.Error"
      ~parent_clauses:[ "fmtDebugInst"; "fmtDisplayInst" ];
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 15 *)
    mk_trait_decl "core::fmt::Debug" "core.fmt.Debug"
      ~methods:[ ("fmt", "fmt") ];
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 68 *)
    mk_trait_decl "core::fmt::Display" "core.fmt.Display"
      ~methods:[ ("fmt", "fmt") ];
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 72 *)
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
    (* file: "Aeneas/Std/Core/Iter.lean", line: 165 *)
    mk_trait_decl "core::iter::traits::accum::Product"
      "core.iter.traits.accum.Product"
      ~methods:[ ("product", "product") ];
    (* file: "Aeneas/Std/Core/Iter.lean", line: 161 *)
    mk_trait_decl "core::iter::traits::accum::Sum" "core.iter.traits.accum.Sum"
      ~methods:[ ("sum", "sum") ];
    (* file: "Aeneas/Std/Core/Iter.lean", line: 208 *)
    mk_trait_decl "core::iter::traits::collect::Extend"
      "core.iter.traits.collect.Extend"
      ~methods:[ ("extend", "extend") ];
    (* file: "Aeneas/Std/Core/Iter.lean", line: 176 *)
    mk_trait_decl "core::iter::traits::collect::FromIterator"
      "core.iter.traits.collect.FromIterator"
      ~methods:[ ("from_iter", "from_iter") ];
    (* file: "Aeneas/Std/Core/Iter.lean", line: 169 *)
    mk_trait_decl "core::iter::traits::collect::IntoIterator"
      "core.iter.traits.collect.IntoIterator" ~parent_clauses:[ "iteratorInst" ]
      ~methods:[ ("into_iter", "into_iter") ];
    (* file: "Aeneas/Std/Core/Iter.lean", line: 213 *)
    mk_trait_decl "core::iter::traits::double_ended::DoubleEndedIterator"
      "core.iter.traits.double_ended.DoubleEndedIterator"
      ~parent_clauses:[ "iteratorInst" ]
      ~methods:[ ("next_back", "next_back") ];
    (* file: "Aeneas/Std/Core/Iter.lean", line: 219 *)
    mk_trait_decl "core::iter::traits::exact_size::ExactSizeIterator"
      "core.iter.traits.exact_size.ExactSizeIterator"
      ~parent_clauses:[ "iteratorInst" ];
    (* file: "Aeneas/Std/Core/Iter.lean", line: 60 *)
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
    (* file: "Aeneas/Std/Core/Ops.lean", line: 47 *)
    mk_trait_decl "core::ops::drop::Drop" "core.ops.drop.Drop"
      ~methods:[ ("drop", "drop") ];
    (* file: "Aeneas/Std/Core/Ops.lean", line: 65 *)
    mk_trait_decl "core::ops::function::Fn" "core.ops.function.Fn"
      ~parent_clauses:[ "FnMutInst" ]
      ~methods:[ ("call", "call") ];
    (* file: "Aeneas/Std/Core/Ops.lean", line: 60 *)
    mk_trait_decl "core::ops::function::FnMut" "core.ops.function.FnMut"
      ~parent_clauses:[ "FnOnceInst" ]
      ~methods:[ ("call_mut", "call_mut") ];
    (* file: "Aeneas/Std/Core/Ops.lean", line: 56 *)
    mk_trait_decl "core::ops::function::FnOnce" "core.ops.function.FnOnce"
      ~methods:[ ("call_once", "call_once") ];
    (* file: "Aeneas/Std/Core/Ops.lean", line: 10 *)
    mk_trait_decl "core::ops::index::Index" "core.ops.index.Index"
      ~methods:[ ("index", "index") ];
    (* file: "Aeneas/Std/Core/Ops.lean", line: 14 *)
    mk_trait_decl "core::ops::index::IndexMut" "core.ops.index.IndexMut"
      ~parent_clauses:[ "indexInst" ]
      ~methods:[ ("index_mut", "index_mut") ];
    (* file: "Aeneas/Std/Core/Ops.lean", line: 88 *)
    mk_trait_decl "core::ops::try_trait::FromResidual"
      "core.ops.try_trait.FromResidual"
      ~methods:[ ("from_residual", "from_residual") ];
    (* file: "Aeneas/Std/Core/Ops.lean", line: 103 *)
    mk_trait_decl "core::ops::try_trait::Residual" "core.ops.try_trait.Residual"
      ~parent_clauses:[ "TryInst" ];
    (* file: "Aeneas/Std/Core/Ops.lean", line: 97 *)
    mk_trait_decl "core::ops::try_trait::Try" "core.ops.try_trait.Try"
      ~parent_clauses:[ "FromResidualInst" ]
      ~methods:[ ("from_output", "from_output"); ("branch", "branch") ];
    (* file: "Aeneas/Std/Slice.lean", line: 340 *)
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
    (* file: "Aeneas/Std/Slice.lean", line: 337 *)
    mk_trait_decl "core::slice::index::private_slice_index::Sealed"
      "core.slice.index.private_slice_index.Sealed";
  ]

let lean_builtin_trait_impls =
  [
    (* file: "Aeneas/Std/Core/Core.lean", line: 53 *)
    mk_trait_impl "core::clone::Clone<Box<@T>>" "core.core.clone.CloneBox"
      ~keep_params:(Some [ true; false ])
      ~keep_trait_clauses:(Some [ true; false ]);
    (* file: "Aeneas/Std/Array/Array.lean", line: 321 *)
    mk_trait_impl "core::clone::Clone<[@T; @N]>" "core.clone.CloneArray";
    (* file: "Aeneas/Std/Core/Core.lean", line: 33 *)
    mk_trait_impl "core::clone::Clone<alloc::alloc::Global>"
      "core.core.clone.CloneGlobal";
    (* file: "Aeneas/Std/Vec.lean", line: 543 *)
    mk_trait_impl "core::clone::Clone<alloc::vec::Vec<@T>>"
      "core.clone.CloneallocvecVec"
      ~keep_params:(Some [ true; false ])
      ~keep_trait_clauses:(Some [ true; false ]);
    (* file: "Aeneas/Std/Core/Core.lean", line: 42 *)
    mk_trait_impl "core::clone::Clone<bool>" "core.clone.CloneBool";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 191 *)
    mk_trait_impl "core::cmp::PartialEq<&'a @A, &'b @B>"
      "core.cmp.PartialEqShared";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 159 *)
    mk_trait_impl "core::cmp::PartialEq<(), ()>" "core.cmp.PartialEqUnit";
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 203 *)
    mk_trait_impl "core::cmp::PartialEq<Box<@T>, Box<@T>>"
      "core.cmp.PartialEqBox"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 571 *)
    mk_trait_impl
      "core::cmp::PartialEq<alloc::vec::Vec<@T>, alloc::vec::Vec<@U>>"
      "core.cmp.PartialEqVec"
      ~keep_params:(Some [ true; true; false; false ]);
    (* file: "Aeneas/Std/Core/Cmp.lean", line: 176 *)
    mk_trait_impl "core::cmp::PartialEq<bool, bool>" "core.cmp.PartialEqBool";
    (* file: "Aeneas/Std/Core/Convert.lean", line: 76 *)
    mk_trait_impl "core::convert::AsMut<Box<@T>, @T>" "core.convert.AsMutBox";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 501 *)
    mk_trait_impl "core::convert::AsMut<[@T; @N], [@T]>"
      "Array.Insts.CoreConvertAsMutSlice";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 495 *)
    mk_trait_impl "core::convert::AsRef<[@T; @N], [@T]>"
      "Array.Insts.CoreConvertAsRefSlice";
    (* file: "Aeneas/Std/Core/Convert.lean", line: 35 *)
    mk_trait_impl "core::convert::From<@Self, @Self>" "core.convert.FromSame";
    (* file: "Aeneas/Std/Vec.lean", line: 467 *)
    mk_trait_impl "core::convert::From<Box<[@T]>, alloc::vec::Vec<@T>>"
      "core.convert.FromBoxSliceVec"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 451 *)
    mk_trait_impl "core::convert::From<alloc::vec::Vec<@T>, [@T; @N]>"
      "core.convert.FromVecArray";
    (* file: "Aeneas/Std/Core/Convert.lean", line: 22 *)
    mk_trait_impl "core::convert::Into<@Self, @T>" "core.convert.IntoFrom";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 320 *)
    mk_trait_impl
      "core::convert::TryFrom<&'a [@T; @N], &'a [@T], \
       core::array::TryFromSliceError>"
      "core.convert.TryFromSharedArraySliceTryFromSliceError";
    (* file: "Aeneas/Std/Core/Convert.lean", line: 65 *)
    mk_trait_impl "core::convert::TryInto<@T, @U, @E>"
      "core.convert.TryInto.Blanket";
    (* file: "Aeneas/Std/Core/Convert.lean", line: 59 *)
    mk_trait_impl "core::convert::{core::convert::TryInto<@T, @U>}"
      "core.convert.TryIntoFrom";
    (* file: "Aeneas/Std/Array/Array.lean", line: 407 *)
    mk_trait_impl "core::default::Default<[@T; 0]>"
      "core.default.DefaultArrayEmpty";
    (* file: "Aeneas/Std/Array/Array.lean", line: 396 *)
    mk_trait_impl "core::default::Default<[@T; @N]>" "core.default.DefaultArray";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 177 *)
    mk_trait_impl "core::fmt::Debug<&'0 @T>" "core.fmt.DebugShared";
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 183 *)
    mk_trait_impl "core::fmt::Debug<()>" "core.fmt.DebugUnit";
    (* file: "Aeneas/Std/Array/ArrayDebug.lean", line: 16 *)
    mk_trait_impl "core::fmt::Debug<[@T; @N]>" "Array.Insts.CoreFmtDebug";
    (* file: "Aeneas/Std/Vec.lean", line: 592 *)
    mk_trait_impl "core::fmt::Debug<alloc::vec::Vec<@T>>" "core.fmt.DebugVec"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Core/Fmt.lean", line: 188 *)
    mk_trait_impl "core::fmt::Debug<bool>" "core.fmt.DebugBool";
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 286 *)
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
    (* file: "Aeneas/Std/Core/Iter.lean", line: 425 *)
    mk_trait_impl "core::iter::range::Step<i128>" "core.iter.range.StepI128";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 398 *)
    mk_trait_impl "core::iter::range::Step<i16>" "core.iter.range.StepI16";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 407 *)
    mk_trait_impl "core::iter::range::Step<i32>" "core.iter.range.StepI32";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 416 *)
    mk_trait_impl "core::iter::range::Step<i64>" "core.iter.range.StepI64";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 389 *)
    mk_trait_impl "core::iter::range::Step<i8>" "core.iter.range.StepI8";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 380 *)
    mk_trait_impl "core::iter::range::Step<isize>" "core.iter.range.StepIsize";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 371 *)
    mk_trait_impl "core::iter::range::Step<u128>" "core.iter.range.StepU128";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 344 *)
    mk_trait_impl "core::iter::range::Step<u16>" "core.iter.range.StepU16";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 353 *)
    mk_trait_impl "core::iter::range::Step<u32>" "core.iter.range.StepU32";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 362 *)
    mk_trait_impl "core::iter::range::Step<u64>" "core.iter.range.StepU64";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 335 *)
    mk_trait_impl "core::iter::range::Step<u8>" "core.iter.range.StepU8";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 326 *)
    mk_trait_impl "core::iter::range::Step<usize>" "core.iter.range.StepUsize";
    (* file: "Aeneas/Std/VecIter.lean", line: 91 *)
    mk_trait_impl
      "core::iter::traits::collect::FromIterator<alloc::vec::Vec<@T>, @T>"
      "core.iter.traits.collect.FromIteratorVec";
    (* file: "Aeneas/Std/SliceIter.lean", line: 111 *)
    mk_trait_impl
      "core::iter::traits::collect::IntoIterator<&'a [@T; @N], &'a @T, \
       core::slice::iter::Iter<'a, @T>>"
      "SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter";
    (* file: "Aeneas/Std/SliceIter.lean", line: 132 *)
    mk_trait_impl
      "core::iter::traits::collect::IntoIterator<&'a [@T], &'a @T, \
       core::slice::iter::Iter<'a, @T>>"
      "SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 190 *)
    mk_trait_impl "core::iter::traits::collect::IntoIterator<@I, @Item, @I>"
      "core.iter.traits.collect.IntoIterator.Blanket";
    (* file: "Aeneas/Std/VecIter.lean", line: 58 *)
    mk_trait_impl
      "core::iter::traits::collect::IntoIterator<alloc::vec::Vec<@T>, @T, \
       alloc::vec::into_iter::IntoIter<@T, @A>>"
      "core.iter.traits.collect.IntoIteratorVec"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/VecIter.lean", line: 42 *)
    mk_trait_impl
      "core::iter::traits::iterator::Iterator<alloc::vec::into_iter::IntoIter<@T, \
       @A>, @T>"
      "core.iter.traits.iterator.IteratorVecIntoIter"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Core/Iter.lean", line: 475 *)
    mk_trait_impl
      "core::iter::traits::iterator::Iterator<core::iter::adapters::enumerate::Enumerate<@I>, \
       (usize, @Clause0_Item)>"
      "core.iter.traits.iterator.IteratorEnumerate";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 150 *)
    mk_trait_impl
      "core::iter::traits::iterator::Iterator<core::iter::adapters::step_by::StepBy<@I>, \
       @Clause0_Item>"
      "core.iter.traits.iterator.IteratorStepBy";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 533 *)
    mk_trait_impl
      "core::iter::traits::iterator::Iterator<core::iter::adapters::take::Take<@I>, \
       @Clause0_Item>"
      "core.iter.traits.iterator.IteratorTake";
    (* file: "Aeneas/Std/Core/Iter.lean", line: 582 *)
    mk_trait_impl
      "core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, @A>"
      "core.iter.traits.iterator.IteratorRange";
    (* file: "Aeneas/Std/SliceIter.lean", line: 181 *)
    mk_trait_impl
      "core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, \
       @T>, &'a [@T]>"
      "core.iter.traits.iterator.IteratorChunksExact";
    (* file: "Aeneas/Std/SliceIter.lean", line: 88 *)
    mk_trait_impl
      "core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, \
       &'a @T>"
      "core.iter.traits.iterator.IteratorSliceIter";
    (* file: "Aeneas/Std/Array/Array.lean", line: 412 *)
    mk_trait_impl "core::marker::Copy<[@T; @N]>" "Array.Insts.CoreMarkerCopy";
    (* file: "Aeneas/Std/Core/Core.lean", line: 63 *)
    mk_trait_impl "core::marker::Copy<bool>" "core.core.marker.CopyBool";
    (* file: "Aeneas/Std/Core/Ops.lean", line: 29 *)
    mk_trait_impl "core::ops::deref::Deref<Box<@T>, @T>"
      "core.ops.deref.DerefBoxInst"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 368 *)
    mk_trait_impl "core::ops::deref::Deref<alloc::vec::Vec<@T>, [@T]>"
      "core.ops.deref.DerefVec"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Core/Ops.lean", line: 36 *)
    mk_trait_impl "core::ops::deref::DerefMut<Box<@T>, @T>"
      "core.ops.deref.DerefMutBoxInst"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Vec.lean", line: 379 *)
    mk_trait_impl "core::ops::deref::DerefMut<alloc::vec::Vec<@T>, [@T]>"
      "core.ops.deref.DerefMutVec"
      ~keep_params:(Some [ true; false ]);
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 108 *)
    mk_trait_impl "core::ops::index::Index<[@T; @N], @I, @O>"
      "core.ops.index.IndexArray";
    (* file: "Aeneas/Std/Slice.lean", line: 523 *)
    mk_trait_impl "core::ops::index::Index<[@T], @I, @O>"
      "core.ops.index.IndexSlice";
    (* file: "Aeneas/Std/Vec.lean", line: 209 *)
    mk_trait_impl "core::ops::index::Index<alloc::vec::Vec<@T>, @T, @O>"
      "alloc.vec.Vec.Index"
      ~keep_params:(Some [ true; true; false; true ]);
    (* file: "Aeneas/Std/Array/ArraySlice.lean", line: 115 *)
    mk_trait_impl "core::ops::index::IndexMut<[@T; @N], @I, @O>"
      "core.ops.index.IndexMutArray";
    (* file: "Aeneas/Std/Slice.lean", line: 530 *)
    mk_trait_impl "core::ops::index::IndexMut<[@T], @I, @O>"
      "core.ops.index.IndexMutSlice";
    (* file: "Aeneas/Std/Vec.lean", line: 217 *)
    mk_trait_impl "core::ops::index::IndexMut<alloc::vec::Vec<@T>, @T, @O>"
      "alloc.vec.Vec.IndexMut"
      ~keep_params:(Some [ true; true; false; true ]);
    (* file: "Aeneas/Std/Slice.lean", line: 438 *)
    mk_trait_impl
      "core::slice::index::SliceIndex<core::ops::range::Range<usize>, [@T], \
       [@T]>"
      "core.slice.index.SliceIndexRangeUsizeSlice";
    (* file: "Aeneas/Std/Slice.lean", line: 663 *)
    mk_trait_impl
      "core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
       [@T], [@T]>"
      "core.slice.index.SliceIndexRangeFromUsizeSlice";
    (* file: "Aeneas/Std/Slice.lean", line: 510 *)
    mk_trait_impl
      "core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, [@T], \
       [@T]>"
      "core.slice.index.SliceIndexRangeToUsizeSlice";
    (* file: "Aeneas/Std/Slice.lean", line: 573 *)
    mk_trait_impl "core::slice::index::SliceIndex<usize, [@T], @T>"
      "core.slice.index.SliceIndexUsizeSlice";
    (* file: "Aeneas/Std/Slice.lean", line: 434 *)
    mk_trait_impl
      "core::slice::index::private_slice_index::Sealed<core::ops::range::Range<usize>>"
      "core.slice.index.private_slice_index.SealedRangeUsize";
    (* file: "Aeneas/Std/Slice.lean", line: 658 *)
    mk_trait_impl
      "core::slice::index::private_slice_index::Sealed<core::ops::range::RangeFrom<usize>>"
      "core.slice.index.private_slice_index.SealedRangeFromUsize";
    (* file: "Aeneas/Std/Slice.lean", line: 450 *)
    mk_trait_impl
      "core::slice::index::private_slice_index::Sealed<core::ops::range::RangeTo<usize>>"
      "core.slice.index.private_slice_index.SealedRangeToUsize";
    (* file: "Aeneas/Std/Slice.lean", line: 569 *)
    mk_trait_impl "core::slice::index::private_slice_index::Sealed<usize>"
      "core.slice.index.private_slice_index.SealedUsize";
  ]
