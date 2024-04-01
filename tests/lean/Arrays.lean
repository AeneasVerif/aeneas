-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [arrays]
import Base
open Primitives

namespace arrays

/- [arrays::AB]
   Source: 'src/arrays.rs', lines 3:0-3:11 -/
inductive AB :=
| A : AB
| B : AB

/- [arrays::incr]:
   Source: 'src/arrays.rs', lines 8:0-8:24 -/
def incr (x : U32) : Result U32 :=
  x + 1#u32

/- [arrays::array_to_shared_slice_]:
   Source: 'src/arrays.rs', lines 16:0-16:53 -/
def array_to_shared_slice_
  (T : Type) (s : Array T 32#usize) : Result (Slice T) :=
  Array.to_slice T 32#usize s

/- [arrays::array_to_mut_slice_]:
   Source: 'src/arrays.rs', lines 21:0-21:58 -/
def array_to_mut_slice_
  (T : Type) (s : Array T 32#usize) :
  Result ((Slice T) × (Slice T → Result (Array T 32#usize)))
  :=
  Array.to_slice_mut T 32#usize s

/- [arrays::array_len]:
   Source: 'src/arrays.rs', lines 25:0-25:40 -/
def array_len (T : Type) (s : Array T 32#usize) : Result Usize :=
  do
  let s1 ← Array.to_slice T 32#usize s
  Result.ret (Slice.len T s1)

/- [arrays::shared_array_len]:
   Source: 'src/arrays.rs', lines 29:0-29:48 -/
def shared_array_len (T : Type) (s : Array T 32#usize) : Result Usize :=
  do
  let s1 ← Array.to_slice T 32#usize s
  Result.ret (Slice.len T s1)

/- [arrays::shared_slice_len]:
   Source: 'src/arrays.rs', lines 33:0-33:44 -/
def shared_slice_len (T : Type) (s : Slice T) : Result Usize :=
  Result.ret (Slice.len T s)

/- [arrays::index_array_shared]:
   Source: 'src/arrays.rs', lines 37:0-37:57 -/
def index_array_shared
  (T : Type) (s : Array T 32#usize) (i : Usize) : Result T :=
  Array.index_usize T 32#usize s i

/- [arrays::index_array_u32]:
   Source: 'src/arrays.rs', lines 44:0-44:53 -/
def index_array_u32 (s : Array U32 32#usize) (i : Usize) : Result U32 :=
  Array.index_usize U32 32#usize s i

/- [arrays::index_array_copy]:
   Source: 'src/arrays.rs', lines 48:0-48:45 -/
def index_array_copy (x : Array U32 32#usize) : Result U32 :=
  Array.index_usize U32 32#usize x 0#usize

/- [arrays::index_mut_array]:
   Source: 'src/arrays.rs', lines 52:0-52:62 -/
def index_mut_array
  (T : Type) (s : Array T 32#usize) (i : Usize) :
  Result (T × (T → Result (Array T 32#usize)))
  :=
  Array.index_mut_usize T 32#usize s i

/- [arrays::index_slice]:
   Source: 'src/arrays.rs', lines 56:0-56:46 -/
def index_slice (T : Type) (s : Slice T) (i : Usize) : Result T :=
  Slice.index_usize T s i

/- [arrays::index_mut_slice]:
   Source: 'src/arrays.rs', lines 60:0-60:58 -/
def index_mut_slice
  (T : Type) (s : Slice T) (i : Usize) :
  Result (T × (T → Result (Slice T)))
  :=
  Slice.index_mut_usize T s i

/- [arrays::slice_subslice_shared_]:
   Source: 'src/arrays.rs', lines 64:0-64:70 -/
def slice_subslice_shared_
  (x : Slice U32) (y : Usize) (z : Usize) : Result (Slice U32) :=
  core.slice.index.Slice.index U32 (core.ops.range.Range Usize)
    (core.slice.index.SliceIndexRangeUsizeSliceTInst U32) x
    { start := y, end_ := z }

/- [arrays::slice_subslice_mut_]:
   Source: 'src/arrays.rs', lines 68:0-68:75 -/
def slice_subslice_mut_
  (x : Slice U32) (y : Usize) (z : Usize) :
  Result ((Slice U32) × (Slice U32 → Result (Slice U32)))
  :=
  do
  let (s, index_mut_back) ←
    core.slice.index.Slice.index_mut U32 (core.ops.range.Range Usize)
      (core.slice.index.SliceIndexRangeUsizeSliceTInst U32) x
      { start := y, end_ := z }
  Result.ret (s, index_mut_back)

/- [arrays::array_to_slice_shared_]:
   Source: 'src/arrays.rs', lines 72:0-72:54 -/
def array_to_slice_shared_ (x : Array U32 32#usize) : Result (Slice U32) :=
  Array.to_slice U32 32#usize x

/- [arrays::array_to_slice_mut_]:
   Source: 'src/arrays.rs', lines 76:0-76:59 -/
def array_to_slice_mut_
  (x : Array U32 32#usize) :
  Result ((Slice U32) × (Slice U32 → Result (Array U32 32#usize)))
  :=
  Array.to_slice_mut U32 32#usize x

/- [arrays::array_subslice_shared_]:
   Source: 'src/arrays.rs', lines 80:0-80:74 -/
def array_subslice_shared_
  (x : Array U32 32#usize) (y : Usize) (z : Usize) : Result (Slice U32) :=
  core.array.Array.index U32 (core.ops.range.Range Usize) 32#usize
    (core.ops.index.IndexSliceTIInst U32 (core.ops.range.Range Usize)
    (core.slice.index.SliceIndexRangeUsizeSliceTInst U32)) x
    { start := y, end_ := z }

/- [arrays::array_subslice_mut_]:
   Source: 'src/arrays.rs', lines 84:0-84:79 -/
def array_subslice_mut_
  (x : Array U32 32#usize) (y : Usize) (z : Usize) :
  Result ((Slice U32) × (Slice U32 → Result (Array U32 32#usize)))
  :=
  do
  let (s, index_mut_back) ←
    core.array.Array.index_mut U32 (core.ops.range.Range Usize) 32#usize
      (core.ops.index.IndexMutSliceTIInst U32 (core.ops.range.Range Usize)
      (core.slice.index.SliceIndexRangeUsizeSliceTInst U32)) x
      { start := y, end_ := z }
  Result.ret (s, index_mut_back)

/- [arrays::index_slice_0]:
   Source: 'src/arrays.rs', lines 88:0-88:38 -/
def index_slice_0 (T : Type) (s : Slice T) : Result T :=
  Slice.index_usize T s 0#usize

/- [arrays::index_array_0]:
   Source: 'src/arrays.rs', lines 92:0-92:42 -/
def index_array_0 (T : Type) (s : Array T 32#usize) : Result T :=
  Array.index_usize T 32#usize s 0#usize

/- [arrays::index_index_array]:
   Source: 'src/arrays.rs', lines 103:0-103:71 -/
def index_index_array
  (s : Array (Array U32 32#usize) 32#usize) (i : Usize) (j : Usize) :
  Result U32
  :=
  do
  let a ← Array.index_usize (Array U32 32#usize) 32#usize s i
  Array.index_usize U32 32#usize a j

/- [arrays::update_update_array]:
   Source: 'src/arrays.rs', lines 114:0-114:70 -/
def update_update_array
  (s : Array (Array U32 32#usize) 32#usize) (i : Usize) (j : Usize) :
  Result Unit
  :=
  do
  let (a, index_mut_back) ←
    Array.index_mut_usize (Array U32 32#usize) 32#usize s i
  let (_, index_mut_back1) ← Array.index_mut_usize U32 32#usize a j
  let a1 ← index_mut_back1 0#u32
  let _ ← index_mut_back a1
  Result.ret ()

/- [arrays::array_local_deep_copy]:
   Source: 'src/arrays.rs', lines 118:0-118:43 -/
def array_local_deep_copy (x : Array U32 32#usize) : Result Unit :=
  Result.ret ()

/- [arrays::take_array]:
   Source: 'src/arrays.rs', lines 122:0-122:30 -/
def take_array (a : Array U32 2#usize) : Result Unit :=
  Result.ret ()

/- [arrays::take_array_borrow]:
   Source: 'src/arrays.rs', lines 123:0-123:38 -/
def take_array_borrow (a : Array U32 2#usize) : Result Unit :=
  Result.ret ()

/- [arrays::take_slice]:
   Source: 'src/arrays.rs', lines 124:0-124:28 -/
def take_slice (s : Slice U32) : Result Unit :=
  Result.ret ()

/- [arrays::take_mut_slice]:
   Source: 'src/arrays.rs', lines 125:0-125:36 -/
def take_mut_slice (s : Slice U32) : Result (Slice U32) :=
  Result.ret s

/- [arrays::const_array]:
   Source: 'src/arrays.rs', lines 127:0-127:32 -/
def const_array : Result (Array U32 2#usize) :=
  Result.ret (Array.make U32 2#usize [ 0#u32, 0#u32 ])

/- [arrays::const_slice]:
   Source: 'src/arrays.rs', lines 131:0-131:20 -/
def const_slice : Result Unit :=
  do
  let _ ←
    Array.to_slice U32 2#usize (Array.make U32 2#usize [ 0#u32, 0#u32 ])
  Result.ret ()

/- [arrays::take_all]:
   Source: 'src/arrays.rs', lines 141:0-141:17 -/
def take_all : Result Unit :=
  do
  let _ ← take_array (Array.make U32 2#usize [ 0#u32, 0#u32 ])
  let _ ← take_array (Array.make U32 2#usize [ 0#u32, 0#u32 ])
  let _ ← take_array_borrow (Array.make U32 2#usize [ 0#u32, 0#u32 ])
  let s ←
    Array.to_slice U32 2#usize (Array.make U32 2#usize [ 0#u32, 0#u32 ])
  let _ ← take_slice s
  let (s1, to_slice_mut_back) ←
    Array.to_slice_mut U32 2#usize (Array.make U32 2#usize [ 0#u32, 0#u32 ])
  let s2 ← take_mut_slice s1
  let _ ← to_slice_mut_back s2
  Result.ret ()

/- [arrays::index_array]:
   Source: 'src/arrays.rs', lines 155:0-155:38 -/
def index_array (x : Array U32 2#usize) : Result U32 :=
  Array.index_usize U32 2#usize x 0#usize

/- [arrays::index_array_borrow]:
   Source: 'src/arrays.rs', lines 158:0-158:46 -/
def index_array_borrow (x : Array U32 2#usize) : Result U32 :=
  Array.index_usize U32 2#usize x 0#usize

/- [arrays::index_slice_u32_0]:
   Source: 'src/arrays.rs', lines 162:0-162:42 -/
def index_slice_u32_0 (x : Slice U32) : Result U32 :=
  Slice.index_usize U32 x 0#usize

/- [arrays::index_mut_slice_u32_0]:
   Source: 'src/arrays.rs', lines 166:0-166:50 -/
def index_mut_slice_u32_0 (x : Slice U32) : Result (U32 × (Slice U32)) :=
  do
  let i ← Slice.index_usize U32 x 0#usize
  Result.ret (i, x)

/- [arrays::index_all]:
   Source: 'src/arrays.rs', lines 170:0-170:25 -/
def index_all : Result U32 :=
  do
  let i ← index_array (Array.make U32 2#usize [ 0#u32, 0#u32 ])
  let i1 ← index_array (Array.make U32 2#usize [ 0#u32, 0#u32 ])
  let i2 ← i + i1
  let i3 ← index_array_borrow (Array.make U32 2#usize [ 0#u32, 0#u32 ])
  let i4 ← i2 + i3
  let s ←
    Array.to_slice U32 2#usize (Array.make U32 2#usize [ 0#u32, 0#u32 ])
  let i5 ← index_slice_u32_0 s
  let i6 ← i4 + i5
  let (s1, to_slice_mut_back) ←
    Array.to_slice_mut U32 2#usize (Array.make U32 2#usize [ 0#u32, 0#u32 ])
  let (i7, s2) ← index_mut_slice_u32_0 s1
  let i8 ← i6 + i7
  let _ ← to_slice_mut_back s2
  Result.ret i8

/- [arrays::update_array]:
   Source: 'src/arrays.rs', lines 184:0-184:36 -/
def update_array (x : Array U32 2#usize) : Result Unit :=
  do
  let (_, index_mut_back) ← Array.index_mut_usize U32 2#usize x 0#usize
  let _ ← index_mut_back 1#u32
  Result.ret ()

/- [arrays::update_array_mut_borrow]:
   Source: 'src/arrays.rs', lines 187:0-187:48 -/
def update_array_mut_borrow
  (x : Array U32 2#usize) : Result (Array U32 2#usize) :=
  do
  let (_, index_mut_back) ← Array.index_mut_usize U32 2#usize x 0#usize
  index_mut_back 1#u32

/- [arrays::update_mut_slice]:
   Source: 'src/arrays.rs', lines 190:0-190:38 -/
def update_mut_slice (x : Slice U32) : Result (Slice U32) :=
  do
  let (_, index_mut_back) ← Slice.index_mut_usize U32 x 0#usize
  index_mut_back 1#u32

/- [arrays::update_all]:
   Source: 'src/arrays.rs', lines 194:0-194:19 -/
def update_all : Result Unit :=
  do
  let _ ← update_array (Array.make U32 2#usize [ 0#u32, 0#u32 ])
  let _ ← update_array (Array.make U32 2#usize [ 0#u32, 0#u32 ])
  let x ← update_array_mut_borrow (Array.make U32 2#usize [ 0#u32, 0#u32 ])
  let (s, to_slice_mut_back) ← Array.to_slice_mut U32 2#usize x
  let s1 ← update_mut_slice s
  let _ ← to_slice_mut_back s1
  Result.ret ()

/- [arrays::range_all]:
   Source: 'src/arrays.rs', lines 205:0-205:18 -/
def range_all : Result Unit :=
  do
  let (s, index_mut_back) ←
    core.array.Array.index_mut U32 (core.ops.range.Range Usize) 4#usize
      (core.ops.index.IndexMutSliceTIInst U32 (core.ops.range.Range Usize)
      (core.slice.index.SliceIndexRangeUsizeSliceTInst U32))
      (Array.make U32 4#usize [ 0#u32, 0#u32, 0#u32, 0#u32 ])
      { start := 1#usize, end_ := 3#usize }
  let s1 ← update_mut_slice s
  let _ ← index_mut_back s1
  Result.ret ()

/- [arrays::deref_array_borrow]:
   Source: 'src/arrays.rs', lines 214:0-214:46 -/
def deref_array_borrow (x : Array U32 2#usize) : Result U32 :=
  Array.index_usize U32 2#usize x 0#usize

/- [arrays::deref_array_mut_borrow]:
   Source: 'src/arrays.rs', lines 219:0-219:54 -/
def deref_array_mut_borrow
  (x : Array U32 2#usize) : Result (U32 × (Array U32 2#usize)) :=
  do
  let i ← Array.index_usize U32 2#usize x 0#usize
  Result.ret (i, x)

/- [arrays::take_array_t]:
   Source: 'src/arrays.rs', lines 227:0-227:31 -/
def take_array_t (a : Array AB 2#usize) : Result Unit :=
  Result.ret ()

/- [arrays::non_copyable_array]:
   Source: 'src/arrays.rs', lines 229:0-229:27 -/
def non_copyable_array : Result Unit :=
  take_array_t (Array.make AB 2#usize [ AB.A, AB.B ])

/- [arrays::sum]: loop 0:
   Source: 'src/arrays.rs', lines 242:0-250:1 -/
divergent def sum_loop (s : Slice U32) (sum1 : U32) (i : Usize) : Result U32 :=
  let i1 := Slice.len U32 s
  if i < i1
  then
    do
    let i2 ← Slice.index_usize U32 s i
    let sum3 ← sum1 + i2
    let i3 ← i + 1#usize
    sum_loop s sum3 i3
  else Result.ret sum1

/- [arrays::sum]:
   Source: 'src/arrays.rs', lines 242:0-242:28 -/
def sum (s : Slice U32) : Result U32 :=
  sum_loop s 0#u32 0#usize

/- [arrays::sum2]: loop 0:
   Source: 'src/arrays.rs', lines 252:0-261:1 -/
divergent def sum2_loop
  (s : Slice U32) (s2 : Slice U32) (sum1 : U32) (i : Usize) : Result U32 :=
  let i1 := Slice.len U32 s
  if i < i1
  then
    do
    let i2 ← Slice.index_usize U32 s i
    let i3 ← Slice.index_usize U32 s2 i
    let i4 ← i2 + i3
    let sum3 ← sum1 + i4
    let i5 ← i + 1#usize
    sum2_loop s s2 sum3 i5
  else Result.ret sum1

/- [arrays::sum2]:
   Source: 'src/arrays.rs', lines 252:0-252:41 -/
def sum2 (s : Slice U32) (s2 : Slice U32) : Result U32 :=
  let i := Slice.len U32 s
  let i1 := Slice.len U32 s2
  if ¬ (i = i1)
  then Result.fail .panic
  else sum2_loop s s2 0#u32 0#usize

/- [arrays::f0]:
   Source: 'src/arrays.rs', lines 263:0-263:11 -/
def f0 : Result Unit :=
  do
  let (s, to_slice_mut_back) ←
    Array.to_slice_mut U32 2#usize (Array.make U32 2#usize [ 1#u32, 2#u32 ])
  let (_, index_mut_back) ← Slice.index_mut_usize U32 s 0#usize
  let s1 ← index_mut_back 1#u32
  let _ ← to_slice_mut_back s1
  Result.ret ()

/- [arrays::f1]:
   Source: 'src/arrays.rs', lines 268:0-268:11 -/
def f1 : Result Unit :=
  do
  let (_, index_mut_back) ←
    Array.index_mut_usize U32 2#usize (Array.make U32 2#usize [ 1#u32, 2#u32 ])
      0#usize
  let _ ← index_mut_back 1#u32
  Result.ret ()

/- [arrays::f2]:
   Source: 'src/arrays.rs', lines 273:0-273:17 -/
def f2 (i : U32) : Result Unit :=
  Result.ret ()

/- [arrays::f4]:
   Source: 'src/arrays.rs', lines 282:0-282:54 -/
def f4 (x : Array U32 32#usize) (y : Usize) (z : Usize) : Result (Slice U32) :=
  core.array.Array.index U32 (core.ops.range.Range Usize) 32#usize
    (core.ops.index.IndexSliceTIInst U32 (core.ops.range.Range Usize)
    (core.slice.index.SliceIndexRangeUsizeSliceTInst U32)) x
    { start := y, end_ := z }

/- [arrays::f3]:
   Source: 'src/arrays.rs', lines 275:0-275:18 -/
def f3 : Result U32 :=
  do
  let i ←
    Array.index_usize U32 2#usize (Array.make U32 2#usize [ 1#u32, 2#u32 ])
      0#usize
  let _ ← f2 i
  let b := Array.repeat U32 32#usize 0#u32
  let s ←
    Array.to_slice U32 2#usize (Array.make U32 2#usize [ 1#u32, 2#u32 ])
  let s1 ← f4 b 16#usize 18#usize
  sum2 s s1

/- [arrays::SZ]
   Source: 'src/arrays.rs', lines 286:0-286:19 -/
def SZ_body : Result Usize := Result.ret 32#usize
def SZ : Usize := eval_global SZ_body

/- [arrays::f5]:
   Source: 'src/arrays.rs', lines 289:0-289:31 -/
def f5 (x : Array U32 32#usize) : Result U32 :=
  Array.index_usize U32 32#usize x 0#usize

/- [arrays::ite]:
   Source: 'src/arrays.rs', lines 294:0-294:12 -/
def ite : Result Unit :=
  do
  let (s, to_slice_mut_back) ←
    Array.to_slice_mut U32 2#usize (Array.make U32 2#usize [ 0#u32, 0#u32 ])
  let (_, s1) ← index_mut_slice_u32_0 s
  let (s2, to_slice_mut_back1) ←
    Array.to_slice_mut U32 2#usize (Array.make U32 2#usize [ 0#u32, 0#u32 ])
  let (_, s3) ← index_mut_slice_u32_0 s2
  let _ ← to_slice_mut_back1 s3
  let _ ← to_slice_mut_back s1
  Result.ret ()

/- [arrays::zero_slice]: loop 0:
   Source: 'src/arrays.rs', lines 303:0-310:1 -/
divergent def zero_slice_loop
  (a : Slice U8) (i : Usize) (len : Usize) : Result (Slice U8) :=
  if i < len
  then
    do
    let (_, index_mut_back) ← Slice.index_mut_usize U8 a i
    let i1 ← i + 1#usize
    let a1 ← index_mut_back 0#u8
    zero_slice_loop a1 i1 len
  else Result.ret a

/- [arrays::zero_slice]:
   Source: 'src/arrays.rs', lines 303:0-303:31 -/
def zero_slice (a : Slice U8) : Result (Slice U8) :=
  let len := Slice.len U8 a
  zero_slice_loop a 0#usize len

/- [arrays::iter_mut_slice]: loop 0:
   Source: 'src/arrays.rs', lines 312:0-318:1 -/
divergent def iter_mut_slice_loop (len : Usize) (i : Usize) : Result Unit :=
  if i < len
  then do
       let i1 ← i + 1#usize
       iter_mut_slice_loop len i1
  else Result.ret ()

/- [arrays::iter_mut_slice]:
   Source: 'src/arrays.rs', lines 312:0-312:35 -/
def iter_mut_slice (a : Slice U8) : Result (Slice U8) :=
  do
  let len := Slice.len U8 a
  let _ ← iter_mut_slice_loop len 0#usize
  Result.ret a

/- [arrays::sum_mut_slice]: loop 0:
   Source: 'src/arrays.rs', lines 320:0-328:1 -/
divergent def sum_mut_slice_loop
  (a : Slice U32) (i : Usize) (s : U32) : Result U32 :=
  let i1 := Slice.len U32 a
  if i < i1
  then
    do
    let i2 ← Slice.index_usize U32 a i
    let s1 ← s + i2
    let i3 ← i + 1#usize
    sum_mut_slice_loop a i3 s1
  else Result.ret s

/- [arrays::sum_mut_slice]:
   Source: 'src/arrays.rs', lines 320:0-320:42 -/
def sum_mut_slice (a : Slice U32) : Result (U32 × (Slice U32)) :=
  do
  let i ← sum_mut_slice_loop a 0#usize 0#u32
  Result.ret (i, a)

end arrays
