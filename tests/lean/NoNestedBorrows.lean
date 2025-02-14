-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [no_nested_borrows]
import Aeneas
open Aeneas.Std
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace no_nested_borrows

/- [no_nested_borrows::Pair]
   Source: 'tests/src/no_nested_borrows.rs', lines 7:0-10:1 -/
structure Pair (T1 : Type) (T2 : Type) where
  x : T1
  y : T2

/- [no_nested_borrows::List]
   Source: 'tests/src/no_nested_borrows.rs', lines 12:0-15:1 -/
inductive List (T : Type) where
| Cons : T → List T → List T
| Nil : List T

/- [no_nested_borrows::One]
   Source: 'tests/src/no_nested_borrows.rs', lines 23:0-25:1 -/
inductive One (T1 : Type) where
| One : T1 → One T1

/- [no_nested_borrows::EmptyEnum]
   Source: 'tests/src/no_nested_borrows.rs', lines 29:0-31:1 -/
inductive EmptyEnum where
| Empty : EmptyEnum

/- [no_nested_borrows::Enum]
   Source: 'tests/src/no_nested_borrows.rs', lines 35:0-38:1 -/
inductive Enum where
| Variant1 : Enum
| Variant2 : Enum

/- [no_nested_borrows::EmptyStruct]
   Source: 'tests/src/no_nested_borrows.rs', lines 42:0-42:25 -/
@[reducible] def EmptyStruct := Unit

/- [no_nested_borrows::Sum]
   Source: 'tests/src/no_nested_borrows.rs', lines 44:0-47:1 -/
inductive Sum (T1 : Type) (T2 : Type) where
| Left : T1 → Sum T1 T2
| Right : T2 → Sum T1 T2

/- [no_nested_borrows::cast_u32_to_i32]:
   Source: 'tests/src/no_nested_borrows.rs', lines 49:0-51:1 -/
def cast_u32_to_i32 (x : U32) : Result I32 :=
  Scalar.cast .I32 x

/- [no_nested_borrows::cast_bool_to_i32]:
   Source: 'tests/src/no_nested_borrows.rs', lines 53:0-55:1 -/
def cast_bool_to_i32 (x : Bool) : Result I32 :=
  Scalar.cast_bool .I32 x

/- [no_nested_borrows::cast_bool_to_bool]:
   Source: 'tests/src/no_nested_borrows.rs', lines 58:0-60:1 -/
def cast_bool_to_bool (x : Bool) : Result Bool :=
  Result.ok x

/- [no_nested_borrows::test2]:
   Source: 'tests/src/no_nested_borrows.rs', lines 63:0-73:1 -/
def test2 : Result Unit :=
  do
  let _ ← 23#u32 + 44#u32
  Result.ok ()

/- Unit test for [no_nested_borrows::test2] -/
#assert (test2 == Result.ok ())

/- [no_nested_borrows::get_max]:
   Source: 'tests/src/no_nested_borrows.rs', lines 75:0-81:1 -/
def get_max (x : U32) (y : U32) : Result U32 :=
  if x >= y
  then Result.ok x
  else Result.ok y

/- [no_nested_borrows::test3]:
   Source: 'tests/src/no_nested_borrows.rs', lines 83:0-88:1 -/
def test3 : Result Unit :=
  do
  let x ← get_max 4#u32 3#u32
  let y ← get_max 10#u32 11#u32
  let z ← x + y
  massert (z = 15#u32)

/- Unit test for [no_nested_borrows::test3] -/
#assert (test3 == Result.ok ())

/- [no_nested_borrows::test_neg1]:
   Source: 'tests/src/no_nested_borrows.rs', lines 90:0-94:1 -/
def test_neg1 : Result Unit :=
  do
  let y ← -. 3#i32
  massert (y = (-3)#i32)

/- Unit test for [no_nested_borrows::test_neg1] -/
#assert (test_neg1 == Result.ok ())

/- [no_nested_borrows::refs_test1]:
   Source: 'tests/src/no_nested_borrows.rs', lines 97:0-106:1 -/
def refs_test1 : Result Unit :=
  massert (1#i32 = 1#i32)

/- Unit test for [no_nested_borrows::refs_test1] -/
#assert (refs_test1 == Result.ok ())

/- [no_nested_borrows::refs_test2]:
   Source: 'tests/src/no_nested_borrows.rs', lines 108:0-120:1 -/
def refs_test2 : Result Unit :=
  do
  massert (2#i32 = 2#i32)
  massert (0#i32 = 0#i32)
  massert (2#i32 = 2#i32)
  massert (2#i32 = 2#i32)

/- Unit test for [no_nested_borrows::refs_test2] -/
#assert (refs_test2 == Result.ok ())

/- [no_nested_borrows::test_list1]:
   Source: 'tests/src/no_nested_borrows.rs', lines 124:0-126:1 -/
def test_list1 : Result Unit :=
  Result.ok ()

/- Unit test for [no_nested_borrows::test_list1] -/
#assert (test_list1 == Result.ok ())

/- [no_nested_borrows::test_box1]:
   Source: 'tests/src/no_nested_borrows.rs', lines 129:0-137:1 -/
def test_box1 : Result Unit :=
  do
  let (_, deref_mut_back) ← alloc.boxed.Box.deref_mut 0#i32
  let b := deref_mut_back 1#i32
  let x ← alloc.boxed.Box.deref b
  massert (x = 1#i32)

/- Unit test for [no_nested_borrows::test_box1] -/
#assert (test_box1 == Result.ok ())

/- [no_nested_borrows::copy_int]:
   Source: 'tests/src/no_nested_borrows.rs', lines 139:0-141:1 -/
def copy_int (x : I32) : Result I32 :=
  Result.ok x

/- [no_nested_borrows::test_unreachable]:
   Source: 'tests/src/no_nested_borrows.rs', lines 145:0-149:1 -/
def test_unreachable (b : Bool) : Result Unit :=
  massert b

/- [no_nested_borrows::test_panic]:
   Source: 'tests/src/no_nested_borrows.rs', lines 152:0-156:1 -/
def test_panic (b : Bool) : Result Unit :=
  massert b

/- [no_nested_borrows::test_panic_msg]:
   Source: 'tests/src/no_nested_borrows.rs', lines 160:0-164:1 -/
def test_panic_msg (b : Bool) : Result Unit :=
  massert b

/- [no_nested_borrows::test_copy_int]:
   Source: 'tests/src/no_nested_borrows.rs', lines 167:0-172:1 -/
def test_copy_int : Result Unit :=
  do
  let y ← copy_int 0#i32
  massert (0#i32 = y)

/- Unit test for [no_nested_borrows::test_copy_int] -/
#assert (test_copy_int == Result.ok ())

/- [no_nested_borrows::is_cons]:
   Source: 'tests/src/no_nested_borrows.rs', lines 174:0-179:1 -/
def is_cons {T : Type} (l : List T) : Result Bool :=
  match l with
  | List.Cons _ _ => Result.ok true
  | List.Nil => Result.ok false

/- [no_nested_borrows::test_is_cons]:
   Source: 'tests/src/no_nested_borrows.rs', lines 181:0-185:1 -/
def test_is_cons : Result Unit :=
  do
  let b ← is_cons (List.Cons 0#i32 List.Nil)
  massert b

/- Unit test for [no_nested_borrows::test_is_cons] -/
#assert (test_is_cons == Result.ok ())

/- [no_nested_borrows::split_list]:
   Source: 'tests/src/no_nested_borrows.rs', lines 187:0-192:1 -/
def split_list {T : Type} (l : List T) : Result (T × (List T)) :=
  match l with
  | List.Cons hd tl => Result.ok (hd, tl)
  | List.Nil => Result.fail .panic

/- [no_nested_borrows::test_split_list]:
   Source: 'tests/src/no_nested_borrows.rs', lines 195:0-200:1 -/
def test_split_list : Result Unit :=
  do
  let p ← split_list (List.Cons 0#i32 List.Nil)
  let (hd, _) := p
  massert (hd = 0#i32)

/- Unit test for [no_nested_borrows::test_split_list] -/
#assert (test_split_list == Result.ok ())

/- [no_nested_borrows::choose]:
   Source: 'tests/src/no_nested_borrows.rs', lines 202:0-208:1 -/
def choose
  {T : Type} (b : Bool) (x : T) (y : T) : Result (T × (T → (T × T))) :=
  if b
  then let back := fun ret => (ret, y)
       Result.ok (x, back)
  else let back := fun ret => (x, ret)
       Result.ok (y, back)

/- [no_nested_borrows::choose_test]:
   Source: 'tests/src/no_nested_borrows.rs', lines 210:0-219:1 -/
def choose_test : Result Unit :=
  do
  let (z, choose_back) ← choose true 0#i32 0#i32
  let z1 ← z + 1#i32
  massert (z1 = 1#i32)
  let (x, y) := choose_back z1
  massert (x = 1#i32)
  massert (y = 0#i32)

/- Unit test for [no_nested_borrows::choose_test] -/
#assert (choose_test == Result.ok ())

/- [no_nested_borrows::test_char]:
   Source: 'tests/src/no_nested_borrows.rs', lines 222:0-224:1 -/
def test_char : Result Char :=
  Result.ok 'a'

/- [no_nested_borrows::panic_mut_borrow]:
   Source: 'tests/src/no_nested_borrows.rs', lines 227:0-229:1 -/
def panic_mut_borrow (i : U32) : Result U32 :=
  Result.fail .panic

mutual

/- [no_nested_borrows::Tree]
   Source: 'tests/src/no_nested_borrows.rs', lines 232:0-235:1 -/
inductive Tree (T : Type) where
| Leaf : T → Tree T
| Node : T → NodeElem T → Tree T → Tree T

/- [no_nested_borrows::NodeElem]
   Source: 'tests/src/no_nested_borrows.rs', lines 237:0-240:1 -/
inductive NodeElem (T : Type) where
| Cons : Tree T → NodeElem T → NodeElem T
| Nil : NodeElem T

end

/- [no_nested_borrows::list_length]:
   Source: 'tests/src/no_nested_borrows.rs', lines 272:0-277:1 -/
divergent def list_length {T : Type} (l : List T) : Result U32 :=
  match l with
  | List.Cons _ l1 => do
                      let i ← list_length l1
                      1#u32 + i
  | List.Nil => Result.ok 0#u32

/- [no_nested_borrows::list_nth_shared]:
   Source: 'tests/src/no_nested_borrows.rs', lines 280:0-293:1 -/
divergent def list_nth_shared {T : Type} (l : List T) (i : U32) : Result T :=
  match l with
  | List.Cons x tl =>
    if i = 0#u32
    then Result.ok x
    else do
         let i1 ← i - 1#u32
         list_nth_shared tl i1
  | List.Nil => Result.fail .panic

/- [no_nested_borrows::list_nth_mut]:
   Source: 'tests/src/no_nested_borrows.rs', lines 296:0-309:1 -/
divergent def list_nth_mut
  {T : Type} (l : List T) (i : U32) : Result (T × (T → List T)) :=
  match l with
  | List.Cons x tl =>
    if i = 0#u32
    then let back := fun ret => List.Cons ret tl
         Result.ok (x, back)
    else
      do
      let i1 ← i - 1#u32
      let (t, list_nth_mut_back) ← list_nth_mut tl i1
      let back := fun ret => let tl1 := list_nth_mut_back ret
                             List.Cons x tl1
      Result.ok (t, back)
  | List.Nil => Result.fail .panic

/- [no_nested_borrows::list_rev_aux]:
   Source: 'tests/src/no_nested_borrows.rs', lines 312:0-322:1 -/
divergent def list_rev_aux
  {T : Type} (li : List T) (lo : List T) : Result (List T) :=
  match li with
  | List.Cons hd tl => list_rev_aux tl (List.Cons hd lo)
  | List.Nil => Result.ok lo

/- [no_nested_borrows::list_rev]:
   Source: 'tests/src/no_nested_borrows.rs', lines 326:0-329:1 -/
def list_rev {T : Type} (l : List T) : Result (List T) :=
  let (li, _) := core.mem.replace l List.Nil
  list_rev_aux li List.Nil

/- [no_nested_borrows::test_list_functions]:
   Source: 'tests/src/no_nested_borrows.rs', lines 331:0-345:1 -/
def test_list_functions : Result Unit :=
  do
  let l := List.Cons 2#i32 List.Nil
  let l1 := List.Cons 1#i32 l
  let i ← list_length (List.Cons 0#i32 l1)
  massert (i = 3#u32)
  let i1 ← list_nth_shared (List.Cons 0#i32 l1) 0#u32
  massert (i1 = 0#i32)
  let i2 ← list_nth_shared (List.Cons 0#i32 l1) 1#u32
  massert (i2 = 1#i32)
  let i3 ← list_nth_shared (List.Cons 0#i32 l1) 2#u32
  massert (i3 = 2#i32)
  let (_, list_nth_mut_back) ← list_nth_mut (List.Cons 0#i32 l1) 1#u32
  let ls := list_nth_mut_back 3#i32
  let i4 ← list_nth_shared ls 0#u32
  massert (i4 = 0#i32)
  let i5 ← list_nth_shared ls 1#u32
  massert (i5 = 3#i32)
  let i6 ← list_nth_shared ls 2#u32
  massert (i6 = 2#i32)

/- Unit test for [no_nested_borrows::test_list_functions] -/
#assert (test_list_functions == Result.ok ())

/- [no_nested_borrows::id_mut_pair1]:
   Source: 'tests/src/no_nested_borrows.rs', lines 347:0-349:1 -/
def id_mut_pair1
  {T1 : Type} {T2 : Type} (x : T1) (y : T2) :
  Result ((T1 × T2) × ((T1 × T2) → (T1 × T2)))
  :=
  Result.ok ((x, y), fun ret => ret)

/- [no_nested_borrows::id_mut_pair2]:
   Source: 'tests/src/no_nested_borrows.rs', lines 351:0-353:1 -/
def id_mut_pair2
  {T1 : Type} {T2 : Type} (p : (T1 × T2)) :
  Result ((T1 × T2) × ((T1 × T2) → (T1 × T2)))
  :=
  Result.ok (p, fun ret => ret)

/- [no_nested_borrows::id_mut_pair3]:
   Source: 'tests/src/no_nested_borrows.rs', lines 355:0-357:1 -/
def id_mut_pair3
  {T1 : Type} {T2 : Type} (x : T1) (y : T2) :
  Result ((T1 × T2) × (T1 → T1) × (T2 → T2))
  :=
  Result.ok ((x, y), fun ret => ret, fun ret => ret)

/- [no_nested_borrows::id_mut_pair4]:
   Source: 'tests/src/no_nested_borrows.rs', lines 359:0-361:1 -/
def id_mut_pair4
  {T1 : Type} {T2 : Type} (p : (T1 × T2)) :
  Result ((T1 × T2) × (T1 → T1) × (T2 → T2))
  :=
  Result.ok (p, fun ret => ret, fun ret => ret)

/- [no_nested_borrows::StructWithTuple]
   Source: 'tests/src/no_nested_borrows.rs', lines 366:0-368:1 -/
structure StructWithTuple (T1 : Type) (T2 : Type) where
  p : (T1 × T2)

/- [no_nested_borrows::new_tuple1]:
   Source: 'tests/src/no_nested_borrows.rs', lines 370:0-372:1 -/
def new_tuple1 : Result (StructWithTuple U32 U32) :=
  Result.ok { p := (1#u32, 2#u32) }

/- [no_nested_borrows::new_tuple2]:
   Source: 'tests/src/no_nested_borrows.rs', lines 374:0-376:1 -/
def new_tuple2 : Result (StructWithTuple I16 I16) :=
  Result.ok { p := (1#i16, 2#i16) }

/- [no_nested_borrows::new_tuple3]:
   Source: 'tests/src/no_nested_borrows.rs', lines 378:0-380:1 -/
def new_tuple3 : Result (StructWithTuple U64 I64) :=
  Result.ok { p := (1#u64, 2#i64) }

/- [no_nested_borrows::StructWithPair]
   Source: 'tests/src/no_nested_borrows.rs', lines 383:0-385:1 -/
structure StructWithPair (T1 : Type) (T2 : Type) where
  p : Pair T1 T2

/- [no_nested_borrows::new_pair1]:
   Source: 'tests/src/no_nested_borrows.rs', lines 387:0-393:1 -/
def new_pair1 : Result (StructWithPair U32 U32) :=
  Result.ok { p := { x := 1#u32, y := 2#u32 } }

/- [no_nested_borrows::test_constants]:
   Source: 'tests/src/no_nested_borrows.rs', lines 395:0-400:1 -/
def test_constants : Result Unit :=
  do
  let swt ← new_tuple1
  let (i, _) := swt.p
  massert (i = 1#u32)
  let swt1 ← new_tuple2
  let (i1, _) := swt1.p
  massert (i1 = 1#i16)
  let swt2 ← new_tuple3
  let (i2, _) := swt2.p
  massert (i2 = 1#u64)
  let swp ← new_pair1
  massert (swp.p.x = 1#u32)

/- Unit test for [no_nested_borrows::test_constants] -/
#assert (test_constants == Result.ok ())

/- [no_nested_borrows::test_weird_borrows1]:
   Source: 'tests/src/no_nested_borrows.rs', lines 404:0-412:1 -/
def test_weird_borrows1 : Result Unit :=
  Result.ok ()

/- Unit test for [no_nested_borrows::test_weird_borrows1] -/
#assert (test_weird_borrows1 == Result.ok ())

/- [no_nested_borrows::test_mem_replace]:
   Source: 'tests/src/no_nested_borrows.rs', lines 414:0-418:1 -/
def test_mem_replace (px : U32) : Result U32 :=
  do
  let (y, _) := core.mem.replace px 1#u32
  massert (y = 0#u32)
  Result.ok 2#u32

/- [no_nested_borrows::test_shared_borrow_bool1]:
   Source: 'tests/src/no_nested_borrows.rs', lines 421:0-430:1 -/
def test_shared_borrow_bool1 (b : Bool) : Result U32 :=
  if b
  then Result.ok 0#u32
  else Result.ok 1#u32

/- [no_nested_borrows::test_shared_borrow_bool2]:
   Source: 'tests/src/no_nested_borrows.rs', lines 434:0-444:1 -/
def test_shared_borrow_bool2 : Result U32 :=
  Result.ok 0#u32

/- [no_nested_borrows::test_shared_borrow_enum1]:
   Source: 'tests/src/no_nested_borrows.rs', lines 449:0-457:1 -/
def test_shared_borrow_enum1 (l : List U32) : Result U32 :=
  match l with
  | List.Cons _ _ => Result.ok 1#u32
  | List.Nil => Result.ok 0#u32

/- [no_nested_borrows::test_shared_borrow_enum2]:
   Source: 'tests/src/no_nested_borrows.rs', lines 461:0-470:1 -/
def test_shared_borrow_enum2 : Result U32 :=
  Result.ok 0#u32

/- [no_nested_borrows::incr]:
   Source: 'tests/src/no_nested_borrows.rs', lines 472:0-474:1 -/
def incr (x : U32) : Result U32 :=
  x + 1#u32

/- [no_nested_borrows::call_incr]:
   Source: 'tests/src/no_nested_borrows.rs', lines 476:0-479:1 -/
def call_incr (x : U32) : Result U32 :=
  incr x

/- [no_nested_borrows::read_then_incr]:
   Source: 'tests/src/no_nested_borrows.rs', lines 481:0-485:1 -/
def read_then_incr (x : U32) : Result (U32 × U32) :=
  do
  let x1 ← x + 1#u32
  Result.ok (x, x1)

/- [no_nested_borrows::Tuple]
   Source: 'tests/src/no_nested_borrows.rs', lines 487:0-487:33 -/
def Tuple (T1 : Type) (T2 : Type) := T1 × T2

/- [no_nested_borrows::read_tuple]:
   Source: 'tests/src/no_nested_borrows.rs', lines 489:0-491:1 -/
def read_tuple (x : (U32 × U32)) : Result U32 :=
  let (i, _) := x
  Result.ok i

/- [no_nested_borrows::update_tuple]:
   Source: 'tests/src/no_nested_borrows.rs', lines 493:0-495:1 -/
def update_tuple (x : (U32 × U32)) : Result (U32 × U32) :=
  let (_, i) := x
  Result.ok (1#u32, i)

/- [no_nested_borrows::read_tuple_struct]:
   Source: 'tests/src/no_nested_borrows.rs', lines 497:0-499:1 -/
def read_tuple_struct (x : Tuple U32 U32) : Result U32 :=
  let (i, _) := x
  Result.ok i

/- [no_nested_borrows::update_tuple_struct]:
   Source: 'tests/src/no_nested_borrows.rs', lines 501:0-503:1 -/
def update_tuple_struct (x : Tuple U32 U32) : Result (Tuple U32 U32) :=
  let (_, i) := x
  Result.ok (1#u32, i)

/- [no_nested_borrows::create_tuple_struct]:
   Source: 'tests/src/no_nested_borrows.rs', lines 505:0-507:1 -/
def create_tuple_struct (x : U32) (y : U64) : Result (Tuple U32 U64) :=
  Result.ok (x, y)

/- [no_nested_borrows::IdType]
   Source: 'tests/src/no_nested_borrows.rs', lines 510:0-510:24 -/
@[reducible] def IdType (T : Type) := T

/- [no_nested_borrows::use_id_type]:
   Source: 'tests/src/no_nested_borrows.rs', lines 512:0-514:1 -/
def use_id_type {T : Type} (x : IdType T) : Result T :=
  Result.ok x

/- [no_nested_borrows::create_id_type]:
   Source: 'tests/src/no_nested_borrows.rs', lines 516:0-518:1 -/
def create_id_type {T : Type} (x : T) : Result (IdType T) :=
  Result.ok x

/- [no_nested_borrows::not_bool]:
   Source: 'tests/src/no_nested_borrows.rs', lines 520:0-522:1 -/
def not_bool (x : Bool) : Result Bool :=
  Result.ok (~~~ x)

/- [no_nested_borrows::not_u32]:
   Source: 'tests/src/no_nested_borrows.rs', lines 524:0-526:1 -/
def not_u32 (x : U32) : Result U32 :=
  Result.ok (~~~ x)

/- [no_nested_borrows::not_i32]:
   Source: 'tests/src/no_nested_borrows.rs', lines 528:0-530:1 -/
def not_i32 (x : I32) : Result I32 :=
  Result.ok (~~~ x)

/- [no_nested_borrows::borrow_mut_tuple]:
   Source: 'tests/src/no_nested_borrows.rs', lines 532:0-534:1 -/
def borrow_mut_tuple
  {T : Type} {U : Type} (x : (T × U)) :
  Result ((T × U) × ((T × U) → (T × U)))
  :=
  Result.ok (x, fun ret => ret)

/- [no_nested_borrows::ExpandSimpliy::Wrapper]
   Source: 'tests/src/no_nested_borrows.rs', lines 538:4-538:32 -/
def ExpandSimpliy.Wrapper (T : Type) := T × T

/- [no_nested_borrows::ExpandSimpliy::check_expand_simplify_symb1]:
   Source: 'tests/src/no_nested_borrows.rs', lines 540:4-546:5 -/
def ExpandSimpliy.check_expand_simplify_symb1
  (x : ExpandSimpliy.Wrapper Bool) : Result (ExpandSimpliy.Wrapper Bool) :=
  let (b, _) := x
  if b
  then Result.ok x
  else Result.ok x

/- [no_nested_borrows::ExpandSimpliy::Wrapper2]
   Source: 'tests/src/no_nested_borrows.rs', lines 548:4-551:5 -/
structure ExpandSimpliy.Wrapper2 where
  b : Bool
  x : U32

/- [no_nested_borrows::ExpandSimpliy::check_expand_simplify_symb2]:
   Source: 'tests/src/no_nested_borrows.rs', lines 553:4-559:5 -/
def ExpandSimpliy.check_expand_simplify_symb2
  (x : ExpandSimpliy.Wrapper2) : Result ExpandSimpliy.Wrapper2 :=
  if x.b
  then Result.ok x
  else Result.ok x

end no_nested_borrows
