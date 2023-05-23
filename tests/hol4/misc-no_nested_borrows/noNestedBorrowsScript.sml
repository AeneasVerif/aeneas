(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [no_nested_borrows] *)
open primitivesLib divDefLib

val _ = new_theory "noNestedBorrows"


Datatype:
  (** [no_nested_borrows::Pair] *)
  pair_t = <| pair_x : 't1; pair_y : 't2; |>
End

Datatype:
  (** [no_nested_borrows::List] *)
  list_t = | ListCons 't list_t | ListNil
End

Datatype:
  (** [no_nested_borrows::One] *)
  one_t = | OneOne 't1
End

Datatype:
  (** [no_nested_borrows::EmptyEnum] *)
  empty_enum_t = | EmptyEnumEmpty
End

Datatype:
  (** [no_nested_borrows::Enum] *)
  enum_t = | EnumVariant1 | EnumVariant2
End

Type empty_struct_t = “: unit”

Datatype:
  (** [no_nested_borrows::Sum] *)
  sum_t = | SumLeft 't1 | SumRight 't2
End

val neg_test_fwd_def = Define ‘
  (** [no_nested_borrows::neg_test] *)
  neg_test_fwd (x : i32) : i32 result =
    i32_neg x
’

val add_test_fwd_def = Define ‘
  (** [no_nested_borrows::add_test] *)
  add_test_fwd (x : u32) (y : u32) : u32 result =
    u32_add x y
’

val subs_test_fwd_def = Define ‘
  (** [no_nested_borrows::subs_test] *)
  subs_test_fwd (x : u32) (y : u32) : u32 result =
    u32_sub x y
’

val div_test_fwd_def = Define ‘
  (** [no_nested_borrows::div_test] *)
  div_test_fwd (x : u32) (y : u32) : u32 result =
    u32_div x y
’

val div_test1_fwd_def = Define ‘
  (** [no_nested_borrows::div_test1] *)
  div_test1_fwd (x : u32) : u32 result =
    u32_div x (int_to_u32 2)
’

val rem_test_fwd_def = Define ‘
  (** [no_nested_borrows::rem_test] *)
  rem_test_fwd (x : u32) (y : u32) : u32 result =
    u32_rem x y
’

val cast_test_fwd_def = Define ‘
  (** [no_nested_borrows::cast_test] *)
  cast_test_fwd (x : u32) : i32 result =
    mk_i32 (u32_to_int x)
’

val test2_fwd_def = Define ‘
  (** [no_nested_borrows::test2] *)
  test2_fwd : unit result =
    do
    _ <- u32_add (int_to_u32 23) (int_to_u32 44);
    Return ()
    od
’

(** Unit test for [no_nested_borrows::test2] *)
val _ = assert_return (“test2_fwd”)

val get_max_fwd_def = Define ‘
  (** [no_nested_borrows::get_max] *)
  get_max_fwd (x : u32) (y : u32) : u32 result =
    if u32_ge x y then Return x else Return y
’

val test3_fwd_def = Define ‘
  (** [no_nested_borrows::test3] *)
  test3_fwd : unit result =
    do
    x <- get_max_fwd (int_to_u32 4) (int_to_u32 3);
    y <- get_max_fwd (int_to_u32 10) (int_to_u32 11);
    z <- u32_add x y;
    if ~ (z = int_to_u32 15) then Fail Failure else Return ()
    od
’

(** Unit test for [no_nested_borrows::test3] *)
val _ = assert_return (“test3_fwd”)

val test_neg1_fwd_def = Define ‘
  (** [no_nested_borrows::test_neg1] *)
  test_neg1_fwd : unit result =
    do
    y <- i32_neg (int_to_i32 3);
    if ~ (y = int_to_i32 (-3)) then Fail Failure else Return ()
    od
’

(** Unit test for [no_nested_borrows::test_neg1] *)
val _ = assert_return (“test_neg1_fwd”)

val refs_test1_fwd_def = Define ‘
  (** [no_nested_borrows::refs_test1] *)
  refs_test1_fwd : unit result =
    if ~ (int_to_i32 1 = int_to_i32 1) then Fail Failure else Return ()
’

(** Unit test for [no_nested_borrows::refs_test1] *)
val _ = assert_return (“refs_test1_fwd”)

val refs_test2_fwd_def = Define ‘
  (** [no_nested_borrows::refs_test2] *)
  refs_test2_fwd : unit result =
    if ~ (int_to_i32 2 = int_to_i32 2)
    then Fail Failure
    else
      if ~ (int_to_i32 0 = int_to_i32 0)
      then Fail Failure
      else
        if ~ (int_to_i32 2 = int_to_i32 2)
        then Fail Failure
        else
          if ~ (int_to_i32 2 = int_to_i32 2) then Fail Failure else Return ()
’

(** Unit test for [no_nested_borrows::refs_test2] *)
val _ = assert_return (“refs_test2_fwd”)

val test_list1_fwd_def = Define ‘
  (** [no_nested_borrows::test_list1] *)
  test_list1_fwd : unit result =
    Return ()
’

(** Unit test for [no_nested_borrows::test_list1] *)
val _ = assert_return (“test_list1_fwd”)

val test_box1_fwd_def = Define ‘
  (** [no_nested_borrows::test_box1] *)
  test_box1_fwd : unit result =
    let b = int_to_i32 1 in
    let x = b in
    if ~ (x = int_to_i32 1) then Fail Failure else Return ()
’

(** Unit test for [no_nested_borrows::test_box1] *)
val _ = assert_return (“test_box1_fwd”)

val copy_int_fwd_def = Define ‘
  (** [no_nested_borrows::copy_int] *)
  copy_int_fwd (x : i32) : i32 result =
    Return x
’

val test_unreachable_fwd_def = Define ‘
  (** [no_nested_borrows::test_unreachable] *)
  test_unreachable_fwd (b : bool) : unit result =
    if b then Fail Failure else Return ()
’

val test_panic_fwd_def = Define ‘
  (** [no_nested_borrows::test_panic] *)
  test_panic_fwd (b : bool) : unit result =
    if b then Fail Failure else Return ()
’

val test_copy_int_fwd_def = Define ‘
  (** [no_nested_borrows::test_copy_int] *)
  test_copy_int_fwd : unit result =
    do
    y <- copy_int_fwd (int_to_i32 0);
    if ~ (int_to_i32 0 = y) then Fail Failure else Return ()
    od
’

(** Unit test for [no_nested_borrows::test_copy_int] *)
val _ = assert_return (“test_copy_int_fwd”)

val is_cons_fwd_def = Define ‘
  (** [no_nested_borrows::is_cons] *)
  is_cons_fwd (l : 't list_t) : bool result =
    (case l of | ListCons t l0 => Return T | ListNil => Return F)
’

val test_is_cons_fwd_def = Define ‘
  (** [no_nested_borrows::test_is_cons] *)
  test_is_cons_fwd : unit result =
    let l = ListNil in
    do
    b <- is_cons_fwd (ListCons (int_to_i32 0) l);
    if ~ b then Fail Failure else Return ()
    od
’

(** Unit test for [no_nested_borrows::test_is_cons] *)
val _ = assert_return (“test_is_cons_fwd”)

val split_list_fwd_def = Define ‘
  (** [no_nested_borrows::split_list] *)
  split_list_fwd (l : 't list_t) : ('t # 't list_t) result =
    (case l of | ListCons hd tl => Return (hd, tl) | ListNil => Fail Failure)
’

val test_split_list_fwd_def = Define ‘
  (** [no_nested_borrows::test_split_list] *)
  test_split_list_fwd : unit result =
    let l = ListNil in
    do
    p <- split_list_fwd (ListCons (int_to_i32 0) l);
    let (hd, _) = p in
    if ~ (hd = int_to_i32 0) then Fail Failure else Return ()
    od
’

(** Unit test for [no_nested_borrows::test_split_list] *)
val _ = assert_return (“test_split_list_fwd”)

val choose_fwd_def = Define ‘
  (** [no_nested_borrows::choose] *)
  choose_fwd (b : bool) (x : 't) (y : 't) : 't result =
    if b then Return x else Return y
’

val choose_back_def = Define ‘
  (** [no_nested_borrows::choose] *)
  choose_back (b : bool) (x : 't) (y : 't) (ret : 't) : ('t # 't) result =
    if b then Return (ret, y) else Return (x, ret)
’

val choose_test_fwd_def = Define ‘
  (** [no_nested_borrows::choose_test] *)
  choose_test_fwd : unit result =
    do
    z <- choose_fwd T (int_to_i32 0) (int_to_i32 0);
    z0 <- i32_add z (int_to_i32 1);
    if ~ (z0 = int_to_i32 1)
    then Fail Failure
    else (
      do
      (x, y) <- choose_back T (int_to_i32 0) (int_to_i32 0) z0;
      if ~ (x = int_to_i32 1)
      then Fail Failure
      else if ~ (y = int_to_i32 0) then Fail Failure else Return ()
      od)
    od
’

(** Unit test for [no_nested_borrows::choose_test] *)
val _ = assert_return (“choose_test_fwd”)

val test_char_fwd_def = Define ‘
  (** [no_nested_borrows::test_char] *)
  test_char_fwd : char result =
    Return #"a"
’

Datatype:
  (** [no_nested_borrows::NodeElem] *)
  node_elem_t = | NodeElemCons tree_t node_elem_t | NodeElemNil ;
  
  (** [no_nested_borrows::Tree] *)
  tree_t = | TreeLeaf 't | TreeNode 't node_elem_t tree_t
End

val [list_length_fwd_def] = DefineDiv ‘
  (** [no_nested_borrows::list_length] *)
  list_length_fwd (l : 't list_t) : u32 result =
    (case l of
    | ListCons t l1 => do
                       i <- list_length_fwd l1;
                       u32_add (int_to_u32 1) i
                       od
    | ListNil => Return (int_to_u32 0))
’

val [list_nth_shared_fwd_def] = DefineDiv ‘
  (** [no_nested_borrows::list_nth_shared] *)
  list_nth_shared_fwd (l : 't list_t) (i : u32) : 't result =
    (case l of
    | ListCons x tl =>
      if i = int_to_u32 0
      then Return x
      else (do
            i0 <- u32_sub i (int_to_u32 1);
            list_nth_shared_fwd tl i0
            od)
    | ListNil => Fail Failure)
’

val [list_nth_mut_fwd_def] = DefineDiv ‘
  (** [no_nested_borrows::list_nth_mut] *)
  list_nth_mut_fwd (l : 't list_t) (i : u32) : 't result =
    (case l of
    | ListCons x tl =>
      if i = int_to_u32 0
      then Return x
      else (do
            i0 <- u32_sub i (int_to_u32 1);
            list_nth_mut_fwd tl i0
            od)
    | ListNil => Fail Failure)
’

val [list_nth_mut_back_def] = DefineDiv ‘
  (** [no_nested_borrows::list_nth_mut] *)
  list_nth_mut_back (l : 't list_t) (i : u32) (ret : 't) : 't list_t result =
    (case l of
    | ListCons x tl =>
      if i = int_to_u32 0
      then Return (ListCons ret tl)
      else (
        do
        i0 <- u32_sub i (int_to_u32 1);
        tl0 <- list_nth_mut_back tl i0 ret;
        Return (ListCons x tl0)
        od)
    | ListNil => Fail Failure)
’

val [list_rev_aux_fwd_def] = DefineDiv ‘
  (** [no_nested_borrows::list_rev_aux] *)
  list_rev_aux_fwd (li : 't list_t) (lo : 't list_t) : 't list_t result =
    (case li of
    | ListCons hd tl => list_rev_aux_fwd tl (ListCons hd lo)
    | ListNil => Return lo)
’

val list_rev_fwd_back_def = Define ‘
  (** [no_nested_borrows::list_rev] *)
  list_rev_fwd_back (l : 't list_t) : 't list_t result =
    let li = mem_replace_fwd l ListNil in list_rev_aux_fwd li ListNil
’

val test_list_functions_fwd_def = Define ‘
  (** [no_nested_borrows::test_list_functions] *)
  test_list_functions_fwd : unit result =
    let l = ListNil in
    let l0 = ListCons (int_to_i32 2) l in
    let l1 = ListCons (int_to_i32 1) l0 in
    do
    i <- list_length_fwd (ListCons (int_to_i32 0) l1);
    if ~ (i = int_to_u32 3)
    then Fail Failure
    else (
      do
      i0 <- list_nth_shared_fwd (ListCons (int_to_i32 0) l1) (int_to_u32 0);
      if ~ (i0 = int_to_i32 0)
      then Fail Failure
      else (
        do
        i1 <- list_nth_shared_fwd (ListCons (int_to_i32 0) l1) (int_to_u32 1);
        if ~ (i1 = int_to_i32 1)
        then Fail Failure
        else (
          do
          i2 <-
            list_nth_shared_fwd (ListCons (int_to_i32 0) l1) (int_to_u32 2);
          if ~ (i2 = int_to_i32 2)
          then Fail Failure
          else (
            do
            ls <-
              list_nth_mut_back (ListCons (int_to_i32 0) l1) (int_to_u32 1)
                (int_to_i32 3);
            i3 <- list_nth_shared_fwd ls (int_to_u32 0);
            if ~ (i3 = int_to_i32 0)
            then Fail Failure
            else (
              do
              i4 <- list_nth_shared_fwd ls (int_to_u32 1);
              if ~ (i4 = int_to_i32 3)
              then Fail Failure
              else (
                do
                i5 <- list_nth_shared_fwd ls (int_to_u32 2);
                if ~ (i5 = int_to_i32 2) then Fail Failure else Return ()
                od)
              od)
            od)
          od)
        od)
      od)
    od
’

(** Unit test for [no_nested_borrows::test_list_functions] *)
val _ = assert_return (“test_list_functions_fwd”)

val id_mut_pair1_fwd_def = Define ‘
  (** [no_nested_borrows::id_mut_pair1] *)
  id_mut_pair1_fwd (x : 't1) (y : 't2) : ('t1 # 't2) result =
    Return (x, y)
’

val id_mut_pair1_back_def = Define ‘
  (** [no_nested_borrows::id_mut_pair1] *)
  id_mut_pair1_back
    (x : 't1) (y : 't2) (ret : ('t1 # 't2)) : ('t1 # 't2) result =
    let (t, t0) = ret in Return (t, t0)
’

val id_mut_pair2_fwd_def = Define ‘
  (** [no_nested_borrows::id_mut_pair2] *)
  id_mut_pair2_fwd (p : ('t1 # 't2)) : ('t1 # 't2) result =
    let (t, t0) = p in Return (t, t0)
’

val id_mut_pair2_back_def = Define ‘
  (** [no_nested_borrows::id_mut_pair2] *)
  id_mut_pair2_back
    (p : ('t1 # 't2)) (ret : ('t1 # 't2)) : ('t1 # 't2) result =
    let (t, t0) = ret in Return (t, t0)
’

val id_mut_pair3_fwd_def = Define ‘
  (** [no_nested_borrows::id_mut_pair3] *)
  id_mut_pair3_fwd (x : 't1) (y : 't2) : ('t1 # 't2) result =
    Return (x, y)
’

val id_mut_pair3_back'a_def = Define ‘
  (** [no_nested_borrows::id_mut_pair3] *)
  id_mut_pair3_back'a (x : 't1) (y : 't2) (ret : 't1) : 't1 result =
    Return ret
’

val id_mut_pair3_back'b_def = Define ‘
  (** [no_nested_borrows::id_mut_pair3] *)
  id_mut_pair3_back'b (x : 't1) (y : 't2) (ret : 't2) : 't2 result =
    Return ret
’

val id_mut_pair4_fwd_def = Define ‘
  (** [no_nested_borrows::id_mut_pair4] *)
  id_mut_pair4_fwd (p : ('t1 # 't2)) : ('t1 # 't2) result =
    let (t, t0) = p in Return (t, t0)
’

val id_mut_pair4_back'a_def = Define ‘
  (** [no_nested_borrows::id_mut_pair4] *)
  id_mut_pair4_back'a (p : ('t1 # 't2)) (ret : 't1) : 't1 result =
    Return ret
’

val id_mut_pair4_back'b_def = Define ‘
  (** [no_nested_borrows::id_mut_pair4] *)
  id_mut_pair4_back'b (p : ('t1 # 't2)) (ret : 't2) : 't2 result =
    Return ret
’

Datatype:
  (** [no_nested_borrows::StructWithTuple] *)
  struct_with_tuple_t = <| struct_with_tuple_p : ('t1 # 't2); |>
End

val new_tuple1_fwd_def = Define ‘
  (** [no_nested_borrows::new_tuple1] *)
  new_tuple1_fwd : (u32, u32) struct_with_tuple_t result =
    Return (<| struct_with_tuple_p := (int_to_u32 1, int_to_u32 2) |>)
’

val new_tuple2_fwd_def = Define ‘
  (** [no_nested_borrows::new_tuple2] *)
  new_tuple2_fwd : (i16, i16) struct_with_tuple_t result =
    Return (<| struct_with_tuple_p := (int_to_i16 1, int_to_i16 2) |>)
’

val new_tuple3_fwd_def = Define ‘
  (** [no_nested_borrows::new_tuple3] *)
  new_tuple3_fwd : (u64, i64) struct_with_tuple_t result =
    Return (<| struct_with_tuple_p := (int_to_u64 1, int_to_i64 2) |>)
’

Datatype:
  (** [no_nested_borrows::StructWithPair] *)
  struct_with_pair_t = <| struct_with_pair_p : ('t1, 't2) pair_t; |>
End

val new_pair1_fwd_def = Define ‘
  (** [no_nested_borrows::new_pair1] *)
  new_pair1_fwd : (u32, u32) struct_with_pair_t result =
    Return
    (<|
       struct_with_pair_p :=
         (<| pair_x := (int_to_u32 1); pair_y := (int_to_u32 2) |>)
       |>)
’

val test_constants_fwd_def = Define ‘
  (** [no_nested_borrows::test_constants] *)
  test_constants_fwd : unit result =
    do
    swt <- new_tuple1_fwd;
    let (i, _) = swt.struct_with_tuple_p in
    if ~ (i = int_to_u32 1)
    then Fail Failure
    else (
      do
      swt0 <- new_tuple2_fwd;
      let (i0, _) = swt0.struct_with_tuple_p in
      if ~ (i0 = int_to_i16 1)
      then Fail Failure
      else (
        do
        swt1 <- new_tuple3_fwd;
        let (i1, _) = swt1.struct_with_tuple_p in
        if ~ (i1 = int_to_u64 1)
        then Fail Failure
        else (
          do
          swp <- new_pair1_fwd;
          if ~ (swp.struct_with_pair_p.pair_x = int_to_u32 1)
          then Fail Failure
          else Return ()
          od)
        od)
      od)
    od
’

(** Unit test for [no_nested_borrows::test_constants] *)
val _ = assert_return (“test_constants_fwd”)

val test_weird_borrows1_fwd_def = Define ‘
  (** [no_nested_borrows::test_weird_borrows1] *)
  test_weird_borrows1_fwd : unit result =
    Return ()
’

(** Unit test for [no_nested_borrows::test_weird_borrows1] *)
val _ = assert_return (“test_weird_borrows1_fwd”)

val test_mem_replace_fwd_back_def = Define ‘
  (** [no_nested_borrows::test_mem_replace] *)
  test_mem_replace_fwd_back (px : u32) : u32 result =
    let y = mem_replace_fwd px (int_to_u32 1) in
    if ~ (y = int_to_u32 0) then Fail Failure else Return (int_to_u32 2)
’

val test_shared_borrow_bool1_fwd_def = Define ‘
  (** [no_nested_borrows::test_shared_borrow_bool1] *)
  test_shared_borrow_bool1_fwd (b : bool) : u32 result =
    if b then Return (int_to_u32 0) else Return (int_to_u32 1)
’

val test_shared_borrow_bool2_fwd_def = Define ‘
  (** [no_nested_borrows::test_shared_borrow_bool2] *)
  test_shared_borrow_bool2_fwd : u32 result =
    Return (int_to_u32 0)
’

val test_shared_borrow_enum1_fwd_def = Define ‘
  (** [no_nested_borrows::test_shared_borrow_enum1] *)
  test_shared_borrow_enum1_fwd (l : u32 list_t) : u32 result =
    (case l of
    | ListCons i l0 => Return (int_to_u32 1)
    | ListNil => Return (int_to_u32 0))
’

val test_shared_borrow_enum2_fwd_def = Define ‘
  (** [no_nested_borrows::test_shared_borrow_enum2] *)
  test_shared_borrow_enum2_fwd : u32 result =
    Return (int_to_u32 0)
’

val _ = export_theory ()
