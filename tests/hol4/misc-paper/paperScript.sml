(** [paper] *)
open primitivesLib divDefLib

val _ = new_theory "paper"


val ref_incr_fwd_back_def = Define ‘
  (** [paper::ref_incr]: merged forward/backward function
      (there is a single backward function, and the forward function returns ()) *)
  ref_incr_fwd_back (x : i32) : i32 result =
    i32_add x (int_to_i32 1)
’

val test_incr_fwd_def = Define ‘
  (** [paper::test_incr]: forward function *)
  test_incr_fwd : unit result =
    do
    x <- ref_incr_fwd_back (int_to_i32 0);
    if ~ (x = int_to_i32 1) then Fail Failure else Return ()
    od
’

(** Unit test for [paper::test_incr] *)
val _ = assert_return (“test_incr_fwd”)

val choose_fwd_def = Define ‘
  (** [paper::choose]: forward function *)
  choose_fwd (b : bool) (x : 't) (y : 't) : 't result =
    if b then Return x else Return y
’

val choose_back_def = Define ‘
  (** [paper::choose]: backward function 0 *)
  choose_back (b : bool) (x : 't) (y : 't) (ret : 't) : ('t # 't) result =
    if b then Return (ret, y) else Return (x, ret)
’

val test_choose_fwd_def = Define ‘
  (** [paper::test_choose]: forward function *)
  test_choose_fwd : unit result =
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

(** Unit test for [paper::test_choose] *)
val _ = assert_return (“test_choose_fwd”)

Datatype:
  (** [paper::List] *)
  list_t = | ListCons 't list_t | ListNil
End

val [list_nth_mut_fwd_def] = DefineDiv ‘
  (** [paper::list_nth_mut]: forward function *)
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
  (** [paper::list_nth_mut]: backward function 0 *)
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

val [sum_fwd_def] = DefineDiv ‘
  (** [paper::sum]: forward function *)
  sum_fwd (l : i32 list_t) : i32 result =
    (case l of
    | ListCons x tl => do
                       i <- sum_fwd tl;
                       i32_add x i
                       od
    | ListNil => Return (int_to_i32 0))
’

val test_nth_fwd_def = Define ‘
  (** [paper::test_nth]: forward function *)
  test_nth_fwd : unit result =
    let l = ListNil in
    let l0 = ListCons (int_to_i32 3) l in
    let l1 = ListCons (int_to_i32 2) l0 in
    do
    x <- list_nth_mut_fwd (ListCons (int_to_i32 1) l1) (int_to_u32 2);
    x0 <- i32_add x (int_to_i32 1);
    l2 <- list_nth_mut_back (ListCons (int_to_i32 1) l1) (int_to_u32 2) x0;
    i <- sum_fwd l2;
    if ~ (i = int_to_i32 7) then Fail Failure else Return ()
    od
’

(** Unit test for [paper::test_nth] *)
val _ = assert_return (“test_nth_fwd”)

val call_choose_fwd_def = Define ‘
  (** [paper::call_choose]: forward function *)
  call_choose_fwd (p : (u32 # u32)) : u32 result =
    let (px, py) = p in
    do
    pz <- choose_fwd T px py;
    pz0 <- u32_add pz (int_to_u32 1);
    (px0, _) <- choose_back T px py pz0;
    Return px0
    od
’

val _ = export_theory ()
