(* Manually written examples of how to use the fixed-point operator from divDefScript *)

open primitivesLib divDefTheory

val _ = new_theory "divDefExample"

(* Rewrite the goal once, and on the left part of the goal seen as an application *)
fun pure_once_rewrite_left_tac ths =
  CONV_TAC (PATH_CONV "l" (PURE_ONCE_REWRITE_CONV ths))

(*=============================================
 * Example 1: nth (simply recursive function)
 *=============================================*)

Datatype:
  list_t =
    ListCons 't list_t
  | ListNil
End

(* We want to use the fixed-point operator ‘fix’ to define a function ‘nth’
   which satisfies the following equation: *)

val nth_qt = ‘
  nth (ls : 't list_t) (i : u32) : 't result =
    case ls of
    | ListCons x tl =>
      if u32_to_int i = (0:int)
      then (Return x)
      else
        do
        i0 <- u32_sub i (int_to_u32 1);
        nth tl i0
        od
    | ListNil => Fail Failure
’

(* When generating a recursive definition, we apply a fixed-point operator to a
   non-recursive function *body*, in which the recursive calls are handled to
   a continuation. In case we define a group of mutually recursive
   definitions, we generate *one* single body for the whole group of definitions.
   It works as follows.

   The input of the body is an enumeration: we start by branching over this input such
   that every branch corresponds to one function in the mutually recursive group.
   Whenever we make a recursive call, we wrap the input parameters into the proper
   variant before calling the continuation: in effect this allows us to choose
   the function from the group which gets evaluated.

   Moreover, because of constraints on the way the fixed-point operator is defined,
   the input of the body must have the same type as its output: we also
   store the outputs of the functions in this big enumeration.

   In order to make this work, we need to shape the body so that:
   - input values (at call sites) and output values (when returning) are properly
     injected into the enumeration
   - whenever we get an output value (which is an enumeration) from a recursive
     call, we extract the value from the proper variant of the enumeration

   We encode the enumeration with a nested sum type, whose constructors
   are ‘INL’ and ‘INR’.

   In the case of ‘nth’, we generate the encoding below, with the following
   peculiarities:
   - the input type is ‘: ('t list_t # u32) + 't’ the same as the output type
     (modulo the ‘:result’). ‘:'t list_t # u32’ is for the input value, while
     ‘t’ is for the output.
 *)

val nth_body_def = Define ‘
  nth_body
    (* The continuation is used for the recursive calls - this is required
       by the fixed-point operator *)
    (f : (('t list_t # u32) + 't) -> (('t list_t # u32) + 't) result)
    
    (* The input. Its type is: nth input type + nth output type *)
    (x : (('t list_t # u32) + 't)) :

    (* The output type is the same as the input type - this constraint
       comes from limitations in the way we can define the fixed-point
       operator inside the HOL logic *)
    (('t list_t # u32) + 't) result =

    (* Destruct the input. We need this to call the proper function in case
       of mutually recursive definitions, but also to eliminate arguments
       which correspond to the output value (the input type is the same
       as the output type). *)
    case x of
    | INL x => ( (* Input case: normal function call *)
      (* Body of nth *)
      let (ls, i) = x in
      case ls of
      | ListCons x tl =>
        if u32_to_int i = (0:int)
        then Return (INR x)
        else
          do
          i0 <- u32_sub i (int_to_u32 1);
          (* Recursive call: we call the continuation.

             We must wrap the input (here, in INL) then extract the
             proper output (this last part is really important in
             case of mutually recursive definitions).
           *)
          x <- (case f (INL (tl, i0)) of
                | Fail e => Fail e
                | Diverge => Diverge
                | Return r =>
                  case r of
                  | INL _ => Fail Failure
                  | INR x => Return x);

          (* Wrap the return value *)
          Return (INR x)
          od
      | ListNil => Fail Failure)
    | INR _ => (* Output case: invalid, we fail *)
      Fail Failure
’

(* Then, we prove that the body we just defined satisfies the validity property
   required by the fixed-point theorem.

   Remark:
   We first prove the theorem with ‘SUC (SUC n)’ where ‘n’ is a variable
   to prevent this quantity from being rewritten to 2 during the proofs. *)
Theorem nth_body_is_valid_aux:
  is_valid_fp_body (SUC (SUC n)) nth_body
Proof
  pure_once_rewrite_tac [is_valid_fp_body_def] >>
  gen_tac >>
  (* Expand *)
  fs [nth_body_def, bind_def] >>
  (* Simply explore all paths *)
  Cases_on ‘x’ >> fs [] >>
  Cases_on ‘x'’ >> fs [] >>
  Cases_on ‘q’ >> fs [] >>
  Cases_on ‘u32_to_int r = 0’ >> fs [] >>
  Cases_on ‘u32_sub r (int_to_u32 1)’ >> fs [] >>
  fs [case_result_switch_eq] >>
  (* Recursive call *)
  disj2_tac >>
  qexists ‘\g x. case case x of INL v => Fail Failure | INR x => Return x of
             Return x => Return (INR x)
           | Fail e => Fail e
           | Diverge => Diverge’ >>
  qexists ‘INL (l, a)’ >>
  conj_tac
  >-(pure_once_rewrite_tac [is_valid_fp_body_def] >> fs []) >>
  gen_tac >>
  (* Explore all paths *)
  Cases_on ‘g (INL (l,a))’ >> fs [] >>
  Cases_on ‘a'’ >> fs []
QED

Theorem nth_body_is_valid:
  is_valid_fp_body (SUC (SUC 0)) nth_body
Proof
  irule nth_body_is_valid_aux
QED

(* We can now define ‘nth’ in terms of the fixed-point operator applied to ‘nth_body’.

   Important points:
   - we apply ‘fix’ to ‘fix_body’
   - we wrap the input to take the proper branch (‘INL (ls, i)’)
   - we extract the output to have a function with the proper output type

   This definition satisfies the equation we want (see next theorem). *)
val nth_raw_def = Define ‘
  nth (ls : 't list_t) (i : u32) =
    case fix nth_body (INL (ls, i)) of
    | Fail e => Fail e
    | Diverge => Diverge
    | Return r =>
      case r of
      | INL _ => Fail Failure
      | INR x => Return x
’

(* We finally prove the target unfolding equation for ‘nth’ *)
Theorem nth_def:
  ∀ls i. nth (ls : 't list_t) (i : u32) : 't result =
    case ls of
    | ListCons x tl =>
      if u32_to_int i = (0:int)
      then (Return x)
      else
        do
        i0 <- u32_sub i (int_to_u32 1);
        nth tl i0
        od
    | ListNil => Fail Failure
Proof
  rpt strip_tac >>
  (* Expand the raw definition *)
  pure_rewrite_tac [nth_raw_def] >>
  (* Use the fixed-point equality - the rewrite must only be applied *on the left* of the equality, in the goal *)
  pure_once_rewrite_left_tac [HO_MATCH_MP fix_fixed_eq nth_body_is_valid] >>
  (* Expand the body definition *)
  pure_rewrite_tac [nth_body_def] >>
  (* Explore all the paths - maybe we can be smarter, but this is fast and really easy *)
  fs [bind_def] >>
  Cases_on ‘ls’ >> fs [] >>
  Cases_on ‘u32_to_int i = 0’ >> fs [] >>
  Cases_on ‘u32_sub i (int_to_u32 1)’ >> fs [] >>
  Cases_on ‘fix nth_body (INL (l,a))’ >> fs [] >>
  Cases_on ‘a'’ >> fs []
QED

(*=======================================================*
 * Example 2: even, odd (mutually recursive definitions)
 *=======================================================*)

(* We consider the following group of mutually recursive definitions: *)

val even_odd_qt = Defn.parse_quote ‘
 (even (i : int) : bool result = if i = 0 then Return T else odd (i - 1)) /\
 (odd (i : int) : bool result = if i = 0 then Return F else even (i - 1))
’

(* Similarly to ‘nth’, we need to introduce a body on which to apply the
   fixed-point operator. Here, the body is slightly more complex because
   we have mutually recursive functions.

   In particular, the input/output types is a sum of 4 types:
   input of even + output of even + input of odd + output of odd
   
   That is: ‘: int + bool + int + bool’

   As a consequence, the body is a case with 4 branches.
 *)

val even_odd_body_def = Define ‘
  even_odd_body
    (* The body takes a continuation - required by the fixed-point operator *)
    (f : (int + bool + int + bool) -> (int + bool + int + bool) result)

    (* The type of the input is:
       input of even + output of even + input of odd + output of odd *)
    (x : int + bool + int + bool) :

    (* The output type is the same as the input type - this constraint
       comes from limitations in the way we can define the fixed-point
       operator inside the HOL logic *)
    (int + bool + int + bool) result =

  (* Case disjunction over the input, in order to figure out which
     function from the group is actually called (even, or odd). *)
  case x of
  | INL i => (* Input of even *)
    (* Body of even *)
    if i = 0 then Return (INR (INL T))
    else
      (* Recursive calls are calls to the continuation f, wrapped
         in the proper variant: here we call odd *)
      (case f (INR (INR (INL (i - 1)))) of
       | Fail e => Fail e
       | Diverge => Diverge
       | Return r =>
         (* Extract the proper value from the enumeration: here, the
            call is tail-call so this is not really necessary, but we
            might need to retrieve the output of the call to odd, which
            is a boolean, and do something more complex with it. *)
         case r of
         | INL _ => Fail Failure
         | INR (INL _) => Fail Failure
         | INR (INR (INL _)) => Fail Failure
         | INR (INR (INR b)) => (* Extract the output of odd *)
           (* Return: inject into the variant for the output of even *)
           Return (INR (INL b))
         )
  | INR (INL _) => (* Output of even *)
    (* We must ignore this one *)
    Fail Failure
  | INR (INR (INL i)) =>
    (* Body of odd *)
    if i = 0 then Return (INR (INR (INR F)))
    else
      (* Call to even *)
      (case f (INL (i - 1)) of
       | Fail e => Fail e
       | Diverge => Diverge
       | Return r =>
         (* Extract the proper value from the enumeration *)
         case r of
         | INL _ => Fail Failure
         | INR (INL b) => (* Extract the output of even *)
           (* Return: inject into the variant for the output of odd *)
           Return (INR (INR (INR b)))
         | INR (INR (INL _)) => Fail Failure
         | INR (INR (INR _)) => Fail Failure
         )
  | INR (INR (INR _)) => (* Output of odd *)
    (* We must ignore this one *)
    Fail Failure
’

(* We then prove that this body satisfies the validity condition *)
Theorem even_odd_body_is_valid_aux:
  is_valid_fp_body (SUC (SUC n)) even_odd_body
Proof
  pure_once_rewrite_tac [is_valid_fp_body_def] >>
  gen_tac >>
  (* Expand *)
  fs [even_odd_body_def, bind_def] >>
  (* Explore the body *)
  Cases_on ‘x’ >> fs []
  >-(
    Cases_on ‘x' = 0’ >> fs [] >>
    (* Recursive call *)
    disj2_tac >>
    qexists ‘\g x. case x of
              | INL v => Fail Failure
              | INR (INL v2) => Fail Failure
              | INR (INR (INL v4)) => Fail Failure
              | INR (INR (INR b)) => Return (INR (INL b))’ >>
    qexists ‘INR (INR (INL (x' − 1)))’ >>
    conj_tac
    >-(pure_once_rewrite_tac [is_valid_fp_body_def] >> fs []) >>
    fs []) >>
  Cases_on ‘y’ >> fs [] >>
  Cases_on ‘y'’ >> fs [] >>
  Cases_on ‘x = 0’ >> fs []  >>
  (* Recursive call *)
  disj2_tac >>
  qexists ‘\g x. case x of
                   INL v => Fail Failure
                 | INR (INL b) => Return (INR (INR (INR b)))
                 | INR (INR v3) => Fail Failure’ >>
  qexists ‘INL (x − 1)’ >>
  conj_tac
  >-(pure_once_rewrite_tac [is_valid_fp_body_def] >> fs []) >>
  fs []
QED

Theorem even_odd_body_is_valid:
  is_valid_fp_body (SUC (SUC 0)) even_odd_body
Proof
  irule even_odd_body_is_valid_aux
QED

(* We finally introduce the definitions for even and odd *)
val even_raw_def = Define ‘
  even (i : int) =
    case fix even_odd_body (INL i) of
    | Fail e => Fail e
    | Diverge => Diverge
    | Return r =>
      case r of
      | INL _ => Fail Failure
      | INR (INL b) => Return b
      | INR (INR (INL b)) => Fail Failure
      | INR (INR (INR _)) => Fail Failure
’

val odd_raw_def = Define ‘
  odd (i : int) =
    case fix even_odd_body (INR (INR (INL i))) of
    | Fail e => Fail e
    | Diverge => Diverge
    | Return r =>
      case r of
      | INL _ => Fail Failure
      | INR (INL _) => Fail Failure
      | INR (INR (INL _)) => Fail Failure
      | INR (INR (INR b)) => Return b
’

Theorem even_def:
  ∀i. even (i : int) : bool result =
    if i = 0 then Return T else odd (i - 1)
Proof
  gen_tac >>
  (* Expand the definition *)
  pure_once_rewrite_tac [even_raw_def] >>
  (* Use the fixed-point equality *)
  pure_once_rewrite_left_tac [HO_MATCH_MP fix_fixed_eq even_odd_body_is_valid] >>
  (* Expand the body definition *)
  pure_rewrite_tac [even_odd_body_def] >>
  (* Expand all the definitions from the group *)
  pure_rewrite_tac [even_raw_def, odd_raw_def] >>
  (* Explore all the paths - maybe we can be smarter, but this is fast and really easy *)
  fs [bind_def] >>
  Cases_on ‘i = 0’ >> fs [] >>
  Cases_on ‘fix even_odd_body (INR (INR (INL (i − 1))))’ >> fs [] >>
  Cases_on ‘a’ >> fs [] >>
  Cases_on ‘y’ >> fs [] >>
  Cases_on ‘y'’ >> fs []
QED

Theorem odd_def:
  ∀i. odd (i : int) : bool result =
    if i = 0 then Return F else even (i - 1)
Proof
  gen_tac >>
  (* Expand the definition *)
  pure_once_rewrite_tac [odd_raw_def] >>
  (* Use the fixed-point equality *)
  pure_once_rewrite_left_tac [HO_MATCH_MP fix_fixed_eq even_odd_body_is_valid] >>
  (* Expand the body definition *)
  pure_rewrite_tac [even_odd_body_def] >>
  (* Expand all the definitions from the group *)
  pure_rewrite_tac [even_raw_def, odd_raw_def] >>
  (* Explore all the paths - maybe we can be smarter, but this is fast and really easy *)
  fs [bind_def] >>
  Cases_on ‘i = 0’ >> fs [] >>
  Cases_on ‘fix even_odd_body (INL (i − 1))’ >> fs [] >>
  Cases_on ‘a’ >> fs [] >>
  Cases_on ‘y’ >> fs []
QED

val _ = export_theory ()
