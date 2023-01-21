open HolKernel boolLib bossLib Parse

val primitives_theory_name = "Primitives"
val _ = new_theory primitives_theory_name

(* SML declarations  *)
(* for example: *)
(*val th = save_thm("SKOLEM_AGAIN",SKOLEM_THM) *)

local open boolTheory integerTheory wordsTheory stringTheory in end

Datatype:
  error = Failure
End

Datatype:
  result = Return 'a | Fail error | Loop
End

Type M = ``: 'a result``

(* TODO: rename *)
val st_ex_bind_def = Define `
  (st_ex_bind : 'a M -> ('a -> 'b M) -> 'b M) x f =
    case x of
      Return y => f y
    | Fail e => Fail e
    | Loop => Loop`;

val bind_name = fst (dest_const “st_ex_bind”)

val st_ex_return_def = Define `
  (st_ex_return : 'a -> 'a M) x =
    Return x`;

Overload monad_bind[local] = ``st_ex_bind``
Overload monad_unitbind[local] = ``\x y. st_ex_bind x (\z. y)``
Overload monad_ignore_bind[local] = ``\x y. st_ex_bind x (\z. y)``
(*Overload ex_bind[local] = ``st_ex_bind`` *)
(* Overload ex_return[local] = ``st_ex_return`` *)
(*Overload failwith = ``raise_Fail``*)

(* Temporarily allow the monadic syntax *)
val _ = monadsyntax.temp_add_monadsyntax ();

val test1_def = Define `
  test1 (x : bool) = Return x`

val is_true_def = Define ‘
  is_true (x : bool) = if x then Return () else Fail Failure’

val test1_def = Define ‘
  test1 (x : bool) = Return x’

val test_monad_def = Define `
  test_monad v =
    do
      x <- Return v;
      Return x
    od`;


val test_monad2_def = Define `
  test_monad2 =
    do
      x <- Return T;
      Return x
    od`;

val test_monad3_def = Define `
  test_monad3 x =
    do
      is_true x;
      Return x
    od`;

(**
 *  Arithmetic
 *)

open intLib

val test_int1 = Define ‘int1 = 32’
val test_int2 = Define ‘int2 = -32’

Theorem INT_THM1:
  !(x y : int). x > 0 ==> y > 0 ==> x + y > 0
Proof
  ARITH_TAC
QED

Theorem INT_THM2:
  !(x : int). T
Proof
  rw[]
QED

val _ = prefer_int ()

val x = “-36217863217862718”

(* Deactivate notations for int *)
val _ = deprecate_int ()
open arithmeticTheory


val m = Hol_pp.print_apropos
val f = Hol_pp.print_find

(* Display types on/off: M-h C-t *)
(* Move back: M-h b *)

val _ = numLib.deprecate_num ()
val _ = numLib.prefer_num ()

Theorem NAT_THM1:
  !(n : num). n < n + 1
Proof
  Induct_on ‘n’ >> DECIDE_TAC
QED

Theorem NAT_THM2:
  !(n : num). n < n + (1 : num)
Proof
  gen_tac >>
  Induct_on ‘n’ >- (
    PURE_REWRITE_TAC [ADD, NUMERAL_DEF, BIT1, ALT_ZERO] >>
    PURE_REWRITE_TAC [prim_recTheory.LESS_0_0]) >>
  PURE_REWRITE_TAC [ADD] >>
  irule prim_recTheory.LESS_MONO >>
  asm_rewrite_tac []
QED


val x = “1278361286371286:num”


(********************** PRIMITIVES *)
val _ = prefer_int ()

val _ = new_type ("u32", 0)
val _ = new_type ("i32", 0)

(*val u32_min_def = Define ‘u32_min = (0:int)’*)
val u32_max_def = Define ‘u32_max = (4294967295:int)’

(* TODO: change that *)
val usize_max_def = Define ‘usize_max = (4294967295:int)’

val i32_min_def = Define ‘i32_min = (-2147483648:int)’
val i32_max_def = Define ‘i32_max = (2147483647:int)’

val _ = new_constant ("u32_to_int", “:u32 -> int”)
val _ = new_constant ("i32_to_int", “:i32 -> int”)

val _ = new_constant ("int_to_u32", “:int -> u32”)
val _ = new_constant ("int_to_i32", “:int -> i32”)


(* TODO: change to "...of..." *)
val u32_to_int_bounds =
  new_axiom (
    "u32_to_int_bounds",
    “!n. 0 <= u32_to_int n /\ u32_to_int n <= u32_max”)

val i32_to_int_bounds =
  new_axiom (
    "i32_to_int_bounds",
    “!n. i32_min <= i32_to_int n /\ i32_to_int n <= i32_max”)

val int_to_u32_id = new_axiom ("int_to_u32_id",
    “!n. 0 <= n /\ n <= u32_max ==> u32_to_int (int_to_u32 n) = n”)

val int_to_i32_id =
  new_axiom (
    "int_to_i32_id",
    “!n. i32_min <= n /\ n <= i32_max ==>
     i32_to_int (int_to_i32 n) = n”)

val mk_u32_def = Define
  ‘mk_u32 n =
    if 0 <= n /\ n <= u32_max then Return (int_to_u32 n)
    else Fail Failure’

val u32_add_def = Define ‘u32_add x y = mk_u32 ((u32_to_int x) + (u32_to_int y))’

Theorem MK_U32_SUCCESS:
  !n. 0 <= n /\ n <= u32_max ==>
  mk_u32 n = Return (int_to_u32 n)
Proof
  rw[mk_u32_def]
QED

Theorem U32_ADD_EQ:
  !x y.
    u32_to_int x + u32_to_int y <= u32_max ==>
    ?z. u32_add x y = Return z /\ u32_to_int z = u32_to_int x + u32_to_int y
Proof
  rpt gen_tac >>
  rpt DISCH_TAC >>
  exists_tac “int_to_u32 (u32_to_int x + u32_to_int y)” >>
  imp_res_tac MK_U32_SUCCESS >>
  (* There is probably a better way of doing this *)
  sg ‘0 <= u32_to_int x’ >- (rw[u32_to_int_bounds]) >>
  sg ‘0 <= u32_to_int y’ >- (rw[u32_to_int_bounds]) >>
  fs [u32_add_def] >>
  irule int_to_u32_id >>
  fs[]
QED

val u32_sub_def = Define ‘u32_sub x y = mk_u32 ((u32_to_int x) - (u32_to_int y))’

Theorem U32_SUB_EQ:
  !x y.
    0 <= u32_to_int x - u32_to_int y ==>
    ?z. u32_sub x y = Return z /\ u32_to_int z = u32_to_int x - u32_to_int y
Proof
  rpt gen_tac >>
  rpt DISCH_TAC >>
  exists_tac “int_to_u32 (u32_to_int x - u32_to_int y)” >>
  imp_res_tac MK_U32_SUCCESS >>
  (* There is probably a better way of doing this *)
  sg ‘u32_to_int x − u32_to_int y ≤ u32_max’ >-(
    sg ‘u32_to_int x <= u32_max’ >- (rw[u32_to_int_bounds]) >>
    sg ‘0 <= u32_to_int y’ >- (rw[u32_to_int_bounds]) >>
    COOPER_TAC
  ) >>
  fs [u32_sub_def] >>
  irule int_to_u32_id >>
  fs[]
QED

val mk_i32_def = Define
  ‘mk_i32 n =
    if i32_min <= n /\ n <= i32_max then Return (int_to_i32 n)
    else Fail Failure’

val i32_add_def = Define ‘i32_add x y = mk_i32 ((i32_to_int x) + (i32_to_int y))’

Theorem MK_I32_SUCCESS:
  !n. i32_min <= n /\ n <= i32_max ==>
  mk_i32 n = Return (int_to_i32 n)
Proof
  rw[mk_i32_def]
QED

Theorem I32_ADD_EQ:
  !x y.
    i32_min <= i32_to_int x + i32_to_int y ==>
    i32_to_int x + i32_to_int y <= i32_max ==>
    ?z. i32_add x y = Return z /\ i32_to_int z = i32_to_int x + i32_to_int y
Proof
  rpt gen_tac >>
  rpt DISCH_TAC >>
  exists_tac “int_to_i32 (i32_to_int x + i32_to_int y)” >>
  imp_res_tac MK_I32_SUCCESS >>
  fs [i32_min_def, i32_add_def] >>
  irule int_to_i32_id >>
  fs[i32_min_def]
QED

open listTheory

val _ = new_type ("vec", 1)
val _ = new_constant ("vec_to_list", “:'a vec -> 'a list”)

val VEC_TO_LIST_NUM_BOUNDS =
  new_axiom (
    "VEC_TO_LIST_BOUNDS",
    “!v. let l = LENGTH (vec_to_list v) in
     (0:num) <= l /\ l <= (4294967295:num)”)

Theorem VEC_TO_LIST_INT_BOUNDS:
  !v. let l = int_of_num (LENGTH (vec_to_list v)) in
     0 <= l /\ l <= u32_max
Proof
  gen_tac >>
  rw [u32_max_def] >>
  assume_tac VEC_TO_LIST_NUM_BOUNDS >>
  fs[]
QED

val VEC_LEN_DEF = Define ‘vec_len v = int_to_u32 (int_of_num (LENGTH (vec_to_list v)))’

(*
(* Useless *)
Theorem VEC_LEN_BOUNDS:
  !v. u32_min <= u32_to_int (vec_len v) /\ u32_to_int (vec_len v) <= u32_max
Proof
  gen_tac >>
  qspec_then ‘v’ assume_tac VEC_TO_LIST_INT_BOUNDS >>
  fs[VEC_LEN_DEF] >>
  IMP_RES_TAC int_to_u32_id >>
  fs[]
QED
*)

(* The type parameters are ordered in alphabetical order *)
Datatype:
  test = Variant1 'b | Variant2 'a
End

Datatype:
  test2 = Variant1_1 'T2 | Variant2_1 'T1
End

Datatype:
  test2 = Variant1_2 'T1 | Variant2_2 'T2
End

(*
“Variant1_1 3”
“Variant1_2 3”

type_of “CONS 3”
*)

(* TODO: argument order, we must also omit arguments in new type *)
Datatype:
  list_t =
    ListCons 't list_t
  | ListNil
End

val list_nth_mut_loop_loop_fwd_def = Define ‘
  list_nth_mut_loop_loop_fwd (ls : 't list_t) (i : u32) : 't result =
  case ls of
  | ListCons x tl =>
    if u32_to_int i = (0:int)
    then Return x
    else
      do
      i0 <- u32_sub i (int_to_u32 1);
      list_nth_mut_loop_loop_fwd tl i0
      od
  | ListNil => 
    Fail Failure
’

(*
CoInductive coind:
 !x y. coind x /\ coind y ==> coind (x + y)
End
*)

(*
(* This generates inconsistent theorems *)
CoInductive loop:
 !x. loop x = if x then loop x else 0
End

CoInductive loop:
 !(x : int). loop x = if x > 0 then loop (x - 1) else 0
End
*)

(* This terminates *)
val list_nth_mut_loop_loop_fwd_def = Define ‘
  list_nth_mut_loop_loop_fwd (ls : 't list_t) (i : u32) : 't result =
  case ls of
  | ListCons x tl =>
    if u32_to_int i = (0:int)
    then Return x
    else
      do
      i0 <- u32_sub i (int_to_u32 1);
      list_nth_mut_loop_loop_fwd tl i0
      od
  | ListNil => 
    Fail Failure
’

(* This is sort of a coinductive definition.

   This can be justified:
   - we first define a version [nth_fuel] which uses fuel (and is thus terminating)
   - we define the predicate P:
     P ls i n = case nth_fuel n ls i of Return _ => T |  _ => F
   - we then use [LEAST] (least upper bound for natural numbers) to define nth as:
     “nth ls i = if (?n. P n) then nth_fuel (LEAST (P ls i)) ls i else Fail Loop ”
   - we finally prove that nth satisfies the proper equation.

     We would need the following intermediate lemma:
     !n.
       n < LEAST (P ls i) ==> nth_fuel n ls i = Fail _ /\
       n >= LEAST (P ls i) ==> nth_fuel n ls i = nth_fuel (LEAST P ls i) ls i
     
 *)
val _ = new_constant ("nth", “:'t list_t -> u32 -> 't result”)
val nth_def = new_axiom ("nth_def", “
 nth (ls : 't list_t) (i : u32) : 't result =
  case ls of
  | ListCons x tl =>
    if u32_to_int i = (0:int)
    then Return x
    else
      do
      i0 <- u32_sub i (int_to_u32 1);
      nth tl i0
      od
  | ListNil => 
    Fail Failure
 ”)


(*** Examples of proofs on [nth] *)
val list_t_v_def = Define ‘
  list_t_v ListNil = [] /\
  list_t_v (ListCons x tl) = x :: list_t_v tl
’

(* TODO: move *)
open dep_rewrite
open integerTheory

(* Ignore a theorem.

   To be used in conjunction with {!pop_assum} for instance.
 *)
fun IGNORE_TAC (_ : thm) : tactic = ALL_TAC


Theorem INT_OF_NUM_INJ:
  !n m. &n = &m ==> n = m
Proof
  rpt strip_tac >>
  fs [Num]
QED

Theorem NUM_SUB_EQ:
  !(x y z : int). x = y - z ==> 0 <= x ==> 0 <= z ==> Num y = Num z + Num x
Proof
  rpt strip_tac >>
  sg ‘0 <= y’ >- COOPER_TAC >>
  rfs [] >>
  (* Convert to integers *)
  irule INT_OF_NUM_INJ >>
  imp_res_tac (GSYM INT_OF_NUM) >>
  (* Associativity of & *)
  PURE_REWRITE_TAC [GSYM INT_ADD] >>
  fs []
QED

Theorem NUM_SUB_1_EQ:
  !(x y : int). x = y - 1 ==> 0 <= x ==> Num y = SUC (Num x)
Proof
  rpt strip_tac >>
  (* Get rid of the SUC *)
  sg ‘SUC (Num x) = 1 + Num x’ >-(rw [ADD]) >> rw [] >>
  (* Massage a bit the goal *)
  qsuff_tac ‘Num y = Num (y − 1) + Num 1’ >- COOPER_TAC >>
  (* Apply the general theorem *)
  irule NUM_SUB_EQ >>
  COOPER_TAC
QED

(* TODO: remove *)
Theorem NUM_SUB_1_EQ1:
  !i. 0 <= i - 1 ==> Num i = SUC (Num (i-1))
Proof
  rpt strip_tac >>
  (* 0 <= i *)
  sg ‘0 <= i’ >- COOPER_TAC >>
  (* Get rid of the SUC *)
  sg ‘SUC (Num (i - 1)) = 1 + Num (i - 1)’ >-(rw [ADD]) >>
  rw [] >>
  (* Convert to integers*)
  irule INT_OF_NUM_INJ >>
  imp_res_tac (GSYM INT_OF_NUM) >>
  (* Associativity of & *)
  PURE_REWRITE_TAC [GSYM INT_ADD] >>
  fs []
QED

(* TODO:
   - list all the integer variables, and insert bounds in the assumptions
   - replace u32_min by 0?
   - i - 1
   - auto lookup of spec lemmas
*)

(* Add a list of theorems in the assumptions - TODO: move *)
fun ASSUME_TACL (thms : thm list) : tactic =
  let
    (* TODO: use MAP_EVERY *)
    fun t thms =
      case thms of
        [] => ALL_TAC
      | thm :: thms => ASSUME_TAC thm >> t thms
  in
  t thms
  end

(* The map from integer type to bounds lemmas *)
val integer_bounds_lemmas =
  Redblackmap.fromList String.compare
  [
    ("u32", u32_to_int_bounds),
    ("i32", i32_to_int_bounds)
  ]

(* The map from integer type to conversion lemmas *)
val integer_conversion_lemmas =
  Redblackmap.fromList String.compare
  [
    ("u32", int_to_u32_id),
    ("i32", int_to_i32_id)
  ]

val integer_conversion_lemmas_list =
  map snd (Redblackmap.listItems integer_conversion_lemmas)

(* Not sure how term nets work, nor how we are supposed to convert Term.term
   to mlibTerm.term.

   TODO: it seems we need to explore the term and convert everything to strings.
 *)
fun term_to_mlib_term (t : term) : mlibTerm.term =
  mlibTerm.string_to_term (term_to_string t)

(*
(* The lhs of the conclusion of the integer conversion lemmas - we use this for
   pattern matching *)
val integer_conversion_lhs_concls =
  let
    val thms = map snd (Redblackmap.listItems integer_conversion_lemmas);
    val concls = map (lhs o concl o UNDISCH_ALL o SPEC_ALL) thms;
  in concls end
*)

(*
val integer_conversion_concls_net =
  let
    val maplets = map (fn x => fst (dest_eq x) |-> ()) integer_conversion_concls;

    val maplets = map (fn x => fst (mlibTerm.dest_eq x) |-> ()) integer_conversion_concls;
    val maplets = map (fn x => fst (mlibThm.dest_unit_eq x) |-> ()) integer_conversion_concls;
    val parameters = { fifo=false };
  in mlibTermnet.from_maplets parameters maplets end

mlibTerm.string_to_term (term_to_string “u32_to_int (int_to_u32 n) = n”)
term_to_quote

SIMP_CONV
mlibThm.dest_thm u32_to_int_bounds
mlibThm.dest_unit u32_to_int_bounds
*)

(* The integer types *)
val integer_types_names =
  Redblackset.fromList String.compare
  (map fst (Redblackmap.listItems integer_bounds_lemmas))

val all_integer_bounds = [
  u32_max_def,
  i32_min_def,
  i32_max_def
]

(* Small utility: compute the set of assumptions in the context.

   We isolate this code in a utility in order to be able to improve it:
   for now we simply put all the assumptions in a set, but in the future
   we might want to split the assumptions which are conjunctions in order
   to be more precise.
 *)
fun compute_asms_set ((asms,g) : goal) : term Redblackset.set =
  Redblackset.fromList Term.compare asms

(* See {!assume_bounds_for_all_int_vars}.

   This tactic is in charge of adding assumptions for one variable.
 *)

fun assume_bounds_for_int_var
  (asms_set: term Redblackset.set) (var : string) (ty : string) :
  tactic =
  let
    (* Lookup the lemma to apply *)
    val lemma = Redblackmap.find (integer_bounds_lemmas, ty);
    (* Instantiate the lemma *)
    val ty_t = mk_type (ty, []);
    val var_t = mk_var (var, ty_t);
    val lemma = SPEC var_t lemma;
    (* Split the theorem into a list of conjuncts.

       The bounds are typically a conjunction:
       {[
         ⊢ 0 ≤ u32_to_int x ∧ u32_to_int x ≤ u32_max: thm
       ]}
     *)
    val lemmas = CONJUNCTS lemma;
    (* Filter the conjuncts: some of them might already be in the context,
       we don't want to introduce them again, as it would pollute it.
     *)
    val lemmas = filter (fn lem => not (Redblackset.member (asms_set, concl lem))) lemmas;
   in
  (* Introduce the assumptions in the context *)
  ASSUME_TACL lemmas
  end

(* Destruct if possible a term of the shape: [x y],
   where [x] is not a comb.

   Returns [(x, y)]
 *)
fun dest_single_comb (t : term) : (term * term) option =
  case strip_comb t of
    (x, [y]) => SOME (x, y)
  | _ => NONE

(** Destruct if possible a term of the shape: [x (y z)].
    Returns [(x, y, z)]
 *)
fun dest_single_comb_twice (t : term) : (term * term * term) option =
  case dest_single_comb t of
    NONE => NONE
  | SOME (x, y) =>
    case dest_single_comb y of
      NONE => NONE
    | SOME (y, z) => SOME (x, y, z)

(* A utility map to lookup integer conversion lemmas *)
val integer_conversion_pat_map =
  let
    val thms = map snd (Redblackmap.listItems integer_conversion_lemmas);
    val tl = map (lhs o concl o UNDISCH_ALL o SPEC_ALL) thms;
    val tl = map (valOf o dest_single_comb_twice) tl;
    val tl = map (fn (x, y, _) => (x, y)) tl;
    val m = Redblackmap.fromList Term.compare tl
  in m end

(* Introduce bound assumptions for all the machine integers in the context.

   Exemple:
   ========
   If there is “x : u32” in the input set, then we introduce:
   {[
     0 <= u32_to_int x
     u32_to_int x <= u32_max
   ]}
 *)
fun assume_bounds_for_all_int_vars (asms, g) =
  let
    (* Compute the set of integer variables in the context *)
    val vars = free_varsl (g :: asms);
    (* Compute the set of assumptions already present in the context *)
    val asms_set = compute_asms_set (asms, g);
    (* Filter the variables to keep only the ones with type machine integer,
       decompose the types at the same time *)
    fun decompose_var (v : term) : (string * string) =
      let
        val (v, ty) = dest_var v;
        val {Args=args, Thy=thy, Tyop=ty} = dest_thy_type ty;
        val _ = assert null args;
        val _ = assert (fn thy => thy = primitives_theory_name) thy;
        val _ = assert (fn ty => Redblackset.member (integer_types_names, ty)) ty;
      in (v, ty) end;
    val vars = mapfilter decompose_var vars; 
    (* Add assumptions for one variable *)
    fun add_var_asm (v, ty) : tactic =
      assume_bounds_for_int_var asms_set v ty;    
    (* Add assumptions for all the variables *)
    (* TODO: use MAP_EVERY *)
    fun add_vars_asm vl : tactic =
      case vl of
        [] => ALL_TAC
      | v :: vl =>
        add_var_asm v >> add_vars_asm vl;
  in
    add_vars_asm vars (asms, g)
  end

(*
dest_thy_type “:u32”
val massage : tactic = assume_bounds_for_all_int_vars
val vl = vars
val (v::vl) = vl
*)

(*
val (asms, g) = top_goal ()
fun bounds_for_ints_in_list (vars : (string * hol_type) list) : tactic =
  foldl
  FAIL_TAC ""
val var = "x"
val ty = "u32"

val asms_set = Redblackset.fromList Term.compare asms;

val x = “1: int”
val ty = "u32"

val thm = lemma
*)

(* Given a theorem of the shape:
   {[
     A0, ..., An ⊢ B0 ==> ... ==> Bm ==> concl
   ]}

   Rewrite it so that it has the shape:
   {[
     ⊢ (A0 /\ ... /\ An /\ B0 /\ ... /\ Bm) ==> concl
   ]}
 *)
fun thm_to_conj_implies (thm : thm) : thm =
  let
    (* Discharge all the assumptions *)
    val thm = DISCH_ALL thm;
    (* Rewrite the implications as one conjunction *)
    val thm = PURE_REWRITE_RULE [GSYM satTheory.AND_IMP] thm;
  in thm end


(* Like THEN1 and >-, but doesn't fail if the first subgoal is not completely
   solved.

   TODO: how to get the notation right?
 *)
fun op PARTIAL_THEN1 (tac1: tactic) (tac2: tactic) : tactic = tac1 THEN_LT (NTH_GOAL tac2 1)

(* If the current goal is [asms ⊢ g], and given a lemma of the form
   [⊢ H ==> C], do the following:
   - introduce [asms ⊢ H] as a subgoal and apply the given tactic on it
   - also calls the theorem tactic with the theorem [asms ⊢ C]
   
   If the lemma is not an implication, we directly call the theorem tactic.
 *)
fun intro_premise_then (premise_tac: tactic) (then_tac: thm_tactic) (thm : thm)  : tactic =
  let
    val c = concl thm;
    (* First case: there is a premise to prove *)
    fun prove_premise_then (h : term) =
      PARTIAL_THEN1 (SUBGOAL_THEN h (fn h_thm => then_tac (MP thm h_thm))) premise_tac;
    (* Second case: no premise to prove *)
    val no_prove_premise_then = then_tac thm;
  in
    if is_imp c then prove_premise_then (fst (dest_imp c)) else no_prove_premise_then
  end

(* Same as {!intro_premise_then} but fails if the premise_tac fails to prove the premise *)
fun prove_premise_then (premise_tac: tactic) (then_tac: thm_tactic) (thm : thm)  : tactic =
  intro_premise_then
    (premise_tac >> FAIL_TAC "prove_premise_then: could not prove premise")
    then_tac thm

(*
val thm = th
*)

(* Call a function on all the subterms of a term *)
fun dep_apply_in_subterms
  (f : string Redblackset.set -> term -> unit)
  (bound_vars : string Redblackset.set)
  (t : term) : unit =
  let
    val dep = dep_apply_in_subterms f;
    val _ = f bound_vars t;
  in
  case dest_term t of
    VAR (name, ty) => ()
  | CONST {Name=name, Thy=thy, Ty=ty} => ()
  | COMB (app, arg) =>
    let
      val _ = dep bound_vars app;
      val _ = dep bound_vars arg;
    in () end
  | LAMB (bvar, body) =>
    let
      val (varname, ty) = dest_var bvar;
      val bound_vars = Redblackset.add (bound_vars, varname);
      val _ = dep bound_vars body;
    in () end
  end

(* Return the set of free variables appearing in the residues of a term substitution *)
fun free_vars_in_subst_residue (s: (term, term) Term.subst) : string Redblackset.set =
  let
    val free_vars = free_varsl (map (fn {redex=_, residue=x} => x) s);
    val free_vars = map (fst o dest_var) free_vars;
    val free_vars = Redblackset.fromList String.compare free_vars;
  in free_vars end

(* Attempt to instantiate a rewrite theorem.

   Remark: this theorem should be of the form:
   H ⊢ x = y
   
   (without quantified variables).
   
   **REMARK**: the function raises a HOL_ERR exception if it fails.
   
   [forbid_vars]: forbid substituting with those vars (typically because
   we are maching in a subterm under lambdas, and some of those variables
   are bounds in the outer lambdas).
*)
fun inst_match_concl (forbid_vars : string Redblackset.set) (th : thm) (t : term) : thm =
  let
    (* Retrieve the lhs of the conclusion of the theorem *)
    val l = lhs (concl th);
    (* Match this lhs with the term *)
    val (var_s, ty_s) = match_term l t;
    (* Check that we are allowed to perform the substitution *)
    val free_vars = free_vars_in_subst_residue var_s;
    val _ = assert Redblackset.isEmpty (Redblackset.intersection (free_vars, forbid_vars));
  in
    (* Perform the substitution *)
    INST var_s (INST_TYPE ty_s th)
  end

(*
val forbid_vars = Redblackset.empty String.compare
val t = “u32_to_int (int_to_u32 x)”
val t = “u32_to_int (int_to_u32 3)”
val th = (UNDISCH_ALL o SPEC_ALL) int_to_u32_id
*)

(* Attempt to instantiate a theorem by matching its first premise.

   Note that we make the hypothesis tha all the free variables which need
   to be instantiated appear in the first premise, of course (the caller should
   enforce this).

   Remark: this theorem should be of the form:
   ⊢ H0 ==> ... ==> Hn ==> H
   
   (without quantified variables).
   
   **REMARK**: the function raises a HOL_ERR exception if it fails.
   
   [forbid_vars]: see [inst_match_concl]
*)
fun inst_match_first_premise
  (forbid_vars : string Redblackset.set) (th : thm) (t : term) : thm =
  let
    (* Retrieve the first premise *)
    val l = (fst o dest_imp o concl) th;
    (* Match this with the term *)
    val (var_s, ty_s) = match_term l t;
    (* Check that we are allowed to perform the substitution *)
    val free_vars = free_vars_in_subst_residue var_s;
    val _ = assert Redblackset.isEmpty (Redblackset.intersection (free_vars, forbid_vars));
  in
    (* Perform the substitution *)
    INST var_s (INST_TYPE ty_s th)
  end

(*
val forbid_vars = Redblackset.empty String.compare
val t = “u32_to_int z = u32_to_int i − 1”
val th = SPEC_ALL NUM_SUB_1_EQ
*)

(* Call a matching function on all the subterms in the provided list of term.
   This is a generic function.

   [try_match] should return an instantiated theorem, as well as a term which
   identifies this theorem (the lhs of the equality, if this is a rewriting
   theorem for instance - we use this to check for collisions, and discard
   redundant instantiations).
 *)
fun inst_match_in_terms
  (try_match: string Redblackset.set -> term -> term * thm)
  (tl : term list) : thm list =
  let
    (* We use a map when storing the theorems, to avoid storing the same theorem twice *)
    val inst_thms: (term, thm) Redblackmap.dict ref = ref (Redblackmap.mkDict Term.compare);
    fun try_instantiate bvars t =
      let
        val (inst_th_tm, inst_th) = try_match bvars t;
      in
        inst_thms := Redblackmap.insert (!inst_thms, inst_th_tm, inst_th)
      end
      handle HOL_ERR _ => ();
    (* Explore the term *)
    val _ = app (dep_apply_in_subterms try_instantiate (Redblackset.empty String.compare)) tl;
  in
    map snd (Redblackmap.listItems (!inst_thms))
  end

(* Given a rewriting theorem [th] which has premises, return all the
   instantiations of this theorem which make its conclusion match subterms
   in the provided list of term.
 *)
fun inst_match_concl_in_terms (th : thm) (tl : term list) : thm list =
  let
    val th = (UNDISCH_ALL o SPEC_ALL) th;
    fun try_match bvars t =
      let
        val inst_th = inst_match_concl bvars th t;
      in
        (lhs (concl inst_th), inst_th)
      end;
  in
    inst_match_in_terms try_match tl
  end

(*
val t = “!x. u32_to_int (int_to_u32 x) = u32_to_int (int_to_u32 y)”
val th = int_to_u32_id

val thms = inst_match_concl_in_terms int_to_u32_id [t]
*)


(* Given a theorem [th] which has premises, return all the
   instantiations of this theorem which make its first premise match subterms
   in the provided list of term.
 *)
fun inst_match_first_premise_in_terms (th : thm) (tl : term list) : thm list =
  let
    val th = SPEC_ALL th;
    fun try_match bvars t =
      let
        val inst_th = inst_match_first_premise bvars th t;
      in
        ((fst o dest_imp o concl) inst_th, inst_th)
      end;
  in
    inst_match_in_terms try_match tl
  end

(*
val t = “x = y - 1 ==> T”
val th = SPEC_ALL NUM_SUB_1_EQ

val thms = inst_match_first_premise_in_terms th [t]
*)

(* Attempt to apply dependent rewrites with a theorem by matching its
   conclusion with subterms of the goal.
 *)
fun apply_dep_rewrites_match_concl_tac
  (prove_premise : tactic) (then_tac : thm_tactic) (th : thm) : tactic =
  fn (asms, g) =>
    let
      (* Discharge the assumptions so that the goal is one single term *)
      val thms = inst_match_concl_in_terms th (g :: asms);
      val thms = map thm_to_conj_implies thms;
    in
      (* Apply each theorem *)
      MAP_EVERY (prove_premise_then prove_premise then_tac) thms (asms, g)
    end

(*
val (asms, g) = ([
  “u32_to_int z = u32_to_int i − u32_to_int (int_to_u32 1)”,
  “u32_to_int (int_to_u32 2) = 2”
], “T”)

apply_dep_rewrites_match_concl_tac
  (FULL_SIMP_TAC simpLib.empty_ss all_integer_bounds >> COOPER_TAC)
  (fn th => FULL_SIMP_TAC simpLib.empty_ss [th])
  int_to_u32_id
*)

(* Attempt to apply dependent rewrites with a theorem by matching its
   first premise with subterms of the goal.
 *)
fun apply_dep_rewrites_match_first_premise_tac
  (prove_premise : tactic) (then_tac : thm_tactic) (th : thm) : tactic =
  fn (asms, g) =>
    let
      (* Discharge the assumptions so that the goal is one single term *)
      val thms = inst_match_first_premise_in_terms th (g :: asms);
      val thms = map thm_to_conj_implies thms;
      fun apply_tac th =
        let
          val th = thm_to_conj_implies th;
        in
          prove_premise_then prove_premise then_tac th
        end;
    in
      (* Apply each theorem *)
      MAP_EVERY apply_tac thms (asms, g)
    end

(* See {!rewrite_all_int_conversion_ids}.

   Small utility which takes care of one rewriting.

   TODO: we actually don't use it. REMOVE?
 *)
fun rewrite_int_conversion_id
  (asms_set: term Redblackset.set) (x : term) (ty : string) :
  tactic =
  let
    (* Lookup the theorem *)
    val lemma = Redblackmap.find (integer_conversion_lemmas, ty);
    (* Instantiate *)
    val lemma = SPEC x lemma;
    (* Rewrite the lemma. The lemma typically has the shape:
       ⊢ u32_min <= x /\ x <= u32_max ==> u32_to_int (int_to_u32 x) = x
       
       Make sure the lemma has the proper shape, attempt to prove the premise,
       then use the conclusion if it succeeds.
     *)
    val lemma = thm_to_conj_implies lemma;
    (* Retrieve the conclusion of the lemma - we do this to check if it is not
       already in the assumptions *)
    val c = concl (UNDISCH_ALL lemma);
    val already_in_asms = Redblackset.member (asms_set, c);
    (* Small utility: the tactic to prove the premise *)
    val prove_premise =
      (* We might need to unfold the bound definitions, in particular if the
         term is a constant (e.g.,  “3:int”) *)
      FULL_SIMP_TAC simpLib.empty_ss all_integer_bounds >>
      COOPER_TAC;
    (* Rewrite with a lemma, then assume it *)
    fun rewrite_then_assum (thm : thm) : tactic =
      FULL_SIMP_TAC simpLib.empty_ss [thm] >> assume_tac thm;
  in
    (* If the conclusion is not already in the assumptions, prove it, use
       it to rewrite the goal and add it in the assumptions, otherwise do nothing *)
    if already_in_asms then ALL_TAC
    else prove_premise_then prove_premise rewrite_then_assum lemma
 end

(* Look for conversions from integers to machine integers and back.
   {[
     u32_to_int (int_to_u32 x)
   ]}

   Attempts to prove and apply equalities of the form:
   {[
     u32_to_int (int_to_u32 x) = x
   ]}
   
   **REMARK**: this function can fail, if it doesn't manage to prove the
   premises of the theorem to apply.

   TODO: update
 *)
val rewrite_with_dep_int_lemmas : tactic =
  (* We're not trying to be smart: we just try to rewrite with each theorem at
     a time *)
  let
    val prove_premise = FULL_SIMP_TAC simpLib.empty_ss all_integer_bounds >> COOPER_TAC;
    val then_tac1 = (fn th => FULL_SIMP_TAC simpLib.empty_ss [th]);
    val rewr_tac1 = apply_dep_rewrites_match_concl_tac prove_premise then_tac1;
    val then_tac2 = (fn th => FULL_SIMP_TAC simpLib.empty_ss [th]);
    val rewr_tac2 = apply_dep_rewrites_match_first_premise_tac prove_premise then_tac2;
  in
      MAP_EVERY rewr_tac1 integer_conversion_lemmas_list >>
      MAP_EVERY rewr_tac2 [NUM_SUB_1_EQ]
  end

(*
apply_dep_rewrites_match_first_premise_tac prove_premise then_tac NUM_SUB_1_EQ

sg ‘u32_to_int z = u32_to_int i − 1 /\ 0 ≤ u32_to_int z’ >- prove_premise

prove_premise_then prove_premise

val thm = thm_to_conj_implies  (SPECL [“u32_to_int z”, “u32_to_int i”] NUM_SUB_1_EQ)

val h = “u32_to_int z = u32_to_int i − 1 ∧ 0 ≤ u32_to_int z”
*)

(* Massage a bit the goal, for instance by introducing integer bounds in the
   assumptions.
*)
val massage : tactic =
  assume_bounds_for_all_int_vars >>
  rewrite_with_dep_int_lemmas

(* Lexicographic order over pairs *)
fun pair_compare (comp1 : 'a * 'a -> order) (comp2 : 'b * 'b -> order)
  ((p1, p2) : (('a * 'b) * ('a * 'b))) : order =
  let
    val (x1, y1) = p1;
    val (x2, y2) = p2;
  in
    case comp1 (x1, x2) of
      LESS => LESS
    | GREATER => GREATER
    | EQUAL => comp2 (y1, y2)
  end

(* A constant name (theory, constant name) *)
type const_name = string * string

val const_name_compare = pair_compare String.compare String.compare

(* The registered spec theorems, that {!progress} will automatically apply.

   The keys are the function names (it is a pair, because constant names
   are made of the theory name and the name of the constant itself).

   Also note that we can store several specs per definition (in practice, when
   looking up specs, we will try them all one by one, in a LIFO order).

   We store theorems where all the premises are in the goal, with implications
   (i.e.: [⊢ H0 ==> ... ==> Hn ==> H], not  [H0, ..., Hn ⊢ H]).

   We do this because, when doing proofs by induction, {!progress} might have to
   handle *unregistered* theorems coming the current goal assumptions and of the shape
   (the conclusion of the theorem is an assumption, and we want to ignore this assumption):
   {[
     [∀i. u32_to_int i < &LENGTH (list_t_v ls) ⇒
         case nth ls i of
           Return x => ...
         | ...      => ...]
     ⊢ ∀i. u32_to_int i < &LENGTH (list_t_v ls) ⇒
         case nth ls i of
           Return x => ...
         | ...      => ...
   ]}
 *)
val reg_spec_thms: (const_name, thm) Redblackmap.dict ref =
  ref (Redblackmap.mkDict const_name_compare)

(* Retrieve the specified application in a spec theorem.

   A spec theorem for a function [f] typically has the shape:
   {[
     !x0 ... xn.
       H0 ==> ... Hm ==>
         (exists ...
           (exists ... . f y0 ... yp = ... /\ ...) \/
           (exists ... . f y0 ... yp = ... /\ ...) \/
           ...
   ]}

   Or:
   {[
    !x0 ... xn.
      H0 ==> ... Hm ==>
        case f y0 ... yp of
          ... => ...
        | ... =>  ...
   ]}

   We return: [f y0 ... yp]
*)
fun get_spec_app (t : term) : term =
  let
    (* Remove the universally quantified variables, the premises and
       the existentially quantified variables *)
    val t = (snd o strip_exists o snd o strip_imp o snd o strip_forall) t;
    (* Remove the exists, take the first disjunct *)
    val t = (hd o strip_disj o snd o strip_exists) t;
    (* Split the conjunctions and take the first conjunct *)
    val t = (hd o strip_conj) t;
    (* Remove the case if there is, otherwise destruct the equality *)
    val t =
      if TypeBase.is_case t then let val (_, t, _) = TypeBase.dest_case t in t end
      else (fst o dest_eq) t;
  in t end

(* Given a function call [f y0 ... yn] return the name of the function *)
fun get_fun_name_from_app (t : term) : const_name =
  let
    val f = (fst o strip_comb) t;
    val {Name=name, Thy=thy, Ty=_} = dest_thy_const f;
    val cn = (thy, name);
  in cn end

(* Register a spec theorem in the spec database.

   For the shape of spec theorems, see {!get_spec_thm_app}.
 *)
fun register_spec_thm (th: thm) : unit =
  let
    (* Transform the theroem a bit before storing it *)
    val th = SPEC_ALL th;
    (* Retrieve the app ([f x0 ... xn]) *)
    val f = get_spec_app (concl th);
    (* Retrieve the function name *)
    val cn = get_fun_name_from_app f;
  in
    (* Store *)
    reg_spec_thms := Redblackmap.insert (!reg_spec_thms, cn, th)
  end

(* TODO: I32_SUB_EQ *)
val _ = app register_spec_thm [U32_ADD_EQ, U32_SUB_EQ, I32_ADD_EQ]

(*
app register_spec_thm [U32_ADD_EQ, U32_SUB_EQ, I32_ADD_EQ]
Redblackmap.listItems (!reg_spec_thms)
*)

(*
(* TODO: remove? *)
datatype monadic_app_kind =
 Call | Bind | Case
*)

(* Repeatedly destruct cases and return the last scrutinee we get *)
fun strip_all_cases_get_scrutinee (t : term) : term =
  if TypeBase.is_case t
  then (strip_all_cases_get_scrutinee o fst o TypeBase.strip_case) t
  else t

(*
TypeBase.dest_case “case ls of [] => T | _ => F”
TypeBase.strip_case “case ls of [] => T | _ => F”
TypeBase.strip_case “case (if b then [] else [0, 1]) of [] => T | _ => F”
TypeBase.strip_case “3”
TypeBase.dest_case “3”

strip_all_cases_get_scrutinee “case ls of [] => T | _ => F”
strip_all_cases_get_scrutinee “case (if b then [] else [0, 1]) of [] => T | _ => F”
strip_all_cases_get_scrutinee “3”
*)


(* Provided the goal contains a call to a monadic function, return this function call.

   The goal should be of the shape:
   1.
   {[
     case (* potentially expanded function body *) of
       ... => ...
     | ... => ...
   ]}

   2. Or:
   {[
     exists ... .
       ... (* potentially expanded function body *) = Return ... /\
       ... (* Various properties *)
   ]}

   3. Or a disjunction of cases like the one above, below existential binders
   (actually: note sure this last case exists in practice):
   {[
     exists ... .
       (exists ... . (* body *) = Return ... /\ ...) \/
       ...
   ]}

   The function body should be of the shape:
   {[
     x <- f y0 ... yn;
     ...
   ]}

   Or (typically if we expanded the monadic binds):
   {[
     case f y0 ... yn of
     ...
   ]}

   Or simply (typically if we reached the end of the function we're analyzing):
   {[
     f y0 ... yn
   ]}

   For all the above cases we would return [f y0 ... yn].
 *)
fun get_monadic_app_call (t : term) : term =
  (* We do something slightly imprecise but hopefully general and robut *)
  let
     (* Case 3.: strip the existential binders, and take the first disjuntion *)
     val t = (hd o strip_disj o snd o strip_exists) t;
     (* Case 2.: strip the existential binders, and take the first conjunction *)
     val t = (hd o strip_conj o snd o strip_exists) t;
     (* If it is an equality, take the lhs *)
     val t = if is_eq t then lhs t else t;
     (* Expand the binders to transform them to cases *)
     val t =
       (rhs o concl) (REWRITE_CONV [st_ex_bind_def] t)
       handle UNCHANGED => t;
     (* Strip all the cases *)
     val t = strip_all_cases_get_scrutinee t;
  in t end

(* Use the given theorem to progress by one step (we use this when
   analyzing a function body: this goes forward by one call to a monadic function).

   We transform the goal by:
   - pushing the theorem premises to a subgoal
   - adding the theorem conclusion in the assumptions in another goal, and
     getting rid of the monadic call

  Then [then_tac] receives as paramter the monadic call on which we applied
  the lemma. This can be useful, for instance, to make a case disjunction.

  This function is the most primitive of the [progress...] functions.
 *)
fun pure_progress_with (premise_tac : tactic)
  (then_tac : term -> thm_tactic) (th : thm) : tactic =
  fn (asms,g) =>
  let
    (* Remove all the universally quantified variables from the theorem *)
    val th = SPEC_ALL th;
    (* Retrieve the monadic call from the goal *)
    val fgoal = get_monadic_app_call g;
    (* Retrieve the app call from the theroem *)
    val gth = get_spec_app (concl th);
    (* Match and instantiate *)
    val (var_s, ty_s) = match_term gth fgoal;
    (* Instantiate the theorem *)
    val th = INST var_s (INST_TYPE ty_s th);
    (* Retrieve the premises of the theorem *)
    val th = PURE_REWRITE_RULE [GSYM satTheory.AND_IMP] th;
  in
    (* Apply the theorem *)
    intro_premise_then premise_tac (then_tac fgoal) th (asms, g)
  end

(*
val (asms, g) = top_goal ()
val t = g

val th = U32_SUB_EQ

val premise_tac =  massage >> TRY COOPER_TAC
fun then_tac fgoal =
  fn thm => ASSUME_TAC thm >> Cases_on ‘^fgoal’ >>
  rw [] >> fs [st_ex_bind_def] >> massage >> fs []

pure_progress_with premise_tac then_tac th
*)

fun progress_with (th : thm) : tactic =
  let
    val premise_tac = massage >> fs [] >> rw [] >> TRY COOPER_TAC;
    fun then_tac fgoal thm =
      ASSUME_TAC thm >> Cases_on ‘^fgoal’ >>
      rw [] >> fs [st_ex_bind_def] >> massage >> fs [];
  in
    pure_progress_with premise_tac then_tac th
  end

(*
progress_with U32_SUB_EQ
*)

(* This function lookups the theorem to use to make progress *)
val progress : tactic =
  fn (asms, g) =>
  let
    (* Retrieve the monadic call from the goal *)
    val fgoal = get_monadic_app_call g;
    val fname = get_fun_name_from_app fgoal;
    (* Lookup the theorem: first look in the assumptions (we might want to
       use the inductive hypothesis for instance) *)
    fun asm_to_spec asm =
      let
        (* Fail if there are no universal quantifiers *)
        val _ =
          if is_forall asm then asm
          else assert is_forall ((snd o strip_imp) asm);
        val asm_fname = (get_fun_name_from_app o get_spec_app) asm;
        (* Fail if the name is not the one we're looking for *)
        val _ = assert (fn n => fname = n) asm_fname;
      in
        ASSUME asm
      end
    val asms_thl = mapfilter asm_to_spec asms;
    (* Lookup a spec in the database *)
    val thl =
      case Redblackmap.peek (!reg_spec_thms, fname) of
        NONE => asms_thl
      | SOME spec => spec :: asms_thl;
    val _ =
      if null thl then
        raise (failwith "progress: could not find a suitable theorem to apply")
      else ();
  in
    (* Attempt to use the theorems one by one *)
    MAP_FIRST progress_with thl (asms, g)
  end

(*
val (asms, g) = top_goal ()
*)

(* TODO: no exfalso tactic?? *)
val EX_FALSO : tactic =
  SUBGOAL_THEN “F” (fn th => ASSUME_TAC th >> fs[])

Theorem nth_lem:
  !(ls : 't list_t) (i : u32).
    u32_to_int i < int_of_num (LENGTH (list_t_v ls)) ==>
    case nth ls i of
    | Return x => x = EL (Num (u32_to_int i)) (list_t_v ls)
    | Fail _ => F
    | Loop => F
Proof
  Induct_on ‘ls’ >> rw [list_t_v_def] >~ [‘ListNil’]
  >-(massage >> EX_FALSO >> COOPER_TAC) >>
  PURE_ONCE_REWRITE_TAC [nth_def] >> rw [] >>
  progress >> progress
QED

(* Example from the hashmap *)
val _ = new_constant ("insert", “: u32 -> 't -> (u32 # 't) list_t -> (u32 # 't) list_t result”)
val insert_def = new_axiom ("insert_def", “
 insert (key : u32) (value : 't) (ls : (u32 # 't) list_t) : (u32 # 't) list_t result =
  case ls of
  | ListCons (ckey, cvalue) tl =>
    if ckey = key
    then Return (ListCons (ckey, value) tl)
    else
      do
      tl0 <- insert key value tl;
      Return (ListCons (ckey, cvalue) tl0)
      od
  | ListNil => Return (ListCons (key, value) ListNil)
 ”)

(* Property that keys are pairwise distinct *)
val distinct_keys_def = Define ‘
  distinct_keys (ls : (u32 # 't) list) =
    !i j.
      i < LENGTH ls ==>
      j < LENGTH ls ==>
      FST (EL i ls) = FST (EL j ls) ==>
      i = j
’

val lookup_raw_def = Define ‘
  lookup_raw key [] = NONE /\
  lookup_raw key ((k, v) :: ls) =
    if k = key then SOME v else lookup_raw key ls
’

val lookup_def = Define ‘
  lookup key ls = lookup_raw key (list_t_v ls)
’

Theorem insert_lem:
  !ls key value.
    (* The keys are pairwise distinct *)
    distinct_keys (list_t_v ls) ==>
    case insert key value ls of
    | Return ls1 =>
      (* We updated the binding *)
      lookup key ls1 = SOME value /\
      (* The other bindings are left unchanged *)
      (!k. k <> key ==> lookup k ls = lookup k ls1)
    | Fail _ => F
    | Loop => F
Proof
  Induct_on ‘ls’ >> rw [list_t_v_def] >~ [‘ListNil’] >>
  PURE_ONCE_REWRITE_TAC [insert_def] >> rw []
  >- (rw [lookup_def, lookup_raw_def, list_t_v_def])
  >- (rw [lookup_def, lookup_raw_def, list_t_v_def]) >>
  CASE_TAC >> rw []
  >- (rw [lookup_def, lookup_raw_def, list_t_v_def])
  >- (rw [lookup_def, lookup_raw_def, list_t_v_def]) >>
  progress
  >- (
    fs [distinct_keys_def] >>
    rpt strip_tac >>
    first_assum (qspecl_then [‘SUC i’, ‘SUC j’] ASSUME_TAC) >>
    fs []
    (* Alternative: *)
    (*
      PURE_ONCE_REWRITE_TAC [GSYM prim_recTheory.INV_SUC_EQ] >>
      first_assum irule >> fs []
     *)) >>
  fs [lookup_def, lookup_raw_def, list_t_v_def]
QED

(***
 * Example of how to get rid of the fuel in practice
 *)
val nth_fuel_def = Define ‘
 nth_fuel (n : num) (ls : 't list_t) (i : u32) : 't result =
  case n of
  | 0 => Loop
  | SUC n => 
    do case ls of
    | ListCons x tl =>
      if u32_to_int i = (0:int)
      then Return x
      else
        do
        i0 <- u32_sub i (int_to_u32 1);
        nth_fuel n tl i0
        od
    | ListNil => 
      Fail Failure
    od
 ’

val is_loop_def = Define ‘is_loop r = case r of Loop => T | _ => F’
 
val nth_fuel_P_def = Define ‘
  nth_fuel_P ls i n = ~is_loop (nth_fuel n ls i)
’

Theorem nth_fuel_mono:
  !n m ls i.
    n <= m ==>
    if is_loop (nth_fuel n ls i) then T
    else nth_fuel n ls i = nth_fuel m ls i
Proof
  Induct_on ‘n’ >- (
    rpt gen_tac >>
    DISCH_TAC >>
    PURE_ONCE_REWRITE_TAC [nth_fuel_def] >>
    rw[is_loop_def]
  ) >>
  (* Interesting case *)
  rpt gen_tac >>
  DISCH_TAC >>
  CASE_TAC >>
  Cases_on ‘m’ >- (
    (* Contradiction: SUC n < 0 *)
    sg ‘SUC n = 0’ >- decide_tac >>
    fs [is_loop_def]
  ) >>
  fs [is_loop_def] >>
  pop_assum mp_tac >>
  PURE_ONCE_REWRITE_TAC [nth_fuel_def] >>
  fs [] >>
  DISCH_TAC >>
  (* We just have to explore all the paths: we can have dedicated tactics for that
     (we need to do case analysis) *)
  Cases_on ‘ls’ >> fs [] >>
  Cases_on ‘u32_to_int (i :u32) = (0 :int)’ >> fs [] >>
  fs [st_ex_bind_def] >>
  Cases_on ‘u32_sub (i :u32) (int_to_u32 (1 :int))’ >> fs [] >>
  (* Apply the induction hypothesis *)
  first_x_assum (qspecl_then [‘n'’, ‘l’, ‘a’] assume_tac) >>
  first_x_assum imp_res_tac >>
  pop_assum mp_tac >>
  CASE_TAC
QED

Theorem nth_fuel_P_mono:
  !n m ls i.
    n <= m ==>
    nth_fuel_P ls i n ==>
    nth_fuel n ls i = nth_fuel m ls i
Proof
  rpt gen_tac >> rpt DISCH_TAC >>
  fs [nth_fuel_P_def] >>
  imp_res_tac nth_fuel_mono >>
  pop_assum (qspecl_then [‘ls’, ‘i’] assume_tac) >>
  pop_assum mp_tac >> CASE_TAC >> fs []
QED

Theorem nth_fuel_least_fail_mono:
  !n ls i.
    n < $LEAST (nth_fuel_P ls i) ==>
    nth_fuel n ls i = Loop
Proof
  rpt gen_tac >>
  disch_tac >>
  imp_res_tac whileTheory.LESS_LEAST >>
  fs [nth_fuel_P_def, is_loop_def] >>
  pop_assum mp_tac >>
  CASE_TAC
QED

Theorem nth_fuel_least_success_mono:
  !n ls i.
    $LEAST (nth_fuel_P ls i) <= n ==>
    nth_fuel n ls i = nth_fuel ($LEAST (nth_fuel_P ls i)) ls i
Proof
  rpt gen_tac >>
  disch_tac >>
  (* Case disjunction on whether there exists a fuel such that it terminates *)
  Cases_on ‘?m. nth_fuel_P ls i m’ >- (
    (* Terminates *)
    irule EQ_SYM >>
    irule nth_fuel_P_mono >> fs [] >>
    (* Prove that calling with the least upper bound of fuel succeeds *)    
    qspec_then ‘nth_fuel_P (ls :α list_t) (i :u32)’ imp_res_tac whileTheory.LEAST_EXISTS_IMP
  ) >>
  (* Doesn't terminate *)
  fs [] >>
  sg ‘~(nth_fuel_P ls i n)’ >- fs [] >>
  sg ‘~(nth_fuel_P ls i ($LEAST (nth_fuel_P ls i)))’ >- fs [] >>
  fs [nth_fuel_P_def, is_loop_def] >>
  pop_assum mp_tac >> CASE_TAC >>
  pop_assum mp_tac >>
  pop_assum mp_tac >> CASE_TAC
QED

val nth_def_raw = Define ‘
  nth ls i =
    if (?n. nth_fuel_P ls i n) then nth_fuel ($LEAST (nth_fuel_P ls i)) ls i
    else Loop
’

(* This makes the proofs easier, in that it helps us control the context *)
val nth_expand_def = Define ‘
  nth_expand nth ls i =
    case ls of
    | ListCons x tl =>
      if u32_to_int i = (0:int)
      then Return x
      else
        do
        i0 <- u32_sub i (int_to_u32 1);
        nth tl i0
        od
    | ListNil => 
      Fail Failure
’             

(* Prove the important theorems *)
Theorem nth_def_terminates:
  !ls i.
  (?n. nth_fuel_P ls i n) ==>
  nth ls i =
    nth_expand nth ls i
Proof
  rpt strip_tac >>
  fs [nth_expand_def] >>
  PURE_ONCE_REWRITE_TAC [nth_def_raw] >>
  (* Prove that the least upper bound is <= n *)
  sg ‘$LEAST (nth_fuel_P ls i) <= n’ >-(
    qspec_then ‘nth_fuel_P (ls :α list_t) (i :u32)’ imp_res_tac whileTheory.LEAST_EXISTS_IMP >>
    spose_not_then assume_tac >> fs []
  ) >>
  (* Use the monotonicity theorem - TODO: ? *)
  imp_res_tac nth_fuel_least_success_mono >>
  (* Rewrite only on the left - TODO: easy way ?? *)
  qspecl_then [‘$LEAST (nth_fuel_P ls i)’, ‘ls’, ‘i’] assume_tac nth_fuel_def >>
  (* TODO: how to discard assumptions?? *)
  fs [] >> pop_assum (fn _ => fs []) >>
  (* Cases on the least upper bound *)
  Cases_on ‘$LEAST (nth_fuel_P ls i)’ >> rw [] >- (
    (* The bound is equal to 0: contradiction *)
    sg ‘nth_fuel 0 ls i = Loop’ >- (PURE_ONCE_REWRITE_TAC [nth_fuel_def] >> rw []) >>
    fs [nth_fuel_P_def, is_loop_def]
  ) >>
  (* Bound not equal to 0 *)
  fs [nth_fuel_P_def, is_loop_def] >>
  (* Explore all the paths *)
  fs [st_ex_bind_def] >>
  Cases_on ‘ls’ >> rw [] >> fs [] >>
  Cases_on ‘u32_sub i (int_to_u32 1)’ >> rw [] >> fs [] >>
  (* Recursive call: use monotonicity - we have an assumption which eliminates the Loop case *)
  Cases_on ‘nth_fuel n' l a’ >> rw [] >> fs [] >>
  (sg ‘nth_fuel_P l a n'’ >- fs [nth_fuel_P_def, is_loop_def]) >>
  (sg ‘$LEAST (nth_fuel_P l a) <= n'’ >-(
   qspec_then ‘nth_fuel_P l a’ imp_res_tac whileTheory.LEAST_EXISTS_IMP >>
   spose_not_then assume_tac >> fs [])) >>
  imp_res_tac nth_fuel_least_success_mono >> fs []
QED

(* Prove the important theorems *)
Theorem nth_def_loop:
  !ls i.
  (!n. ~nth_fuel_P ls i n) ==>
  nth ls i =
    nth_expand nth ls i
Proof
  rpt gen_tac >>
  PURE_ONCE_REWRITE_TAC [nth_def_raw] >>
  strip_tac >> rw[] >>
  (* Non-terminating case *)
  sg ‘∀n. ¬nth_fuel_P ls i (SUC n)’ >- rw [] >>
  fs [nth_fuel_P_def, is_loop_def] >>
  pop_assum mp_tac >>
  PURE_ONCE_REWRITE_TAC [nth_fuel_def] >>
  rw [] >>  
  fs [nth_expand_def] >>
  (* Evaluate all the paths *)
  fs [st_ex_bind_def] >>
  Cases_on ‘ls’ >> rw [] >> fs [] >>
  Cases_on ‘u32_sub i (int_to_u32 1)’ >> rw [] >> fs [] >>
  (* Use the definition of nth *)
  rw [nth_def_raw] >>
  first_x_assum (qspec_then ‘$LEAST (nth_fuel_P l a)’ assume_tac) >>
  Cases_on ‘nth_fuel ($LEAST (nth_fuel_P l a)) l a’ >> fs []
QED

(* The final theorem *)
Theorem nth_def:
  !ls i.
  nth ls i =
    case ls of
    | ListCons x tl =>
      if u32_to_int i = (0:int)
      then Return x
      else
        do
        i0 <- u32_sub i (int_to_u32 1);
        nth tl i0
        od
    | ListNil => 
      Fail Failure
Proof
  rpt strip_tac >>
  Cases_on ‘?n. nth_fuel_P ls i n’ >-(
    assume_tac nth_def_terminates >>
    fs [nth_expand_def] >>
    pop_assum irule >>
    metis_tac []) >>
  fs [] >> imp_res_tac nth_def_loop >> fs [nth_expand_def]
QED

(*

Je viens de finir ma petite expérimentation avec le fuel : ça marche bien. Par exemple, si je pose les définitions suivantes :
Datatype:
  result = Return 'a | Fail error | Loop
End

(* Omitting some definitions like the bind *)

val _ = Define ‘
 nth_fuel (n : num) (ls : 't list_t) (i : u32) : 't result =
  case n of
  | 0 => Loop
  | SUC n => 
    do case ls of
    | ListCons x tl =>
      if u32_to_int i = (0:int)
      then Return x
      else
        do
        i0 <- u32_sub i (int_to_u32 1);
        nth_fuel n tl i0
        od
    | ListNil => 
      Fail Failure
    od
 ’

val _ = Define 'is_loop r = case r of Loop => T | _ => F'
 
val _ = Define 'nth_fuel_P ls i n = ~is_loop (nth_fuel n ls i)'

(* $LEAST returns the least upper bound for a predicate (if it exists - otherwise it returns an arbitrary number) *)
val _ = Define ‘
  nth ls i =
    if (?n. nth_fuel_P ls i n) then nth_fuel ($LEAST (nth_fuel_P ls i)) ls i
    else Loop
’
J'arrive à montrer (c'est un chouïa technique) :
Theorem nth_def:
  !ls i.
  nth ls i =
    case ls of
    | ListCons x tl =>
      if u32_to_int i = (0:int)
      then Return x
      else
        do
        i0 <- u32_sub i (int_to_u32 1);
        nth tl i0
        od
    | ListNil => 
      Fail Failure

*)
