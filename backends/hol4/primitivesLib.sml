(* Advanced tactics for the primitives library *)
structure primitivesLib =
struct

open HolKernel boolLib bossLib Parse
open boolTheory arithmeticTheory integerTheory intLib listTheory stringTheory

open primitivesArithTheory primitivesBaseTacLib ilistTheory primitivesTheory

val primitives_theory_name = "primitives"

(* Small utility: compute the set of assumptions in the context.

   We isolate this code in a utility in order to be able to improve it:
   for now we simply put all the assumptions in a set, but in the future
   we might want to split the assumptions which are conjunctions in order
   to be more precise.
 *)
fun compute_asms_set ((asms,g) : goal) : term Redblackset.set =
  Redblackset.fromList Term.compare asms

val integer_bounds_defs_list = [
  i8_min_def,
  i8_max_def,
  i16_min_def,
  i16_max_def,
  i32_min_def,
  i32_max_def,
  i64_min_def,
  i64_max_def,
  i128_min_def,
  i128_max_def,
  u8_max_def,
  u16_max_def,
  u32_max_def,
  u64_max_def,
  u128_max_def
]

val integer_bounds_lemmas =
  Redblackmap.fromList String.compare
  [
    ("isize", isize_to_int_bounds),
    ("i8", i8_to_int_bounds),
    ("i16", i16_to_int_bounds),
    ("i32", i32_to_int_bounds),
    ("i64", i64_to_int_bounds),
    ("i128", i128_to_int_bounds),
    ("usize", usize_to_int_bounds),
    ("u8", u8_to_int_bounds),
    ("u16", u16_to_int_bounds),
    ("u32", u32_to_int_bounds),
    ("u64", u64_to_int_bounds),
    ("u128", u128_to_int_bounds)
  ]

val integer_types_names =
  Redblackset.fromList String.compare
  (map fst (Redblackmap.listItems integer_bounds_lemmas))

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
  assume_tacl lemmas
  end

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
    val vartys_set = ref (Redblackset.empty String.compare);
    (* Filter the variables to keep only the ones with type machine integer,
       decompose the types at the same time *)
    fun decompose_var (v : term) : (string * string) =
      let
        val (v, ty) = dest_var v;
        val {Args=args, Thy=thy, Tyop=ty} = dest_thy_type ty;
        val _ = assert null args;
        val _ = assert (fn thy => thy = primitives_theory_name) thy;
        val _ = assert (fn ty => Redblackset.member (integer_types_names, ty)) ty;
        val _ = vartys_set := Redblackset.add (!vartys_set, ty);
      in (v, ty) end;
    val vars = mapfilter decompose_var vars; 
    (* Add assumptions for one variable *)
    fun add_var_asm (v, ty) : tactic =
      assume_bounds_for_int_var asms_set v ty;
    (* Add the bounds for isize, usize *)
    val size_bounds =
      append
        (if Redblackset.member (!vartys_set, "usize") then CONJUNCTS usize_bounds else [])
        (if Redblackset.member (!vartys_set, "isize") then CONJUNCTS isize_bounds else []);
    val size_bounds =
      filter (fn th => not (Redblackset.member (asms_set, concl th))) size_bounds;
  in
    ((* Add assumptions for all the variables *)
     map_every_tac add_var_asm vars >>
     (* Add assumptions about the size bounds *)
     assume_tacl size_bounds) (asms, g)
  end

val integer_conversion_lemmas_list = [
  isize_to_int_int_to_isize,
  i8_to_int_int_to_i8,
  i16_to_int_int_to_i16,
  i32_to_int_int_to_i32,
  i64_to_int_int_to_i64,
  i128_to_int_int_to_i128,
  usize_to_int_int_to_usize,
  u8_to_int_int_to_u8,
  u16_to_int_int_to_u16,
  u32_to_int_int_to_u32,
  u64_to_int_int_to_u64,
  u128_to_int_int_to_u128
]

(* Look for conversions from integers to machine integers and back.
   {[
     u32_to_int (int_to_u32 x)
   ]}

   Attempts to prove and apply equalities of the form:
   {[
     u32_to_int (int_to_u32 x) = x
   ]}
 *)
val rewrite_with_dep_int_lemmas : tactic =
  (* We're not trying to be smart: we just try to rewrite with each theorem at
     a time *)
  let
    val prove_premise = full_simp_tac simpLib.empty_ss integer_bounds_defs_list >> int_tac;
    val then_tac1 = (fn th => full_simp_tac simpLib.empty_ss [th]);
    val rewr_tac1 = apply_dep_rewrites_match_concl_with_all_tac prove_premise then_tac1;
    val then_tac2 = (fn th => full_simp_tac simpLib.empty_ss [th]);
    val rewr_tac2 = apply_dep_rewrites_match_first_premise_with_all_tac (fn _ => true) prove_premise then_tac2;
  in
      map_every_tac rewr_tac1 integer_conversion_lemmas_list >>
      map_every_tac rewr_tac2 []
  end

(* Massage a bit the goal, for instance by introducing integer bounds in the
   assumptions.
*)
val massage : tactic =
  assume_bounds_for_all_int_vars >>
  rewrite_with_dep_int_lemmas

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

val all_add_eqs = [
  isize_add_eq,
  i8_add_eq,
  i16_add_eq,
  i32_add_eq,
  i64_add_eq,
  i128_add_eq,
  usize_add_eq,
  u8_add_eq,
  u16_add_eq,
  u32_add_eq,
  u64_add_eq,
  u128_add_eq
]
val _ = app register_spec_thm all_add_eqs

val all_sub_eqs = [
  isize_sub_eq,
  i8_sub_eq,
  i16_sub_eq,
  i32_sub_eq,
  i64_sub_eq,
  i128_sub_eq,
  usize_sub_eq,
  u8_sub_eq,
  u16_sub_eq,
  u32_sub_eq,
  u64_sub_eq,
  u128_sub_eq
]
val _ = app register_spec_thm all_sub_eqs

val all_mul_eqs = [
  isize_mul_eq,
  i8_mul_eq,
  i16_mul_eq,
  i32_mul_eq,
  i64_mul_eq,
  i128_mul_eq,
  usize_mul_eq,
  u8_mul_eq,
  u16_mul_eq,
  u32_mul_eq,
  u64_mul_eq,
  u128_mul_eq
]
val _ = app register_spec_thm all_mul_eqs

val all_div_eqs = [
  isize_div_eq,
  i8_div_eq,
  i16_div_eq,
  i32_div_eq,
  i64_div_eq,
  i128_div_eq,
  usize_div_eq,
  u8_div_eq,
  u16_div_eq,
  u32_div_eq,
  u64_div_eq,
  u128_div_eq
]
val _ = app register_spec_thm all_div_eqs

val all_rem_eqs = [
  isize_rem_eq,
  i8_rem_eq,
  i16_rem_eq,
  i32_rem_eq,
  i64_rem_eq,
  i128_rem_eq,
  usize_rem_eq,
  u8_rem_eq,
  u16_rem_eq,
  u32_rem_eq,
  u64_rem_eq,
  u128_rem_eq
]
val _ = app register_spec_thm all_rem_eqs

val all_vec_lems = [
  vec_len_spec,
  vec_insert_back_spec
]
val _ = app register_spec_thm all_vec_lems

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
       (rhs o concl) (REWRITE_CONV [bind_def] t)
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
    sg_premise_then premise_tac (then_tac fgoal) th (asms, g)
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
      mp_tac thm >> strip_tac >> Cases_on ‘^fgoal’ >>
      fs [bind_def] >> massage >> fs [];
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
    map_first_tac progress_with thl (asms, g)
  end

end
