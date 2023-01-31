(* This file implements utilities to define potentially diverging functions *)

open HolKernel boolLib bossLib Parse
open boolTheory arithmeticTheory integerTheory intLib listTheory stringTheory

open primitivesArithTheory primitivesBaseTacLib ilistTheory primitivesTheory
open primitivesLib

(* TODO:
pred_def_thms -> pred_defs
pred_def_thm -> pred_def
raw_def_thms -> raw_defs
raw_def_thm -> raw_def

fuel_defs_thm -> fuel_defs (and split the theorem)
*)

(* TotalDefn.Define *)

(*
Datatype:
  list_t =
    ListCons 't list_t
  | ListNil
End
*)

(* TODO: move *)
fun list_mk_arrow (tys : hol_type list) (ret_ty : hol_type) : hol_type =
  foldr (fn (ty, aty) => ty --> aty) ret_ty tys

(*“test (x : bool) = (x <> F)” *)

val def_qt = ‘
  (even (i : int) : bool result =
    if i = 0 then Return T else odd (i - 1)) /\
  (odd (i : int) : bool result =
    if i = 0 then Return F else even (i - 1))
’
val def_tms = (strip_conj o list_mk_conj o rev) (Defn.parse_quote def_qt)
val def_tm = hd def_tms

(* Small utilities *)
val current_goal : term option ref = ref NONE

(* Save a goal in {!current_goal} then prove it.

   This way if the proof fails we can easily retrieve the goal for debugging
   purposes.
 *)
fun save_goal_and_prove (g, tac) : thm =
  let
    val _ = current_goal := SOME g
  in
    prove (g, tac)
  end
  

(*val def_qt = ‘
(nth_fuel (n : num) (ls : 't list_t) (i : u32) : 't result =
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
    od)
’*)

val num_zero_tm = “0:num”
val num_suc_tm = “SUC: num -> num”
val num_ty = “:num”

val fuel_def_suffix = "___fuel" (* TODO: name collisions *)
val fuel_var_name = "$n" (* TODO: name collisions *)
val fuel_var = mk_var (fuel_var_name, num_ty)
val fuel_var0 = fuel_var
val fuel_var1 = mk_var ("$m", “:num”) (* TODO: name collisions *)
val fuel_vars_le = “^fuel_var0 <= ^fuel_var1”

val fuel_predicate_suffix = "___P" (* TODO: name collisions *)

val bool_ty = “:bool”

val alpha_tyvar : hol_type = “:'a”
val is_diverge_def = Define ‘
  is_diverge (r: 'a result) : bool = case r of Diverge => T | _ => F’
val is_diverge_tm = “is_diverge: 'a result -> bool”
val diverge_tm = “Diverge : 'a result”

val least_tm = “$LEAST”
val le_tm = (fst o strip_comb) “x:num <= y:num”
val true_tm = “T”
val false_tm = “F”

fun mk_diverge_tm (ty : hol_type) : term =
  let
    val diverge_ty = mk_thy_type {Thy="primitives", Tyop="result", Args = [ty] }
    val diverge_tm = mk_thy_const { Thy="primitives", Name="Diverge", Ty=diverge_ty }
  in
    diverge_tm
  end

fun mk_fuel_defs (def_tms : term list) : thm =
  let
    (* Retrieve the identifiers.

       Ex.: def_tm = “even (n : int) : bool result = if i = 0 then Return T else odd (i - 1))”
       We want to retrive: id = “even”
     *)
    val app = lhs def_tm
    val ids = map (fst o strip_comb o lhs) def_tms
    (* In the definitions, replace the identifiers by new identifiers which use
       fuel.

       Ex.:
       def_fuel_tm = “
         even_fuel (fuel : nat) (n : int) : result bool =
           case fuel of 0 => Diverge
           | SUC fuel => 
             if i = 0 then Return T else odd_fuel (i - 1))”
     *)
     fun mk_fuel_id (id : term) : term =
       let
         val (id_str, ty) = dest_var id
         (* Note: we use symbols forbidden in the generation of code to
            prevent name collisions *)
         val fuel_id_str = id_str ^ fuel_def_suffix
         val fuel_id = mk_var (fuel_id_str, num_ty --> ty)
       in fuel_id end
     val fuel_ids = map mk_fuel_id ids

     val fuel_ids_with_fuel = map (fn id => mk_comb (id, fuel_var)) fuel_ids

     (* Recurse through the terms and replace the calls *)
     val rwr_thms = map (ASSUME o mk_eq) (zip ids fuel_ids_with_fuel)
     val fuel_tms = map (rhs o concl o (PURE_REWRITE_CONV rwr_thms)) def_tms

     (* Add the case over the fuel *)
     fun add_fuel_case (tm : term) : term =
       let
         val (app, body) = dest_eq tm
         (* Create the “Diverge” term with the proper type *)
         val body_ty = type_of body
         val return_ty =
           case (snd o dest_type) body_ty of [ty] => ty
           | _ => failwith "unexpected"
         val diverge_tm = mk_diverge_tm return_ty
         (* Create the “SUC fuel” term *)
         val suc_tm = mk_comb (num_suc_tm, fuel_var)
         val fuel_tm = TypeBase.mk_case (fuel_var, [(num_zero_tm, diverge_tm), (suc_tm, body)])
       in mk_eq (app, fuel_tm) end
     val fuel_tms = map add_fuel_case fuel_tms

     (* Define the auxiliary definitions which use fuel *)
     val fuel_defs_conj = list_mk_conj fuel_tms
     (* Define the fuel definitions *)
     val fuel_defs_thm = Define ‘^fuel_defs_conj’
   in
     fuel_defs_thm
   end

(*
val (fuel_tms, fuel_defs_thm) = mk_fuel_defs def_tms
val fuel_def_tms = map (snd o strip_forall) ((strip_conj o concl) fuel_defs_thm)
val (def_tm, fuel_def_tm) = hd (zip def_tms fuel_def_tms)
*)

fun mk_is_diverge_tm (fuel_tm : term) : term =
  case snd (dest_type (type_of fuel_tm)) of
    [ret_ty] => mk_comb (inst [alpha_tyvar |-> ret_ty] is_diverge_tm, fuel_tm)
   | _ => failwith "mk_is_diverge_tm: unexpected"

fun mk_fuel_predicate_defs (def_tm, fuel_def_tm) : thm =
  let
    (* From [even i] create the term [even_P i n], where [n] is the fuel *)
    val (id, args) = (strip_comb o lhs) def_tm
    val (id_str, id_ty) = dest_var id
    val {Args=tys, Thy=thy, Tyop=tyop} = dest_thy_type id_ty
    val _ = assert (fn x => x = "fun") tyop;
    val tys = rev tys;
    val ret_ty = hd tys;
    val tys = rev (num_ty :: tl tys);
    val pred_ty = list_mk_arrow tys bool_ty
    val pred_id = mk_var (id_str ^ fuel_predicate_suffix, pred_ty)
    val pred_tm = list_mk_comb (pred_id, append args [fuel_var])

    (* Create the term ~is_diverge (even_fuel n i) *)
    val fuel_tm = lhs fuel_def_tm
    val not_is_diverge_tm = mk_neg (mk_is_diverge_tm fuel_tm)

    (* Create the term: even_P i n = ~(is_diverge (even_fuel n i) *)
    val pred_def_tm = mk_eq (pred_tm, not_is_diverge_tm)
  in
    (* Create the definition *)
    Define ‘^pred_def_tm’
  end

(*
val pred_def_thms = map mk_fuel_predicate_defs (zip def_tms fuel_def_tms)
*)

(* Tactic which makes progress in a proof by making a case disjunction (we use
   this to explore all the paths in a function body). *)
fun case_progress (asms, g) =
  let
    val scrut = (strip_all_cases_get_scrutinee o lhs) g
  in Cases_on ‘^scrut’ (asms, g) end

(* Tactic to prove the fuel monotonicity theorem *)
fun prove_fuel_mono_tac (pred_def_thms : thm list) (fuel_defs_thm : thm) =
  Induct_on ‘^fuel_var0’ >-(
    (* The ___P predicates are false: n is 0 *)
    fs pred_def_thms >>
    fs [is_diverge_def] >>
    pure_once_rewrite_tac [fuel_defs_thm] >> fs []) >>
  gen_tac >>
  Cases_on ‘^fuel_var1’ >-(
    (* Contradiction: SUC n < 0 *)
    rw [] >> exfalso >> int_tac) >>
  fs pred_def_thms >>
  fs [is_diverge_def] >>
  pure_once_rewrite_tac [fuel_defs_thm] >> fs [bind_def] >>
  (* Split the goals *)
  rw [] >>
  (* Explore all the paths *)
  rpt (case_progress >> fs [])

(* Prove the fuel monotonicity properties.

   We want to prove a theorem of the shape:
   {[
     !n m.
       (!i. n <= m ==> even___P i n ==> even___fuel n i = even___fuel m i) /\
       (!i. n <= m ==> odd___P i n ==> odd___fuel n i = odd___fuel m i)
   ]}
*)
fun prove_fuel_mono (pred_def_thms : thm list) (fuel_defs_thm : thm) : thm =
  let
    val pred_tms = map (lhs o snd o strip_forall o concl) pred_def_thms
    val fuel_tms = map (lhs o snd o strip_forall o concl) (CONJUNCTS fuel_defs_thm)
    val pred_fuel_tms = zip pred_tms fuel_tms
    (* Generate terms of the shape:
       !i. n <= m ==> even___P i n ==> even___fuel n i = even___fuel m i
     *)
    fun mk_fuel_eq_tm (pred_tm, fuel_tm) : term =
      let
        (* Retrieve the variables which are not the fuel - for the quantifiers *)
        val vars = (tl o snd o strip_comb) fuel_tm
        (* Introduce the fuel term which uses “m” *)
        val m_fuel_tm = subst [fuel_var0 |-> fuel_var1] fuel_tm
        (* Introduce the equality *)
        val fuel_eq_tm = mk_eq (fuel_tm, m_fuel_tm)
        (* Introduce the implication with the _P pred *)
        val fuel_eq_tm = mk_imp (pred_tm, fuel_eq_tm)
        (* Introduce the “n <= m ==> ...” implication *)
        val fuel_eq_tm = mk_imp (fuel_vars_le, fuel_eq_tm)
        (* Quantify *)
        val fuel_eq_tm = list_mk_forall (vars, fuel_eq_tm)
      in fuel_eq_tm end
     val fuel_eq_tms = map mk_fuel_eq_tm pred_fuel_tms
     (* Create the conjunction *)
     val fuel_eq_tms = list_mk_conj fuel_eq_tms
(*     (* Add the “n <= m ==> ...” implication *)
     val fuel_eq_tms = mk_imp (fuel_vars_le, fuel_eq_tms) *)
     (* Qantify over the fuels *)
     val fuel_eq_tms = list_mk_forall ([fuel_var0, fuel_var1], fuel_eq_tms)
   in
     (* Prove *)
     save_goal_and_prove (fuel_eq_tms, prove_fuel_mono_tac pred_def_thms fuel_defs_thm)
   end

(*
val fuel_mono_thm = prove_fuel_mono pred_def_thms fuel_defs_thm
*)

(* Prove the property about the least upper bound.

   We want to prove theorems of the shape:
   {[
     (!n i. $LEAST (even___P i) <= n ==> even___fuel n i = even___fuel ($LEAST (even___P i)) i)
   ]}
   {[
     (!n i. $LEAST (odd___P i) <= n ==> odd___fuel n i = odd___fuel ($LEAST (odd___P i)) i)
   ]}

   TODO: merge with other functions? (prove_pred_imp_fuel_eq_raw_thms)
*)
fun prove_least_fuel_mono (pred_def_thms : thm list) (fuel_mono_thm : thm) : thm list =
  let
    val thl = (CONJUNCTS o SPECL [fuel_var0, fuel_var1]) fuel_mono_thm
    fun mk_least_fuel_thm (pred_def_thm, mono_thm) : thm =
      let
        (* Retrieve the predicate, without the fuel *)
        val pred_tm = (lhs o snd o strip_forall o concl) pred_def_thm
        val (pred_tm, args) = strip_comb pred_tm
        val args = rev (tl (rev args))
        val pred_tm = list_mk_comb (pred_tm, args)
        (* Add $LEAST *)
        val least_pred_tm = mk_comb (least_tm, pred_tm)
        (* Specialize all *)
        val vars = (fst o strip_forall o concl) mono_thm
        val th = SPECL vars mono_thm
        (* Substitute in the mono theorem *)
        val th = INST [fuel_var0 |-> least_pred_tm] th
        (* Symmetrize the equality *)
        val th = PURE_ONCE_REWRITE_RULE [EQ_SYM_EQ] th
        (* Quantify *)
        val th = GENL (fuel_var1 :: vars) th
      in
        th
      end
  in
    map mk_least_fuel_thm (zip pred_def_thms thl)
  end

(* Prove theorems of the shape:

   {[
     !n i. even___P i n ==> $LEAST (even___P i) <= n
   ]}

   TODO: merge with other functions? (prove_pred_imp_fuel_eq_raw_thms)
 *)
fun prove_least_pred_thms (pred_def_thms : thm list) : thm list =
  let
    fun prove_least_pred_thm (pred_def_thm : thm) : thm =
      let
        val pred_tm = (lhs o snd o strip_forall o concl) pred_def_thm
        val (pred_no_fuel_tm, args) = strip_comb pred_tm
        val args = rev (tl (rev args))
        val pred_no_fuel_tm = list_mk_comb (pred_no_fuel_tm, args)
        (* Make the “$LEAST (even___P i)” term *)
        val least_pred_tm = mk_comb (least_tm, pred_no_fuel_tm)
        (* Make the inequality *)
        val tm = list_mk_comb (le_tm, [least_pred_tm, fuel_var0])
        (* Add the implication *)
        val tm = mk_imp (pred_tm, tm)
        (* Quantify *)
        val tm = list_mk_forall (args, tm)
        val tm = mk_forall (fuel_var0, tm)
        (* Prove *)
        val prove_tac =
          rpt gen_tac >>
          disch_tac >>
          (* Use the "fundamental" property about $LEAST *)
          qspec_assume ‘^pred_no_fuel_tm’ whileTheory.LEAST_EXISTS_IMP >>
          (* Prove the premise *)
          pop_assum sg_premise_tac >- (exists_tac fuel_var0 >> fs []) >>
          rw [] >>
          (* Finish the proof by contraposition *)
          spose_not_then assume_tac >>
          fs [not_le_eq_gt]
      in
        save_goal_and_prove (tm, prove_tac)
      end
  in
    map prove_least_pred_thm pred_def_thms
  end


(*
val least_pred_thms = prove_least_pred_thms pred_def_thms

val least_pred_thm = hd least_pred_thms
*)

(* Prove theorems of the shape:

   {[
     !n i. even___P i n ==> even___P i ($LEAST (even___P i))
   ]}
*)
fun prove_pred_n_imp_pred_least_thms (pred_def_thms : thm list) : thm list =
  let
    fun prove_pred_n_imp_pred_least (pred_def_thm : thm) : thm =
      let
        val pred_tm = (lhs o snd o strip_forall o concl) pred_def_thm
        val (pred_no_fuel_tm, args) = strip_comb pred_tm
        val args = rev (tl (rev args))
        val pred_no_fuel_tm = list_mk_comb (pred_no_fuel_tm, args)
        (* Make the “$LEAST (even___P i)” term *)
        val least_pred_tm = mk_comb (least_tm, pred_no_fuel_tm)
        (* Make the “even___P i ($LEAST (even___P i))” *)
        val tm = subst [fuel_var0 |-> least_pred_tm] pred_tm
        (* Add the implication *)
        val tm = mk_imp (pred_tm, tm)
        (* Quantify *)
        val tm = list_mk_forall (args, tm)
        val tm = mk_forall (fuel_var0, tm)
        (* The proof tactic *)
        val prove_tac =
          rpt gen_tac >>
          disch_tac >>
          (* Use the "fundamental" property about $LEAST *)
          qspec_assume ‘^pred_no_fuel_tm’ whileTheory.LEAST_EXISTS_IMP >>
          (* Prove the premise *)
          pop_assum sg_premise_tac >- (exists_tac fuel_var0 >> fs []) >>
          rw []
      in
        save_goal_and_prove (tm, prove_tac)
      end
  in
    map prove_pred_n_imp_pred_least pred_def_thms
  end

(*
val (pred_def_thm, mono_thm) = hd (zip pred_def_thms thl)
val least_fuel_mono_thms = prove_least_fuel_mono pred_def_thms fuel_defs_thm fuel_mono_thm

val least_fuel_mono_thm = hd least_fuel_mono_thms
*)

(* Define the "raw" definitions:

   {[
     even i = if (?n. even___P i n) then even___P ($LEAST (even___P i)) i else Diverge
   ]}
 *)
fun define_raw_defs (def_tms : term list) (pred_def_thms : thm list) (fuel_defs_thm : thm) : thm list =
  let
    fun define_raw_def (def_tm, (pred_def_thm, fuel_def_thm)) : thm =
      let
        val app = lhs def_tm
        val pred_tm = (lhs o snd o strip_forall o concl) pred_def_thm
        (* Make the “?n. even___P i n” term *)
        val exists_fuel_tm = mk_exists (fuel_var0, pred_tm)
        (* Make the “even___fuel ($LEAST (even___P i)) i” term *)
        val fuel_tm = (lhs o snd o strip_forall o concl) fuel_def_thm
        val (pred_tm, args) = strip_comb pred_tm
        val args = rev (tl (rev args))
        val pred_tm = list_mk_comb (pred_tm, args)
        val least_pred_tm = mk_comb (least_tm, pred_tm)
        val fuel_tm = subst [fuel_var0 |-> least_pred_tm] fuel_tm
        (* Create the Diverge term *)
        val ret_ty = (hd o snd o dest_type) (type_of app)
        (* Create the “if then else” *)
        val body = TypeBase.mk_case (exists_fuel_tm, [(true_tm, fuel_tm), (false_tm, mk_diverge_tm ret_ty)])
        (* *)
        val raw_def_tm = mk_eq (app, body)
      in
        Define ‘^raw_def_tm’
      end
  in
    map define_raw_def (zip def_tms (zip pred_def_thms (CONJUNCTS fuel_defs_thm)))
  end

(*
val raw_def_thms = define_raw_defs def_tms pred_def_thms fuel_defs_thm
 *)

(*
val pred_def_thm = hd pred_def_thms

val pred_n_imp_pred_least_thms = prove_pred_n_imp_pred_least_thms pred_def_thms

val pred_n_imp_pred_least_thm = hd pred_n_imp_pred_least_thms
*)

(* Prove theorems of the shape:

   !n i. even___P i n ==> even___fuel n i = even i
 *)
fun prove_pred_imp_fuel_eq_raw_def_thms
  (pred_def_thms : thm list)
  (fuel_def_tms : term list)
  (least_fuel_mono_thms : thm list)
  (least_pred_thms : thm list)
  (pred_n_imp_pred_least_thms : thm list)
  (raw_def_thms : thm list) :
  thm list =
  let
    fun prove_thm (pred_def_thm,
                   (fuel_def_tm,
                    (least_fuel_mono_thm,
                     (least_pred_thm,
                      (pred_n_imp_pred_least_thm, raw_def_thm))))) : thm =
      let
        (* Generate: “even___P i n” *)
        val pred_tm = (lhs o snd o strip_forall o concl) pred_def_thm
        val (pred_no_fuel_tm, args) = strip_comb pred_tm
        val args = rev (tl (rev args))
        (* Generate: “even___fuel n i” *)
        val fuel_tm = lhs fuel_def_tm
        (* Generate: “even i” *)
        val raw_def_tm = (lhs o snd o strip_forall o concl) raw_def_thm
        (* Generate: “even___fuel n i = even i” *)
        val tm = mk_eq (fuel_tm, raw_def_tm)
        (* Add the implication *)
        val tm = mk_imp (pred_tm, tm)
        (* Quantify *)
        val tm = list_mk_forall (args, tm)
        val tm = mk_forall (fuel_var0, tm)
        (* Prove *)
        val prove_tac =
          rpt gen_tac >>
          strip_tac >>
          fs raw_def_thms >>
          (* Case on ‘?n. even___P i n’ *)
          CASE_TAC >> fs [] >>
          (* Use the monotonicity property *)
          irule least_fuel_mono_thm >>
          imp_res_tac pred_n_imp_pred_least_thm >> fs [] >>
          irule least_pred_thm >> fs []
      in
        save_goal_and_prove (tm, prove_tac)
      end
  in
    map prove_thm (zip pred_def_thms (zip fuel_def_tms (zip least_fuel_mono_thms
                   (zip least_pred_thms (zip pred_n_imp_pred_least_thms raw_def_thms)))))
  end

(*
val pred_imp_fuel_eq_raw_def_thms =
  prove_pred_imp_fuel_eq_raw_def_thms
    pred_def_thms fuel_def_tms least_fuel_mono_thms least_pred_thms
    pred_n_imp_pred_least_thms raw_def_thms

val (pred_def_thm,
                   (fuel_def_tm,
                    (least_fuel_mono_thm,
                     (least_pred_thm,
                      (pred_n_imp_pred_least_thm, raw_def_thm))))) =
  hd (zip pred_def_thms (zip fuel_def_tms (zip least_fuel_mono_thms
                   (zip least_pred_thms (zip pred_n_imp_pred_least_thms raw_def_thms)))))
 *)


(* Generate "expand" definitions of the following shape (we use them to
   hide the raw function bodies, to control the rewritings):

   {[
     even___expand even odd i : bool result =
       if i = 0 then Return T else odd (i - 1)
   ]}

   {[
     odd___expand even odd i : bool result =
       if i = 0 then Return F else even (i - 1)
   ]}

 *)
fun gen_expand_defs (def_tms : term list) =
  let
    (* Generate the variables for “even”, “odd”, etc. *)
    val fun_vars = map (fst o strip_comb o lhs) def_tms
    val fun_tys = map type_of fun_vars
    (* Generate the expansion *)
    fun mk_def (def_tm : term) : thm =
      let
        val (exp_fun, args) = (strip_comb o lhs) def_tm
        val (exp_fun_str, exp_fun_ty) = dest_var exp_fun
        val exp_fun_str = exp_fun_str ^ expand_suffix
        val exp_fun_ty = list_mk_arrow fun_tys exp_fun_ty
        val exp_fun = mk_var (exp_fun_str, exp_fun_ty)
        val exp_fun = list_mk_comb (exp_fun, fun_vars)
        val exp_fun = list_mk_comb (exp_fun, args)
        val tm = mk_eq (exp_fun, rhs def_tm)
      in
        Define ‘^tm’
      end
  in
    map mk_def def_tms
  end

(*
val def_tm = hd def_tms

val expand_defs = gen_expand_defs def_tms
*)

(* Small utility:

   Return the list:
   {[
     (“even___P i n”, “even i = even___expand even odd i”),
     ...
   ]}
   
 *)
fun mk_termination_diverge_tms
  (pred_def_thms : thm list)
  (raw_def_thms : thm list)
  (expand_defs : thm list) :
  (term * term) list =
  let
    (* Create the substitution for the "expand" functions:
       {[
         even -> even
         odd -> odd
         ...
       ]}

       where on the left we have *variables* and on the right we have
       the "raw" definitions.
     *)
    fun mk_fun_subst (def_tm, raw_def_thm) =
      let
        val var = (fst o strip_comb o lhs) def_tm
        val f = (fst o strip_comb o lhs o snd o strip_forall o concl) raw_def_thm
      in
        (var |-> f)
      end
    val fun_subst = map mk_fun_subst (zip def_tms raw_def_thms)
  
    fun mk_tm (pred_def_thm, (raw_def_thm, expand_def)) :
      term * term =
      let
        (* “even___P i n” *)
        val pred_tm = (lhs o snd o strip_forall o concl) pred_def_thm
        (* “even i = even___expand even odd i” *)
        val expand_tm = (lhs o snd o strip_forall o concl) expand_def
        val expand_tm = subst fun_subst expand_tm
        val fun_tm = (lhs o snd o strip_forall o concl) raw_def_thm
        val fun_eq_tm = mk_eq (fun_tm, expand_tm)
      in (pred_tm, fun_eq_tm) end
  in
    map mk_tm (zip pred_def_thms (zip raw_def_thms expand_defs))
  end

(*
val term_div_tms =
  mk_termination_diverge_tms pred_def_thms raw_def_thms expand_defs
*)

(* Prove the termination lemmas:
   
   {[
     !i.
       (?n. even___P i n) ==>
         even i = even___expand even odd i
   ]}
 *)
fun prove_termination_thms
  (term_div_tms : (term * term) list)
  (fuel_defs_thm : thm)
  (pred_def_thms : thm list)
  (raw_def_thms : thm list)
  (expand_defs : thm list)
  (pred_n_imp_pred_least_thms : thm list)
  (pred_imp_fuel_eq_raw_def_thms : thm list)
  : thm list =
  let
    (* Create a map from functions in the recursive group to lemmas
       to apply *)
    fun mk_rec_fun_eq_pair (fuel_def_thm, eq_th) =
      let
        val rfun = (get_fun_name_from_app o lhs o snd o strip_forall o concl) fuel_def_thm
      in
        (rfun, eq_th)
      end
    val rec_fun_eq_map =
      Redblackmap.fromList const_name_compare (
        map mk_rec_fun_eq_pair
          (zip (CONJUNCTS fuel_defs_thm) pred_imp_fuel_eq_raw_def_thms))

    (* Small tactic which rewrites the recursive calls *)
    fun rewrite_rec_call (asms, g) =
      let
        val scrut = (strip_all_cases_get_scrutinee o lhs) g
        val fun_id = get_fun_name_from_app scrut (* This can fail *)
        (* This can raise an exception - hence the handle at the end
           of the function *)
        val eq_th = Redblackmap.find (rec_fun_eq_map, fun_id)
        val eq_th = (UNDISCH_ALL o SPEC_ALL) eq_th
        (* Match the theorem *)
        val eq_th_tm = (lhs o concl) eq_th
        val (var_s, ty_s) = match_term eq_th_tm scrut
        val eq_th = INST var_s (INST_TYPE ty_s eq_th)
        val eq_th = thm_to_conj_implies eq_th
        (* Some tactics *)
        val premise_tac = fs pred_def_thms >> fs [is_diverge_def]
      in
        (* Apply the theorem, prove the premise, and rewrite *)
        (prove_premise_then premise_tac assume_tac eq_th >> fs []) (asms, g)
      end handle NotFound => all_tac (asms, g)
          | HOL_ERR _ => all_tac (asms, g) (* Getting the function name can also fail *)
  
    fun prove_one ((pred_tm, fun_eq_tm), pred_n_imp_pred_least_thm) :
      thm =
      let
        (* “?n. even___P i n” *)
        val pred_tm = mk_exists (fuel_var0, pred_tm)
        (* “even i = even___expand even odd i” *)
        val tm = fun_eq_tm
        (* Add the implication *)
        val tm = mk_imp (pred_tm, tm)
        (* Quantify *)
        val (_, args) = strip_comb fun_tm
        val tm = list_mk_forall (args, tm)

        (* Prove *)
        val prove_tac =
          rpt gen_tac >>
          disch_tac >>

          (* Expand the raw definition and get rid of the ‘?n ...’ *)
          pure_once_rewrite_tac raw_def_thms >>
          pure_asm_rewrite_tac [] >>

          (* Simplify *)
          fs [] >>

          (* Prove that: “even___P i $(LEAST ...)” *)
          imp_res_tac pred_n_imp_pred_least_thm >>

          (* We don't need the ‘even___P i n’ assumption anymore: we have a more
             precise one with the least upper bound *)
          last_x_assum ignore_tac >>

          (* Expand *)
          fs pred_def_thms >>
          fs [is_diverge_def] >>
          fs expand_defs >>

          (* We need to be a bit careful when expanding the definitions which use fuel:
             it can make the simplifier loop. *)
          rpt (pop_assum mp_tac) >>
          pure_once_rewrite_tac [fuel_defs_thm]  >>
          rpt disch_tac >>

          (* Expand the binds *)
          fs [bind_def] >>

          (* Explore all the paths by doing case disjunctions *)
          rpt (rewrite_rec_call >> case_progress >> fs [])
      in
        save_goal_and_prove (tm, prove_tac)
      end
  in
    map prove_one
      (zip term_div_tms pred_n_imp_pred_least_thms)
  end

(*
val termination_thms =
  prove_termination_thms term_div_tms fuel_defs_thm pred_def_thms
    raw_def_thms expand_defs pred_n_imp_pred_least_thms
    pred_imp_fuel_eq_raw_def_thms

val expand_def = hd expand_defs

val all_args = (zip pred_def_thms (zip raw_def_thms (zip expand_defs pred_n_imp_pred_least_thms)))
val (pred_def_thm, (raw_def_thm, (expand_def,  pred_n_imp_pred_least_thm))) = hd all_args
val (pred_def_thm, (raw_def_thm, (expand_def,  pred_n_imp_pred_least_thm))) = hd (tl all_args)

set_goal ([], tm)
*)

(* Prove the divergence lemmas:

   {[
     !i.
       (!n. ~even___P i n) ==>
        (!n. ~even___P i (SUC n)) ==>
         even i = even___expand even odd i
   ]}

   Note that the shape of the theorem is very precise: this helps for the proof.
   Also, by correctly ordering the assumptions, we make sure that by rewriting
   we don't convert one of the two to “T”.
 *)
fun prove_divergence_thms
  (term_div_tms : (term * term) list)
  (fuel_defs_thm : thm)
  (pred_def_thms : thm list)
  (raw_def_thms : thm list)
  (expand_defs : thm list)
  : thm list =
  let
    (* Create a set containing the names of all the functions in the recursive group *)
    fun get_rec_fun_id (fuel_def_thm : thm) =
     (get_fun_name_from_app o lhs o snd o strip_forall o concl) fuel_def_thm
    val rec_fun_set =
      Redblackset.fromList const_name_compare (
        map get_rec_fun_id raw_def_thms)

    (* Small tactic which rewrites the recursive calls *)
    fun rewrite_rec_call (asms, g) =
      let
        val scrut = (strip_all_cases_get_scrutinee o lhs) g
        val fun_id = get_fun_name_from_app scrut (* This can fail *)
      in
        (* Check if the function is part of the group we are considering *)
        if Redblackset.member (rec_fun_set, fun_id) then
          let
            (* Create a subgoal “odd i = Diverge” *)
            val ret_ty = (hd o snd o dest_type o type_of) scrut
            val g = mk_eq (scrut, mk_diverge_tm ret_ty)

            (* Create a subgoal: “?n. odd___P i n”.

               It is a bit cumbersome because we have to lookup the proper
               predicate (from “odd” we need to lookup “odd___P”) and we
               may have to perform substitutions... We hack a bit by using
               a conversion to rewrite “odd i” to a term which contains
               the “?n. odd___P i n” we are looking for.
             *)
            val exists_g = (rhs o concl) (PURE_REWRITE_CONV raw_def_thms scrut)
            val (_, exists_g, _) = TypeBase.dest_case exists_g
            (* The tactic to prove the subgoal *)
            val prove_sg_tac =
              pure_rewrite_tac raw_def_thms >>
              Cases_on ‘^exists_g’ >> pure_asm_rewrite_tac [] >> fs [] >>
              (* There must only remain the positive case (i.e., “?n. ...”):
                 we have a contradiction *)
              exfalso >>
              (* The end of the proof is done by opening the definitions *)
              pop_assum mp_tac >>
              fs pred_def_thms >> fs [is_diverge_def]
          in
            (SUBGOAL_THEN g assume_tac >- prove_sg_tac >> fs []) (asms, g)
          end
        else all_tac (asms, g) (* Nothing to do *)
      end handle HOL_ERR _ => all_tac (asms, g)
  
    fun prove_one (pred_tm, fun_eq_tm) :
      thm =
      let
        (* “!n. ~even___P i n” *)
        val neg_pred_tm = mk_neg pred_tm
        val pred_tm = mk_forall (fuel_var0, neg_pred_tm)
        val pred_suc_tm = subst [fuel_var0 |-> numSyntax.mk_suc fuel_var0] neg_pred_tm
        val pred_suc_tm = mk_forall (fuel_var0, pred_suc_tm)

        (* “even i = even___expand even odd i” *)
        val tm = fun_eq_tm

        (* Add the implications *)
        val tm = list_mk_imp ([pred_tm, pred_suc_tm], tm)

        (* Quantify *)
        val (_, args) = strip_comb fun_tm
        val tm = list_mk_forall (args, tm)

        (* Prove *)
        val prove_tac =
          rpt gen_tac >>

          pure_rewrite_tac raw_def_thms >>
          rpt disch_tac >>

          (* This allows to simplify the “?n. even___P i n” *)
          fs [] >>
          (* We don't need the last assumption anymore *)
          last_x_assum ignore_tac >>

          (* Expand *)
          fs pred_def_thms >> fs [is_diverge_def] >>
          fs expand_defs >>

          (* We need to be a bit careful when expanding the definitions which use fuel:
             it can make the simplifier loop.
           *)
          pop_assum mp_tac >>
          pure_once_rewrite_tac [fuel_defs_thm]  >>
          rpt disch_tac >> fs [] >>

          (* Evaluate all the paths *)
          rpt (rewrite_rec_call >> case_progress >> fs [])
      in
        save_goal_and_prove (tm, prove_tac)
      end
  in
    map prove_one term_div_tms
  end

(*
val divergence_thms =
  prove_divergence_thms
    term_div_tms
    fuel_defs_thm
    pred_def_thms
    raw_def_thms
    expand_defs

val (pred_tm, fun_eq_tm) = hd term_div_tms

set_goal ([], tm)

val (asms, g) = top_goal ()
*)
