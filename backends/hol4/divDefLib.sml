structure divDefLib :> divDefLib =
struct

open primitivesBaseTacLib primitivesLib divDefTheory

val dbg = ref false
fun print_dbg s = if (!dbg) then print s else ()

val result_ty = “:'a result”
val error_ty = “:error”
val alpha_ty = “:'a”
val num_ty = “:num”

val zero_num_tm = “0:num”
val suc_tm = “SUC”

val return_tm = “Return : 'a -> 'a result”
val fail_tm = “Fail : error -> 'a result”
val fail_failure_tm = “Fail Failure : 'a result”
val diverge_tm = “Diverge : 'a result”

(* Switch to use ‘fix_exec’ (leading to executable definitions) and ‘fix’ (non
   executable) *)
val use_fix_exec = ref true

val fix_tm = “fix”
val fix_exec_tm = “fix_exec”
val is_valid_fp_body_tm = “is_valid_fp_body”

fun mk_result (ty : hol_type) : hol_type = Type.type_subst [ alpha_ty |-> ty ] result_ty
fun dest_result (ty : hol_type) : hol_type =
  let
    val {Args=out_ty, Thy=thy, Tyop=tyop} = dest_thy_type ty
  in
    if thy = "primitives" andalso tyop = "result" then hd out_ty
    else failwith "dest_result: not a result"
  end

fun mk_return (x : term) : term = mk_icomb (return_tm, x)
fun mk_fail (ty : hol_type) (e : term) : term = mk_comb (inst [ alpha_ty |-> ty ] fail_tm, e)
fun mk_fail_failure (ty : hol_type) : term = inst [ alpha_ty |-> ty ] fail_failure_tm
fun mk_diverge (ty : hol_type) : term = inst [ alpha_ty |-> ty ] diverge_tm

fun mk_suc (n : term) = mk_comb (suc_tm, n)

fun enumerate (ls : 'a list) : (int * 'a) list =
  zip (List.tabulate (List.length ls, fn i => i)) ls

(*=============================================================================*
 *
 * Generate the (non-recursive) body to give to the fixed-point operator
 *
 * ============================================================================*)

(* Small helper to generate wrappers of the shape: ‘INL x’, ‘INR (INL x)’, etc.
   Note that we should have: ‘length before_tys + 1 + length after tys >= 2’

   Ex.:
   ====
   The enumeration has type: “: 'a + 'b + 'c + 'd”.
   We want to generate the variant which injects “x:'c” into this enumeration.

   We need to split the list of types into:
   {[
     before_tys = [“:'a”, “'b”]
     tm = “x: 'c”
     after_tys = [“:'d”]
   ]}

   The function will generate:
   {[
     INR (INR (INL x) : 'a + 'b + 'c + 'd
   ]}

   (* Debug *)
   val before_tys = [“:'a”, “:'b”, “:'c”]
   val tm = “x:'d”
   val after_tys = [“:'e”, “:'f”]

   val before_tys = [“:'a”, “:'b”, “:'c”]
   val tm = “x:'d”
   val after_tys = []

   mk_inl_inr_wrapper before_tys tm after_tys
 *)
fun list_mk_inl_inr (before_tys : hol_type list) (tm : term) (after_tys : hol_type list) :
  term =
  let
    val (before_tys, pat) =
      if after_tys = []
      then
        let
          val just_before_ty = List.last before_tys
          val before_tys = List.take (before_tys, List.length before_tys - 1)
          val pat = sumSyntax.mk_inr (tm, just_before_ty)
        in
          (before_tys, pat)
        end
      else (before_tys, sumSyntax.mk_inl (tm, sumSyntax.list_mk_sum after_tys))
    val pat = foldr (fn (ty, pat) => sumSyntax.mk_inr (pat, ty)) pat before_tys
  in
    pat
  end

(* This function wraps a term into the proper variant of the input/output
   sum.

   Ex.:
   ====
   For the input of the first function, we generate: ‘INL x’
   For the output of the first function, we generate: ‘INR (INL x)’
   For the input of the 2nd function, we generate: ‘INR (INR (INL x))’
   etc.

   If ‘is_input’ is true: we are wrapping an input. Otherwise we are wrapping
   an output.

   (* Debug *)
   val tys = [(“:'a”, “:'b”), (“:'c”, “:'d”), (“:'e”, “:'f”)]
   val j = 1
   val tm = “x:'c”
   val tm = “y:'d”
   val is_input = true
 *)
fun inject_in_param_sum (tys : (hol_type * hol_type) list) (j : int) (is_input : bool)
  (tm : term) : term =
  let
    fun flatten ls = List.concat (map (fn (x, y) => [x, y]) ls)
    val before_tys = flatten (List.take (tys, j))
    val (input_ty, output_ty) = List.nth (tys, j)
    val after_tys = flatten (List.drop (tys, j + 1))
    val (before_tys, after_tys) =
      if is_input then (before_tys, output_ty :: after_tys)
      else (before_tys @ [input_ty], after_tys)
  in
    list_mk_inl_inr before_tys tm after_tys
  end

(* Remark: the order of the branches when creating matches is important.
   For instance, in the case of ‘result’ it must be: ‘Return’, ‘Fail’, ‘Diverge’.

   For the purpose of stability and maintainability, we introduce this small helper
   which reorders the cases in a pattern before actually creating the case
   expression.
 *)
fun unordered_mk_case (scrut: term, pats: (term * term) list) : term =
  let
    (* Retrieve the constructors *)
    val cl = TypeBase.constructors_of (type_of scrut)
    (* Retrieve the names of the constructors *)
    val names = map (fst o dest_const) cl
    (* Use those to reorder the patterns *)
    fun is_pat (name : string) (pat, _) =
      let
        val app = (fst o strip_comb) pat
        val app_name = (fst o dest_const) app
      in
        app_name = name
      end
    val pats = map (fn name => valOf (List.find (is_pat name) pats)) names
  in
    (* Create the case *)
    TypeBase.mk_case (scrut, pats)
  end

(* Wrap a term of type “:'a result” into a ‘case of’ which matches over
   the result.

   Ex.:
   ====
   {[
     f x

       ~~>

     case f x of
     | Fail e => Fail e
     | Diverge => Diverge
     | Return y => ... (* The branch content is generated by the continuation *)
   ]}

   ‘gen_ret_branch’ is a *continuation* which generates the content of the
   ‘Return’ branch (i.e., the content of the ‘...’ in the example above).
   It receives as input the value contained by the ‘Return’ (i.e., the variable
   ‘y’ in the example above).

   Remark.: the type of the term generated by ‘gen_ret_branch’ must have
   the type ‘result’, but it can change the content of the result (i.e.,
   if ‘scrut’ has type ‘:'a result’, we can change the type of the wrapped
   expression to ‘:'b result’).

   (* Debug *)
   val scrut = “x: int result”
   fun gen_ret_branch x = mk_return x

   val scrut = “x: int result”
   fun gen_ret_branch _ = “Return T”

   mk_result_case scrut gen_ret_branch
 *)
fun mk_result_case (scrut : term) (gen_ret_branch : term -> term) : term =
  let
    val scrut_ty = dest_result (type_of scrut)
    (* Return branch *)
    val ret_var = genvar scrut_ty
    val ret_pat = mk_return ret_var
    val ret_br = gen_ret_branch ret_var
    val ret_ty = dest_result (type_of ret_br)
    (* Failure branch *)
    val fail_var = genvar error_ty
    val fail_pat = mk_fail scrut_ty fail_var
    val fail_br = mk_fail ret_ty fail_var
    (* Diverge branch *)
    val div_pat = mk_diverge scrut_ty
    val div_br = mk_diverge ret_ty
  in
    unordered_mk_case (scrut, [(ret_pat, ret_br), (fail_pat, fail_br), (div_pat, div_br)])
  end

(* Generate a ‘case ... of’ over a sum type.

   Ex.:
   ====
   If the scrutinee is: “x : 'a + 'b + 'c” (i.e., the tys list is: [“:'a”, “:b”, “:c”]),
   we generate:

   {[
     case x of
     | INL y0 => ... (* Branch of index 0 *)
     | INR (INL y1) => ... (* Branch of index 1 *)
     | INR (INR (INL y2)) => ... (* Branch of index 2 *)
     | INR (INR (INR y3)) => ... (* Branch of index 3 *)
   ]}

   The content of the branches is generated by the ‘gen_branch’ continuation,
   which receives as input the index of the branch as well as the variable
   introduced by the pattern (in the example above: ‘y0’ for the branch 0,
   ‘y1’ for the branch 1, etc.)

   (* Debug *)
   val tys = [“:'a”, “:'b”]
   val scrut = mk_var ("x", sumSyntax.list_mk_sum tys)
   fun gen_branch i (x : term) = “F”

   val tys = [“:'a”, “:'b”, “:'c”, “:'d”]
   val scrut = mk_var ("x", sumSyntax.list_mk_sum tys)
   fun gen_branch i (x : term) = if type_of x = “:'c” then mk_return x else mk_fail_failure “:'c”

   list_mk_sum_case scrut tys gen_branch
 *)
(* For debugging *)
val list_mk_sum_case_case = ref (“T”, [] : (term * term) list)
(*
val (scrut, [(pat1, br1), (pat2, br2)]) = !list_mk_sum_case_case
*)
fun list_mk_sum_case (scrut : term) (tys : hol_type list)
  (gen_branch : int -> term -> term) : term =
  let
    (* Create the cases. Note that without sugar, the match actually looks like this:
       {[
         case x of
         | INL y0 => ... (* Branch of index 0 *)
         | INR x1
           case x1 of
           | INL y1 => ... (* Branch of index 1 *)
           | INR x2 =>
             case x2 of
             | INL y2 => ... (* Branch of index 2 *)
             | INR y3 => ... (* Branch of index 3 *)
       ]}
     *)
    fun create_case (j : int) (scrut : term) (tys : hol_type list) : term =
      let
        val _ = print_dbg ("list_mk_sum_case: " ^
                           String.concatWith ", " (map type_to_string tys) ^ "\n")
      in
        case tys of
          [] => failwith "tys is too short"
        | [ ty ] =>
          (* Last element: no match to perform *)
          gen_branch j scrut
        | ty1 :: tys =>
          (* Not last: we create a pattern:
             {[
               case scrut of
               | INL pat_var1 => ... (* Branch of index i *)
               | INR pat_var2 =>
                 ... (* Generate this term recursively *)
             ]}
           *)
          let
            (* INL branch *)
            val after_ty = sumSyntax.list_mk_sum tys
            val pat_var1 = genvar ty1
            val pat1 = sumSyntax.mk_inl (pat_var1, after_ty)
            val br1 = gen_branch j pat_var1
            (* INR branch *)
            val pat_var2 = genvar after_ty
            val pat2 = sumSyntax.mk_inr (pat_var2, ty1)
            val br2 = create_case (j+1) pat_var2 tys
            val _ = print_dbg ("list_mk_sum_case: assembling:\n" ^
                               term_to_string scrut ^ ",\n" ^
                               "[(" ^ term_to_string pat1 ^ ",\n  " ^ term_to_string br1 ^ "),\n\n" ^
                               " (" ^ term_to_string pat2 ^ ",\n  " ^ term_to_string br2 ^ ")]\n\n")
            val case_elems = (scrut, [(pat1, br1), (pat2, br2)])
            val _ = list_mk_sum_case_case := case_elems
          in
            (* Put everything together *)
            TypeBase.mk_case case_elems
          end
      end
  in
    create_case 0 scrut tys
  end

(* Generate a ‘case ... of’ to select the input/output of the ith variant of
   the param enumeration.

   Ex.:
   ====
   There are two functions in the group, and we select the input of the function of index 1:
   {[
     case x of
     | INL _ => Fail Failure              (* Input of function of index 0 *)
     | INR (INL _) => Fail Failure        (* Output of function of index 0 *)
     | INR (INR (INL y)) => Return y      (* Input of the function of index 1: select this one *)
     | INR (INR (INR _)) => Fail Failure  (* Output of the function of index 1 *)
   ]}

   (* Debug *)
   val tys = [(“:'a”, “:'b”)]
   val scrut = “x : 'a + 'b”
   val fi = 0
   val is_input = true

   val tys = [(“:'a”, “:'b”), (“:'c”, “:'d”)]
   val scrut = “x : 'a + 'b + 'c + 'd”
   val fi = 1
   val is_input = false

   val scrut = mk_var ("x", sumSyntax.list_mk_sum (flatten tys))

   list_mk_case_select scrut tys fi is_input
 *)
fun list_mk_case_sum_select (scrut : term) (tys : (hol_type * hol_type) list)
  (fi : int) (is_input : bool) : term =
  let
    (* The index of the element in the enumeration that we will select *)
    val i = 2 * fi + (if is_input then 0 else 1)
    (* Flatten the types and numerotate them *)
    fun flatten ls = List.concat (map (fn (x, y) => [x, y]) ls)
    val tys = flatten tys
    (* Get the return type *)
    val ret_ty = List.nth (tys, i)
    (* The continuation which will generate the content of the branches *)
    fun gen_branch j var = if j = i then mk_return var else mk_fail_failure ret_ty
  in
    (* Generate the ‘case ... of’ *)
    list_mk_sum_case scrut tys gen_branch
  end

(* Generate a ‘case ... of’ to select the input/output of the ith variant of
   the param enumeration.

   Ex.:
   ====
   There are two functions in the group, and we select the input of the function of index 1:
   {[
     case x of
     | Fail e => Fail e
     | Diverge => Diverge
     | Return r =>
       case r of
       | INL _ => Fail Failure              (* Input of function of index 0 *)
       | INR (INL _) => Fail Failure        (* Output of function of index 0 *)
       | INR (INR (INL y)) => Return y      (* Input of the function of index 1: select this one *)
       | INR (INR (INR _)) => Fail Failure  (* Output of the function of index 1 *)
   ]}
 *)
fun mk_case_select_result_sum (scrut : term) (tys : (hol_type * hol_type) list)
  (fi : int) (is_input : bool) : term =
  (* We match over the result, then over the enumeration *)
  mk_result_case scrut (fn x => list_mk_case_sum_select x tys fi is_input)

(* Generate a body for the fixed-point operator from a quoted group of mutually
   recursive definitions.

   See TODO for detailed explanations: from the quoted equations for ‘nth’
   (or for [‘even’, ‘odd’]) we generate the body ‘nth_body’ (or ‘even_odd_body’,
   respectively).
 *)
fun mk_body (fnames : string list) (in_out_tys : (hol_type * hol_type) list)
  (def_tms : term list) : term =
  let
    val fnames_set = Redblackset.fromList String.compare fnames

    (* Compute a map from function name to function index *)
    val fnames_map = Redblackmap.fromList String.compare
      (map (fn (x, y) => (y, x)) (enumerate fnames))

    (* Compute the input/output type, that we dub the "parameter type" *)
    fun flatten ls = List.concat (map (fn (x, y) => [x, y]) ls)
    val param_type = sumSyntax.list_mk_sum (flatten in_out_tys)

    (* Introduce a variable for the confinuation *)
    val fcont = genvar (param_type --> mk_result param_type)

    (* In the function equations, replace all the recursive calls with calls to the continuation.

       When replacing a recursive call, we have to do two things:
       - we need to inject the input parameters into the parameter type
         Ex.:
         - ‘nth tl i’ becomes ‘f (INL (tl, i))’ where ‘f’ is the continuation
         - ‘even i’ becomes ‘f (INL i)’ where ‘f’ is the continuation
       - we need to wrap the the call to the continuation into a ‘case ... of’
         to extract its output (we need to make sure that the transformation
         preserves the type of the expression!)
         Ex.: ‘nth tl i’ becomes:
         {[
           case f (INL (tl, i)) of
           | Fail e => Fail e
           | Diverge => Diverge
           | Return r =>
             case r of
             | INL _ => Fail Failure
             | INR x => Return (INR x)
         ]}
     *)
     (* For debugging *)
     val replace_rec_calls_rec_call_tm = ref “T”
     fun replace_rec_calls (fnames_set : string Redblackset.set) (tm : term) : term =
       let
         val _ = print_dbg ("replace_rec_calls: original expression:\n" ^
                            term_to_string tm ^ "\n\n")
         val ntm =
           case dest_term tm of
             VAR (name, ty) =>
             (* Check that this is not one of the functions in the group - remark:
                we could handle that by introducing lambdas.
              *)
             if Redblackset.member (fnames_set, name)
             then failwith ("mk_body: not well-formed definition: found " ^ name ^
                            " in an improper position")
             else tm
           | CONST _ => tm
           | LAMB (x, tm) =>
             let
               (* The variable might shadow one of the functions: remove it from
                  the set of function names - remark: Redblackset.delete raises
                  [NotFound] if the value is not present in the set *)
               val varname = (fst o dest_var) x
               val fnames_set =
                 if Redblackset.member (fnames_set, varname)
                 then Redblackset.delete (fnames_set, varname)
                 else fnames_set
               (* Update the term in the lambda *)
               val tm = replace_rec_calls fnames_set tm
             in
               (* Reconstruct *)
               mk_abs (x, tm)
             end
           | COMB (_, _) =>
             let
               (* Completely destruct the application, check if this is a recursive call *)
               val (app, args) = strip_comb tm
               val is_rec_call = Redblackset.member (fnames_set, (fst o dest_var) app)
                 handle HOL_ERR _ => false
               (* Whatever the case, apply the transformation to all the inputs *)
               val args = map (replace_rec_calls fnames_set) args
             in
               (* If this is not a recursive call: apply the transformation to all the
                  terms. Otherwise, replace. *)
               if not is_rec_call then list_mk_comb (replace_rec_calls fnames_set app, args)
               else
                 (* Rec call: replace *)
                 let
                   val _ = print_dbg ("replace_rec_calls: rec call\n\n")
                   val _ = replace_rec_calls_rec_call_tm := tm
                   (* First, find the index of the function *)
                   val fname = (fst o dest_var) app
                   val fi = Redblackmap.find (fnames_map, fname)
                   (* Inject the input values into the param type *)
                   val input = pairSyntax.list_mk_pair args
                   val input = inject_in_param_sum in_out_tys fi true input
                   (* Create the recursive call *)
                   val call = mk_comb (fcont, input)
                   (* Wrap the call into a ‘case ... of’ to extract the output *)
                   val call = mk_case_select_result_sum call in_out_tys fi false
                 in
                   (* Return *)
                   call
                 end
             end
         val _ = print_dbg ("replace_rec_calls: new expression:\n" ^ term_to_string ntm ^ "\n\n")
       in
         ntm
       end
       handle HOL_ERR e =>
         let
           val _ = print_dbg ("replace_rec_calls: failed on:\n" ^ term_to_string tm ^ "\n\n")
         in
           raise (HOL_ERR e)
         end
     fun replace_rec_calls_in_eq (eq : term) : term =
       let
         val (l, r) = dest_eq eq
       in
         mk_eq (l, replace_rec_calls fnames_set r)
       end
     val def_tms_with_fcont = map replace_rec_calls_in_eq def_tms

     (* Wrap all the function bodies to inject their result into the param type.

        We collect the function inputs at the same time, because they will be
        grouped into a tuple that we will have to deconstruct.
      *)
     fun inject_body_to_enums (i : int, def_eq : term) : term list * term =
       let
         val (l, body) = dest_eq def_eq
         val (_, args) = strip_comb l
         (* We have the deconstruct the result, then, in the ‘Return’ branch,
            properly wrap the returned value *)
         val body = mk_result_case body (fn x => mk_return (inject_in_param_sum in_out_tys i false x))
       in
         (args, body)
       end
     val def_tms_inject = map inject_body_to_enums (enumerate def_tms_with_fcont)

     (* Currify the body inputs.

        For instance, if the body has inputs: ‘x’, ‘y’; we return the following:
        {[
          (‘z’, ‘case z of (x, y) => ... (* body *) ’)
        ]}
        where ‘z’ is fresh.

        We return: (curried input, body).

        (* Debug *)
        val body = “(x:'a, y:'b, z:'c)”
        val args = [“x:'a”, “y:'b”, “z:'c”]
        currify_body_inputs (args, body)
      *)
     fun currify_body_inputs (args : term list, body : term) : term * term =
       let
         fun mk_curry (args : term list) (body : term) : term * term =
           case args of
             [] => failwith "no inputs"
           | [x] => (x, body)
           | x1 :: args =>
             let
               val (x2, body) = mk_curry args body
               val scrut = genvar (pairSyntax.list_mk_prod (map type_of (x1 :: args)))
               val pat = pairSyntax.mk_pair (x1, x2)
               val br = body
             in
               (scrut, TypeBase.mk_case (scrut, [(pat, br)]))
             end
       in
         mk_curry args body
       end
     val def_tms_currified = map currify_body_inputs def_tms_inject

     (* Group all the functions into a single body, with an outer ‘case .. of’
        which selects the appropriate body depending on the input *)
     val param_ty = sumSyntax.list_mk_sum (flatten in_out_tys)
     val input = genvar param_ty
     fun mk_mut_rec_body_branch (i : int) (patvar : term) : term =
       (* Case disjunction on whether the branch is for an input value (in
          which case we call the proper body) or an output value (in which
          case we return ‘Fail ...’ *)
       if i mod 2 = 0 then
         let
           val fi = i div 2
           val (x, def_tm) = List.nth (def_tms_currified, fi)
           (* The variable in the pattern and the variable expected by the
              body may not be the same: we introduce a let binding *)
           val def_tm = mk_let (mk_abs (x, def_tm), patvar)
         in
           def_tm
         end
       else
         (* Output value: fail *)
         mk_fail_failure param_ty
     val mut_rec_body = list_mk_sum_case input (flatten in_out_tys) mk_mut_rec_body_branch


     (* Abstract away the parameters to produce the final body of the fixed point *)
     val mut_rec_body = list_mk_abs ([fcont, input], mut_rec_body)
  in
    mut_rec_body
  end

(*=============================================================================*
 *
 * Prove that the body satisfies the validity condition
 *
 * ============================================================================*)

(* Tactic to prove that a body is valid: perform one step. *)
fun prove_body_is_valid_tac_step (asms, g) =
  let
    (* The goal has the shape:
       {[
         (∀g h. ... g x = ... h x) ∨
         ∃h y. is_valid_fp_body n h ∧ ∀g. ... g x = ... od
       ]}   
     *)
    (* Retrieve the scrutinee in the goal (‘x’) *)
    val body = (lhs o snd o strip_forall o fst o dest_disj) g
    val scrut = strip_all_cases_get_scrutinee_or_curried body
    (* Retrieve the first quantified continuations from the goal (‘g’) *)
    val qc = (hd o fst o strip_forall o fst o dest_disj) g
    (* Check if the scrutinee is a recursive call *)
    val (scrut_app, _) = strip_comb scrut
    val _ = print_dbg ("prove_body_is_valid_step: Scrutinee: " ^ term_to_string scrut ^ "\n")
    (* For the recursive calls: *)
    fun step_rec () =
      let
        val _ = print_dbg ("prove_body_is_valid_step: rec call\n")
        (* We need to instantiate the ‘h’ existantially quantified function *)
        (* First, retrieve the body of the function: it is given by the ‘Return’ branch *)
        val (_, _, branches) = TypeBase.dest_case body
        (* Find the branch corresponding to the return *)
        val ret_branch = List.find (fn (pat, _) =>
          let
            val {Name=name, Thy=thy, Ty = _ } = (dest_thy_const o fst o strip_comb) pat
          in
            thy = "primitives" andalso name = "Return"
          end) branches
        val var = (hd o snd o strip_comb o fst o valOf) ret_branch
        val br = (snd o valOf) ret_branch
        (* Abstract away the input variable introduced by the pattern and the continuation ‘g’ *)
        val h = list_mk_abs ([qc, var], br)
        val _ = print_dbg ("prove_body_is_valid_step: h: " ^ term_to_string h ^ "\n")
        (* Retrieve the input parameter ‘x’ *)
        val input = (snd o dest_comb) scrut
        val _ = print_dbg ("prove_body_is_valid_step: y: " ^ term_to_string input ^ "\n")
      in
        ((* Choose the right possibility (this is a recursive call) *)
         disj2_tac >>
         (* Instantiate the quantifiers *)
         qexists ‘^h’ >>
         qexists ‘^input’ >>
         (* Unfold the predicate once *)
         pure_once_rewrite_tac [is_valid_fp_body_def] >>
         (* We have two subgoals:
            - we have to prove that ‘h’ is valid
            - we have to finish the proof of validity for the current body
          *)
         conj_tac >> fs [case_result_switch_eq, bind_def] >>
         (* The first subgoal should have been eliminated *)
         gen_tac)
      end
  in
    (* If recursive call: special treatment. Otherwise, we do a simple disjunction *)
    (if term_eq scrut_app qc then step_rec ()
     else (Cases_on ‘^scrut’ >> fs [case_result_switch_eq])) (asms, g)
  end

(* Tactic to prove that a body is valid *)
fun prove_body_is_valid_tac (body_def : thm option) : tactic =
  let val body_def_thm = case body_def of SOME th => [th] | NONE => []
  in
    pure_once_rewrite_tac [is_valid_fp_body_def] >> gen_tac >>
    (* Expand *)
    fs body_def_thm >>
    fs [bind_def, case_result_switch_eq] >>
    (* Explore the body *)
    rpt prove_body_is_valid_tac_step
  end

(* Prove that a body satisfies the validity condition of the fixed point *)
fun prove_body_is_valid (body : term) : thm =
  let
    (* Explore the body and count the number of occurrences of recursive
       calls so that we can properly instantiate the ‘N’ argument of ‘is_valid_fp_body’
       (note: we compute an overapproximation).

       We first retrieve the name of the continuation parameter.

       Rem.: we generated fresh names so that, for instance, the continuation name
       doesn't collide with other names. Because of this, we don't need to look for
       collisions when exploring the body (and in the worst case, we would cound
       an overapproximation of the number of recursive calls).
     *)
    val fcont = (hd o fst o strip_abs) body
    val fcont_name = (fst o dest_var) fcont
    fun count_body_rec_calls (body : term) : int =
      case dest_term body of
        VAR (name, _) => if name = fcont_name then 1 else 0
      | CONST _ => 0
      | COMB (x, y) => count_body_rec_calls x + count_body_rec_calls y
      | LAMB (_, x) => count_body_rec_calls x
    val num_rec_calls = count_body_rec_calls body

    (* Generate the term ‘SUC (SUC ... (SUC n))’ where ‘n’ is a fresh variable.

       Remark: we first prove ‘is_valid_fp_body (SUC ... n) body’ then substitue
       ‘n’ with ‘0’ to prevent the quantity from being rewritten to a bit
       representation, which would prevent unfolding of the ‘is_valid_fp_body’.
     *)
    val nvar = genvar num_ty
    (* Rem.: we stack num_rec_calls + 1 occurrences of ‘SUC’ (and the + 1 is important) *)
    fun mk_n i = if i = 0 then mk_suc nvar else mk_suc (mk_n (i-1))
    val n_tm = mk_n num_rec_calls

    (* Generate the lemma statement *)
    val is_valid_tm = list_mk_icomb (is_valid_fp_body_tm, [n_tm, body])

    val is_valid_thm = prove (is_valid_tm, prove_body_is_valid_tac NONE)
    (* Replace ‘nvar’ with ‘0’ *)
    val is_valid_thm = INST [nvar |-> zero_num_tm] is_valid_thm
  in
    is_valid_thm
  end

(*=============================================================================*
 *
 * Generate the definitions with the fixed-point operator
 *
 * ============================================================================*)

(* Generate the raw definitions by using the grouped definition body and the
   fixed point operator *)
fun mk_raw_defs (in_out_tys : (hol_type * hol_type) list)
  (def_tms : term list) (body_is_valid : thm) : thm list =
  let
    (* Retrieve the body *)
    val body = (List.last o snd o strip_comb o concl) body_is_valid

    (* Create the term ‘fix_exec body’ *)
    val fixed_body = mk_icomb (if !use_fix_exec then fix_exec_tm else fix_tm, body)

    (* For every function in the group, generate the equation that we will
       use as definition. In particular:
       - add the properly injected input ‘x’ to ‘fix body’ (ex.: for ‘nth ls i’
         we add the input ‘INL (ls, i)’)
       - wrap ‘fix body x’ into a case disjunction to extract the relevant output

       For instance, in the case of ‘nth ls i’:
       {[
         nth (ls : 't list_t) (i : u32) =
           case fix nth_body (INL (ls, i)) of
           | Fail e => Fail e
           | Diverge => Diverge
           | Return r =>
             case r of
             | INL _ => Fail Failure
             | INR x => Return x
       ]}
     *)
    fun mk_def_eq (i : int, def_tm : term) : term =
      let
        (* Retrieve the lhs of the original definition equation, and in
           particular the inputs *)
        val def_lhs = lhs def_tm
        val args = (snd o strip_comb) def_lhs

        (* Inject the inputs into the param type *)
        val input = pairSyntax.list_mk_pair args
        val input = inject_in_param_sum in_out_tys i true input

        (* Compose*)
        val def_rhs = mk_comb (fixed_body, input)

        (* Wrap in the case disjunction *)
        val def_rhs = mk_case_select_result_sum def_rhs in_out_tys i false

        (* Create the equation *)
        val def_eq_tm = mk_eq (def_lhs, def_rhs)
      in
        def_eq_tm
      end
    val raw_def_tms = map mk_def_eq (enumerate def_tms)

    (* Generate the definitions *)
    val raw_defs = map (fn tm => Define ‘^tm’) raw_def_tms
  in
    raw_defs
  end

(*=============================================================================*
 *
 * Prove that the definitions satisfy the target equations
 *
 * ============================================================================*)

(* Tactic which makes progress in a proof by making a case disjunction (we use
   this to explore all the paths in a function body). *)
fun case_progress (asms, g) =
  let
    val scrut = (strip_all_cases_get_scrutinee o lhs) g
  in Cases_on ‘^scrut’ (asms, g) end

(* Prove the final equation, that we will use as definition. *)
fun prove_def_eq_tac
  (current_raw_def : thm) (all_raw_defs : thm list) (is_valid : thm)
  (body_def : thm option) : tactic =
  let
    val body_def_thm = case body_def of SOME th => [th] | NONE => []
    val fix_eq = if !use_fix_exec then fix_exec_fixed_eq else fix_fixed_eq
  in
    rpt gen_tac >>
    (* Expand the definition *)
    pure_once_rewrite_tac [current_raw_def] >>
    (* Use the fixed-point equality *)
    pure_once_rewrite_left_tac [HO_MATCH_MP fix_eq is_valid] >>
    (* Expand the body definition *)
    pure_rewrite_tac body_def_thm >>
    (* Expand all the definitions from the group *)
    pure_rewrite_tac all_raw_defs >>
    (* Explore all the paths - maybe we can be smarter, but this is fast and really easy *)
    fs [bind_def] >>
    rpt (case_progress >> fs [])
  end

(* Prove the final equations that we will give to the user as definitions *)
fun prove_def_eqs (body_is_valid : thm) (def_tms : term list) (raw_defs : thm list) : thm list=
  let
    val defs_tgt_raw = zip def_tms raw_defs
    (* Substitute the function variables with the constants introduced in the raw
       definitions *)
    fun compute_fsubst (def_tm, raw_def) : {redex: term, residue: term} =
      let
        val (fvar, _) = (strip_comb o lhs) def_tm
        val fconst = (fst o strip_comb o lhs o snd o strip_forall o concl) raw_def
      in
        (fvar |-> fconst)
      end
    val fsubst = map compute_fsubst defs_tgt_raw
    val defs_tgt_raw = map (fn (x, y) => (subst fsubst x, y)) defs_tgt_raw

    fun prove_def_eq (def_tm, raw_def) : thm =
      let
        (* Quantify the parameters *)
        val (_, params) = (strip_comb o lhs) def_tm
        val def_eq_tm = list_mk_forall (params, def_tm)
        (* Prove *)
        val def_eq = prove (def_eq_tm, prove_def_eq_tac raw_def raw_defs body_is_valid NONE)
      in
        def_eq
      end
    val def_eqs = map prove_def_eq defs_tgt_raw
  in
    def_eqs
  end

(*=============================================================================*
 *
 * The final DefineDiv function
 *
 * ============================================================================*)

type absyn = Absyn.absyn

(* Helper: convert an absyn to a vstruct (i.e., turn a "standard" term into
   a quantified term; we use it to transform function arguments into abstracted
   terms (in a lambda) *)
fun absyn_to_vstruct (x : absyn) : Absyn.vstruct =
  case x of
    Absyn.AQ (l, t) => Absyn.VAQ (l, t)
  | Absyn.IDENT (l, s) => Absyn.VIDENT (l, s)
  | Absyn.QIDENT _ => raise (mk_HOL_ERR "divDefLib" "absyn_to_vstruct" "Unsupported: QIDENT")
  | Absyn.APP _ => raise (mk_HOL_ERR "divDefLib" "absyn_to_vstruct" "Unsupported: APP")
  | Absyn.LAM _ => raise (mk_HOL_ERR "divDefLib" "absyn_to_vstruct" "Unsupported: LAM")
  | Absyn.TYPED (l, y, ty) => Absyn.VTYPED (l, absyn_to_vstruct y, ty)

(* We need to parse the quotation in a specific manner.

   The issue is that, with mutually recursive functions, the parser sometimes
   gets confused if some funtions have parameters with the same name but with
   different types.

   For instance:
   {[
     f (x : int) = ... /\
     g (x : bool) = ...
   ]}

   The solution is to rewrite the equations to make lambdas appear explicitely,
   like so:
   {[
     f = λ(x : int) = ... /\
     g = λ(x : bool) = ...
   ]}

   We do the following:
   - we convert the quotation to an abstract syntax tree
   - transform this tree into a shape where function bodies are abstractions
   - parse this to a term
   - change the shape of the term back to the original shape (with arguments
     on the left of the “=”)
 *)
fun parse_quote (defs_qt : term quotation) : term =
  let
    val def_abs = Parse.Absyn defs_qt
    val absl = Absyn.strip_conj def_abs

    (* Turn an equation of the shape “f x = ...” into “f = \x. ...” *)
    fun make_lambda_def (def_abs : absyn) : absyn =
      let
        (* Retrieve the body *)
        val (app, body) = Absyn.dest_eq def_abs
        (* Remove the typing annotation from around the lhs, if there is,
           and put it around the rhs *)
        val (app, body) =
          if Absyn.is_typed app then
            let val (app, ty) = Absyn.dest_typed app in (app, Absyn.mk_typed (body, ty)) end
          else (app, body)
        (* Strip the arguments *)
        val (f, args) = Absyn.strip_app app
        (* Make a lambda abstraction *)
        val args = map absyn_to_vstruct args
        val body = Absyn.list_mk_lam (args, body)
      in
        Absyn.mk_eq (f, body)
      end
    val absl = map make_lambda_def absl
    val def_abs = Absyn.list_mk_conj absl

    (* Parse the quote now that it is in the proper shape *)
    val def_tm =
      (* This is taken from Defn.sml: we removed the [sort_eqns] because it is not
         useful in our case (its untangle the dependencies so that functions are
         defined before use). *)
        fst (Defn.parse_absyn def_abs)
        handle e => raise wrap_exn "divDefLib" "parse_quote" e

    (* Put the definition back into the original shape *)
    fun make_args_def (tm : term) : term =
      let
        val (f, body) = dest_eq tm
        val (args, body) = strip_abs body
      in
        mk_eq (list_mk_comb (f, args), body)
      end
    val def_tms = strip_conj def_tm
    val def_tms = map make_args_def def_tms
    val def_tm = list_mk_conj def_tms
  in
    def_tm
  end

fun DefineDiv (def_qt : term quotation) =
  let
    (* Parse the definitions *)
    val def_tms = strip_conj (parse_quote def_qt)

    (* Compute the names and the input/output types of the functions *)
    fun compute_names_in_out_tys (tm : term) : string * (hol_type * hol_type) =
      let
        val app = lhs tm
        val name = (fst o dest_var o fst o strip_comb) app
        val out_ty = dest_result (type_of app)
        val input_tys = pairSyntax.list_mk_prod (map type_of ((snd o strip_comb) app))
      in
        (name, (input_tys, out_ty))
      end
    val (fnames, in_out_tys) = unzip (map compute_names_in_out_tys def_tms)

    (* Generate the body to give to the fixed-point operator *)
    val body = mk_body fnames in_out_tys def_tms

    (* Prove that the body satisfies the validity property required by the fixed point *)
    val body_is_valid = prove_body_is_valid body
    
    (* Generate the definitions for the various functions by using the fixed point
       and the body *)
    val raw_defs = mk_raw_defs in_out_tys def_tms body_is_valid

    (* Prove the final equations *)
    val def_eqs = prove_def_eqs body_is_valid def_tms raw_defs

    (* Save the final equations as definitions. *)
    val thm_names = map (fn x => x ^ "_def") fnames
    (* Because [store_definition] overrides existing names, it seems that in
       practice we don't really need to  delete the previous definitions
       (we still do it: it doesn't cost much). *)
    val _ = List.app delete_binding thm_names
    val _ = map store_definition (zip thm_names def_eqs)
    (* Also save the custom unfoldings, for evaluation (unit tests) *)
    val _ = evalLib.add_unfold_thms thm_names
  in
    def_eqs
  end

end
