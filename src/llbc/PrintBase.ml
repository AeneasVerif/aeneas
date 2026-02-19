include Charon.PrintUtils
include Charon.PrintTypes
include Charon.PrintLlbcAst
open Charon.PrintTypes
open Charon.PrintExpressions
open Types
open Values
open ValuesUtils
open Expressions
open LlbcAst

(** Helper to make a function which colorizes text *)
let mk_colorize ((r, g, b) : int * int * int) : string -> string =
  (* ANSI escape sequence for 24-bit RGB foreground color *)
  let color_start = Printf.sprintf "\027[38;2;%d;%d;%dm" r g b in
  (* ANSI escape sequence to reset formatting *)
  let color_end = "\027[0m" in
  fun text ->
    if !Config.log_with_colors then color_start ^ text ^ color_end else text

let value_to_rgb (t : float) : int * int * int =
  (* Clamp t to [0, 1] *)
  let fmax (x : float) (y : float) = if x > y then x else y in
  let fmin (x : float) (y : float) = if x > y then y else x in
  let t = fmax 0.0 (fmin 1.0 t) in

  (* Scale t to [0, 3) to identify which segment we're in *)
  let scaled = t *. 3.0 in
  let segment = int_of_float scaled in
  let local_t = scaled -. float_of_int segment in

  (* Interpolate within the segment *)
  let r, g, b =
    match segment with
    | 0 ->
        (* red to green *)
        ( int_of_float (255.0 *. (1.0 -. local_t)),
          int_of_float (255.0 *. local_t),
          0 )
    | 1 ->
        (* green to blue *)
        ( 0,
          int_of_float (255.0 *. (1.0 -. local_t)),
          int_of_float (255.0 *. local_t) )
    | _ ->
        (* blue to red (segment 2 or edge case for t=1.0) *)
        ( int_of_float (255.0 *. local_t),
          0,
          int_of_float (255.0 *. (1.0 -. local_t)) )
  in
  (r, g, b)

let num_colors = 19 (* choosing a prime number on purpose *)
let borrow_factor = 13 (* prime with [num_color] *)
let symb_id_factor = 17 (* prime with [num_color] *)

let rotating_colors =
  let rec enumerate n = if n = 0 then [ 0 ] else n :: enumerate (n - 1) in
  let l = enumerate (num_colors - 1) in
  let floats =
    List.map (fun x -> float_of_int x /. float_of_int num_colors) l
  in
  Array.of_list (List.map value_to_rgb floats)

let get_color (i : int) : int * int * int =
  let i = i mod num_colors in
  Array.get rotating_colors i

let type_color = (0, 255, 255)
let abs_cont_color = type_color
let borrow_color = (255, 0, 0)
let loan_color = (255, 109, 35)
let borrow_proj_color = (255, 0, 255)
let loan_proj_color = (184, 0, 255)
let var_color = (0, 250, 0)
let abs_color = var_color

let add_type_color s =
  if !Config.log_rotating_colors then mk_colorize (200, 200, 200) s
  else mk_colorize type_color s

let add_var_color s =
  if !Config.log_rotating_colors then mk_colorize (56, 193, 49) s
  else mk_colorize var_color s

let add_borrow_color id =
  if !Config.log_rotating_colors then
    mk_colorize (get_color (BorrowId.to_int id * borrow_factor))
  else mk_colorize borrow_color

let add_loan_color id =
  if !Config.log_rotating_colors then
    mk_colorize (get_color (BorrowId.to_int id * borrow_factor))
  else mk_colorize loan_color

let add_borrow_proj_color id =
  if !Config.log_rotating_colors then
    mk_colorize (get_color (SymbolicValueId.to_int id * symb_id_factor))
  else mk_colorize borrow_proj_color

let add_loan_proj_color id =
  if !Config.log_rotating_colors then
    mk_colorize (get_color (SymbolicValueId.to_int id * symb_id_factor))
  else mk_colorize loan_proj_color

let add_abs_color s =
  if !Config.log_rotating_colors then mk_colorize (0, 97, 170) s
  else mk_colorize abs_color s

let add_abs_cont_color s =
  if !Config.log_rotating_colors then mk_colorize (65, 174, 204) s
  else mk_colorize abs_cont_color s

let list_to_string ?(sep = "; ") (to_string : 'a -> string) (ls : 'a list) :
    string =
  "[" ^ String.concat sep (List.map to_string ls) ^ "]"

let pair_to_string (to_string0 : 'a -> string) (to_string1 : 'b -> string)
    ((x, y) : 'a * 'b) : string =
  "(" ^ to_string0 x ^ ", " ^ to_string1 y ^ ")"

let bool_to_string (b : bool) : string = if b then "true" else "false"

(** Pretty-printing for values *)
module Values = struct
  include Charon.PrintValues

  let symbolic_value_id_to_pretty_string (id : SymbolicValueId.id) : string =
    "s@" ^ SymbolicValueId.to_string id

  let symbolic_value_to_string (env : fmt_env) (sv : symbolic_value) : string =
    (symbolic_value_id_to_pretty_string sv.sv_id
    |> add_borrow_proj_color sv.sv_id)
    ^ " : "
    ^ (ty_to_string env sv.sv_ty |> add_type_color)

  let symbolic_value_proj_to_string (env : fmt_env) (sv_id : symbolic_value_id)
      (rty : ty) : string =
    symbolic_value_id_to_pretty_string sv_id
    ^ " <: "
    ^ (ty_to_string env rty |> add_type_color)

  let adt_to_string (span : Meta.span option) (env : fmt_env)
      (value_to_debug_string : unit -> string) (ty : ty)
      (variant_id : variant_id option) (fields : string list) : string =
    match ty with
    | TArray _ ->
        (* Happens when we aggregate values *)
        "@Array[" ^ String.concat ", " fields ^ "]"
    | TAdt { id = TTuple; _ } ->
        (* Tuple *)
        "(" ^ String.concat ", " fields ^ ")"
    | TAdt { id = TAdtId def_id; _ } ->
        (* "Regular" ADT *)
        let adt_ident =
          match variant_id with
          | Some vid -> adt_variant_to_string env def_id vid
          | None -> type_decl_id_to_string env def_id
        in
        if List.length fields > 0 then
          match adt_field_names env def_id variant_id with
          | None ->
              let fields = String.concat ", " fields in
              adt_ident ^ " (" ^ fields ^ ")"
          | Some field_names ->
              let fields = List.combine field_names fields in
              let fields =
                List.map
                  (fun (field, value) -> field ^ " = " ^ value ^ ";")
                  fields
              in
              let fields = String.concat " " fields in
              adt_ident ^ " { " ^ fields ^ " }"
        else adt_ident
    | TAdt { id = TBuiltin aty; _ } -> (
        (* Builtin type *)
        match (aty, fields) with
        | TBox, [ bv ] -> "@Box(" ^ bv ^ ")"
        | _ ->
            [%craise_opt_span] span
              ("Inconsistent value: " ^ value_to_debug_string ()))
    | _ ->
        [%craise_opt_span] span
          ("Inconsistently typed value: " ^ value_to_debug_string ())

  (* TODO: it may be a good idea to try to factorize this function with
   * tavalue_to_string. At some point we had done it, because [tvalue]
   * and [tavalue] were instances of the same general type [g_tvalue],
   * but then we removed this general type because it proved to be a bad idea. *)
  let rec tvalue_to_string ?(span : Meta.span option = None) (env : fmt_env)
      (v : tvalue) : string =
    match v.value with
    | VLiteral cv -> literal_to_string cv
    | VAdt av ->
        let fields = List.map (tvalue_to_string ~span env) av.fields in
        adt_to_string span env
          (fun () -> show_tvalue v)
          v.ty av.variant_id fields
    | VBottom -> "⊥ : " ^ ty_to_string env v.ty
    | VBorrow bc -> borrow_content_to_string ~span env bc
    | VLoan lc -> loan_content_to_string ~span env lc
    | VSymbolic s -> symbolic_value_to_string env s

  and borrow_content_to_string ?(span : Meta.span option = None) (env : fmt_env)
      (bc : borrow_content) : string =
    match bc with
    | VSharedBorrow (bid, sid) ->
        add_borrow_color bid
          ("SB@" ^ BorrowId.to_string bid ^ "(^"
          ^ SharedBorrowId.to_string sid
          ^ ")")
    | VMutBorrow (bid, tv) ->
        add_borrow_color bid ("MB@" ^ BorrowId.to_string bid)
        ^ " ("
        ^ tvalue_to_string ~span env tv
        ^ ")"
    | VReservedMutBorrow (bid, sid) ->
        add_borrow_color bid
          ("RB@" ^ BorrowId.to_string bid ^ "(^"
          ^ SharedBorrowId.to_string sid
          ^ ")")

  and loan_content_to_string ?(span : Meta.span option = None) (env : fmt_env)
      (lc : loan_content) : string =
    match lc with
    | VSharedLoan (lid, v) ->
        add_loan_color lid ("SL@" ^ BorrowId.to_string lid)
        ^ "("
        ^ tvalue_to_string ~span env v
        ^ ")"
    | VMutLoan bid -> add_loan_color bid ("ML@" ^ BorrowId.to_string bid)

  let abstract_shared_borrow_to_string (env : fmt_env)
      (abs : abstract_shared_borrow) : string =
    match abs with
    | AsbBorrow (bid, sid) ->
        "@" ^ BorrowId.to_string bid ^ "(^" ^ SharedBorrowId.to_string sid ^ ")"
        |> add_borrow_color bid
    | AsbProjReborrows proj ->
        "{" ^ symbolic_value_proj_to_string env proj.sv_id proj.proj_ty ^ "}"
        |> add_borrow_proj_color proj.sv_id

  let abstract_shared_borrows_to_string (env : fmt_env)
      (abs : abstract_shared_borrows) : string =
    "{"
    ^ String.concat "," (List.map (abstract_shared_borrow_to_string env) abs)
    ^ "}"

  let rec aproj_to_string ?(with_ended : bool = false) (env : fmt_env)
      (pv : aproj) : string =
    match pv with
    | AProjLoans proj -> aproj_loans_to_string ~with_ended env proj
    | AProjBorrows proj -> aproj_borrows_to_string ~with_ended env proj
    | AEndedProjLoans { proj = msv; consumed; borrows } ->
        let msv =
          if with_ended then
            "original_loan = " ^ symbolic_value_id_to_pretty_string msv
          else "_"
        in
        let consumed =
          if consumed = [] then ""
          else
            let consumed = List.map snd consumed in
            let consumed =
              List.map (aproj_to_string ~with_ended env) consumed
            in
            ", consumed=[" ^ String.concat "," consumed ^ "]"
        in
        let borrows =
          if borrows = [] then ""
          else
            let borrows = List.map snd borrows in
            let borrows = List.map (aproj_to_string ~with_ended env) borrows in
            ", borrows=[" ^ String.concat "," borrows ^ "]"
        in
        "ended_aproj_loans (" ^ msv ^ consumed ^ borrows ^ ")"
    | AEndedProjBorrows { mvalues; loans } ->
        let meta =
          if with_ended then
            "original_borrow = "
            ^ symbolic_value_id_to_pretty_string mvalues.consumed
            ^ ", given_back = "
            ^ symbolic_value_to_string env mvalues.given_back
          else "_"
        in
        let loans =
          if loans = [] then ""
          else
            let loans = List.map snd loans in
            let loans = List.map (aproj_to_string ~with_ended env) loans in
            ", loans=[" ^ String.concat "," loans ^ "]"
        in
        "ended_aproj_borrows (" ^ meta ^ loans ^ ")"
    | AEmpty -> "_"

  and aproj_borrows_to_string ?(with_ended : bool = false) (env : fmt_env)
      (proj : aproj_borrows) =
    let { proj; loans } : aproj_borrows = proj in
    let loans =
      if loans = [] then ""
      else
        let loans = List.map snd loans in
        let loans = List.map (aproj_to_string ~with_ended env) loans in
        ", loans=[" ^ String.concat "," loans ^ "]"
    in
    "("
    ^ (symbolic_value_proj_to_string env proj.sv_id proj.proj_ty
      |> add_borrow_proj_color proj.sv_id)
    ^ loans ^ ")"

  and aproj_loans_to_string ?(with_ended : bool = false) (env : fmt_env)
      (proj : aproj_loans) =
    let { proj; consumed; borrows } : aproj_loans = proj in
    let consumed =
      if consumed = [] then ""
      else
        let consumed = List.map snd consumed in
        let consumed = List.map (aproj_to_string ~with_ended env) consumed in
        ", consumed=[" ^ String.concat "," consumed ^ "]"
    in
    let borrows =
      if borrows = [] then ""
      else
        let borrows = List.map snd borrows in
        let borrows = List.map (aproj_to_string ~with_ended env) borrows in
        ", borrows=[" ^ String.concat "," borrows ^ "]"
    in
    "⌊"
    ^ (symbolic_value_proj_to_string env proj.sv_id proj.proj_ty
      |> add_loan_proj_color proj.sv_id)
    ^ consumed ^ borrows ^ "⌋"

  let symbolic_proj_to_string env (proj : symbolic_proj) : string =
    symbolic_value_proj_to_string env proj.sv_id proj.proj_ty

  (** Wrap a value inside its marker, if there is one *)
  let add_proj_marker (pm : proj_marker) (s : string) : string =
    match pm with
    | PNone -> s
    | PLeft -> "|" ^ s ^ "|"
    | PRight -> "︙" ^ s ^ "︙"

  let aended_mut_borrow_meta_to_string (env : fmt_env)
      (mv : aended_mut_borrow_meta) : string =
    let { bid; given_back } : aended_mut_borrow_meta = mv in
    "{ bid = " ^ BorrowId.to_string bid ^ "; given_back_ = "
    ^ symbolic_value_to_string env given_back
    ^ " }"

  let eended_mut_borrow_meta_to_string (env : fmt_env)
      (mv : eended_mut_borrow_meta) : string =
    let { bid; given_back } = mv in
    "{ bid = " ^ BorrowId.to_string bid ^ "; given_back = "
    ^ symbolic_value_to_string env given_back
    ^ " }"

  let rec tavalue_to_string ?(span : Meta.span option = None)
      ?(with_ended : bool = false) (env : fmt_env) (v : tavalue) : string =
    match v.value with
    | AAdt av ->
        let fields =
          List.map (tavalue_to_string ~span ~with_ended env) av.fields
        in
        adt_to_string span env
          (fun () -> show_tavalue v)
          v.ty av.variant_id fields
    | ABorrow bc -> aborrow_content_to_string ~span ~with_ended env bc
    | ALoan lc -> aloan_content_to_string ~span ~with_ended env lc
    | ASymbolic (pm, proj) ->
        aproj_to_string ~with_ended env proj |> add_proj_marker pm
    | AIgnored _ -> "_"

  and aloan_content_to_string ?(span : Meta.span option = None)
      ?(with_ended : bool = false) (env : fmt_env) (lc : aloan_content) : string
      =
    match lc with
    | AMutLoan (pm, bid, av) ->
        add_loan_color bid ("ML@" ^ BorrowId.to_string bid)
        ^ "("
        ^ tavalue_to_string ~span ~with_ended env av
        ^ ")"
        |> add_proj_marker pm
    | ASharedLoan (pm, lid, v, av) ->
        add_loan_color lid ("SL@" ^ BorrowId.to_string lid)
        ^ "("
        ^ tvalue_to_string ~span env v
        ^ ", "
        ^ tavalue_to_string ~span ~with_ended env av
        ^ ")"
        |> add_proj_marker pm
    | AEndedMutLoan ml ->
        let consumed =
          if with_ended then
            "consumed = " ^ tvalue_to_string env ml.given_back_meta ^ "; "
          else ""
        in
        "@ended_mut_loan{" ^ consumed ^ "child: "
        ^ tavalue_to_string ~span ~with_ended env ml.child
        ^ "; given_back: "
        ^ tavalue_to_string ~span ~with_ended env ml.given_back
        ^ " }"
    | AEndedSharedLoan (v, av) ->
        "@ended_shared_loan("
        ^ tvalue_to_string ~span env v
        ^ ", "
        ^ tavalue_to_string ~span ~with_ended env av
        ^ ")"
    | AIgnoredMutLoan (opt_bid, av) ->
        "@ignored_mut_loan("
        ^ option_to_string BorrowId.to_string opt_bid
        ^ ", "
        ^ tavalue_to_string ~span ~with_ended env av
        ^ ")"
    | AEndedIgnoredMutLoan ml ->
        "@ended_ignored_mut_loan{ child: "
        ^ tavalue_to_string ~span ~with_ended env ml.child
        ^ "; given_back: "
        ^ tavalue_to_string ~span ~with_ended env ml.given_back
        ^ "}"
    | AIgnoredSharedLoan sl ->
        "@ignored_shared_loan("
        ^ tavalue_to_string ~span ~with_ended env sl
        ^ ")"

  and aborrow_content_to_string ?(span : Meta.span option = None)
      ?(with_ended : bool = false) (env : fmt_env) (bc : aborrow_content) :
      string =
    match bc with
    | AMutBorrow (pm, bid, av) ->
        add_borrow_color bid ("MB@" ^ BorrowId.to_string bid)
        ^ "("
        ^ tavalue_to_string ~span ~with_ended env av
        ^ ")"
        |> add_proj_marker pm
    | ASharedBorrow (pm, bid, sid) ->
        "SB@" ^ BorrowId.to_string bid ^ "(^"
        ^ SharedBorrowId.to_string sid
        ^ ")"
        |> add_borrow_color bid |> add_proj_marker pm
    | AIgnoredMutBorrow (opt_bid, av) ->
        let add_color s =
          match opt_bid with
          | Some bid -> add_borrow_color bid s
          | None -> s
        in
        "@ignored_mut_borrow("
        ^ (option_to_string BorrowId.to_string opt_bid |> add_color)
        ^ ", "
        ^ tavalue_to_string ~span ~with_ended env av
        ^ ")"
    | AEndedMutBorrow (mv, child) ->
        "@ended_mut_borrow("
        ^
        if with_ended then
          "meta_given_back= " ^ aended_mut_borrow_meta_to_string env mv
        else "" ^ tavalue_to_string ~span ~with_ended env child ^ ")"
    | AEndedIgnoredMutBorrow { child; given_back; given_back_meta = _ } ->
        "@ended_ignored_mut_borrow("
        ^ tavalue_to_string ~span ~with_ended env child
        ^ ", "
        ^ tavalue_to_string ~span ~with_ended env given_back
        ^ ")"
    | AEndedSharedBorrow -> "@ended_shared_borrow"
    | AProjSharedBorrow sb ->
        "@proj_shared_borrow(" ^ abstract_shared_borrows_to_string env sb ^ ")"

  (** An environment specific to abstraction expressions. We use it to properly
      print the bound variables: as it is hard to interpret deBruijn indices, we
      also use a unique identifier for all the bound variables. *)
  type evalue_env = {
    fresh_index : unit -> int;
    bvars : string AbsBVarId.Map.t list;
    bvars_stack : string AbsBVarId.Map.t option;
        (** Partial map of bound variables that we're pushing.

            This is useful when exploring a binder: we start accumulating the
            names here, then push it in [bvars] when we're done.

            The way to proceed is:
            {[
              let env = fmt_env_start_stack env in
              ... (* Explore the binder to accumulate the mappings from bid to name *)
              let env = fmt_env_push_stack in
            ]} *)
    bvar_id_counter : int;
        (** We use this counter to generate unique names for the nameless bound
            var ids *)
    bvars_stack_counter : abs_bvar_id;
        (** Id to use for the next bound variable we push in [bvars_stack] *)
  }

  let empty_evalue_env : evalue_env =
    {
      fresh_index =
        (let r = ref 0 in
         fun () ->
           let i = !r in
           r := i + 1;
           i);
      bvars = [];
      bvars_stack = None;
      bvar_id_counter = 0;
      bvars_stack_counter = AbsBVarId.zero;
    }

  (** Start a new partial map (call this before exploring a binder) *)
  let evalue_env_start_stack (env : evalue_env) : evalue_env =
    assert (env.bvars_stack = None);
    {
      env with
      bvars_stack = Some AbsBVarId.Map.empty;
      bvars_stack_counter = AbsBVarId.zero;
    }

  (** After we're done accumulating the bound variables of a pattern in
      [pbvars], push this partial map to [bvars] *)
  let evalue_env_push_stack (env : evalue_env) : evalue_env =
    let bvars_stack = Option.get env.bvars_stack in
    {
      env with
      bvars = bvars_stack :: env.bvars;
      bvars_stack = None;
      bvars_stack_counter = AbsBVarId.zero;
    }

  (** Register a bound variable.

      Only call this between [evalue_env_start_stack] and
      [evalue_env_push_stack]. *)
  let evalue_env_push_var (env : evalue_env) (_ty : ty) :
      evalue_env * abs_bvar_id * string =
    let bvars_stack = Option.get env.bvars_stack in
    let uid = env.bvar_id_counter in
    let counter = uid + 1 in
    let name = "@" ^ string_of_int uid in
    let bvar_id = env.bvars_stack_counter in
    let bvars_stack = Some (AbsBVarId.Map.add bvar_id name bvars_stack) in
    let env =
      {
        env with
        bvars_stack;
        bvar_id_counter = counter;
        bvars_stack_counter = AbsBVarId.incr env.bvars_stack_counter;
      }
    in
    (env, bvar_id, name)

  let abs_bvar_to_pretty_string (bv : abs_bvar) (unique_name : string option) :
      string =
    let unique_name =
      match unique_name with
      | None -> ""
      | Some n -> n ^ ","
    in
    "bv@(" ^ unique_name ^ "scope=" ^ string_of_int bv.scope ^ ",id="
    ^ AbsBVarId.to_string bv.bvar_id
    ^ ")"

  let evalue_env_get_bvar (aenv : evalue_env) (bv : abs_bvar) : string =
    match List.nth_opt aenv.bvars bv.scope with
    | None -> abs_bvar_to_pretty_string bv None
    | Some m ->
        let unique_name = AbsBVarId.Map.find_opt bv.bvar_id m in
        abs_bvar_to_pretty_string bv unique_name

  let abs_fun_to_string (f : abs_fun) : string =
    match f with
    | EOutputAbs rg_id -> "OutputAbs@" ^ RegionGroupId.to_string rg_id
    | EInputAbs rg_id -> "InputAbs@" ^ RegionGroupId.to_string rg_id
    | EFunCall aid -> "FunCall(abs_id@" ^ AbsId.to_string aid ^ ")"
    | ELoop (abs_id, lp_id) ->
        "Loop(abs_id@" ^ AbsId.to_string abs_id ^ ",loop_id@"
        ^ LoopId.to_string lp_id ^ ")"
    | EJoin abs_id -> "Join(abs_id@" ^ AbsId.to_string abs_id ^ ")"

  let rec eproj_to_string ?(with_ended : bool = false) (env : fmt_env)
      (pv : eproj) : string =
    match pv with
    | EProjLoans { proj; consumed; borrows } ->
        let consumed =
          if consumed = [] then ""
          else
            let consumed = List.map snd consumed in
            let consumed =
              List.map (eproj_to_string ~with_ended env) consumed
            in
            ", consumed=[" ^ String.concat "," consumed ^ "]"
        in
        let borrows =
          if borrows = [] then ""
          else
            let borrows = List.map snd borrows in
            let borrows = List.map (eproj_to_string ~with_ended env) borrows in
            ", borrows=[" ^ String.concat "," borrows ^ "]"
        in
        "⌊"
        ^ symbolic_value_proj_to_string env proj.sv_id proj.proj_ty
        ^ consumed ^ borrows ^ "⌋"
    | EProjBorrows { proj; loans } ->
        let loans =
          if loans = [] then ""
          else
            let loans = List.map snd loans in
            let loans = List.map (eproj_to_string ~with_ended env) loans in
            ", loans=[" ^ String.concat "," loans ^ "]"
        in
        "("
        ^ symbolic_value_proj_to_string env proj.sv_id proj.proj_ty
        ^ loans ^ ")"
    | EEndedProjLoans { proj = msv; consumed; borrows } ->
        let msv =
          if with_ended then
            "original_loan = " ^ symbolic_value_id_to_pretty_string msv
          else "_"
        in
        let consumed =
          if consumed = [] then ""
          else
            let consumed = List.map snd consumed in
            let consumed =
              List.map (eproj_to_string ~with_ended env) consumed
            in
            ", consumed=[" ^ String.concat "," consumed ^ "]"
        in
        let borrows =
          if borrows = [] then ""
          else
            let borrows = List.map snd borrows in
            let borrows = List.map (eproj_to_string ~with_ended env) borrows in
            ", borrows=[" ^ String.concat "," borrows ^ "]"
        in
        "ended_eproj_loans (" ^ msv ^ consumed ^ borrows ^ ")"
    | EEndedProjBorrows { mvalues; loans } ->
        let meta =
          if with_ended then
            "original_borrow = "
            ^ symbolic_value_id_to_pretty_string mvalues.consumed
            ^ ", given_back = "
            ^ symbolic_value_to_string env mvalues.given_back
          else "_"
        in
        let loans =
          if loans = [] then ""
          else
            let loans = List.map snd loans in
            let loans = List.map (eproj_to_string ~with_ended env) loans in
            ", loans=[" ^ String.concat "," loans ^ "]"
        in
        "ended_eproj_borrows (" ^ meta ^ loans ^ "])"
    | EEmpty -> "_"

  let rec tevalue_to_string ?(span : Meta.span option = None)
      ?(with_ended : bool = false) (env : fmt_env) (aenv : evalue_env)
      (indent : string) (indent_incr : string) (v : tevalue) : string =
    match v.value with
    | ELet (regions, pat, bound, next) ->
        let indent1 = indent ^ indent_incr in
        let bound =
          tevalue_to_string ~span env aenv indent1 indent_incr bound
        in
        let aenv, pat = tepat_to_string ~span env aenv indent indent_incr pat in
        let next =
          tevalue_to_string ~span ~with_ended env aenv indent indent_incr next
        in
        "let " ^ pat ^ " ="
        ^ RegionId.Set.to_string None regions
        ^ "\n" ^ indent1 ^ bound ^ "\n" ^ indent ^ "in\n" ^ indent ^ next
    | EJoinMarkers (left, right) ->
        "@join_markers("
        ^ tevalue_to_string ~span ~with_ended env aenv indent indent_incr left
        ^ ", "
        ^ tevalue_to_string ~span ~with_ended env aenv indent indent_incr right
        ^ ")"
    | EBVar bv ->
        "(" ^ evalue_env_get_bvar aenv bv ^ " : " ^ ty_to_string env v.ty ^ ")"
    | EFVar fvid ->
        "(@" ^ AbsFVarId.to_string fvid ^ " : " ^ ty_to_string env v.ty ^ ")"
    | EApp (f, args) ->
        let tevalues_to_string =
          List.map
            (tevalue_to_string ~span ~with_ended env aenv (indent ^ indent_incr)
               indent_incr)
        in
        let args =
          List.map
            (fun args ->
              "(" ^ String.concat ", " (tevalues_to_string args) ^ ")")
            args
        in
        let f = abs_fun_to_string f in
        f ^ "[" ^ String.concat ", " args ^ "]"
    | EAdt av ->
        let fields =
          List.map
            (tevalue_to_string ~span ~with_ended env aenv indent indent_incr)
            av.fields
        in
        adt_to_string span env
          (fun () -> show_tevalue v)
          v.ty av.variant_id fields
    | EBottom -> "⊥ : " ^ ty_to_string env v.ty
    | EBorrow bc ->
        eborrow_content_to_string ~span ~with_ended env aenv indent indent_incr
          v.ty bc
    | ELoan lc ->
        eloan_content_to_string ~span ~with_ended env aenv indent indent_incr
          v.ty lc
    | ESymbolic (pm, proj) ->
        eproj_to_string ~with_ended env proj |> add_proj_marker pm
    | EValue (_, mv) -> "@mvalue(" ^ tvalue_to_string ~span env mv ^ ")"
    | EIgnored -> "(_ : " ^ ty_to_string env v.ty ^ ")"
    | EMutBorrowInput x ->
        "@mut_input("
        ^ tevalue_to_string ~span ~with_ended env aenv indent indent_incr x
        ^ ")"

  and eloan_content_to_string ?(span : Meta.span option = None)
      ?(with_ended : bool = false) (env : fmt_env) (aenv : evalue_env)
      (indent : string) (indent_incr : string) (ty : ty) (lc : eloan_content) :
      string =
    match lc with
    | EMutLoan (pm, bid, av) ->
        "@mut_loan(" ^ BorrowId.to_string bid ^ ", "
        ^ tevalue_to_string ~span ~with_ended env aenv indent indent_incr av
        ^ ") : " ^ ty_to_string env ty
        |> add_proj_marker pm
    | EEndedMutLoan ml ->
        let consumed =
          if with_ended then
            "consumed = " ^ tvalue_to_string env ml.given_back_meta ^ "; "
          else ""
        in
        "@ended_mut_loan{ child: " ^ consumed
        ^ tevalue_to_string ~span ~with_ended env aenv indent indent_incr
            ml.child
        ^ "; given_back: "
        ^ tevalue_to_string ~span ~with_ended env aenv indent indent_incr
            ml.given_back
        ^ " }"
    | EIgnoredMutLoan (opt_bid, av) ->
        "@ignored_mut_loan("
        ^ option_to_string BorrowId.to_string opt_bid
        ^ ", "
        ^ tevalue_to_string ~span ~with_ended env aenv indent indent_incr av
        ^ ")"
    | EEndedIgnoredMutLoan ml ->
        "@ended_ignored_mut_loan{ child: "
        ^ tevalue_to_string ~span ~with_ended env aenv indent indent_incr
            ml.child
        ^ "; given_back: "
        ^ tevalue_to_string ~span ~with_ended env aenv indent indent_incr
            ml.given_back
        ^ "}"

  (** Not safe to use: call [tepat_to_string] directly *)
  and tepat_to_string_core ?(span : Meta.span option = None) (env : fmt_env)
      (aenv : evalue_env) (indent : string) (indent_incr : string) (pat : tepat)
      : evalue_env * string =
    match pat.pat with
    | PBound ->
        let aenv, _, s = evalue_env_push_var aenv pat.ty in
        (aenv, "(" ^ s ^ " : " ^ ty_to_string env pat.ty ^ ")")
    | POpen bid ->
        ( aenv,
          "(@" ^ AbsFVarId.to_string bid ^ " : " ^ ty_to_string env pat.ty ^ ")"
        )
    | PAdt (variant_id, fields) ->
        let aenv, fields =
          List.fold_left_map
            (fun aenv field ->
              tepat_to_string_core ~span env aenv indent indent_incr field)
            aenv fields
        in
        ( aenv,
          adt_to_string span env
            (fun () -> show_tepat pat)
            pat.ty variant_id fields )
    | PIgnored -> (aenv, "(_ : " ^ ty_to_string env pat.ty ^ ")")

  and tepat_to_string ?(span : Meta.span option = None) (env : fmt_env)
      (aenv : evalue_env) (indent : string) (indent_incr : string) (pat : tepat)
      : evalue_env * string =
    let aenv = evalue_env_start_stack aenv in
    let aenv, string =
      tepat_to_string_core ~span env aenv indent indent_incr pat
    in
    let aenv = evalue_env_push_stack aenv in
    (aenv, string)

  and eborrow_content_to_string ?(span : Meta.span option = None)
      ?(with_ended : bool = false) (env : fmt_env) (aenv : evalue_env)
      (indent : string) (indent_incr : string) (ty : ty) (bc : eborrow_content)
      : string =
    match bc with
    | EMutBorrow (pm, bid, av) ->
        "@mb(" ^ BorrowId.to_string bid ^ ", "
        ^ tevalue_to_string ~span ~with_ended env aenv indent indent_incr av
        ^ ") : " ^ ty_to_string env ty
        |> add_proj_marker pm
    | EIgnoredMutBorrow (opt_bid, av) ->
        "@ignored_mut_borrow("
        ^ option_to_string BorrowId.to_string opt_bid
        ^ ", "
        ^ tevalue_to_string ~span ~with_ended env aenv indent indent_incr av
        ^ ")"
    | EEndedMutBorrow (mv, child) ->
        "@ended_mut_borrow("
        ^
        if with_ended then
          "given_back= " ^ eended_mut_borrow_meta_to_string env mv
        else
          ""
          ^ tevalue_to_string ~span ~with_ended env aenv indent indent_incr
              child
          ^ ")"
    | EEndedIgnoredMutBorrow { child; given_back; given_back_meta = _ } ->
        "@ended_ignored_mut_borrow{ "
        ^ tevalue_to_string ~span ~with_ended env aenv indent indent_incr child
        ^ "; "
        ^ tevalue_to_string ~span ~with_ended env aenv indent indent_incr
            given_back
        ^ ")"

  let abs_kind_to_string (kind : abs_kind) : string =
    match kind with
    | FunCall (fid, rg_id) ->
        "FunCall(fid:" ^ FunCallId.to_string fid ^ ", rg_id:"
        ^ RegionGroupId.to_string rg_id
        ^ ")"
    | SynthInput rg_id ->
        "SynthInput(rg_id:" ^ RegionGroupId.to_string rg_id ^ ")"
    | SynthRet rg_id -> "SynthRet(rg_id:" ^ RegionGroupId.to_string rg_id ^ ")"
    | Loop lp_id -> "Loop(loop_id:" ^ LoopId.to_string lp_id ^ ")"
    | Identity -> "Identity"
    | CopySymbolicValue -> "CopySymbolicValue"
    | Join -> "Join"
    | WithCont -> "WithCont"

  let abs_cont_to_string ?(span : Meta.span option = None) (env : fmt_env)
      ?(with_ended : bool = false) (indent : string) (indent_incr : string)
      (cont : abs_cont) : string =
    let { output; input } = cont in
    let to_string (e : tevalue option) =
      match e with
      | None -> "∅ "
      | Some e ->
          tevalue_to_string ~span ~with_ended env empty_evalue_env indent
            indent_incr e
    in
    to_string output ^ " :=\n" ^ indent ^ to_string input

  let abs_to_string ?(span : Meta.span option = None) (env : fmt_env)
      ?(with_ended : bool = false) (verbose : bool) (indent : string)
      (indent_incr : string) (abs : abs) : string =
    let indent2 = indent ^ indent_incr in
    let avs =
      List.map
        (fun av -> indent2 ^ tavalue_to_string ~span ~with_ended env av)
        abs.avalues
    in
    let avs = String.concat ",\n" avs in
    let kind =
      if verbose then "kind:" ^ abs_kind_to_string abs.kind ^ "," else ""
    in
    let can_end = if abs.can_end then "endable" else "frozen" in
    let cont =
      match abs.cont with
      | None -> ""
      | Some cont ->
          "⟦"
          ^ abs_cont_to_string ~span env ~with_ended:true (indent ^ indent_incr)
              indent_incr cont
          ^ "⟧"
    in
    let cont = add_abs_cont_color cont in
    indent
    ^ ("abs@" ^ AbsId.to_string abs.abs_id |> add_abs_color)
    ^ "{" ^ kind ^ "parents="
    ^ AbsId.Set.to_string None abs.parents
    ^ ",regions="
    ^ RegionId.Set.to_string None abs.regions.owned
    ^ "," ^ can_end ^ "} {\n" ^ avs ^ "\n" ^ indent ^ "}" ^ cont

  let abs_region_group_to_string (gr : abs_region_group) : string =
    g_region_group_to_string RegionId.to_string AbsId.to_string gr

  let abs_region_groups_to_string (gl : abs_region_groups) : string =
    String.concat "\n" (List.map abs_region_group_to_string gl)

  let inst_fun_sig_to_string (env : fmt_env) (sg : LlbcAst.inst_fun_sig) :
      string =
    (* TODO: print the trait type constraints? *)
    let ty_to_string = ty_to_string env in

    let inputs =
      "(" ^ String.concat ", " (List.map ty_to_string sg.inputs) ^ ")"
    in
    let output = ty_to_string sg.output in
    inputs ^ " -> " ^ output ^ "\n- regions_hierarchy:\n"
    ^ region_var_groups_to_string sg.regions_hierarchy
    ^ "\n- abs_regions_hierarchy:\n"
    ^ abs_region_groups_to_string sg.abs_regions_hierarchy

  let symbolic_expansion_to_string (env : fmt_env) (ty : ty)
      (se : symbolic_expansion) : string =
    match se with
    | SeLiteral lit -> literal_to_string lit
    | SeAdt (variant_id, svl) ->
        let fields = List.map ValuesUtils.mk_tvalue_from_symbolic_value svl in
        let v : tvalue = { value = VAdt { variant_id; fields }; ty } in
        tvalue_to_string env v
    | SeMutRef (bid, sv) ->
        "MB " ^ BorrowId.to_string bid ^ " " ^ symbolic_value_to_string env sv
    | SeSharedRef (bid, sv) ->
        "SB " ^ BorrowId.to_string bid ^ " " ^ symbolic_value_to_string env sv
end

module Env = struct
  open Values

  let real_var_binder_to_string (env : fmt_env) (bv : real_var_binder) : string
      =
    match bv.name with
    | None -> local_id_to_string env bv.index
    | Some name -> name ^ "^" ^ LocalId.to_string bv.index

  let dummy_var_id_to_string (bid : DummyVarId.id) : string =
    "_@" ^ DummyVarId.to_string bid

  let var_binder_to_string (env : fmt_env) (bv : var_binder) : string =
    match bv with
    | BVar b -> real_var_binder_to_string env b
    | BDummy bid -> dummy_var_id_to_string bid

  let env_elem_to_string ?(span : Meta.span option = None) (env : fmt_env)
      (verbose : bool) (with_var_types : bool) (indent : string)
      (indent_incr : string) (ev : env_elem) : string =
    match ev with
    | EBinding (var, tv) ->
        let bv = var_binder_to_string env var in
        let bv =
          match var with
          | BVar _ -> add_var_color bv
          | _ -> bv
        in
        let ty =
          if with_var_types then
            " : " ^ ty_to_string env tv.ty |> add_type_color
          else ""
        in
        indent ^ bv ^ ty ^ " -> " ^ tvalue_to_string ~span env tv ^ " ;"
    | EAbs abs -> abs_to_string ~span env verbose indent indent_incr abs
    | EFrame -> [%craise_opt_span] span "Can't print a Frame element"

  let opt_env_elem_to_string ?(span : Meta.span option = None) (env : fmt_env)
      (verbose : bool) (with_var_types : bool) (indent : string)
      (indent_incr : string) (ev : env_elem option) : string =
    match ev with
    | None -> indent ^ "..."
    | Some ev ->
        env_elem_to_string ~span env verbose with_var_types indent indent_incr
          ev

  (** Filters "dummy" bindings from an environment, to gain space and clarity/
      See [env_to_string]. *)
  let filter_env (ended_regions : RegionId.Set.t) (env : env) :
      env_elem option list =
    (* We filter:
       - non-dummy bindings which point to ⊥
       - dummy bindings which don't contain loans nor borrows
       Note that the first case can sometimes be confusing: we may try to improve
       it...
    *)
    let filter_elem (ev : env_elem) : env_elem option =
      match ev with
      | EBinding (BVar _, tv) ->
          (* Not a dummy binding: check if the value is ⊥ *)
          if is_bottom tv.value then None else Some ev
      | EBinding (BDummy _, tv) ->
          (* Dummy binding: check if the value contains borrows or loans *)
          if value_has_non_ended_borrows_or_loans ended_regions tv.value then
            Some ev
          else None
      | _ -> Some ev
    in
    let env = List.map filter_elem env in
    (* We collapse groups of filtered values - so that we can print one
     * single "..." for a whole group of filtered values *)
    let rec group_filtered (env : env_elem option list) : env_elem option list =
      match env with
      | [] -> []
      | None :: None :: env -> group_filtered (None :: env)
      | x :: env -> x :: group_filtered env
    in
    group_filtered env

  (** Environments can have a lot of dummy or uninitialized values: [filter]
      allows to filter them when printing, replacing groups of such bindings
      with "..." to gain space and clarity. [with_var_types]: if true, print the
      type of the variables *)
  let env_to_string ?(span : Meta.span option = None) (filter : bool)
      (fmt_env : fmt_env) (verbose : bool) (with_var_types : bool)
      (ended_regions : RegionId.Set.t) (env : env) : string =
    let env =
      if filter then filter_env ended_regions env
      else List.map (fun ev -> Some ev) env
    in
    "{\n"
    ^ String.concat "\n"
        (List.map
           (fun ev ->
             opt_env_elem_to_string ~span fmt_env verbose with_var_types "  "
               "  " ev)
           env)
    ^ "\n}"
end
