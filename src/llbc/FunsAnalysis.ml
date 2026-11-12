(** Compute various information, including:
    - can a function fail (by having `Fail` in its body, or transitively calling
      a function which can fail - this is false for globals)
    - can a function diverge (by being recursive, containing a loop or
      transitively calling a function which can diverge)
    - does a function perform stateful operations (i.e., do we need a state to
      translate it) *)

open LlbcAst
open LlbcAstUtils
open ExpressionsUtils
open Charon.GAstUtils
open Errors

let log = Logging.funs_analysis_log

(** Various information about a function.

    Note that not all this information is used yet to adjust the extraction yet.
*)
type fun_info = {
  can_fail : bool;
      (* Not used yet: all the extracted functions use an error monad *)
  stateful : bool;
  can_diverge : bool;
  (* The function can diverge if:
     - it is recursive
     - it contains a loop
     - it calls a functions which can diverge
  *)
  is_rec : bool;
      (* [true] if the function is recursive (or in a mutually recursive group) *)
  has_stateful_lifetime_attr : bool;
  stateful_lifetime_regions : Values.stateful_lifetime Types.RegionId.Map.t;
}
[@@deriving show]

(** Various information about a module's functions and trait methods. *)
type modules_funs_info = { infos : fun_info FunOrMethodId.Map.t }
[@@deriving show]

type stateful_lifetime_spec = {
  lifetime : string option;
  mode : Values.stateful_lifetime;
}

let has_raw_stateful_lifetime_attr (item_meta : Types.item_meta) : bool =
  List.exists
    (fun (attr : Meta.attribute) ->
      match attr with
      | AttrUnknown { path = "verify::stateful_lifetime"; _ } -> true
      | _ -> false)
    item_meta.attr_info.attributes

let is_valid_lifetime_ident (s : string) : bool =
  let len = String.length s in
  if len < 2 || s.[0] <> '\'' then false
  else
    let is_ident_start = function
      | 'a' .. 'z' | 'A' .. 'Z' | '_' -> true
      | _ -> false
    in
    let is_ident_cont = function
      | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> true
      | _ -> false
    in
    is_ident_start s.[1]
    &&
    let ok = ref true in
    for i = 2 to len - 1 do
      if not (is_ident_cont s.[i]) then ok := false
    done;
    !ok

let parse_stateful_lifetime_specs ?(emit_errors : bool = false)
    (item_meta : Types.item_meta) : stateful_lifetime_spec list =
  let parse_mode (raw_mode : string) : Values.stateful_lifetime option =
    match raw_mode with
    | "long" -> Some Values.Long
    | "default" -> Some Values.Default
    | "short" -> Some Values.Short
    | _ ->
        if emit_errors then
          [%save_error] item_meta.span
            ("Invalid #[verify::stateful_lifetime] mode `" ^ raw_mode
           ^ "`: expected `long`, `default`, or `short`");
        None
  in
  let validate_lifetime_tok (lt_tok : string) : string option =
    if lt_tok = "'static" then (
      if emit_errors then
        [%save_error] item_meta.span
          "`'static` cannot be marked #[verify::stateful_lifetime]";
      None)
    else if lt_tok = "'_" then (
      if emit_errors then
        [%save_error] item_meta.span
          "Anonymous lifetime `'_` cannot be named in \
           #[verify::stateful_lifetime]; name the lifetime explicitly or omit \
           it to apply to all lifetimes";
      None)
    else if not (is_valid_lifetime_ident lt_tok) then (
      if emit_errors then
        [%save_error] item_meta.span
          ("Invalid lifetime `" ^ lt_tok ^ "` in #[verify::stateful_lifetime]");
      None)
    else Some lt_tok
  in
  let parse_arg (args : string option) : stateful_lifetime_spec option =
    match Option.map String.trim args with
    | None | Some "" -> Some { lifetime = None; mode = Values.Default }
    | Some raw -> (
        let parts = List.map String.trim (String.split_on_char ',' raw) in
        let parts =
          match List.rev parts with
          | "" :: (_ :: _ as rev_rest) -> List.rev rev_rest
          | _ -> parts
        in
        match parts with
        | [ tok ] when String.length tok > 0 && tok.[0] = '\'' ->
            Option.map
              (fun lt -> { lifetime = Some lt; mode = Values.Default })
              (validate_lifetime_tok tok)
        | [ tok ] ->
            Option.map (fun mode -> { lifetime = None; mode }) (parse_mode tok)
        | [ lt_tok; mode_tok ] -> (
            if String.length lt_tok = 0 || lt_tok.[0] <> '\'' then (
              if emit_errors then
                [%save_error] item_meta.span
                  ("Invalid #[verify::stateful_lifetime(" ^ raw
                 ^ ")]: expected a lifetime such as `'a` as the first argument"
                  );
              None)
            else
              match (validate_lifetime_tok lt_tok, parse_mode mode_tok) with
              | Some lt, Some mode -> Some { lifetime = Some lt; mode }
              | _ -> None)
        | _ ->
            if emit_errors then
              [%save_error] item_meta.span
                ("Invalid #[verify::stateful_lifetime(" ^ raw
               ^ ")]: expected `#[verify::stateful_lifetime]`, \
                  `#[verify::stateful_lifetime(mode)]`, \
                  `#[verify::stateful_lifetime('a)]`, or \
                  `#[verify::stateful_lifetime('a, mode)]`");
            None)
  in
  List.filter_map
    (fun (attr : Meta.attribute) ->
      match attr with
      | AttrUnknown { path = "verify::stateful_lifetime"; args } ->
          parse_arg args
      | _ -> None)
    item_meta.attr_info.attributes

let resolve_stateful_lifetimes (f : fun_decl) :
    bool * Values.stateful_lifetime Types.RegionId.Map.t =
  let has_attr = has_raw_stateful_lifetime_attr f.item_meta in
  if not has_attr then (false, Types.RegionId.Map.empty)
  else
    let specs = parse_stateful_lifetime_specs ~emit_errors:true f.item_meta in
    match f.src with
    | TraitDefaultFun _ | TraitImplFun _ ->
        [%save_error] f.item_meta.span
          "#[verify::stateful_lifetime] is not allowed on trait methods";
        (false, Types.RegionId.Map.empty)
    | _ ->
        let wildcard = ref None in
        let named = ref Collections.StringMap.empty in
        List.iter
          (fun (spec : stateful_lifetime_spec) ->
            match spec.lifetime with
            | None ->
                if Option.is_some !wildcard then
                  [%save_error] f.item_meta.span
                    "Duplicate #[verify::stateful_lifetime] attribute for all \
                     lifetimes"
                else wildcard := Some spec.mode
            | Some lt_name ->
                if Collections.StringMap.mem lt_name !named then
                  [%save_error] f.item_meta.span
                    ("Duplicate #[verify::stateful_lifetime] attribute for \
                      lifetime `" ^ lt_name ^ "`")
                else (
                  if
                    not
                      (List.exists
                         (fun (rp : Types.region_param) ->
                           rp.name = Some lt_name)
                         f.generics.regions)
                  then
                    [%save_error] f.item_meta.span
                      ("Unknown lifetime `" ^ lt_name
                     ^ "` in #[verify::stateful_lifetime]");
                  named := Collections.StringMap.add lt_name spec.mode !named))
          specs;
        if Option.is_some !wildcard && f.generics.regions = [] then
          [%save_error] f.item_meta.span
            "#[verify::stateful_lifetime] requires at least one lifetime in \
             the function signature";
        let region_map =
          List.fold_left
            (fun m (rp : Types.region_param) ->
              let mode_opt =
                match rp.name with
                | Some name -> (
                    match Collections.StringMap.find_opt name !named with
                    | Some _ as mode -> mode
                    | None -> !wildcard)
                | None -> !wildcard
              in
              match mode_opt with
              | Some mode -> Types.RegionId.Map.add rp.index mode m
              | None -> m)
            Types.RegionId.Map.empty f.generics.regions
        in
        (true, region_map)

let has_stateful_lifetime (info : fun_info) : bool =
  info.has_stateful_lifetime_attr
  || not (Types.RegionId.Map.is_empty info.stateful_lifetime_regions)

let rg_stateful_lifetime (span : Meta.span option)
    ?(decl_region_map : decl_region_map option = None) (info : fun_info)
    (rg : Types.region_group) : Values.stateful_lifetime option =
  if Types.RegionId.Map.is_empty info.stateful_lifetime_regions then None
  else
    let merge_decl_rid acc decl_rid =
      ValuesUtils.merge_stateful_lifetimes span acc
        (Types.RegionId.Map.find_opt decl_rid info.stateful_lifetime_regions)
    in
    let merge_decl_rids acc decl_rids =
      Types.RegionId.Set.fold
        (fun rid acc -> merge_decl_rid acc rid)
        decl_rids acc
    in
    List.fold_left
      (fun acc (r : Types.region) ->
        match (decl_region_map, r) with
        | None, RVar (Free rid) -> merge_decl_rid acc rid
        | None, (RStatic | RVar (Bound _) | RErased | RBody _ | RLub _) -> acc
        | Some m, RVar (Free rid) -> (
            match Types.RegionId.Map.find_opt rid m.free_regions with
            | Some decl_rids -> merge_decl_rids acc decl_rids
            | None -> acc)
        | Some m, RStatic -> merge_decl_rids acc m.static_regions
        | Some _, (RVar (Bound _) | RErased | RBody _ | RLub _) -> acc)
      None rg.regions

let lookup_fun_info (infos : modules_funs_info) (id : FunOrMethodId.id) :
    fun_info option =
  FunOrMethodId.Map.find_opt id infos.infos

let fun_or_method_id_of_fn_ptr (kind : fn_ptr_kind) : FunOrMethodId.id option =
  match kind with
  | Fun id -> Some (FunOrMethodId.Fun id)
  | TraitMethod (trait_ref, method_id) ->
      Some (FunOrMethodId.of_trait_method trait_ref method_id)

let lookup_fun_decl_info (infos : modules_funs_info) (id : FunDeclId.id) :
    fun_info option =
  lookup_fun_info infos (FunOrMethodId.Fun id)

let lookup_fn_ptr_info (infos : modules_funs_info) (kind : fn_ptr_kind) :
    fun_info option =
  Option.bind (fun_or_method_id_of_fn_ptr kind) (lookup_fun_info infos)

let analyze_module (m : crate) (funs_map : fun_decl FunDeclId.Map.t) :
    modules_funs_info =
  let fmt_env = Charon.Print.crate_to_fmt_env m in
  let infos = ref { infos = FunOrMethodId.Map.empty } in
  let register_info (id : FunOrMethodId.id) (info : fun_info) : unit =
    assert (not (FunOrMethodId.Map.mem id !infos.infos));
    infos := { infos = FunOrMethodId.Map.add id info !infos.infos }
  in
  let register_fun_decl_info (id : FunDeclId.id) (info : fun_info) : unit =
    register_info (FunOrMethodId.Fun id) info
  in
  let register_trait_method_info (trait_decl_id : TraitDeclId.id)
      (method_id : Types.TraitMethodId.id) (m : trait_method Types.binder) :
      unit =
    let item_meta = m.binder_value.item_meta in
    if has_raw_stateful_lifetime_attr item_meta then
      [%save_error] item_meta.span
        "#[verify::stateful_lifetime] is not allowed on trait methods";
    register_info
      (FunOrMethodId.Method (trait_decl_id, method_id))
      {
        can_fail = true;
        stateful = false;
        can_diverge = false;
        is_rec = false;
        has_stateful_lifetime_attr = false;
        stateful_lifetime_regions = Types.RegionId.Map.empty;
      }
  in

  TraitDeclId.Map.iter
    (fun trait_decl_id (trait_decl : trait_decl) ->
      Types.TraitMethodId.Map.iter
        (fun method_id m ->
          register_trait_method_info trait_decl_id method_id m)
        trait_decl.methods)
    m.trait_decls;

  (* Analyze a group of mutually recursive functions.
   * As the functions can call each other, we compute the same information
   * for all of them (if one of the functions can fail, then all of them
   * can fail, etc.).
   *
   * We simply check whether the functions contains panic statements, loop statements,
   * recursive calls, etc. We use the previously computed information in case
   * of function calls.
   *)
  let analyze_fun_decls (fun_ids : FunDeclId.TreeSet.t) (d : fun_decl list) :
      fun_info =
    let can_fail = ref false in
    let stateful = ref false in
    let can_diverge = ref false in
    let is_rec = ref false in
    let group_has_builtin_info = ref false in
    let name_matcher_ctx : Charon.NameMatcher.ctx =
      Charon.NameMatcher.ctx_from_crate m
    in

    (* We have some specialized knowledge of some library functions; we don't
       have any more custom treatment than this, and these functions can be modeled
       suitably in the backend libraries, rather than special-casing for them all the
       way. *)
    let get_builtin_info (f : fun_decl) : ExtractBuiltin.effect_info option =
      let open ExtractBuiltin in
      NameMatcherMap.find_opt name_matcher_ctx f.item_meta.name
        (builtin_fun_effects_map ())
    in

    (* JP: Why not use a reduce visitor here with a tuple of the values to be
       computed? *)
    let visit_fun (f : fun_decl) : unit =
      [%ltrace
        "Analyzing fun:\n"
        ^ Charon.Print.name_to_string fmt_env f.item_meta.name];
      let obj =
        object (self)
          inherit [_] iter_statement as super
          method may_fail b = can_fail := !can_fail || b
          method maybe_stateful b = stateful := !stateful || b
          method! visit_statement _ st = super#visit_statement st.span st

          (* Custom function called by hand, this isn't visit_fun_decl_id! *)
          method visit_fid span id =
            if FunDeclId.TreeSet.mem id fun_ids then (
              can_diverge := true;
              is_rec := true)
            else
              let info = lookup_fun_decl_info !infos id in
              let info =
                [%unwrap_opt_span] (Some span) info
                  "The function called here is missing from the crate \
                   (probably because of a previous error, or because of the \
                   use of --exclude)"
              in
              self#may_fail info.can_fail;
              stateful := !stateful || info.stateful;
              can_diverge := !can_diverge || info.can_diverge

          method! visit_Assert env a =
            self#may_fail true;
            super#visit_Assert env a

          method! visit_rvalue env rv =
            (match rv with
            | Use _
            | RvRef ({ kind = PlaceLocal _ | PlaceProjection _; _ }, _, _)
            | Discriminant _ | Aggregate _ | NullaryOp _ | RawPtr _ | Repeat _
              -> ()
            | RvRef ({ kind = PlaceGlobal gref; _ }, _, _) -> (
                (* A reference to a global: propagate can_fail.

                   Check the builtin globals map first (for opaque builtins like
                   [u32::MAX]), then fall back to the initializer function's info. *)
                let global = GlobalDeclId.Map.find gref.id m.global_decls in
                let open ExtractBuiltin in
                let builtin_info =
                  NameMatcherMap.find_opt name_matcher_ctx global.item_meta.name
                    (builtin_globals_map ())
                in
                match builtin_info with
                | Some info -> self#may_fail info.can_fail
                | None -> (
                    (* Globals without initializers are constants *)
                    match init_fun_id_of_global global with
                    | Some fid -> self#visit_fid env fid
                    | None -> ()))
            | UnaryOp (uop, _) -> can_fail := unop_can_fail uop || !can_fail
            | BinaryOp (bop, _, _) ->
                can_fail := binop_can_fail bop || !can_fail);
            super#visit_rvalue env rv

          method! visit_constant_expr env cv =
            (match cv.kind with
            | CTraitConst _ ->
                (* We consider that trait constants can fail, similarly to
                   trait methods. *)
                self#may_fail true
            | CFnDef ptr -> (
                match ptr.kind with
                | Fun fid -> (
                    match FunDeclId.Map.find_opt fid funs_map with
                    | Some fdecl
                      when has_raw_stateful_lifetime_attr fdecl.item_meta ->
                        [%save_error] env
                          "Cannot take a function pointer to a function marked \
                           #[verify::stateful_lifetime]"
                    | _ -> ())
                | TraitMethod _ -> ())
            | _ -> ());
            super#visit_constant_expr env cv

          method! visit_Call env call dest on_unwind =
            (match call.func with
            | FnOpDynamic _ ->
                (* Ignoring this: we lookup the called function upon creating
                   the closure *)
                ()
            | FnOpRegular func -> (
                match func.kind with
                | Fun id -> self#visit_fid env id
                | TraitMethod _ ->
                    (* We consider trait functions can fail, but can not diverge and are not stateful.
                       TODO: this may cause issues if we use use a fuel parameter.
                    *)
                    can_fail := true));
            super#visit_Call env call dest on_unwind

          method! visit_Panic env =
            self#may_fail true;
            super#visit_Panic env

          method! visit_Loop env loop =
            can_diverge := true;
            super#visit_Loop env loop
        end
      in
      (* Sanity check: global bodies don't contain stateful calls *)
      [%cassert] f.item_meta.span
        ((not (fun_decl_is_global_initializer f)) || not !stateful)
        "Global definition containing a stateful call in its body";
      let builtin_info = get_builtin_info f in
      let has_builtin_info = builtin_info <> None in
      group_has_builtin_info := !group_has_builtin_info || has_builtin_info;
      match f.body with
      | StructuredBody body -> obj#visit_block body.body.span body.body
      | TargetDispatchBody targets ->
          (* get_target can fail, and so can each target function *)
          obj#may_fail true;
          (* Also propagate effects from the target implementations *)
          List.iter
            (fun ((_target_name : string), (fdr : Types.fun_decl_ref)) ->
              obj#visit_fid f.item_meta.span fdr.id)
            targets
      | _ ->
          let info_can_fail =
            match builtin_info with
            | None -> true
            | Some { can_fail } -> can_fail
          in
          obj#may_fail info_can_fail
    in
    List.iter visit_fun d;
    (* We need to know if the declaration group contains a global - note that
     * groups containing globals contain exactly one declaration *)
    let is_global_decl_body = List.exists fun_decl_is_global_initializer d in
    [%cassert] (List.hd d).item_meta.span
      ((not is_global_decl_body) || List.length d = 1)
      "This global definition is in a group of mutually recursive definitions";
    [%cassert] (List.hd d).item_meta.span
      ((not !group_has_builtin_info) || List.length d = 1)
      "This builtin function belongs to a group of mutually recursive \
       definitions";
    (* We ignore on purpose functions that cannot fail and consider they *can*
     * fail: the result of the analysis is not used yet to adjust the translation
     * so that the functions which syntactically can't fail don't use an error monad.
     * However, we do keep the result of the analysis for global bodies and for
     * builtin functions which are marked as non-fallible.
     *)
    can_fail :=
      if is_global_decl_body then !can_fail
      else if !group_has_builtin_info then !can_fail
      else true;
    {
      can_fail = !can_fail;
      stateful = !stateful;
      can_diverge = !can_diverge;
      is_rec = !is_rec;
      has_stateful_lifetime_attr = false;
      stateful_lifetime_regions = Types.RegionId.Map.empty;
    }
  in

  let analyze_fun_decl_group (funs : fun_decl_id list) : unit =
    (* Retrieve the function declarations *)
    let funs =
      List.map
        (fun id ->
          [%silent_unwrap_opt_span] None (FunDeclId.Map.find_opt id funs_map))
        funs
    in
    let fun_ids = List.map (fun (d : fun_decl) -> d.def_id) funs in
    let fun_ids = FunDeclId.TreeSet.of_list fun_ids in
    let info = analyze_fun_decls fun_ids funs in
    List.iter
      (fun (f : fun_decl) ->
        let has_stateful_lifetime_attr, stateful_lifetime_regions =
          resolve_stateful_lifetimes f
        in
        let info =
          { info with has_stateful_lifetime_attr; stateful_lifetime_regions }
        in
        register_fun_decl_info f.def_id info)
      funs
  in

  let rec analyze_decl_groups (decls : declaration_group list) : unit =
    match decls with
    | [] -> ()
    | (TypeGroup _ | TraitDeclGroup _ | TraitImplGroup _ | GlobalGroup _)
      :: decls' -> analyze_decl_groups decls'
    | FunGroup decl :: decls' ->
        (try analyze_fun_decl_group (g_declaration_group_to_list decl)
         with CFailure error ->
           let fmt_env = Charon.Print.crate_to_fmt_env m in
           let decls = Charon.GAstUtils.g_declaration_group_to_list decl in
           let decl_id_to_string (id : FunDeclId.id) : string =
             match FunDeclId.Map.find_opt id m.fun_decls with
             | None -> show_fun_decl_id id
             | Some d ->
                 Charon.Print.name_to_string fmt_env d.item_meta.name
                 ^ " ("
                 ^ span_to_string d.item_meta.span
                 ^ ")"
           in
           let decls = List.map decl_id_to_string decls in
           let decls = String.concat "\n" decls in
           [%save_error_opt_span] error.span
             ("Encountered an error when analyzing the following function \
               declaration group:\n" ^ decls ^ "\n\nInitial error:\n"
            ^ error.msg));
        analyze_decl_groups decls'
    | MixedGroup ids :: _ ->
        [%save_error_opt_span] None
          ("Mixed declaration groups (which contain both type and function \
            declarations or functions and traits, for instance) are not \
            supported yet: ["
          ^ String.concat ", "
              (List.map Charon.Print.item_id_to_string
                 (Charon.GAstUtils.g_declaration_group_to_list ids))
          ^ "]")
  in

  analyze_decl_groups (Option.get m.declarations);

  !infos
