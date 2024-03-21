(** Compute various information, including:
    - can a function fail (by having `Fail` in its body, or transitively
      calling a function which can fail - this is false for globals)
    - can a function diverge (by being recursive, containing a loop or
      transitively calling a function which can diverge)
    - does a function perform stateful operations (i.e., do we need a state
      to translate it)
 *)

open LlbcAst
open ExpressionsUtils
open Errors

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
}
[@@deriving show]

(** Various information about a module's functions *)
type modules_funs_info = fun_info FunDeclId.Map.t

let analyze_module (m : crate) (funs_map : fun_decl FunDeclId.Map.t)
    (globals_map : global_decl GlobalDeclId.Map.t) (use_state : bool) :
    modules_funs_info =
  let infos = ref FunDeclId.Map.empty in
  let register_info (id : FunDeclId.id) (info : fun_info) : unit =
    assert (not (FunDeclId.Map.mem id !infos));
    infos := FunDeclId.Map.add id info !infos
  in

  (* Analyze a group of mutually recursive functions.
   * As the functions can call each other, we compute the same information
   * for all of them (if one of the functions can fail, then all of them
   * can fail, etc.).
   *
   * We simply check if the functions contains panic statements, loop statements,
   * recursive calls, etc. We use the previously computed information in case
   * of function calls.
   *)
  let analyze_fun_decls (fun_ids : FunDeclId.Set.t) (d : fun_decl list) :
      fun_info =
    let can_fail = ref false in
    let stateful = ref false in
    let can_diverge = ref false in
    let is_rec = ref false in
    let group_has_builtin_info = ref false in
    let name_matcher_ctx : Charon.NameMatcher.ctx =
      {
        type_decls = m.type_decls;
        global_decls = m.global_decls;
        fun_decls = m.fun_decls;
        trait_decls = m.trait_decls;
        trait_impls = m.trait_impls;
      }
    in

    (* We have some specialized knowledge of some library functions; we don't
       have any more custom treatment than this, and these functions can be modeled
       suitably in Primitives.fst, rather than special-casing for them all the
       way. *)
    let get_builtin_info (f : fun_decl) : ExtractBuiltin.effect_info option =
      let open ExtractBuiltin in
      NameMatcherMap.find_opt name_matcher_ctx f.name builtin_fun_effects_map
    in

    (* JP: Why not use a reduce visitor here with a tuple of the values to be
       computed? *)
    let visit_fun (f : fun_decl) : unit =
      let obj =
        object (self)
          inherit [_] iter_statement as super
          method may_fail b = can_fail := !can_fail || b
          method maybe_stateful b = stateful := !stateful || b

          method visit_fid id =
            if FunDeclId.Set.mem id fun_ids then (
              can_diverge := true;
              is_rec := true)
            else
              let info = FunDeclId.Map.find id !infos in
              self#may_fail info.can_fail;
              stateful := !stateful || info.stateful;
              can_diverge := !can_diverge || info.can_diverge

          method! visit_Assert env a =
            self#may_fail true;
            super#visit_Assert env a

          method! visit_rvalue _env rv =
            match rv with
            | Use _ | RvRef _ | Global _ | Discriminant _ | Aggregate _ -> ()
            | UnaryOp (uop, _) -> can_fail := unop_can_fail uop || !can_fail
            | BinaryOp (bop, _, _) ->
                can_fail := binop_can_fail bop || !can_fail

          method! visit_Closure env id args =
            (* Remark: `Closure` is a trait instance id - TODO: rename this variant *)
            self#visit_fid id;
            super#visit_Closure env id args

          method! visit_AggregatedClosure env id args =
            self#visit_fid id;
            super#visit_AggregatedClosure env id args

          method! visit_Call env call =
            (match call.func with
            | FnOpMove _ ->
                (* Ignoring this: we lookup t he called function upon creating
                   the closure *)
                ()
            | FnOpRegular func -> (
                match func.func with
                | FunId (FRegular id) -> self#visit_fid id
                | FunId (FAssumed id) ->
                    (* None of the assumed functions can diverge nor are considered stateful *)
                    can_fail := !can_fail || Assumed.assumed_fun_can_fail id
                | TraitMethod _ ->
                    (* We consider trait functions can fail, but can not diverge and are not stateful.
                       TODO: this may cause issues if we use use a fuel parameter.
                    *)
                    can_fail := true));
            super#visit_Call env call

          method! visit_Panic env =
            self#may_fail true;
            super#visit_Panic env

          method! visit_Loop env loop =
            can_diverge := true;
            super#visit_Loop env loop
        end
      in
      (* Sanity check: global bodies don't contain stateful calls *)
      cassert ((not f.is_global_decl_body) || not !stateful) f.meta "Global bodies should not contain stateful calls";
      let builtin_info = get_builtin_info f in
      let has_builtin_info = builtin_info <> None in
      group_has_builtin_info := !group_has_builtin_info || has_builtin_info;
      match f.body with
      | None ->
          let info_can_fail, info_stateful =
            match builtin_info with
            | None -> (true, use_state)
            | Some { can_fail; stateful } -> (can_fail, stateful)
          in
          obj#may_fail info_can_fail;
          obj#maybe_stateful
            (if f.is_global_decl_body then false
             else if not use_state then false
             else info_stateful)
      | Some body -> obj#visit_statement () body.body
    in
    List.iter visit_fun d;
    (* We need to know if the declaration group contains a global - note that
     * groups containing globals contain exactly one declaration *)
    let is_global_decl_body = List.exists (fun f -> f.is_global_decl_body) d in
    cassert ((not is_global_decl_body) || List.length d = 1) (List.hd d).meta "The declaration group should containing globals should contain exactly one declaration"; (*TODO recheck how to get meta*)
    cassert ((not !group_has_builtin_info) || List.length d = 1) (List.hd d).meta "The declaration group should containing globals should contain exactly one declaration";
    (* We ignore on purpose functions that cannot fail and consider they *can*
     * fail: the result of the analysis is not used yet to adjust the translation
     * so that the functions which syntactically can't fail don't use an error monad.
     * However, we do keep the result of the analysis for global bodies and for
     * builtin functions which are marked as non-fallible.
     * *)
    can_fail :=
      if is_global_decl_body then !can_fail
      else if !group_has_builtin_info then !can_fail
      else true;
    {
      can_fail = !can_fail;
      stateful = !stateful;
      can_diverge = !can_diverge;
      is_rec = !is_rec;
    }
  in

  let analyze_fun_decl_group (d : fun_declaration_group) : unit =
    (* Retrieve the function declarations *)
    let funs = match d with NonRecGroup id -> [ id ] | RecGroup ids -> ids in
    let funs = List.map (fun id -> FunDeclId.Map.find id funs_map) funs in
    let fun_ids = List.map (fun (d : fun_decl) -> d.def_id) funs in
    let fun_ids = FunDeclId.Set.of_list fun_ids in
    let info = analyze_fun_decls fun_ids funs in
    List.iter (fun (f : fun_decl) -> register_info f.def_id info) funs
  in

  let rec analyze_decl_groups (decls : declaration_group list) : unit =
    match decls with
    | [] -> ()
    | (TypeGroup _ | TraitDeclGroup _ | TraitImplGroup _) :: decls' ->
        analyze_decl_groups decls'
    | FunGroup decl :: decls' ->
        analyze_fun_decl_group decl;
        analyze_decl_groups decls'
    | GlobalGroup id :: decls' ->
        (* Analyze a global by analyzing its body function *)
        let global = GlobalDeclId.Map.find id globals_map in
        analyze_fun_decl_group (NonRecGroup global.body);
        analyze_decl_groups decls'
  in

  analyze_decl_groups m.declarations;

  !infos
