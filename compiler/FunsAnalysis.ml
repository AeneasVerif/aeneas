(** Compute various information, including:
    - can a function fail (by having `Fail` in its body, or transitively
      calling a function which can fail - this is false for globals)
    - can a function diverge (by being recursive, containing a loop or
      transitively calling a function which can diverge)
    - does a function perform stateful operations (i.e., do we need a state
      to translate it)
 *)

open LlbcAst
module EU = ExpressionsUtils

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

    let visit_fun (f : fun_decl) : unit =
      let obj =
        object (self)
          inherit [_] iter_statement as super
          method may_fail b = can_fail := !can_fail || b

          method! visit_Assert env a =
            self#may_fail true;
            super#visit_Assert env a

          method! visit_rvalue _env rv =
            match rv with
            | Use _ | RvRef _ | Global _ | Discriminant _ | Aggregate _ -> ()
            | UnaryOp (uop, _) -> can_fail := EU.unop_can_fail uop || !can_fail
            | BinaryOp (bop, _, _) ->
                can_fail := EU.binop_can_fail bop || !can_fail

          method! visit_Call env call =
            (match call.func with
            | FunId (Regular id) ->
                if FunDeclId.Set.mem id fun_ids then (
                  can_diverge := true;
                  is_rec := true)
                else
                  let info = FunDeclId.Map.find id !infos in
                  self#may_fail info.can_fail;
                  stateful := !stateful || info.stateful;
                  can_diverge := !can_diverge || info.can_diverge
            | FunId (Assumed id) ->
                (* None of the assumed functions can diverge nor are considered stateful *)
                can_fail := !can_fail || Assumed.assumed_can_fail id
            | TraitMethod _ ->
                (* We consider trait functions can fail, diverge, and are not stateful *)
                can_fail := true;
                can_diverge := true);
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
      assert ((not f.is_global_decl_body) || not !stateful);
      match f.body with
      | None ->
          (* Opaque function: we consider they fail by default *)
          obj#may_fail true;
          stateful := (not f.is_global_decl_body) && use_state
      | Some body -> obj#visit_statement () body.body
    in
    List.iter visit_fun d;
    (* We need to know if the declaration group contains a global - note that
     * groups containing globals contain exactly one declaration *)
    let is_global_decl_body = List.exists (fun f -> f.is_global_decl_body) d in
    assert ((not is_global_decl_body) || List.length d = 1);
    (* We ignore on purpose functions that cannot fail and consider they *can*
     * fail: the result of the analysis is not used yet to adjust the translation
     * so that the functions which syntactically can't fail don't use an error monad.
     * However, we do keep the result of the analysis for global bodies.
     * *)
    can_fail := (not is_global_decl_body) || !can_fail;
    {
      can_fail = !can_fail;
      stateful = !stateful;
      can_diverge = !can_diverge;
      is_rec = !is_rec;
    }
  in

  let analyze_fun_decl_group (d : fun_declaration_group) : unit =
    (* Retrieve the function declarations *)
    let funs = match d with NonRec id -> [ id ] | Rec ids -> ids in
    let funs = List.map (fun id -> FunDeclId.Map.find id funs_map) funs in
    let fun_ids = List.map (fun (d : fun_decl) -> d.def_id) funs in
    let fun_ids = FunDeclId.Set.of_list fun_ids in
    let info = analyze_fun_decls fun_ids funs in
    List.iter (fun (f : fun_decl) -> register_info f.def_id info) funs
  in

  let rec analyze_decl_groups (decls : declaration_group list) : unit =
    match decls with
    | [] -> ()
    | (Type _ | TraitDecl _ | TraitImpl _) :: decls' ->
        analyze_decl_groups decls'
    | Fun decl :: decls' ->
        analyze_fun_decl_group decl;
        analyze_decl_groups decls'
    | Global id :: decls' ->
        (* Analyze a global by analyzing its body function *)
        let global = GlobalDeclId.Map.find id globals_map in
        analyze_fun_decl_group (NonRec global.body_id);
        analyze_decl_groups decls'
  in

  analyze_decl_groups m.declarations;

  !infos
