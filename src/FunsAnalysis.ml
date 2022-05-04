(** Compute various information, including:
    - can a function fail (by having `Fail` in its body, or transitively
      calling a function which can fail)
    - can a function diverge
    - does a function perform stateful operations (i.e., do we need a state
      to translate it)
 *)

open LlbcAst
open Modules

type fun_info = {
  can_fail : bool;
  (* Not used yet: all the extracted functions use an error monad *)
  stateful : bool;
  divergent : bool; (* Not used yet *)
}
[@@deriving show]
(** Various information about a function.

    Note that not all this information is used yet to adjust the extraction yet.
 *)

type modules_funs_info = fun_info FunDeclId.Map.t
(** Various information about a module's functions *)

let analyze_module (m : llbc_module) (funs_map : fun_decl FunDeclId.Map.t)
    (use_state : bool) : modules_funs_info =
  let infos = ref FunDeclId.Map.empty in

  let register_info (id : FunDeclId.id) (info : fun_info) : unit =
    assert (not (FunDeclId.Map.mem id !infos));
    infos := FunDeclId.Map.add id info !infos
  in

  (* Analyze a group of mutually recursive functions.
   * As the functions can call each other, we compute the same information
   * for all of them.
   *)
  let analyze_fun_decls (fun_ids : FunDeclId.Set.t) (d : fun_decl list) :
      fun_info =
    let can_fail = ref false in
    let stateful = ref false in
    let divergent = ref false in

    let obj =
      object
        inherit [_] iter_statement as super

        method! visit_Assert env a =
          can_fail := true;
          super#visit_Assert env a

        method! visit_Call env call =
          (match call.func with
          | Regular id ->
              if FunDeclId.Set.mem id fun_ids then divergent := true
              else
                let info = FunDeclId.Map.find id !infos in
                can_fail := !can_fail || info.can_fail;
                stateful := !stateful || info.stateful;
                divergent := !divergent || info.divergent
          | Assumed id ->
              (* None of the assumed functions is stateful for now *)
              can_fail := !can_fail || Assumed.assumed_can_fail id);
          super#visit_Call env call

        method! visit_Panic env =
          can_fail := true;
          super#visit_Panic env

        method! visit_Loop env loop =
          divergent := true;
          super#visit_Loop env loop
      end
    in

    let visit_fun (f : fun_decl) : unit =
      match f.body with
      | None ->
          (* Opaque function *)
          can_fail := true;
          stateful := use_state
      | Some body -> obj#visit_statement () body.body
    in
    List.iter visit_fun d;
    { can_fail = !can_fail; stateful = !stateful; divergent = !divergent }
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
    | Type _ :: decls' -> analyze_decl_groups decls'
    | Fun decl :: decls' ->
        analyze_fun_decl_group decl;
        analyze_decl_groups decls'
  in

  analyze_decl_groups m.declarations;

  !infos
