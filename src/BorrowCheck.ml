open Interp
open LlbcAst

(** The local logger *)
let log = Logging.borrow_check_log

(** Borrow-check a crate.

    Note that we don't return anything: if we find borrow-checking errors, we
    register them and print them later. *)
let borrow_check_crate (crate : crate) (marked_ids : Contexts.marked_ids) : unit
    =
  (* Debug *)
  [%ldebug "translate_crate_to_pure"];

  (* Compute the translation context *)
  let trans_ctx = compute_contexts crate in

  (* Borrow-check *)
  let borrow_check_fun (fdef : fun_decl) : unit =
    match fdef.body with
    | None -> ()
    | Some _ ->
        let synthesize = false in
        let _ =
          evaluate_function_symbolic synthesize trans_ctx marked_ids fdef
        in
        ()
  in
  List.iter borrow_check_fun (FunDeclId.Map.values crate.fun_decls)
