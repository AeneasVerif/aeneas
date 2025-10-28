open Ppxlib
open Ast_builder.Default

(* let empty_expr_payload = Ast_pattern.(pstr nil) *)
let single_expr_payload = Ast_pattern.single_expr_payload

let double_expr_payload t0 t1 =
  Ast_pattern.(single_expr_payload (pexp_tuple (t0 ^:: t1 ^:: nil)))

let triple_expr_payload t0 t1 t2 =
  Ast_pattern.(single_expr_payload (pexp_tuple (t0 ^:: t1 ^:: t2 ^:: nil)))

let mk_raw_check_rule (full_name : string) (rule_name : string) :
    Context_free.Rule.t =
  let expand ~ctxt : expression =
    let loc = Expansion_context.Extension.extension_point_loc ctxt in
    pexp_apply ~loc (evar ~loc full_name)
      [
        (Nolabel, estring ~loc loc.loc_start.pos_fname);
        (Nolabel, eint ~loc loc.loc_start.pos_lnum);
      ]
  in
  let extension =
    Extension.V3.declare rule_name Extension.Context.expression
      Ast_pattern.(pstr nil)
      expand
  in
  Ppxlib.Context_free.Rule.extension extension

(** Given [MODULE] and [FUN], create a rule to expand [[%FUN]] to
    [MODULE.FUN __FILE__ __LINE__] *)
let mk_check_rule (m : string) (f : string) : Context_free.Rule.t =
  mk_raw_check_rule (m ^ "." ^ f) f

(** Given [MODULE] and [[FUN1; ...]] create rules to expand [[%FUN1]] (resp.,
    [[%FUN1_opt_span]]) to [MODULE.FUN1 __FILE__ __LINE__] (resp.,
    [MODULE.FUN1_opt_span __FILE__ __LINE__]). *)
let mk_check_rules (m : string) (fl : string list) : Context_free.Rule.t list =
  List.flatten
    (List.map
       (fun f -> [ mk_check_rule m f; mk_check_rule m (f ^ "_opt_span") ])
       fl)

(** Keeping this alternative here as it might prove convenient *)
let declare_cassert_opt_span_full_rule () =
  let expand ~ctxt (b : bool) (msg : string) : expression =
    let loc = Expansion_context.Extension.extension_point_loc ctxt in
    pexp_apply ~loc
      (evar ~loc "Errors.cassert_opt_span")
      [
        (Nolabel, estring ~loc loc.loc_start.pos_fname);
        (Nolabel, eint ~loc loc.loc_start.pos_lnum);
        (Nolabel, ebool ~loc b);
        (Nolabel, pexp_construct ~loc (Located.lident ~loc "None") None);
        (Nolabel, estring ~loc msg);
      ]
  in
  let extension =
    Extension.V3.declare "cassert_opt_span" Extension.Context.expression
      Ast_pattern.(double_expr_payload (ebool __) (estring __))
      expand
  in
  Ppxlib.Context_free.Rule.extension extension

(** The rules for the helpers which raise errors *)
let () =
  Driver.register_transformation
    ~rules:
      (* The rules for the helpers in `Errors.ml` *)
      (mk_check_rules "Errors"
         [
           "save_error";
           "craise";
           "classert";
           "cassert";
           "sanity_check";
           "internal_error";
           "cassert_warn";
           "silent_unwrap";
         ]
      @ [
          mk_check_rule "Errors" "unwrap_opt_span";
          mk_check_rule "Errors" "unwrap_with_span";
          mk_check_rule "Errors" "try_unwrap";
        ]
      (* The rules for the helpers in `ExtractErrors.ml` *)
      @ mk_check_rules "ExtractErrors"
          [ "extract_raise"; "admit_raise"; "admit_string" ]
      (* The rules for the helpers in `PureErrors.ml` *)
      @ [ mk_check_rule "PureErrors" "pure_type_check" ]
      (* Misc. *)
      @ [ mk_raw_check_rule "Errors.add_loc" "add_loc" ])
    "expand_asserts"

(** Given [MODULE] and [FUN], create a rule to expand [[%FUN]] to
    [MODULE.FUN __FILE__ __LINE__] *)
let mk_log_rule ~(lazylog : bool) (logfun : string) : Context_free.Rule.t =
  let expand ~ctxt (msg : expression) : expression =
    let loc = Expansion_context.Extension.extension_point_loc ctxt in
    (* log#logfun (lazy (Logging.to_log_msg __FUNCTION__ MSG)) *)
    (* Logging.to_log_msg __FUNCTION__ MSG *)
    let msg =
      pexp_apply ~loc
        (evar ~loc "Logging.to_log_msg")
        [
          (Nolabel, evar ~loc "__FUNCTION__");
          (Nolabel, eint ~loc loc.loc_start.pos_lnum);
          (Nolabel, msg);
        ]
    in
    (* lazy (...) *)
    let exp = if lazylog then pexp_lazy ~loc msg else msg in
    (* log#logfun (lazy (...)) *)
    let log = evar ~loc "log" in
    (* Construct the method access: [log#logfun] *)
    let log = pexp_send ~loc log (Located.mk ~loc logfun) in
    (* The full expression *)
    pexp_apply ~loc log [ (Nolabel, exp) ]
  in
  let extension =
    Extension.V3.declare logfun Extension.Context.expression
      Ast_pattern.(single_expr_payload __)
      expand
  in
  Ppxlib.Context_free.Rule.extension extension

let mk_log_rules logs =
  List.map (fun (lazylog, logfun) -> mk_log_rule ~lazylog logfun) logs

(** The rules for the loggers *)
let () =
  Driver.register_transformation
    ~rules:
      (mk_log_rules
         [
           (true, "linfo");
           (true, "ldebug");
           (true, "ltrace");
           (true, "sinfo");
           (true, "sdebug");
           (true, "strace");
         ])
    "expand_loggers"
