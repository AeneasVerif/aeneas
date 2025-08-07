open Ppxlib
open Ast_builder.Default

(* let empty_expr_payload = Ast_pattern.(pstr nil) *)
let single_expr_payload = Ast_pattern.single_expr_payload

let double_expr_payload t0 t1 =
  Ast_pattern.(single_expr_payload (pexp_tuple (t0 ^:: t1 ^:: nil)))

let triple_expr_payload t0 t1 t2 =
  Ast_pattern.(single_expr_payload (pexp_tuple (t0 ^:: t1 ^:: t2 ^:: nil)))

let mk_rule (f : string) : Context_free.Rule.t =
  let expand ~ctxt : expression =
    let loc = Expansion_context.Extension.extension_point_loc ctxt in
    pexp_apply ~loc
      (evar ~loc ("Errors." ^ f))
      [
        (Nolabel, estring ~loc loc.loc_start.pos_fname);
        (Nolabel, eint ~loc loc.loc_start.pos_lnum);
      ]
  in
  let extension =
    Extension.V3.declare f Extension.Context.expression
      Ast_pattern.(pstr nil)
      expand
  in
  Ppxlib.Context_free.Rule.extension extension

let mk_rules (fl : string list) : Context_free.Rule.t list =
  List.flatten (List.map (fun f -> [ mk_rule f; mk_rule (f ^ "_opt_span") ]) fl)

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

let () =
  Driver.register_transformation
    ~rules:
      (mk_rules
         [
           "craise";
           "classert";
           "cassert";
           "sanity_check";
           "internal_error";
           "cassert_warn";
           "silent_unwrap";
         ]
      @ [ mk_rule "unwrap_opt_span" ])
    "expand_asserts"
