open Aeneas

let loc : Meta.loc = { line = 1; col = 0 }

let span : Meta.span =
  let file : Meta.file =
    {
      name = Meta.NotReal "loop-exit-shape-test";
      crate_name = "aeneas";
      contents = None;
    }
  in
  { data = { file; beg_loc = loc; end_loc = loc }; generated_from_span = None }

let unit_ty = PureUtils.mk_unit_ty
let bool_ty = Pure.TLiteral Pure.TBool
let nat_ty = Pure.TLiteral Pure.TPureNat
let int_ty = Pure.TLiteral Pure.TPureInt

let loop_exit_ty =
  PureUtils.mk_loop_exit_ty unit_ty bool_ty nat_ty int_ty

let generic_args =
  PureUtils.mk_generic_args_from_types [ unit_ty; bool_ty; nat_ty; int_ty ]

let shape_value ty : Pure.texpr = { e = Pure.EError (None, "shape-only"); ty }

let check_field_type variant expected_ty =
  let field_tys =
    PureTypeCheck.get_adt_field_types span Pure.TypeDeclId.Map.empty
      (Pure.TBuiltin Pure.TLoopExit) (Some variant) generic_args
  in
  match field_tys with
  | [ ty ] when ty = expected_ty -> ()
  | _ -> failwith "unexpected LoopExit field type"

let check_constructor variant (value : Pure.texpr) (expr : Pure.texpr) =
  if expr.ty <> loop_exit_ty then failwith "unexpected LoopExit type";
  match PureUtils.opt_destruct_qualif_apps expr with
  | Some
      ( {
          id =
            Pure.AdtCons
              {
                adt_id = Pure.TBuiltin Pure.TLoopExit;
                variant_id = Some actual_variant;
              };
          generics;
        },
        args )
    when actual_variant = variant && generics = generic_args && args = [ value ]
    -> ()
  | _ -> failwith "unexpected LoopExit constructor shape"

let check_extract_variant_name backend_name variant expected_name =
  Config.set_backend backend_name;
  let matches =
    List.exists
      (fun (ty, actual_variant, actual_name) ->
        ty = Pure.TLoopExit && actual_variant = variant
        && actual_name = expected_name)
      (ExtractBase.builtin_variants ())
  in
  if not matches then failwith "missing LoopExit extraction variant name"

let check_extract_names () =
  List.iter
    (fun (backend_name, normal_break, propagated_break, propagated_continue,
          propagated_return) ->
      check_extract_variant_name backend_name Pure.loop_exit_normal_break_id
        normal_break;
      check_extract_variant_name backend_name Pure.loop_exit_propagated_break_id
        propagated_break;
      check_extract_variant_name backend_name
        Pure.loop_exit_propagated_continue_id propagated_continue;
      check_extract_variant_name backend_name
        Pure.loop_exit_propagated_return_id propagated_return)
    [
      ( "lean",
        "normalBreak",
        "propagatedBreak",
        "propagatedContinue",
        "propagatedReturn" );
      ( "fstar",
        "NormalBreak",
        "PropagatedBreak",
        "PropagatedContinue",
        "PropagatedReturn" );
      ( "coq",
        "NormalBreak",
        "PropagatedBreak",
        "PropagatedContinue",
        "PropagatedReturn" );
      ( "hol4",
        "NormalBreak",
        "PropagatedBreak",
        "PropagatedContinue",
        "PropagatedReturn" );
    ]

let () =
  let normal_break = shape_value unit_ty in
  let propagated_break = shape_value bool_ty in
  let propagated_continue = shape_value nat_ty in
  let propagated_return = shape_value int_ty in
  check_field_type Pure.loop_exit_normal_break_id unit_ty;
  check_field_type Pure.loop_exit_propagated_break_id bool_ty;
  check_field_type Pure.loop_exit_propagated_continue_id nat_ty;
  check_field_type Pure.loop_exit_propagated_return_id int_ty;
  check_constructor Pure.loop_exit_normal_break_id normal_break
    (PureUtils.mk_loop_exit_normal_break_texpr span normal_break bool_ty nat_ty
       int_ty);
  check_constructor Pure.loop_exit_propagated_break_id propagated_break
    (PureUtils.mk_loop_exit_propagated_break_texpr span unit_ty propagated_break
       nat_ty int_ty);
  check_constructor Pure.loop_exit_propagated_continue_id propagated_continue
    (PureUtils.mk_loop_exit_propagated_continue_texpr span unit_ty bool_ty
       propagated_continue int_ty);
  check_constructor Pure.loop_exit_propagated_return_id propagated_return
    (PureUtils.mk_loop_exit_propagated_return_texpr span unit_ty bool_ty nat_ty
       propagated_return);
  check_extract_names ()
