module F = Format

module Helpers = struct
  (** Emit [words] separated by breakable spaces *)
  let emit_words (fmt : F.formatter) (words : string list) : unit =
    List.iteri
      (fun i w ->
        if i > 0 then F.pp_print_space fmt ();
        F.pp_print_string fmt w)
      words

  (** Emit a pre/post condition function declaration. [extract_fun_decl] emits
      its own leading break, so we add no trailing separator here. *)
  let emit_cond (ctx : ExtractBase.extraction_ctx) (fmt : F.formatter)
      (f : Pure.fun_decl) : unit =
    Extract.extract_fun_decl ctx fmt ExtractBase.SingleNonRec false f

  (** Run [k] on its own line inside an [hovbox] *)
  let line (fmt : F.formatter) (k : unit -> unit) : unit =
    F.pp_print_cut fmt ();
    F.pp_open_hovbox fmt 0;
    k ();
    F.pp_close_box fmt ()

  (** Wrap [k] in a Hoare-triple postcondition delimiter [⦃ … ⦄]. *)
  let emit_wp (fmt : F.formatter) (k : unit -> unit) : unit =
    Extract.emit_delim fmt "⦃" k "⦄"

  (** Emit [<name> <generics> <args>] — an application head applied to its
      generic and value arguments (caller controls the surrounding box). *)
  let emit_app span ctx fmt explicit generics args (name : string) =
    F.pp_print_string fmt name;
    (* Generic args, matching the head's generic binders. *)
    ExtractTypes.extract_generic_args span ctx fmt Pure.TypeDeclId.Set.empty
      ~explicit:(Some explicit) generics;
    List.iter
      (fun te ->
        F.pp_print_space fmt ();
        Extract.extract_texpr span ctx fmt ~inside:true ~inside_do:false te)
      args

  (** Emit [(<cond> <generics> <args>).holds] for a fn [f] *)
  let emit_holds span ctx fmt explicit generics args (f : Pure.fun_decl) =
    let name = ExtractBase.ctx_get_local_function span f.def_id None ctx in
    F.pp_open_hovbox fmt 0;
    F.pp_print_string fmt "(";
    emit_app span ctx fmt explicit generics args name;
    F.pp_print_string fmt ").holds";
    F.pp_close_box fmt ()
end

open Helpers

(** Emit the proof of a spec/theorem as [:= by <tactic>]. *)
let emit_proof fmt (p : HaxSpecs.proof) =
  let tactic =
    match p with
    | Admitted -> "sorry"
  in
  F.pp_print_string fmt (":= by " ^ tactic)

(** Emit the pre/post condition function declarations, if present. *)
let emit_conditions ctx fmt ~pre ~post =
  Option.iter (emit_cond ctx fmt) pre;
  Option.iter (emit_cond ctx fmt) post

(** Compute the [<fn>.spec] definition name for a hax-annotated function: the
    formatted function name followed by the [.spec] suffix. The single source of
    truth for the spec name — used by both the spec declaration ({!emit_spec})
    and the proof obligation that references it ({!emit_obligation}). *)
let compute_spec_name (def : Pure.fun_decl) (ctx : ExtractBase.extraction_ctx) :
    string =
  let fname =
    ExtractBase.ctx_compute_fun_global_name_no_suffix def.item_meta def.src
      ~is_trait_decl_field:false ctx
  in
  let lp_suffix =
    ExtractBase.default_fun_suffix def.num_loops def.loop_id def.loop_pos
  in
  fname ^ lp_suffix ^ ".spec"

(** Prelude shared by both statement styles: register the result variable (a
    collision-safe fvar), build the [.holds] / application printers, emit the
    (shared) optional precondition hypothesis [(<fn>.pre <args>).holds →] *)
let emit_statement_prelude ctx fmt span (fn : Pure.FunDeclId.id) explicit
    generics output_ty arg_texprs res_id ~(pre : Pure.fun_decl option)
    ~(post : Pure.fun_decl option) =
  let open ExtractBase in
  (* Register the postcondition's result variable *)
  let ctx, res_name = ctx_add_var span "res" res_id ctx in
  let res_texpr : Pure.texpr = { e = FVar res_id; ty = output_ty } in

  let emit_holds = emit_holds span ctx fmt explicit generics in

  (* The real function application [<fn> <args>], via the standard printer. *)
  let emit_fn_call () : unit =
    let head : Pure.texpr =
      {
        e =
          Qualif
            {
              id = FunOrOp (Fun (FromLlbc (FunId (FRegular fn), None)));
              generics;
            };
        ty = output_ty;
      }
    in
    Extract.extract_App span ctx fmt ~inside:false ~inside_do:false head
      arg_texprs output_ty
  in

  (* Optional pre-hypothesis: [(<fn>.pre <args>).holds →]. *)
  (match pre with
  | None -> ()
  | Some pre_fn ->
      line fmt (fun () ->
          emit_holds arg_texprs pre_fn;
          F.pp_print_space fmt ();
          F.pp_print_string fmt "→"));

  (* The postcondition body: [(<fn>.post <args> res).holds] or [True] *)
  let emit_post_content () =
    match post with
    | None -> F.pp_print_string fmt "True"
    | Some post_fn -> emit_holds (arg_texprs @ [ res_texpr ]) post_fn
  in
  (emit_fn_call, res_name, emit_post_content)

(** Emits the [Step]-style spec statement — the body of
    [def foo.spec … : Prop :=] (the
    [@[step] theorem foo.spec.proof … := by sorry] wrapper is the obligation,
    emitted separately):
    {[
      (foo.pre args).holds →
      foo args
      ⦃ res => (foo.post args res).holds ⦄
    ]} *)
let emit_statement_step ctx fmt span fn explicit generics output_ty arg_texprs
    res_id pre post =
  let emit_fn_call, res_name, emit_post_content =
    emit_statement_prelude ctx fmt span fn explicit generics output_ty
      arg_texprs res_id ~pre ~post
  in
  line fmt emit_fn_call;
  line fmt (fun () ->
      emit_wp fmt (fun () ->
          emit_words fmt [ res_name; "=>" ];
          F.pp_print_space fmt ();
          emit_post_content ()))

(** Emits the [Mvcgen]-style spec statement — the body of
    [def foo.spec … : Prop :=] (the
    [@[spec] theorem foo.spec.proof … := by sorry] wrapper is the obligation,
    emitted separately):
    {[
      (foo.pre args).holds →
      ⦃ ⌜ True ⌝ ⦄
      foo args
      ⦃ ⇓ res => ⌜ (foo.post args res).holds ⌝ ⦄
    ]} *)
let emit_statement_mvcgen ctx fmt span fn explicit generics output_ty arg_texprs
    res_id pre post =
  let emit_fn_call, res_name, emit_post_content =
    emit_statement_prelude ctx fmt span fn explicit generics output_ty
      arg_texprs res_id ~pre ~post
  in
  let emit_pure k = Extract.emit_delim fmt "⌜" k "⌝" in
  line fmt (fun () ->
      emit_wp fmt (fun () -> emit_pure (fun () -> F.pp_print_string fmt "True")));
  line fmt emit_fn_call;
  line fmt (fun () ->
      emit_wp fmt (fun () ->
          emit_words fmt [ "⇓"; res_name; "=>" ];
          F.pp_print_space fmt ();
          emit_pure emit_post_content))

(** The spec backend selected via [-specs] (defaults to [Step]). *)
let current_spec_backend () : Config.spec_backend =
  Option.value (Config.spec_backend ()) ~default:Config.Step

(** Emit the spec statement shape, dispatching on the spec backend configured
    via [-specs]. *)
let emit_statement ctx fmt span fn explicit generics output_ty arg_texprs res_id
    pre post =
  let emit =
    match current_spec_backend () with
    | Config.Mvcgen -> emit_statement_mvcgen
    | Config.Step -> emit_statement_step
  in
  emit ctx fmt span fn explicit generics output_ty arg_texprs res_id pre post

(** Emit one [Spec.spec] entry *)
let emit_spec ctx fmt (s : HaxSpecs.spec) opt_span =
  let open ExtractBase in
  match s with
  | FunctionSpec { fn; pre; post } -> (
      match Pure.FunDeclId.Map.find_opt fn ctx.trans_funs with
      | None ->
          [%warn_opt_span] opt_span
            ("Trying to print a spec for an unknown function '"
            ^ Pure.FunDeclId.to_string fn
            ^ "'")
      | Some ft ->
          (* Register the pre/post condition fns' names in the (local) context *)
          let reg f_opt ctx =
            Option.fold ~some:(fun f -> ctx_add_fun_decl f ctx) ~none:ctx f_opt
          in
          let ctx = ctx |> reg pre |> reg post in
          let parent = ft.f in
          let span = parent.item_meta.span in
          let sg = parent.signature in
          let explicit = sg.explicit_info in
          let generics = PureUtils.generic_args_of_params sg.generics in

          (* Open the parent's body binders *)
          let _, fresh_fvar_id = Pure.FVarId.fresh_stateful_generator () in
          let parent =
            {
              parent with
              body =
                Option.map
                  (fun b ->
                    snd (PureUtils.open_all_fun_body fresh_fvar_id span b))
                  parent.body;
            }
          in
          let arg_texprs =
            match parent.body with
            | None -> []
            | Some { inputs; _ } ->
                List.filter_map (PureUtils.tpat_to_texpr span) inputs
          in
          (* Fresh result-var id, from the body generator so it can't clash. *)
          let res_id = fresh_fvar_id () in

          (* Blank line before the entry. *)
          F.pp_print_break fmt 0 0;

          emit_conditions ctx fmt ~pre ~post;

          (* Spec definition header: [def <fn>.spec <binders> : Prop :=] *)
          F.pp_print_break fmt 0 0;
          F.pp_open_vbox fmt 0;
          F.pp_open_vbox fmt ctx.indent_incr;
          F.pp_open_hovbox fmt ctx.indent_incr;
          (match fun_decl_kind_to_qualif SingleNonRec with
          | Some qualif ->
              F.pp_print_string fmt qualif;
              F.pp_print_space fmt ()
          | None -> ());
          F.pp_print_string fmt (compute_spec_name parent ctx);
          (* Generic + value binders via the standard param extractor. *)
          let space = ref false in
          let _, ctx, _ = Extract.extract_fun_parameters space ctx fmt parent in
          ExtractTypes.insert_req_space fmt space;
          F.pp_print_string fmt ": Prop :=";
          F.pp_close_box fmt ();

          (* Statement shape (the def body). *)
          emit_statement ctx fmt span fn explicit generics sg.output arg_texprs
            res_id pre post;
          F.pp_close_box fmt ();
          (* inner vbox *)
          F.pp_close_box fmt ();
          (* outer vbox *)
          F.pp_print_cut fmt ())

(** Emit one [HaxSpecs.obligation] entry as the proof obligation that discharges
    a spec's statement of correctness:
    {[
      @[spec]/@[step]
      theorem foo.spec.proof args : foo.spec args := by sorry
    ]}
    The attribute ([step] / [spec]) follows the configured spec backend. *)
let emit_obligation ctx fmt (o : HaxSpecs.obligation) opt_span =
  let open ExtractBase in
  match o with
  | FunctionContract { spec = { fn; _ }; proof } -> (
      match Pure.FunDeclId.Map.find_opt fn ctx.trans_funs with
      | None ->
          [%warn_opt_span] opt_span
            ("Trying to print a proof obligation for an unknown function '"
            ^ Pure.FunDeclId.to_string fn
            ^ "'")
      | Some ft ->
          let parent = ft.f in
          let span = parent.item_meta.span in
          let sg = parent.signature in
          let explicit = sg.explicit_info in
          let generics = PureUtils.generic_args_of_params sg.generics in
          (* The canonical [<fn>.spec] name, from the shared {!compute_spec_name}
           (same as the spec declaration). *)
          let spec_name = compute_spec_name parent ctx in

          (* Open the parent's body binders *)
          let _, fresh_fvar_id = Pure.FVarId.fresh_stateful_generator () in
          let parent =
            {
              parent with
              body =
                Option.map
                  (fun b ->
                    snd (PureUtils.open_all_fun_body fresh_fvar_id span b))
                  parent.body;
            }
          in
          let arg_texprs =
            match parent.body with
            | None -> []
            | Some { inputs; _ } ->
                List.filter_map (PureUtils.tpat_to_texpr span) inputs
          in

          (* Blank line before the entry. *)
          F.pp_print_break fmt 0 0;

          (* Box layout (brackets = boxes):
             [ [theorem name] binders : [statement] ]  [:= by sorry]
             The outer [hvbox] keeps the whole theorem on one line if it fits;
             otherwise [:= by sorry] breaks onto its own line first, and only if
             the statement box itself still overflows do the binders/type wrap.
             [extract_attributes]'s trailing break becomes a newline in the vbox. *)
          let attr =
            match current_spec_backend () with
            | Config.Mvcgen -> "spec"
            | Config.Step -> "step"
          in
          F.pp_open_vbox fmt 0;
          ExtractTypes.extract_attributes span ctx fmt parent.item_meta.name
            None [ attr ] "" [] ~is_external:false;
          (* Outer box: [<statement> := by sorry] — break before the proof first. *)
          F.pp_open_hvbox fmt ctx.indent_incr;
          (* The theorem statement: [theorem name binders : <type>]. *)
          F.pp_open_hovbox fmt ctx.indent_incr;
          F.pp_print_string fmt "theorem";
          F.pp_print_space fmt ();
          F.pp_print_string fmt (spec_name ^ ".proof");
          (* Generic + value binders via the standard param extractor. *)
          let space = ref false in
          let _, ctx, _ = Extract.extract_fun_parameters space ctx fmt parent in
          ExtractTypes.insert_req_space fmt space;
          F.pp_print_string fmt ":";
          F.pp_print_space fmt ();
          (* The statement of correctness, in its own box:
             [<fn>.spec <generics> <args>]. *)
          F.pp_open_hovbox fmt 0;
          emit_app span ctx fmt explicit generics arg_texprs spec_name;
          F.pp_close_box fmt ();
          F.pp_close_box fmt ();
          (* statement hovbox *)
          F.pp_print_space fmt ();
          emit_proof fmt proof;
          F.pp_close_box fmt ();
          (* outer hvbox *)
          F.pp_close_box fmt ();
          (* attribute vbox *)
          F.pp_print_cut fmt ())
