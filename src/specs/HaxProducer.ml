(** The hax specs producer.

    Hax encodes [#[hax_lib::requires(...)]] / [#[hax_lib::ensures(|r| ...)]]
    annotations as separate "decoration" functions plus [_hax::json] attributes
    that link a real function to its pre/post decorations by UUID. This module
    parses those attributes, and the [produce] producer folds them into
    {!Spec.spec} / {!Spec.proof_obligation} entries (consuming the decoration
    functions). The [_hax::json] attribute payloads are parsed by
    {!HaxAttributes}. *)

open HaxAttributes

let log = Logging.translate_log

(** Per-parent accumulator while scanning attributes. *)
type assoc = {
  parent : Pure.fun_decl;
  requires_uid : string option;
  ensures_uid : string option;
}

let empty_assoc parent = { parent; requires_uid = None; ensures_uid = None }

(** Update an accumulator with one [AssociatedItem]. Per design we accept at
    most one of each role per fn: extras are logged and ignored. *)
let update_assoc (role : hax_role) (uid : string) (a : assoc) : assoc =
  let warn_extra side =
    [%lwarning
      Printf.sprintf "hax-specs: multiple #[%s] on fn `%s`; ignoring extras"
        side a.parent.name]
  in
  match role with
  | Requires -> (
      match a.requires_uid with
      | None -> { a with requires_uid = Some uid }
      | Some _ ->
          warn_extra "requires";
          a)
  | Ensures -> (
      match a.ensures_uid with
      | None -> { a with ensures_uid = Some uid }
      | Some _ ->
          warn_extra "ensures";
          a)
  | Other_role -> a

(** Read a hax-annotated crate: emit one [FunctionSpec] per real fn that carries
    [AssociatedItem] attribute(s), and strip the decoration fns whose bodies
    have been folded into those specs. *)
let produce (_ctx : TranslateCore.trans_ctx)
    (crate : TranslateCore.translated_crate) : TranslateCore.translated_crate =
  let _, fresh_spec_id = Spec.SpecId.fresh_stateful_generator () in
  let _, fresh_proof_id = Spec.ProofId.fresh_stateful_generator () in
  let uid_map : Pure.fun_decl Collections.StringMap.t ref =
    ref Collections.StringMap.empty
  in
  let dec_set : Pure.FunDeclId.Set.t ref = ref Pure.FunDeclId.Set.empty in
  let assoc_map : assoc Pure.FunDeclId.Map.t ref =
    ref Pure.FunDeclId.Map.empty
  in
  (* Pass 1: classify each fun_decl by its [_hax::json] payloads. *)
  List.iter
    (fun (ft : TranslateCore.pure_fun_translation) ->
      let f = ft.f in
      List.iter
        (fun a ->
          match parse_attr a with
          | None | Some Other_payload | Some Late_skip -> ()
          | Some (Uid uid) ->
              uid_map := Collections.StringMap.add uid f !uid_map;
              dec_set := Pure.FunDeclId.Set.add f.def_id !dec_set
          | Some (Associated_item { role; uid }) ->
              let cur =
                match Pure.FunDeclId.Map.find_opt f.def_id !assoc_map with
                | Some a -> a
                | None -> empty_assoc f
              in
              assoc_map :=
                Pure.FunDeclId.Map.add f.def_id
                  (update_assoc role uid cur)
                  !assoc_map)
        f.item_meta.attr_info.attributes)
    crate.fun_decls;

  (* Pass 2: resolve uids to decoration fns and build [Spec.spec] /
     [Spec.proof_obligation] entries.

     A decoration fn is reused as a proper function: we rename it to
     [<parent>::<suffix>] and mark it [reducible], so the standard function
     extractor prints it as [@[reducible] def <fn>.pre …] / [… .post …]. The
     whole [Pure.fun_decl] is stashed in the spec (it is stripped from
     [crate.fun_decls] in pass 3, so it isn't also printed among the regular
     functions). *)
  let rename_decoration (parent : Pure.fun_decl) (suffix : string)
      (dec : Pure.fun_decl) : Pure.fun_decl =
    let name =
      parent.item_meta.name
      @ [ Types.PeIdent (suffix, Pure.Disambiguator.zero) ]
    in
    let item_meta = { dec.item_meta with name } in
    {
      dec with
      item_meta;
      name = parent.name ^ "." ^ suffix;
      backend_attributes = { reducible = true };
    }
  in
  (* Resolve a decoration uid. Checks the arity. *)
  let lookup_dec (parent : Pure.fun_decl) ~(suffix : string) ?(is_post = false)
      (uid : string) : Pure.fun_decl option =
    match Collections.StringMap.find_opt uid !uid_map with
    | None ->
        [%lwarning
          Printf.sprintf
            "hax-specs: fn `%s` references unknown decoration uid %s; skipping \
             that side"
            parent.name uid];
        None
    | Some dec ->
        let decl = rename_decoration parent suffix dec in
        let expected_arity =
          List.length parent.signature.inputs + if is_post then 1 else 0
        in
        let actual_arity = List.length decl.signature.inputs in
        if expected_arity = actual_arity then Some decl
        else begin
          [%lwarning
            Printf.sprintf
              "hax-specs: argument count mismatch for `%s.%s` (takes %d, \
               expected %d); dropping this condition"
              parent.name suffix actual_arity expected_arity];
          None
        end
  in
  let shape = function
    | None -> "absent"
    | Some _ -> "present"
  in
  (* Build the spec (statement of correctness) and the proof obligation that
     discharges it, for one parent fn's accumulated [AssociatedItem]s. *)
  let build_entry (parent_id, a) : (Spec.spec * Spec.proof_obligation) option =
    let pre = Option.bind a.requires_uid (lookup_dec a.parent ~suffix:"pre") in
    let post =
      Option.bind a.ensures_uid
        (lookup_dec a.parent ~suffix:"post" ~is_post:true)
    in
    if Option.is_none pre && Option.is_none post then None
    else (
      [%ltrace
        Printf.sprintf "hax-specs:   fn=%s pre=%s post=%s" a.parent.name
          (shape pre) (shape post)];
      let span = Some a.parent.item_meta.span in
      (* One [function_spec] payload, shared between the spec and the proof
         obligation that discharges it. *)
      let fspec : HaxSpecs.function_spec = { fn = parent_id; pre; post } in
      let spec : Spec.spec =
        { id = fresh_spec_id (); span; kind = HaxSpec (FunctionSpec fspec) }
      in
      let obligation : Spec.proof_obligation =
        {
          id = fresh_proof_id ();
          span;
          kind = HaxProof (FunctionContract { spec = fspec; proof = Admitted });
        }
      in
      Some (spec, obligation))
  in
  let new_specs, new_obligations =
    Pure.FunDeclId.Map.bindings !assoc_map
    |> List.filter_map build_entry
    |> List.split
  in

  (* Pass 3: strip consumed decoration fns from [crate.fun_decls]. *)
  let new_fun_decls =
    List.filter
      (fun (ft : TranslateCore.pure_fun_translation) ->
        not (Pure.FunDeclId.Set.mem ft.f.def_id !dec_set))
      crate.fun_decls
  in

  [%linfo
    Printf.sprintf "hax-specs: produced %d FunctionSpec entries"
      (List.length new_specs)];

  {
    crate with
    fun_decls = new_fun_decls;
    specs = crate.specs @ new_specs;
    proof_obligations = crate.proof_obligations @ new_obligations;
  }
