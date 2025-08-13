(** The following module defines micro-passes which operate on the pure AST *)

open Pure
open PureUtils
open TranslateCore

(** The local logger *)
let log = Logging.pure_micro_passes_log

type ctx = { fun_decls : fun_decl FunDeclId.Map.t; trans_ctx : trans_ctx }

let fun_decl_to_string (ctx : ctx) (def : fun_decl) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.fun_decl_to_string fmt def

let fun_sig_to_string (ctx : ctx) (sg : fun_sig) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.fun_sig_to_string fmt sg

let var_to_string (ctx : ctx) (v : var) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.var_to_string fmt v

let texpression_to_string (ctx : ctx) (x : texpression) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.texpression_to_string fmt false "" "  " x

let fun_body_to_string (ctx : ctx) (x : fun_body) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.fun_body_to_string fmt x

let switch_to_string (ctx : ctx) scrut (x : switch_body) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.switch_to_string fmt "" "  " scrut x

let struct_update_to_string (ctx : ctx) supd : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.struct_update_to_string fmt "" "  " supd

let typed_pattern_to_string (ctx : ctx) pat : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.typed_pattern_to_string fmt pat

let lift_map_fun_decl_body (f : ctx -> fun_decl -> fun_body -> fun_body)
    (ctx : ctx) (def : fun_decl) : fun_decl =
  (* We open all the bound variables in the body before exploring it, then
     close them all after performing the updates - this makes it easier to
     deal with variables *)
  map_open_fun_decl_body (f ctx def) def

(** Lift a visitor of expressions to a function which updates a function body *)
let lift_expr_map_visitor_with_state
    (obj :
      ctx ->
      fun_decl ->
      < visit_texpression : 'a -> texpression -> texpression ; .. >)
    (state : 'a) (ctx : ctx) (def : fun_decl) : fun_decl =
  (* We open all the bound variables in the body before exploring it, then
     close them all after performing the updates - this makes it easier to
     deal with variables *)
  map_open_fun_decl_body_expr ((obj ctx def)#visit_texpression state) def

(** Lift a visitor of expressions to a function which updates a function body *)
let lift_expr_map_visitor
    (obj :
      ctx ->
      fun_decl ->
      < visit_texpression : unit -> texpression -> texpression ; .. >)
    (ctx : ctx) (def : fun_decl) : fun_decl =
  lift_expr_map_visitor_with_state obj () ctx def

let lift_iter_fun_decl_body (f : ctx -> fun_decl -> fun_body -> unit)
    (ctx : ctx) (def : fun_decl) : unit =
  (* We open all the bound variables in the body before exploring it, then
     close them all after performing the updates - this makes it easier to
     deal with variables *)
  iter_open_fun_decl_body (f ctx def) def

(** Lift a visitor of expressions to a function which updates a function body *)
let lift_expr_iter_visitor_with_state
    (obj :
      ctx -> fun_decl -> < visit_texpression : 'a -> texpression -> unit ; .. >)
    (state : 'a) (ctx : ctx) (def : fun_decl) : unit =
  (* We open all the bound variables in the body before exploring it, then
     close them all after performing the updates - this makes it easier to
     deal with variables *)
  iter_open_fun_decl_body_expr ((obj ctx def)#visit_texpression state) def

(** Lift a visitor of expressions to a function which updates a function body *)
let lift_expr_iter_visitor
    (obj :
      ctx ->
      fun_decl ->
      < visit_texpression : unit -> texpression -> unit ; .. >) (ctx : ctx)
    (def : fun_decl) : unit =
  lift_expr_iter_visitor_with_state obj () ctx def

(** A node in the constraints graph *)
type nc_node = Pure of fvar_id | Llbc of E.local_id [@@deriving show, ord]

(** An edge in the constraints graph *)
type nc_edge = { src : nc_node; dest : nc_node; dist : int }
[@@deriving show, ord]

(** Naming constraint deriving from the fact that we assigned a value to a
    different value *)
type nc_assign = {
  rhs_id : nc_node;
  rhs_depth : int;
  lhs_id : nc_node;
  lhs_depth : int;
}
[@@deriving show, ord]

let nc_node_to_string (n : nc_node) =
  match n with
  | Pure id -> "Pure " ^ FVarId.to_string id
  | Llbc id -> "Llbc " ^ E.LocalId.to_string id

let nc_edge_to_string (e : nc_edge) =
  nc_node_to_string e.src ^ " -(" ^ string_of_int e.dist ^ ")-> "
  ^ nc_node_to_string e.dest

module NcNodeOrderedType = struct
  type t = nc_node

  let compare = compare_nc_node
  let to_string = nc_node_to_string
  let pp_t = pp_nc_node
  let show_t = nc_node_to_string
end

module NcNodeMap = Collections.MakeMap (NcNodeOrderedType)
module NcNodeSet = Collections.MakeSet (NcNodeOrderedType)

module NcEdgeOrderedType = struct
  type t = nc_edge

  let compare = compare_nc_edge
  let to_string = nc_edge_to_string
  let pp_t = pp_nc_edge
  let show_t = nc_edge_to_string
end

module NcEdgeMap = Collections.MakeMap (NcEdgeOrderedType)
module NcEdgeSet = Collections.MakeSet (NcEdgeOrderedType)

module NcAssignOrderedType = struct
  type t = nc_assign

  let compare = compare_nc_assign
  let to_string = show_nc_assign
  let pp_t = pp_nc_assign
  let show_t = show_nc_assign
end

module NcAssignMap = Collections.MakeMap (NcAssignOrderedType)
module NcAssignSet = Collections.MakeSet (NcAssignOrderedType)

let rec decompose_typed_pattern span (x : typed_pattern) : (fvar * int) option =
  match x.value with
  | PatBound _ -> [%internal_error] span
  | PatOpen (v, _) -> Some (v, 0)
  | PatAdt { variant_id = None; field_values = [ x ] } -> begin
      Option.map
        (fun (vid, depth) -> (vid, depth + 1))
        (decompose_typed_pattern span x)
    end
  | PatConstant _ | PatDummy | PatAdt _ -> None

let rec decompose_texpression span (x : texpression) : (fvar_id * int) option =
  match x.e with
  | FVar vid -> Some (vid, 0)
  | BVar _ -> [%internal_error] span
  | App _ ->
      let f, args = destruct_apps x in
      begin
        match (f.e, args) with
        | Qualif { id = AdtCons _; _ }, [ x ] ->
            Option.map
              (fun (vid, depth) -> (vid, depth + 1))
              (decompose_texpression span x)
        | _ -> None
      end
  | CVar _
  | Const _
  | Lambda _
  | Qualif _
  | Let _
  | Switch _
  | Loop _
  | StructUpdate _
  | EError _ -> None
  | Meta (_, x) -> decompose_texpression span x

type loop_info = {
  inputs : typed_pattern list;  (** The inputs bound by the loop *)
  outputs : typed_pattern list;
      (** The outputs that we accumulated at each loop call.

          We use this to propagate naming information between all the call
          sites. For instance, if we have:

          {[
            if b then
              let x <- loop ...
            else
              let y <- loop ...
          ]}
          it can happen that we derive a pretty name for [x] but not [y], in
          which case we might want to use the same name for [y] (but we must
          know they are related). *)
}

(** Helper for [compute_pretty_names].

    We explore the function body, while accumulating constraints. Note that all
    the binders should have been opened, and the variable ids should be unique:
    this is important because we will need the information computed for, say,
    one branch of the function to influence the naming of the variables in a
    different branch of the function.

    We use every place meta information. For instance, if we read the free
    variable 0 at place [x.1], we store the mapping [0 -> ("x", 1)]. The number
    is the "depth" of the place, that is the number of projection elements that
    are applied on the base variable. The more projections, the less likely we
    want to use that name for the variable. If we later find a place information
    which gives us a strictly smaller depth, say, we store [0] at place [y], we
    update the mapping (to [0 -> ("y", 0)].

    If we find a variable and we *know* its name (because it is an input of a
    function for instance), then we register the mapping with distance -1.

    We also register how variables influcence each other. For instance, if we
    find an assignment [1 := 0], then we register the fact that variables [0]
    and [1] are linked at distance 0. If we have: [1 := Box 0], then they are
    linked at distance 1, etc. We then use this information to propagate the
    names we computed above. *)
let compute_pretty_names_accumulate_constraints (ctx : ctx) (def : fun_decl)
    (body : fun_body) : (string * int) NcNodeMap.t * nc_edge list =
  [%ldebug fun_body_to_string ctx body];
  (*
     The way we do is as follows:
     - we explore the expressions
     - we register the variables introduced by the let-bindings
     - we use the naming information we find (through the variables and the
       meta-places) to update our context (i.e., maps from variable ids to
       names)
     - we use this information to update the names of the variables used in the
       expressions
   *)
  let span = def.item_meta.span in

  let nodes : (string * int) NcNodeMap.t ref = ref NcNodeMap.empty in

  (* We use a list instead of a set on purpose: we want to propagate following
     the first edges we found *first*.
     TODO: we can make this even more sophisticated.
   *)
  let edges : nc_edge list ref = ref [] in

  (* Information about the loops: we remember the binders defining their inputs so that
     later, when we find a call site, we can equate those binders and the input arguments
     actually used.

     For instance, if the loop has two inputs and we have at the call site:
     {[
       loop1 x y
     ]}
     then 'x' and 'y' are candidate names for the inputs.
  *)
  let loop_infos = ref LoopId.Map.empty in

  let register_node (node : nc_node) (name : string) (dist : int) =
    [%ldebug
      "register_node: id=" ^ nc_node_to_string node ^ ", name=" ^ name
      ^ ", dist=" ^ string_of_int dist];
    nodes :=
      NcNodeMap.update node
        (fun x ->
          match x with
          | None -> Some (name, dist)
          | Some (name', dist') ->
              if dist < dist' then Some (name, dist) else Some (name', dist'))
        !nodes
  in
  let register_var (v : fvar) =
    Option.iter (fun name -> register_node (Pure v.id) name (-1)) v.basename
  in
  let register_local (id : E.local_id) (name : string option) =
    Option.iter (fun name -> register_node (Llbc id) name (-1)) name
  in

  let register_edge (src : nc_node) (dist : int) (dest : nc_node) =
    [%ldebug
      "register_edge: src=" ^ nc_node_to_string src ^ ", dist="
      ^ string_of_int dist ^ ", dist=" ^ nc_node_to_string dest];
    edges := { src; dist; dest } :: !edges
  in

  (* Register an mplace the first time we find one *)
  let register_var_at_place (v : fvar) (mp : mplace option) =
    register_var v;
    match Option.map decompose_mplace_to_local mp with
    | Some (Some (id, _, [])) -> register_edge (Pure v.id) 0 (Llbc id)
    | _ -> ()
  in

  (* *)
  let register_assign (lv : typed_pattern) (rv : texpression) =
    match (decompose_typed_pattern span lv, decompose_texpression span rv) with
    | Some (lhs, lhs_depth), Some (rhs_id, rhs_depth) ->
        register_edge (Pure lhs.id) (lhs_depth + rhs_depth) (Pure rhs_id)
    | _ -> ()
  in
  let register_expression_eq (lv : texpression) (rv : texpression) =
    match (decompose_texpression span lv, decompose_texpression span rv) with
    | Some (lhs_id, lhs_depth), Some (rhs_id, rhs_depth) ->
        register_edge (Pure lhs_id) (lhs_depth + rhs_depth) (Pure rhs_id)
    | _ -> ()
  in
  let register_texpression_has_name (e : texpression) (name : string)
      (depth : int) =
    match decompose_texpression span e with
    | Some (id, depth') -> register_node (Pure id) name (depth + depth')
    | _ -> ()
  in
  let register_texpression_at_place (e : texpression) (mp : mplace) =
    match (decompose_texpression span e, decompose_mplace_to_local mp) with
    | Some (fid, depth), Some (lid, _, []) ->
        register_edge (Pure fid) depth (Llbc lid)
    | _ -> ()
  in

  let visitor =
    object (self)
      inherit [_] iter_expression as super
      method! visit_fvar _ v = register_var v

      method! visit_Let env monadic lv re e =
        (* There might be meta information wrapped around the RHS *)
        Option.iter
          (fun mp ->
            match
              (decompose_typed_pattern span lv, decompose_mplace_to_local mp)
            with
            | Some (lhs, depth), Some (lid, _, []) ->
                register_edge (Pure lhs.id) depth (Llbc lid)
            | _ -> ())
          (fst (opt_unmeta_mplace re));
        register_assign lv re;
        (* Check if this is a loop call *)
        let f, args = destruct_apps re in
        begin
          match f.e with
          | Qualif
              {
                id = FunOrOp (Fun (FromLlbc (FunId (FRegular fid), Some lp_id)));
                _;
              }
            when fid = def.def_id ->
              (* This is a loop! *)
              let info = LoopId.Map.find lp_id !loop_infos in
              (* Link the input arguments to the input variables.
               Note that there shouldn't be partial applications *)
              List.iter
                (fun (lv, re) -> register_assign lv re)
                (List.combine info.inputs args);
              (* Register the output *)
              let info = { info with outputs = lv :: info.outputs } in
              loop_infos := LoopId.Map.add lp_id info !loop_infos
          | _ -> ()
        end;
        (* Continue exploring *)
        super#visit_Let env monadic lv re e

      method! visit_PatBound _ _ _ = [%internal_error] span

      method! visit_PatOpen env lv mp =
        register_var_at_place lv mp;
        super#visit_PatOpen env lv mp

      method! visit_Meta env meta e =
        begin
          match meta with
          | Assignment (mp, rvalue, rmp) ->
              register_texpression_at_place rvalue mp;
              Option.iter (register_texpression_at_place rvalue) rmp
          | SymbolicAssignments infos ->
              List.iter
                (fun (var, rvalue) -> register_expression_eq var rvalue)
                infos
          | SymbolicPlaces infos ->
              List.iter
                (fun (var, name) -> register_texpression_has_name var name 1)
                infos
          | MPlace mp -> register_texpression_at_place e mp
          | Tag _ | TypeAnnot -> ()
        end;
        super#visit_Meta env meta e

      method! visit_loop env loop =
        let info : loop_info = { inputs = loop.inputs; outputs = [] } in
        loop_infos := LoopId.Map.add loop.loop_id info !loop_infos;
        (* The body should be wrapped in "sym places" meta information: we want to use
           it with priority 0 (rather than 1 as is done by default in visit_Meta).
        *)
        (match loop.loop_body.e with
        | Meta (SymbolicPlaces infos, _) ->
            List.iter
              (fun (var, name) -> register_texpression_has_name var name 0)
              infos
        | _ -> ());
        super#visit_loop env loop

      method! visit_mplace _ mp =
        match decompose_mplace_to_local mp with
        | Some (vid, name, _) -> register_local vid name
        | _ -> ()
    end
  in
  List.iter (visitor#visit_typed_pattern ()) body.inputs;
  visitor#visit_texpression () body.body;

  (* Equate the loop outputs *)
  let rec equate (out0 : typed_pattern) (out1 : typed_pattern) : unit =
    match (out0.value, out1.value) with
    | PatOpen (v0, _), PatOpen (v1, _) ->
        register_edge (Pure v0.id) 0 (Pure v1.id)
    | PatAdt adt0, PatAdt adt1 ->
        if
          adt0.variant_id = adt1.variant_id
          && List.length adt0.field_values = List.length adt1.field_values
        then
          List.iter
            (fun (x, y) -> equate x y)
            (List.combine adt0.field_values adt1.field_values)
    | _ -> ()
  in
  LoopId.Map.iter
    (fun _ (info : loop_info) ->
      (* TODO: do we really need to equate them two by two? *)
      let rec go outputs =
        match outputs with
        | [] -> ()
        | out0 :: outputs ->
            let rec go_inner outputs =
              match outputs with
              | [] -> ()
              | out1 :: outputs ->
                  equate out0 out1;
                  go_inner outputs
            in
            go_inner outputs
      in
      go info.outputs)
    !loop_infos;

  [%ldebug
    "nodes:\n"
    ^ NcNodeMap.to_string None
        (fun (n, i) -> "(" ^ n ^ "," ^ string_of_int i ^ ")")
        !nodes];
  (!nodes, List.rev !edges)

(** Partial edge *)
type nc_pedge = { dest : nc_node; dist : int } [@@deriving show, ord]

module NcPEdgeOrderedType = struct
  type t = nc_pedge

  let compare = compare_nc_pedge
  let to_string = show_nc_pedge
  let pp_t = pp_nc_pedge
  let show_t = show_nc_pedge
end

module NcPEdgeMap = Collections.MakeMap (NcPEdgeOrderedType)
module NcPEdgeSet = Collections.MakeSet (NcPEdgeOrderedType)

(** Helper for [compute_pretty_names].

    Compute names for the variables given sets of constraints. *)
let compute_pretty_names_propagate_constraints
    (nodes : (string * int) NcNodeMap.t) (edges0 : nc_edge list) :
    string FVarId.Map.t =
  (* *)
  let nodes = ref nodes in

  (* Initialize the map from variable to set of [assign] constraints *)
  let edges : NcPEdgeSet.t NcNodeMap.t ref = ref NcNodeMap.empty in
  let register_edge (src : nc_node) (dist : int) (dest : nc_node) =
    edges :=
      NcNodeMap.update src
        (fun s ->
          let e : nc_pedge = { dest; dist } in
          match s with
          | None -> Some (NcPEdgeSet.singleton e)
          | Some s -> Some (NcPEdgeSet.add e s))
        !edges
  in

  List.iter
    (fun (c : nc_edge) ->
      register_edge c.src c.dist c.dest;
      register_edge c.dest c.dist c.src)
    edges0;

  (* Push the [assign] constraints to the stack. As long as the stack is not empty,
     pop the first constraint, apply it, if it leads to changes lookup the constraints
     which apply to the modified variables, push them to the stack, continue.

     Note that the edges in the stack are bidirectional: we explore them both ways.
  *)
  let stack : nc_edge list ref = ref edges0 in
  let push_constraints (src : nc_node) =
    match NcNodeMap.find_opt src !edges with
    | None -> ()
    | Some cs ->
        let edges =
          List.map
            (fun { dest; dist } -> { src; dist; dest })
            (NcPEdgeSet.elements cs)
        in
        (* We push the constraints at the end of the stack *)
        stack := !stack @ edges
  in
  let update_one_way (src : nc_node) (dist : int) (dst : nc_node) =
    (* Lookup the information about the source  *)
    match NcNodeMap.find_opt src !nodes with
    | None -> ()
    | Some (name, weight) ->
        let nweight = max weight 0 + dist in
        nodes :=
          NcNodeMap.update dst
            (fun nw ->
              match nw with
              | None ->
                  (* We update: lookup the constraints about the destination and push them to the stack *)
                  push_constraints dst;
                  Some (name, nweight)
              | Some (name', weight') ->
                  if nweight < weight' then (
                    (* Similar to case above *)
                    push_constraints dst;
                    Some (name, nweight))
                  else Some (name', weight'))
            !nodes
  in

  (* Propagate the constraints until we reach a fixed-point *)
  let rec go () =
    match !stack with
    | [] -> ()
    | c :: stack' ->
        stack := stack';
        (* Update in both ways *)
        update_one_way c.src c.dist c.dest;
        update_one_way c.dest c.dist c.src;
        [%ldebug
          "After applying edge:\n" ^ nc_edge_to_string c ^ "\nNodes:\n"
          ^ NcNodeMap.to_string None
              (fun (n, i) -> "(" ^ n ^ "," ^ string_of_int i ^ ")")
              !nodes];
        (* Recursive *)
        go ()
  in
  go ();

  (* Return the result *)
  FVarId.Map.of_list
    (List.filter_map
       (fun (n, (name, _)) ->
         match n with
         | Pure id -> Some (id, name)
         | Llbc _ -> None)
       (NcNodeMap.bindings !nodes))

(** Helper for [compute_pretty_name]: update a fun body given naming
    constraints.

    As with [compute_pretty_names_accumulate_constraints] the binders should
    have been opened so that every variable is uniquely identified. *)
let compute_pretty_names_update (def : fun_decl) (names : string FVarId.Map.t)
    (body : fun_body) : fun_body =
  let span = def.item_meta.span in
  (* Update a variable  *)
  let update_var (v : fvar) : fvar =
    match v.basename with
    | Some _ -> v
    | None -> (
        match FVarId.Map.find_opt v.id names with
        | Some basename -> { v with basename = Some basename }
        | None -> v)
  in

  (* The visitor to update the whole body *)
  let visitor =
    object
      inherit [_] map_expression
      method! visit_PatOpen _ v mp = PatOpen (update_var v, mp)
      method! visit_PatBound _ _ _ = [%internal_error] span
    end
  in

  (* Apply *)
  let { inputs; body } = body in
  let inputs = List.map (visitor#visit_typed_pattern ()) inputs in
  let body = visitor#visit_texpression () body in
  { inputs; body }

(** This function computes pretty names for the variables in the pure AST. It
    relies on the "meta"-place information in the AST to generate naming
    constraints, and then uses those to compute the names. *)
let compute_pretty_names ctx (def : fun_decl) : fun_decl =
  (* We open all the bound variables in the body before exploring it, then
     close them all after performing the updates - this makes it easier to
     deal with variables *)
  map_open_fun_decl_body
    (fun (body : fun_body) ->
      let var_at_place, assign =
        compute_pretty_names_accumulate_constraints ctx def body
      in
      let names =
        compute_pretty_names_propagate_constraints var_at_place assign
      in
      compute_pretty_names_update def names body)
    def

(** Remove the meta-information *)
let remove_meta (def : fun_decl) : fun_decl =
  map_open_fun_decl_body_expr PureUtils.remove_meta def

(** Introduce calls to [massert] (monadic assertion).

    The pattern below is very frequent especially as it is introduced by the
    [assert!] macro. We perform the following simplification:
    {[
      if b then e else fail ~~>massert b;
      e
    ]} *)
let intro_massert_visitor (_ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in
  object
    inherit [_] map_expression as super

    method! visit_Switch env scrut switch =
      match switch with
      | If (e_true, e_false) ->
          if is_fail_panic e_false.e then begin
            (* Introduce a call to [massert] *)
            let massert =
              Qualif
                {
                  id = FunOrOp (Fun (Pure Assert));
                  generics = empty_generic_args;
                }
            in
            let massert =
              {
                e = massert;
                ty = mk_arrow mk_bool_ty (mk_result_ty mk_unit_ty);
              }
            in
            let massert = mk_app span massert scrut in
            (* Introduce the let-binding *)
            let monadic = true in
            let pat = mk_dummy_pattern mk_unit_ty in
            super#visit_Let env monadic pat massert e_true
          end
          else super#visit_Switch env scrut switch
      | _ -> super#visit_Switch env scrut switch
  end

let intro_massert = lift_expr_map_visitor intro_massert_visitor

(** Simplify the let-bindings which bind the fields of structures.

    For instance, given the following structure definition:
    {[
      struct Struct {
        x : u32,
        y : u32,
      }
    ]}

    We perform the following transformation:
    {[
      let StructCons x y = s in
      ...

       ~~>

      let x = s.x in
      let y = s.y in
      ...
    ]}

    Of course, this is not always possible depending on the backend. Also,
    recursive structures, and more specifically structures mutually recursive
    with inductives, are usually not supported. We define such recursive
    structures as inductives, in which case it is not always possible to use a
    notation for the field projections.

    The subsequent passes, in particular the ones which inline the useless
    assignments, simplify this further. *)
let simplify_decompose_struct_visitor (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in
  object
    inherit [_] map_expression as super

    method! visit_Let env (monadic : bool) (lv : typed_pattern)
        (scrutinee : texpression) (next : texpression) =
      match (lv.value, lv.ty) with
      | PatAdt adt_pat, TAdt (TAdtId adt_id, generics) ->
          (* Detect if this is an enumeration or not *)
          let tdef =
            TypeDeclId.Map.find adt_id ctx.trans_ctx.type_ctx.type_decls
          in
          let is_enum = TypesUtils.type_decl_is_enum tdef in
          (* We deconstruct the ADT with a single let-binding in two situations:
               - if the ADT is an enumeration (which must have exactly one branch)
               - if we forbid using field projectors
            *)
          let use_let_with_cons =
            is_enum
            || !Config.dont_use_field_projectors
            (* Also, there is a special case when the ADT is to be extracted as
                 a tuple, because it is a structure with unnamed fields. Some backends
                 like Lean have projectors for tuples (like so: `x.3`), but others
                 like Coq don't, in which case we have to deconstruct the whole ADT
                 at once (`let (a, b, c) = x in`) *)
            || TypesUtils.type_decl_from_type_id_is_tuple_struct
                 ctx.trans_ctx.type_ctx.type_infos (T.TAdtId adt_id)
               && not !Config.use_tuple_projectors
          in
          if use_let_with_cons then
            super#visit_Let env monadic lv scrutinee next
          else
            (* This is not an enumeration: introduce let-bindings for every
                 field.
                 We use the [dest] variable in order not to have to recompute
                 the type of the result of the projection... *)
            let gen_field_proj (field_id : FieldId.id) (dest : typed_pattern) :
                texpression =
              let proj_kind = { adt_id = TAdtId adt_id; field_id } in
              let qualif = { id = Proj proj_kind; generics } in
              let proj_e = Qualif qualif in
              let proj_ty = mk_arrow scrutinee.ty dest.ty in
              let proj = { e = proj_e; ty = proj_ty } in
              mk_app span proj scrutinee
            in
            let id_var_pairs =
              FieldId.mapi (fun fid v -> (fid, v)) adt_pat.field_values
            in
            let monadic = false in
            let e =
              List.fold_right
                (fun (fid, pat) e ->
                  let field_proj = gen_field_proj fid pat in
                  mk_opened_let monadic pat field_proj e)
                id_var_pairs next
            in
            (super#visit_texpression env e).e
      | _ -> super#visit_Let env monadic lv scrutinee next
  end

let simplify_decompose_struct =
  lift_expr_map_visitor simplify_decompose_struct_visitor

(** Introduce the special structure create/update expressions.

    Upon generating the pure code, we introduce structure values by using the
    structure constructors:
    {[
      Cons x0 ... xn
    ]}

    This micro-pass turns those into expressions which use structure syntax:
    {[
      type struct = { f0 : nat; f1 : nat; f2 : nat }

      Mkstruct x.f0 x.f1 y ~~> { x with f2 = y }
    ]}

    Note however that we do not apply this transformation if the structure is to
    be extracted as a tuple. *)
let intro_struct_updates_visitor (ctx : ctx) (def : fun_decl) =
  object (self)
    inherit [_] map_expression as super

    method! visit_texpression env (e : texpression) =
      match e.e with
      | App _ -> (
          let app, args = destruct_apps e in
          let ignore () =
            mk_apps def.item_meta.span
              (self#visit_texpression env app)
              (List.map (self#visit_texpression env) args)
          in
          match app.e with
          | Qualif
              {
                id = AdtCons { adt_id = TAdtId adt_id; variant_id = None };
                generics = _;
              } ->
              (* Lookup the def *)
              let decl =
                TypeDeclId.Map.find adt_id ctx.trans_ctx.type_ctx.type_decls
              in
              (* Check if the def will be extracted as a tuple *)
              if
                TypesUtils.type_decl_from_decl_id_is_tuple_struct
                  ctx.trans_ctx.type_ctx.type_infos adt_id
              then ignore ()
              else
                (* Check that there are as many arguments as there are fields - note
                     that the def should have a body (otherwise we couldn't use the
                     constructor) *)
                let fields = TypesUtils.type_decl_get_fields decl None in
                if List.length fields = List.length args then
                  (* Check if the definition is recursive *)
                  let is_rec =
                    match
                      TypeDeclId.Map.find adt_id
                        ctx.trans_ctx.type_ctx.type_decls_groups
                    with
                    | NonRecGroup _ -> false
                    | RecGroup _ -> true
                  in
                  (* Convert, if possible - note that for now for Lean and Coq
                       we don't support the structure syntax on recursive structures *)
                  if
                    (Config.backend () <> Lean && Config.backend () <> Coq)
                    || not is_rec
                  then
                    let struct_id = TAdtId adt_id in
                    let init = None in
                    let updates =
                      FieldId.mapi
                        (fun fid fe -> (fid, self#visit_texpression env fe))
                        args
                    in
                    let ne = { struct_id; init; updates } in
                    let nty = e.ty in
                    { e = StructUpdate ne; ty = nty }
                  else ignore ()
                else ignore ()
          | _ -> ignore ())
      | _ -> super#visit_texpression env e
  end

let intro_struct_updates = lift_expr_map_visitor intro_struct_updates_visitor

(** Simplify the let-bindings by performing the following rewritings:

    Move inner let-bindings outside. This is especially useful to simplify the
    backward expressions, when we merge the forward/backward functions. Note
    that the rule is also applied with monadic let-bindings.
    {[
      let x :=
        let y := ... in
        e

        ~~>

      let y := ... in
      let x := e
    ]}

    Simplify panics and returns:
    {[
      let x ← fail
      ...
        ~~>
      fail

      let x ← return y
      ...
        ~~>
      let x := y
      ...
    ]}

    Simplify tuples:
    {[
      let (y0, y1) := (x0, x1) in
      ...
        ~~>
      let y0 = x0 in
      let y1 = x1 in
      ...
    ]}

    Simplify arrows:
    {[
      let f := fun x => g x in
      ...
        ~~>
      let f := g in
      ...
    ]} *)
let simplify_let_bindings_visitor (ctx : ctx) (def : fun_decl) =
  object (self)
    inherit [_] map_expression as super

    method! visit_Let env monadic lv rv next =
      match rv.e with
      | Let (rmonadic, rlv, rrv, rnext) ->
          (* Case 1: move the inner let outside then re-visit *)
          let rnext1 = Let (monadic, lv, rnext, next) in
          let rnext1 = { ty = next.ty; e = rnext1 } in
          self#visit_Let env rmonadic rlv rrv rnext1
      | App
          ( {
              e =
                Qualif
                  {
                    id =
                      AdtCons
                        {
                          adt_id = TBuiltin TResult;
                          variant_id = Some variant_id;
                        };
                    generics = _;
                  };
              ty = _;
            },
            x ) ->
          (* return/fail case *)
          if variant_id = result_ok_id then
            (* Return case - note that the simplification we just perform
                 might have unlocked the tuple simplification below *)
            self#visit_Let env false lv x next
          else if variant_id = result_fail_id then
            (* Fail case *)
            self#visit_expression env rv.e
          else [%craise] def.item_meta.span "Unexpected"
      | App _ ->
          (* This might be the tuple case *)
          if not monadic then
            match
              (opt_dest_struct_pattern lv, opt_dest_tuple_texpression rv)
            with
            | Some pats, Some vals ->
                (* Tuple case *)
                let pat_vals = List.combine pats vals in
                let e =
                  List.fold_right
                    (fun (pat, v) next -> mk_opened_let false pat v next)
                    pat_vals next
                in
                super#visit_expression env e.e
            | _ -> super#visit_Let env monadic lv rv next
          else super#visit_Let env monadic lv rv next
      | Lambda _ ->
          if not monadic then
            (* Arrow case *)
            let pats, e = raw_destruct_lambdas rv in
            let g, args = destruct_apps e in
            if List.length pats = List.length args then
              (* Check if the arguments are exactly the lambdas *)
              let check_pat_arg ((pat, arg) : typed_pattern * texpression) =
                match (pat.value, arg.e) with
                | PatOpen (v, _), FVar vid -> v.id = vid
                | _ -> false
              in
              if List.for_all check_pat_arg (List.combine pats args) then
                (* Check if the application is a tuple constructor
                     or will be extracted as a projector: if
                     it is, keep the lambdas, otherwise simplify *)
                let simplify =
                  match g.e with
                  | Qualif { id = AdtCons { adt_id; _ }; _ } ->
                      not
                        (PureUtils.type_decl_from_type_id_is_tuple_struct
                           ctx.trans_ctx.type_ctx.type_infos adt_id)
                  | Qualif { id = Proj _; _ } -> false
                  | _ -> true
                in
                if simplify then self#visit_Let env monadic lv g next
                else super#visit_Let env monadic lv rv next
              else super#visit_Let env monadic lv rv next
            else super#visit_Let env monadic lv rv next
          else super#visit_Let env monadic lv rv next
      | _ -> super#visit_Let env monadic lv rv next
  end

let simplify_let_bindings = lift_expr_map_visitor simplify_let_bindings_visitor

(** Remove the duplicated function calls.

    We naturally write code which contains several times the same expression.
    For instance:
    {[
      a[i + j] = b[i + j] + 1;
        ^^^^^      ^^^^^
    ]}

    This is an issue in the generated model, because we then have to reason
    several times about the same function call. For instance, below, we have to
    prove *twice* that [i + j] is in bounds, and the proof context grows bigger
    than necessary.
    {[
      let i1 <- i + j (* *)
      let x1 <- array_index b i1
      let x2 <- x1 + 1
      let i2 <- i + j (* duplicates the expression above *)
      let a1 = array_update a i2 x2
    ]}

    This micro pass removes those duplicate function calls. *)
let simplify_duplicate_calls_visitor (_ctx : ctx) (def : fun_decl) =
  object (self)
    inherit [_] map_expression as super

    method! visit_Let env monadic pat bound next =
      let bound = self#visit_texpression env bound in
      (* Register the function call if the pattern doesn't contain dummy
           variables *)
      let env =
        if monadic then
          match typed_pattern_to_texpression def.item_meta.span pat with
          | None -> env
          | Some pat_expr -> TExprMap.add bound (monadic, pat_expr) env
        else env
      in
      let next = self#visit_texpression env next in
      Let (monadic, pat, bound, next)

    method! visit_texpression env e =
      let e =
        match TExprMap.find_opt e env with
        | None -> e
        | Some (monadic, e) ->
            if monadic then mk_result_ok_texpression def.item_meta.span e else e
      in
      super#visit_texpression env e
  end

let simplify_duplicate_calls =
  lift_expr_map_visitor_with_state simplify_duplicate_calls_visitor
    TExprMap.empty

(** A helper predicate *)
let lift_unop (unop : unop) : bool =
  match unop with
  | Not None -> false
  | Not (Some _) | Neg _ | Cast _ | ArrayToSlice -> true

(** A helper predicate *)
let inline_unop unop = not (lift_unop unop)

(** A helper predicate *)
let lift_binop (binop : binop) : bool =
  match binop with
  | Eq | Lt | Le | Ne | Ge | Gt -> false
  | BitXor
  | BitAnd
  | BitOr
  | Div _
  | Rem _
  | Add _
  | Sub _
  | Mul _
  | AddChecked
  | SubChecked
  | MulChecked
  | Shl _
  | Shr _
  | Offset
  | Cmp -> true

(** A helper predicate *)
let inline_binop binop = not (lift_binop binop)

(** A helper predicate *)
let lift_fun (ctx : ctx) (fun_id : fun_id) : bool =
  (* Lookup if the function is builtin: we only lift builtin functions
     which were explictly marked to be lifted. *)
  match fun_id with
  | FromLlbc (FunId (FRegular fid), _) -> begin
      match FunDeclId.Map.find_opt fid ctx.fun_decls with
      | None -> false
      | Some def -> (
          match def.builtin_info with
          | None -> false
          | Some info -> info.lift)
    end
  | FromLlbc (FunId (FBuiltin (ArrayToSliceShared | ArrayToSliceMut)), _) ->
      true
  | _ -> false

(** A helper predicate *)
let inline_fun (_ : fun_id) : bool = false

(** Inline the useless variable (re-)assignments:

    A lot of intermediate variable assignments are introduced through the
    compilation to MIR and by the translation itself (and the variable used on
    the left is often unnamed).

    Note that many of them are just variable "reassignments":
    [let x = y in ...]. Some others come from ??

    TODO: how do we call that when we introduce intermediate variable
    assignments for the arguments of a function call?

    [inline_named]: if [true], inline all the assignments of the form
    [let VAR = VAR in ...], otherwise inline only the ones where the variable on
    the left is anonymous.

    [inline_pure]: if [true], inline all the pure assignments where the variable
    on the left is anonymous, but the assignments where the r-expression is a
    function call (i.e.: ADT constructions, etc.), except certain cases of
    function calls.

    [inline_identity]: if [true], inline the identity functions (i.e., lambda
    functions of the shape [fun x -> x]).

    TODO: we have a smallish issue which is that rvalues should be merged with
    expressions... For now, this forces us to substitute whenever we can, but
    leave the let-bindings where they are, and eliminated them in a subsequent
    pass (if they are useless). *)
let inline_useless_var_assignments_visitor ~(inline_named : bool)
    ~(inline_const : bool) ~(inline_pure : bool) ~(inline_identity : bool)
    (ctx : ctx) (def : fun_decl) =
  object (self)
    inherit [_] map_expression as super

    (** Visit the let-bindings to filter the useless ones (and update the
        substitution map while doing so *)
    method! visit_Let (env : texpression FVarId.Map.t) monadic lv re e =
      (* In order to filter, we need to check first that:
           - the let-binding is not monadic
           - the left-value is a variable

           We also inline if the binding decomposes a structure that is to be
           extracted as a tuple, and the right value is a variable.
        *)
      match (monadic, lv.value) with
      | false, PatOpen (lv_var, _) ->
          (* We can filter if: 1. *)
          let filter_pure =
            (* 1.1. the left variable is unnamed or [inline_named] is true *)
            let filter_left =
              match (inline_named, lv_var.basename) with
              | true, _ | _, None -> true
              | _ -> false
            in
            (* And either:
                 1.2.1 the right-expression is a variable, a global or a const generic var *)
            let var_or_global = is_fvar re || is_cvar re || is_global re in
            (* Or:
                 1.2.2 the right-expression is a constant-value and we inline constant values,
                     *or* it is a qualif with no arguments (we consider this as a const) *)
            let const_re =
              inline_const
              &&
              let is_const_adt =
                let app, args = destruct_apps re in
                if args = [] then
                  match app.e with
                  | Qualif _ -> true
                  | StructUpdate upd -> upd.updates = []
                  | _ -> false
                else false
              in
              is_const re || is_const_adt
            in
            (* Or:
                 1.2.3 the right-expression is an ADT value, a projection or a
                     primitive function call *and* the flag [inline_pure] is set *)
            let pure_re =
              inline_pure
              &&
              let app, _ = destruct_apps re in
              match app.e with
              | Qualif qualif -> (
                  match qualif.id with
                  | AdtCons _ -> true (* ADT constructor *)
                  | Proj _ -> true (* Projector *)
                  | FunOrOp (Unop unop) -> inline_unop unop
                  | FunOrOp (Binop (binop, _)) -> inline_binop binop
                  | FunOrOp (Fun fun_id) -> inline_fun fun_id
                  | _ -> false)
              | StructUpdate _ -> true (* ADT constructor *)
              | _ -> false
            in
            filter_left && (var_or_global || const_re || pure_re)
          in

          (* Or if: 2. the let-binding bounds the identity function *)
          let filter_id =
            inline_identity
            &&
            match re.e with
            | Lambda ({ value = PatOpen (v0, _); _ }, { e = FVar v1; _ }) ->
                v0.id = v1
            | _ -> false
          in

          let filter = filter_pure || filter_id in

          (* Update the rhs (we may perform substitutions inside, and it is
           * better to do them *before* we inline it *)
          let re = self#visit_texpression env re in
          (* Update the substitution environment *)
          let env = if filter then FVarId.Map.add lv_var.id re env else env in
          (* Update the next expression *)
          let e = self#visit_texpression env e in
          (* Reconstruct the [let], only if the binding is not filtered *)
          if filter then e.e else Let (monadic, lv, re, e)
      | ( false,
          PatAdt
            {
              variant_id = None;
              field_values = [ { value = PatOpen (lv_var, _); ty = _ } ];
            } ) ->
          (* Second case: we deconstruct a structure with one field that we will
               extract as tuple. *)
          let adt_id, _ = PureUtils.ty_as_adt def.item_meta.span re.ty in
          (* Update the rhs (we may perform substitutions inside, and it is
           * better to do them *before* we inline it *)
          let re = self#visit_texpression env re in
          if
            PureUtils.is_fvar re
            && type_decl_from_type_id_is_tuple_struct
                 ctx.trans_ctx.type_ctx.type_infos adt_id
          then
            (* Update the substitution environment *)
            let env = FVarId.Map.add lv_var.id re env in
            (* Update the next expression *)
            let e = self#visit_texpression env e in
            (* We filter the [let], and thus do not reconstruct it *)
            e.e
          else (* Nothing to do *)
            super#visit_Let env monadic lv re e
      | _ -> super#visit_Let env monadic lv re e

    (** Substitute the variables *)
    method! visit_FVar (env : texpression FVarId.Map.t) (vid : FVarId.id) =
      match FVarId.Map.find_opt vid env with
      | None -> (* No substitution *) super#visit_FVar env vid
      | Some ne ->
          (* Substitute - note that we need to reexplore, because
           * there may be stacked substitutions, if we have:
           * var0 --> var1
           * var1 --> var2.
           *)
          self#visit_expression env ne.e
  end

let inline_useless_var_assignments ~inline_named ~inline_const ~inline_pure
    ~inline_identity =
  lift_expr_map_visitor_with_state
    (inline_useless_var_assignments_visitor ~inline_named ~inline_const
       ~inline_pure ~inline_identity)
    FVarId.Map.empty

(** Filter the useless assignments (removes the useless variables, filters the
    function calls) *)
let filter_useless (_ctx : ctx) (def : fun_decl) : fun_decl =
  let span = def.item_meta.span in
  (* We first need a transformation on *left-values*, which filters the useless
     variables and tells us whether the value contains any variable which has
     not been replaced by [_] (in which case we need to keep the assignment,
     etc.).

     This is implemented as a map-reduce.

     Returns: ( filtered_left_value, *all_dummies* )

     [all_dummies]:
     If the returned boolean is true, it means that all the variables appearing
     in the filtered left-value are *dummies* (meaning that if this left-value
     appears at the left of a let-binding, this binding might potentially be
     removed).
  *)
  let lv_visitor =
    object
      inherit [_] mapreduce_typed_pattern
      method zero _ = true
      method plus b0 b1 _ = b0 () && b1 ()

      method! visit_PatOpen env v mp =
        if FVarId.Set.mem v.id env then (PatOpen (v, mp), fun _ -> false)
        else (PatDummy, fun _ -> true)

      method! visit_PatBound _ _ _ = [%internal_error] span
    end
  in
  let filter_typed_pattern (used_vars : FVarId.Set.t) (lv : typed_pattern) :
      typed_pattern * bool =
    let lv, all_dummies = lv_visitor#visit_typed_pattern used_vars lv in
    (lv, all_dummies ())
  in

  (* We then implement the transformation on *expressions* through a mapreduce.
     Note that the transformation is bottom-up.
     The map filters the useless assignments, the reduce computes the set of
     used variables.
  *)
  let expr_visitor =
    object (self)
      inherit [_] mapreduce_expression as super
      method zero _ = FVarId.Set.empty
      method plus s0 s1 _ = FVarId.Set.union (s0 ()) (s1 ())

      (** Whenever we visit a variable, we need to register the used variable *)
      method! visit_FVar _ vid = (FVar vid, fun _ -> FVarId.Set.singleton vid)

      method! visit_expression env e =
        match e with
        | BVar _ -> [%internal_error] span
        | FVar _ | CVar _ | Const _ | App _ | Qualif _
        | Meta (_, _)
        | StructUpdate _ | Lambda _
        | EError (_, _) -> super#visit_expression env e
        | Switch (scrut, switch) -> (
            match switch with
            | If (_, _) -> super#visit_expression env e
            | Match branches ->
                (* Simplify the branches *)
                let simplify_branch (br : match_branch) =
                  (* Compute the set of values used inside the branch *)
                  let branch, used = self#visit_texpression env br.branch in
                  (* Simplify the pattern *)
                  let pat, _ = filter_typed_pattern (used ()) br.pat in
                  { pat; branch }
                in
                super#visit_expression env
                  (Switch (scrut, Match (List.map simplify_branch branches))))
        | Let (monadic, lv, re, e) ->
            (* Compute the set of values used in the next expression *)
            let e, used = self#visit_texpression env e in
            let used = used () in
            (* Filter the left values *)
            let lv, all_dummies = filter_typed_pattern used lv in
            (* Small utility - called if we can't filter the let-binding *)
            let dont_filter () =
              let re, used_re = self#visit_texpression env re in
              let used = FVarId.Set.union used (used_re ()) in
              (* Simplify the left pattern if it only contains dummy variables *)
              let lv =
                if all_dummies then
                  let ty = lv.ty in
                  let value = PatDummy in
                  { value; ty }
                else lv
              in
              (Let (monadic, lv, re, e), fun _ -> used)
            in
            (* Potentially filter the let-binding *)
            if all_dummies then
              if not monadic then
                (* Not a monadic let-binding: simple case *)
                (e.e, fun _ -> used)
              else (* Monadic let-binding: can't filter *)
                dont_filter ()
            else (* There are used variables: don't filter *)
              dont_filter ()
        | Loop loop ->
            (* We take care to ignore the varset computed on the *loop body* *)
            let fun_end, s = self#visit_texpression () loop.fun_end in
            let loop_body, _ = self#visit_texpression () loop.loop_body in
            (Loop { loop with fun_end; loop_body }, s)
    end
    (* We filter only inside of transparent (i.e., non-opaque) definitions *)
  in
  map_open_fun_decl_body
    (fun body ->
      (* Visit the body *)
      let body_exp, used_vars = expr_visitor#visit_texpression () body.body in
      (* Visit the parameters - TODO: update: we can filter only if the definition
         is not recursive (otherwise it might mess up with the decrease clauses:
         the decrease clauses uses all the inputs given to the function, if some
         inputs are replaced by '_' we can't give it to the function used in the
         decreases clause).
         For now we deactivate the filtering. *)
      let used_vars = used_vars () in
      let inputs =
        if false then
          List.map
            (fun lv -> fst (filter_typed_pattern used_vars lv))
            body.inputs
        else body.inputs
      in
      (* Return *)
      { body = body_exp; inputs })
    def

(** Simplify the lets immediately followed by an ok.

    Ex.:
    {[
      x <-- f y;
      Ok x

        ~~>

      f y
    ]} *)
let simplify_let_then_ok_visitor _ctx (def : fun_decl) =
  (* Match a pattern and an expression: evaluates to [true] if the expression
     is actually exactly the pattern *)
  let rec match_pattern_and_expr (pat : typed_pattern) (e : texpression) : bool
      =
    match (pat.value, e.e) with
    | PatConstant plit, Const lit -> plit = lit
    | PatOpen (pv, _), FVar vid -> pv.id = vid
    | PatDummy, _ ->
        (* It is ok only if we ignore the unit value *)
        pat.ty = mk_unit_ty && e = mk_unit_rvalue
    | PatAdt padt, _ -> (
        let qualif, args = destruct_apps e in
        match qualif.e with
        | Qualif { id = AdtCons cons_id; generics = _ } ->
            if
              pat.ty = e.ty
              && padt.variant_id = cons_id.variant_id
              && List.length padt.field_values = List.length args
            then
              List.for_all
                (fun (p, e) -> match_pattern_and_expr p e)
                (List.combine padt.field_values args)
            else false
        | _ -> false)
    | _ -> false
  in

  object (self)
    inherit [_] map_expression

    method! visit_Let env monadic lv rv next_e =
      (* We do a bottom up traversal (simplifying in the children nodes
           can allow to simplify in the parent nodes) *)
      let rv = self#visit_texpression env rv in
      let next_e = self#visit_texpression env next_e in
      let not_simpl_e = Let (monadic, lv, rv, next_e) in
      match next_e.e with
      | Switch _ | Loop _ | Let _ ->
          (* Small shortcut to avoid doing the check on every let-binding *)
          not_simpl_e
      | _ -> (
          if
            (* Do the check *)
            monadic
          then
            (* The first let-binding is monadic *)
            match opt_destruct_ret next_e with
            | Some e ->
                if match_pattern_and_expr lv e then rv.e else not_simpl_e
            | None -> not_simpl_e
          else
            (* The first let-binding is not monadic *)
            match opt_destruct_ret next_e with
            | Some e ->
                if match_pattern_and_expr lv e then
                  (* We need to wrap the right-value in a ret *)
                  (mk_result_ok_texpression def.item_meta.span rv).e
                else not_simpl_e
            | None ->
                if match_pattern_and_expr lv next_e then rv.e else not_simpl_e)
  end

let simplify_let_then_ok = lift_expr_map_visitor simplify_let_then_ok_visitor

(** Simplify the aggregated ADTs. Ex.:
    {[
      type struct = { f0 : nat; f1 : nat; f2 : nat }

      Mkstruct x.f0 x.f1 x.f2 ~~> x
    ]} *)
let simplify_aggregates_visitor (ctx : ctx) (def : fun_decl) =
  object
    inherit [_] map_expression as super

    (* Look for a type constructor applied to arguments *)
    method! visit_texpression env e =
      (* First simplify the sub-expressions *)
      let e = super#visit_texpression env e in
      match e.e with
      | App _ -> (
          (* TODO: we should remove this case, which dates from before the
               introduction of [StructUpdate] *)
          let app, args = destruct_apps e in
          match app.e with
          | Qualif
              {
                id = AdtCons { adt_id = TAdtId adt_id; variant_id = None };
                generics;
              } ->
              (* This is a struct *)
              (* Retrieve the definiton, to find how many fields there are *)
              let adt_decl =
                TypeDeclId.Map.find adt_id ctx.trans_ctx.type_ctx.type_decls
              in
              let fields =
                match adt_decl.kind with
                | Enum _ | Alias _ | Opaque | TDeclError _ ->
                    [%craise] def.item_meta.span "Unreachable"
                | Union _ ->
                    [%craise] def.item_meta.span "Unions are not supported"
                | Struct fields -> fields
              in
              let num_fields = List.length fields in
              (* In order to simplify, there must be as many arguments as
               * there are fields *)
              [%sanity_check] def.item_meta.span (num_fields > 0);
              if num_fields = List.length args then
                (* We now need to check that all the arguments are of the form:
                 * [x.field] for some variable [x], and where the projection
                 * is for the proper ADT *)
                let to_var_proj (i : int) (arg : texpression) :
                    (generic_args * fvar_id) option =
                  match arg.e with
                  | App (proj, x) -> (
                      match (proj.e, x.e) with
                      | ( Qualif
                            {
                              id =
                                Proj { adt_id = TAdtId proj_adt_id; field_id };
                              generics = proj_generics;
                            },
                          FVar v ) ->
                          (* We check that this is the proper ADT, and the proper field *)
                          if proj_adt_id = adt_id && FieldId.to_int field_id = i
                          then Some (proj_generics, v)
                          else None
                      | _ -> None)
                  | _ -> None
                in
                let args = List.mapi to_var_proj args in
                let args = List.filter_map (fun x -> x) args in
                (* Check that all the arguments are of the expected form *)
                if List.length args = num_fields then
                  (* Check that this is the same variable we project from -
                   * note that we checked above that there is at least one field *)
                  let (_, x), end_args = Collections.List.pop args in
                  if List.for_all (fun (_, y) -> y = x) end_args then (
                    (* We can substitute *)
                    (* Sanity check: all types correct *)
                    [%sanity_check] def.item_meta.span
                      (List.for_all
                         (fun (generics1, _) -> generics1 = generics)
                         args);
                    { e with e = FVar x })
                  else e
                else e
              else e
          | _ -> e)
      | StructUpdate { struct_id; init = None; updates } ->
          let adt_ty = e.ty in
          (* Attempt to convert all the field updates to projections
               of fields from an ADT with the same type *)
          let to_expr_proj ((fid, arg) : FieldId.id * texpression) :
              texpression option =
            match arg.e with
            | App (proj, x) -> (
                match proj.e with
                | Qualif
                    {
                      id = Proj { adt_id = TAdtId proj_adt_id; field_id };
                      generics = _;
                    } ->
                    (* We check that this is the proper ADT, and the proper field *)
                    if
                      TAdtId proj_adt_id = struct_id
                      && field_id = fid && x.ty = adt_ty
                    then Some x
                    else None
                | _ -> None)
            | _ -> None
          in
          let expr_projs = List.map to_expr_proj updates in
          let filt_expr_projs = List.filter_map (fun x -> x) expr_projs in
          if filt_expr_projs = [] then e
          else
            (* If all the projections are from the same expression [x], we
                 simply replace the whole expression with [x] *)
            let x = List.hd filt_expr_projs in
            if
              List.length filt_expr_projs = List.length updates
              && List.for_all (fun y -> y = x) filt_expr_projs
            then x
            else if
              (* Attempt to create an "update" expression (i.e., of
                   the shape [{ x with f := v }]).

                   This is not supported by Coq.
                *)
              Config.backend () <> Coq
            then (
              (* Compute the number of occurrences of each init value *)
              let occurs = ref TExprMap.empty in
              List.iter
                (fun x ->
                  let num =
                    match TExprMap.find_opt x !occurs with
                    | None -> 1
                    | Some n -> n + 1
                  in
                  occurs := TExprMap.add x num !occurs)
                filt_expr_projs;
              (* Find the max - note that we can initialize the max at 0,
                   because there is at least one init value *)
              let max = ref 0 in
              let x = ref x in
              List.iter
                (fun (y, n) ->
                  if n > !max then (
                    max := n;
                    x := y))
                (TExprMap.bindings !occurs);
              (* Create the update expression *)
              let updates =
                List.filter_map
                  (fun ((fid, fe), y_opt) ->
                    if y_opt = Some !x then None else Some (fid, fe))
                  (List.combine updates expr_projs)
              in
              let supd = StructUpdate { struct_id; init = Some !x; updates } in
              let e = { e with e = supd } in
              e)
            else e
      | _ -> e
  end

let simplify_aggregates = lift_expr_map_visitor simplify_aggregates_visitor

(** Remark: it might be better to use egraphs *)
type simp_aggr_env = {
  (* Expansion map that we use in particular to simplify fields.

     For instance, if we see the expression [let (x, y) = p in ...]
     we store the mappings:
     {[
       p   -> (x, y)
       p.0 -> x
       p.1 -> y
     ]}
  *)
  expand_map : expression ExprMap.t;
  (* The list of values which were expanded through matches or let-bindings.

     For instance, if we see the expression [let (x, y) = p in ...] we push
     the expression [p].
  *)
  expanded : expression list;
}

(** Simplify the unchanged fields in the aggregated ADTs.

    Because of the way the symbolic execution works, we often see the following
    pattern:
    {[
      if x.field then { x with field = true } else { x with field = false }
    ]}
    This micro-pass simplifies it to:
    {[
      if x.field then x else x
    ]} *)
let simplify_aggregates_unchanged_fields_visitor (ctx : ctx) (def : fun_decl) =
  let log = Logging.simplify_aggregates_unchanged_fields_log in
  let span = def.item_meta.span in
  (* Some helpers *)
  let add_expand v e m = { m with expand_map = ExprMap.add v e m.expand_map } in
  let add_expands l m =
    { m with expand_map = ExprMap.add_list l m.expand_map }
  in
  let get_expand v m = ExprMap.find_opt v m.expand_map in
  let add_expanded e m = { m with expanded = e :: m.expanded } in
  let add_pattern_eqs (bound_adt : texpression) (pat : typed_pattern)
      (env : simp_aggr_env) : simp_aggr_env =
    (* Register the pattern - note that we may not be able to convert the
       pattern to an expression if, for instance, it contains [_] *)
    let env =
      match typed_pattern_to_texpression span pat with
      | Some pat_expr -> add_expand bound_adt.e pat_expr.e env
      | None -> env
    in
    (* Register the fact that the scrutinee got expanded *)
    let env = add_expanded bound_adt.e env in
    (* Check if we are decomposing an ADT to introduce variables for its fields *)
    match pat.value with
    | PatAdt adt ->
        (* Check if the fields are all variables, and compute the tuple:
           (variable introduced for the field, projection) *)
        let fields = FieldId.mapi (fun id x -> (id, x)) adt.field_values in
        let vars_to_projs =
          Collections.List.filter_map
            (fun ((fid, f) : _ * typed_pattern) ->
              match f.value with
              | PatOpen (var, _) ->
                  let proj = mk_adt_proj span bound_adt fid f.ty in
                  let var = { e = FVar var.id; ty = f.ty } in
                  Some (var.e, proj.e)
              | PatBound _ -> [%internal_error] span
              | _ -> None)
            fields
        in
        (* We register the various mappings *)
        let env =
          add_expands (List.map (fun (x, y) -> (y, x)) vars_to_projs) env
        in
        env
    | _ -> env
  in

  (* Recursively expand a value and its subvalues *)
  let expand_expression simp_env (v : expression) : expression =
    let visitor =
      object
        inherit [_] map_expression as super

        method! visit_expression env e =
          match get_expand e simp_env with
          | None -> super#visit_expression env e
          | Some e -> super#visit_expression env e
      end
    in
    visitor#visit_expression () v
  in

  (* The visitor *)
  object (self)
    inherit [_] map_expression as super

    method! visit_Switch env scrut switch =
      [%ltrace "Visiting switch: " ^ switch_to_string ctx scrut switch];
      (* Update the scrutinee *)
      let scrut = self#visit_texpression env scrut in
      let switch =
        match switch with
        | If (b0, b1) ->
            (* Register the expansions:
                 {[
                   scrut -> true    (for the then branch)
                   scrut -> false   (for the else branch)
                 ]}
              *)
            let update v st =
              self#visit_texpression
                (add_expand scrut.e (mk_bool_value v).e env)
                st
            in
            let b0 = update true b0 in
            let b1 = update false b1 in
            If (b0, b1)
        | Match branches ->
            let update_branch (b : match_branch) =
              (* Register the information introduced by the patterns *)
              let env = add_pattern_eqs scrut b.pat env in
              { b with branch = self#visit_texpression env b.branch }
            in
            let branches = List.map update_branch branches in
            Match branches
      in
      Switch (scrut, switch)

    (* We need to detect patterns of the shape: [let (x, y) = t in ...] *)
    method! visit_Let env monadic pat bound next =
      (* Register the pattern if it is not a monadic let binding *)
      let env = if monadic then env else add_pattern_eqs bound pat env in
      (* Continue *)
      super#visit_Let env monadic pat bound next

    (* Update the ADT values *)
    method! visit_texpression env e0 =
      let e =
        match e0.e with
        | StructUpdate updt ->
            [%ltrace
              "Visiting struct update: " ^ struct_update_to_string ctx updt];
            (* Update the fields *)
            let updt = super#visit_struct_update env updt in
            (* Simplify *)
            begin
              match updt.init with
              | None -> super#visit_StructUpdate env updt
              | Some init ->
                  let update_field ((fid, e) : field_id * texpression) :
                      (field_id * texpression) option =
                    (* Recursively expand the value of the field, to check if it is
                         equal to the updated value: if it is the case, we can omit
                         the update. *)
                    let adt = init in
                    let field_value = mk_adt_proj span adt fid e.ty in
                    let field_value = expand_expression env field_value.e in
                    (* If this value is equal to the value we update the field
                         with, we can simply ignore the update *)
                    if field_value = expand_expression env e.e then (
                      [%ltrace
                        "Simplifying field: " ^ texpression_to_string ctx e];
                      None)
                    else (
                      [%ltrace
                        "Not simplifying field: " ^ texpression_to_string ctx e];
                      Some (fid, e))
                  in
                  let updates = List.filter_map update_field updt.updates in
                  if updates = [] then (
                    [%ltrace
                      "StructUpdate: "
                      ^ texpression_to_string ctx e0
                      ^ " ~~> "
                      ^ texpression_to_string ctx init];
                    init.e)
                  else
                    let updt1 = { updt with updates } in
                    [%ltrace
                      "StructUpdate: "
                      ^ struct_update_to_string ctx updt
                      ^ " ~~> "
                      ^ struct_update_to_string ctx updt1];
                    super#visit_StructUpdate env updt1
            end
        | App _ ->
            [%ltrace "Visiting app: " ^ texpression_to_string ctx e0];
            (* It may be an ADT expression (e.g., [Cons x y] or [(x, y)]):
                 check if it is the case, and if it is, compute the expansion
                 of all the values expanded so far, and see if exactly one of
                 those is equal to the current expression *)
            let e1 = super#visit_texpression env e0 in
            let e1_exp = expand_expression env e1.e in
            let f, _ = destruct_apps e1 in
            if is_adt_cons f then
              let expanded =
                List.filter_map
                  (fun e ->
                    let e' = expand_expression env e in
                    if e1_exp = e' then Some e else None)
                  env.expanded
              in
              begin
                match expanded with
                | [ e2 ] ->
                    [%ltrace
                      "Simplified: "
                      ^ texpression_to_string ctx e1
                      ^ " ~~> "
                      ^ texpression_to_string ctx { e1 with e = e2 }];
                    e2
                | _ -> e1.e
              end
            else e1.e
        | _ -> super#visit_expression env e0.e
      in
      { e0 with e }
  end

let simplify_aggregates_unchanged_fields =
  lift_expr_map_visitor_with_state simplify_aggregates_unchanged_fields_visitor
    { expand_map = ExprMap.empty; expanded = [] }

(** Retrieve the loop definitions from the function definition.

    {!SymbolicToPure} generates an AST in which the loop bodies are part of the
    function body (see the {!Pure.Loop} node). This function extracts those
    function bodies into independent definitions while removing occurrences of
    the {!Pure.Loop} node. *)
let decompose_loops_aux (ctx : ctx) (def : fun_decl) (body : fun_body) :
    fun_decl * fun_decl list =
  let span = def.item_meta.span in

  (* Reset the fvart counter and open all the binders - it is easier to manipulate unique variable indices *)
  reset_fvar_id_counter ();
  let body = open_all_fun_body span body in

  (* Count the number of loops *)
  let loops = ref LoopId.Set.empty in
  let expr_visitor =
    object
      inherit [_] iter_expression as super

      method! visit_Loop env loop =
        loops := LoopId.Set.add loop.loop_id !loops;
        super#visit_Loop env loop
    end
  in
  expr_visitor#visit_texpression () body.body;
  let num_loops = LoopId.Set.cardinal !loops in

  (* Store the loops here *)
  let loops = ref LoopId.Map.empty in
  let expr_visitor =
    object (self)
      inherit [_] map_expression

      method! visit_Loop env loop =
        let span = loop.span in
        let fun_sig = def.signature in
        let fwd_info = fun_sig.fwd_info in
        let fwd_effect_info = fwd_info.effect_info in
        let ignore_output = fwd_info.ignore_output in

        (* Generate the loop definition *)
        let loop_fwd_effect_info = fwd_effect_info in

        let loop_fwd_sig_info : fun_sig_info =
          { effect_info = loop_fwd_effect_info; ignore_output }
        in

        let inputs_tys =
          let fwd_inputs =
            List.map (fun (v : typed_pattern) -> v.ty) loop.inputs
          in
          fwd_inputs
        in

        let output = loop.output_ty in

        let loop_sig =
          {
            generics = fun_sig.generics;
            explicit_info = fun_sig.explicit_info;
            known_from_trait_refs = fun_sig.known_from_trait_refs;
            llbc_generics = fun_sig.llbc_generics;
            preds = fun_sig.preds;
            inputs = inputs_tys;
            output;
            fwd_info = loop_fwd_sig_info;
            back_effect_info = fun_sig.back_effect_info;
          }
        in

        let inputs : fvar list =
          List.map (fun x -> fst (as_pat_open span x)) loop.inputs
        in

        let inputs =
          List.map (fun x -> mk_typed_pattern_from_fvar x None) inputs
        in
        let loop_body =
          close_all_fun_body loop.span { inputs; body = loop.loop_body }
        in
        (* We retrieve the meta information from the parent function
         *but* replace its span with the span of the loop *)
        let item_meta = { def.item_meta with span = loop.span } in

        [%sanity_check] def.item_meta.span (def.builtin_info = None);

        let loop_def : fun_decl =
          {
            def_id = def.def_id;
            item_meta;
            builtin_info = def.builtin_info;
            kind = def.kind;
            backend_attributes = def.backend_attributes;
            num_loops;
            loop_id = Some loop.loop_id;
            name = def.name;
            signature = loop_sig;
            is_global_decl_body = def.is_global_decl_body;
            body = Some loop_body;
          }
        in
        (* Store the loop definition *)
        loops := LoopId.Map.add_strict loop.loop_id loop_def !loops;

        (* Update the current expression to remove the [Loop] node, and continue *)
        (self#visit_texpression env loop.fun_end).e
    end
  in

  let body_expr = expr_visitor#visit_texpression () body.body in
  [%ldebug
    "Resulting body:\n" ^ fun_body_to_string ctx { body with body = body_expr }];
  let body = close_all_fun_body span { body with body = body_expr } in
  let def = { def with body = Some body; num_loops } in
  let loops = List.map snd (LoopId.Map.bindings !loops) in
  (def, loops)

let decompose_loops (ctx : ctx) (def : fun_decl) =
  match def.body with
  | None -> (def, [])
  | Some body -> decompose_loops_aux ctx def body

(** Convert the unit variables to [()] if they are used as right-values or [_]
    if they are used as left values in patterns. *)
let unit_vars_to_unit _ (def : fun_decl) : fun_decl =
  let span = def.item_meta.span in

  (* The map visitor *)
  let obj =
    object
      inherit [_] map_expression as super

      (** Replace in patterns *)
      method! visit_PatOpen _ v mp =
        if v.ty = mk_unit_ty then PatDummy else PatOpen (v, mp)

      method! visit_PatBound _ _ _ = [%internal_error] span

      (** Replace in "regular" expressions - note that we could limit ourselves
          to variables, but this is more powerful *)
      method! visit_texpression env e =
        if e.ty = mk_unit_ty then mk_unit_rvalue
        else super#visit_texpression env e
    end
  in
  (* Update the body *)
  map_open_fun_decl_body
    (fun body ->
      let body_exp = obj#visit_texpression () body.body in
      (* Update the input parameters *)
      let inputs = List.map (obj#visit_typed_pattern ()) body.inputs in
      (* Return *)
      { body = body_exp; inputs })
    def

(** Eliminate the box functions like [Box::new] (which is translated to the
    identity) and [Box::free] (which is translated to [()]).

    Note that the box types have already been eliminated during the translation
    from symbolic to pure. The reason why we don't eliminate the box functions
    at the same time is that we would need to eliminate them in two different
    places: when translating function calls, and when translating end
    abstractions. Here, we can do something simpler, in one micro-pass. *)
let eliminate_box_functions_visitor (_ctx : ctx) (def : fun_decl) =
  (* The map visitor *)
  object
    inherit [_] map_expression as super

    method! visit_texpression env e =
      match opt_destruct_function_call e with
      | Some (fun_id, _tys, args) -> (
          (* Below, when dealing with the arguments: we consider the very
           * general case, where functions could be boxed (meaning we
           * could have: [box_new f x])
           *)
          match fun_id with
          | Fun (FromLlbc (FunId (FBuiltin aid), _lp_id)) -> (
              match aid with
              | BoxNew ->
                  let arg, args = Collections.List.pop args in
                  mk_apps def.item_meta.span arg args
              | Index _
              | ArrayToSliceShared
              | ArrayToSliceMut
              | ArrayRepeat
              | PtrFromParts _ -> super#visit_texpression env e)
          | _ -> super#visit_texpression env e)
      | _ -> super#visit_texpression env e
  end

let eliminate_box_functions =
  lift_expr_map_visitor eliminate_box_functions_visitor

(** Simplify the lambdas by applying beta-reduction *)
let apply_beta_reduction_visitor (_ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in

  object (self)
    inherit [_] map_expression as super

    method! visit_FVar env vid =
      match FVarId.Map.find_opt vid env with
      | None -> FVar vid
      | Some e -> e.e

    method! visit_texpression env e =
      let f, args = destruct_apps e in
      let args = List.map (self#visit_texpression env) args in
      let pats, body = raw_destruct_lambdas f in
      if args <> [] && pats <> [] then
        (* Apply the beta-reduction

             First split the arguments/patterns between those that
             will disappear and those we have to preserve.
          *)
        let min = Int.min (List.length args) (List.length pats) in
        let pats, kept_pats = Collections.List.split_at pats min in
        let args, kept_args = Collections.List.split_at args min in
        (* Substitute *)
        let vars = List.map (fun v -> (fst (as_pat_open span v)).id) pats in
        let body =
          let env = FVarId.Map.add_list (List.combine vars args) env in
          super#visit_texpression env body
        in
        (* Reconstruct the term *)
        mk_apps span
          (mk_opened_lambdas span kept_pats (super#visit_texpression env body))
          kept_args
      else
        mk_apps span
          (mk_opened_lambdas span pats (super#visit_texpression env body))
          args
  end

let apply_beta_reduction =
  lift_expr_map_visitor_with_state apply_beta_reduction_visitor FVarId.Map.empty

(** This pass simplifies uses of array/slice index operations.

    We perform the following transformations:
    {[
      let (_, back) = Array.index_mut_usize a i in
      let a' = back x in
      ...

       ~~>

      let a' = Array.update a i x in
      ...
    ]}

    {[
      let _, back = Array.index_mut_usize a i in
      back x ~~>Array.update a i x
    ]} *)
let simplify_array_slice_update_visitor (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in

  (* The difficulty is that the let-binding which uses the backward function
     may not appear immediately after the let-binding which introduces it.

     The micro-pass is written in a general way: for instance we do not leverage
     the fact that a backward function should be used only once.
  *)
  object (self)
    inherit [_] map_expression as super

    method! visit_Let env monadic pat e1 e2 =
      (* Update the first expression *)
      let e1 = super#visit_texpression env e1 in
      (* Check if the current let-binding is a call to an index function *)
      let e1_app, e1_args = destruct_apps e1 in
      match (pat.value, e1_app.e, e1_args) with
      | ( (* let (_, back) = ... *)
          PatAdt
            {
              variant_id = None;
              field_values =
                [
                  { value = PatDummy; _ }; { value = PatOpen (back_var, _); _ };
                ];
            },
          (* ... = Array.index_mut_usize a i *)
          Qualif
            {
              id =
                FunOrOp
                  (Fun
                     (FromLlbc
                        ( FunId
                            (FBuiltin
                               (Index
                                  {
                                    is_array;
                                    mutability = RMut;
                                    is_range = false;
                                  })),
                          None )));
              generics = index_generics;
            },
          [ a; i ] ) ->
          [%ldebug
            "identified a pattern to simplify:\n"
            ^ texpression_to_string ctx
                { e = Let (monadic, pat, e1, e2); ty = e2.ty }];

          (* Some auxiliary functions *)
          (* Helper to check if an expression is actually the backward function *)
          let is_call_to_back (app : texpression) =
            match app.e with
            | FVar id -> id = back_var.id
            | _ -> false
          in
          (* Helper to introduce a call to the proper update function *)
          let mk_call_to_update (back_v : texpression) =
            let array_or_slice = if is_array then Array else Slice in
            let qualif =
              Qualif
                {
                  id = FunOrOp (Fun (Pure (UpdateAtIndex array_or_slice)));
                  generics = index_generics;
                }
            in
            let qualif =
              { e = qualif; ty = mk_arrows [ a.ty; i.ty; back_v.ty ] e2.ty }
            in
            mk_apps span qualif [ a; i; back_v ]
          in
          (* Attempt to remove the let-binding.

               We perform two attempts:
               1. we check if we can actually insert the update in place of the index
                 function as it leads to a more natural translation. We do so if:
                 - there is a single call to the backward function
                 - the inputs to this call only use variables which have been introduced
                   *before*
               2. otherwise, we check that we manage to replace all the uses to the
                 backward function before comitting the changes . *)
          let count = ref 0 in
          let back_call = ref None in
          let back_call_with_fresh = ref None in
          let fresh_vars = ref FVarId.Set.empty in
          let register_back_call pat arg =
            count := !count + 1;
            back_call_with_fresh := Some (pat, arg);
            (* Check that the argument doesn't use fresh vars *)
            if
              FVarId.Set.is_empty
                (FVarId.Set.inter (texpression_get_fvars arg) !fresh_vars)
            then back_call := Some (pat, arg)
          in
          let updt_visitor1 =
            object
              inherit [_] map_expression as super
              method! visit_PatBound _ _ _ = [%internal_error] span

              method! visit_PatOpen env var mp =
                fresh_vars := FVarId.Set.add var.id !fresh_vars;
                super#visit_PatOpen env var mp

              method! visit_Let env monadic' pat' e' e3 =
                (* Check if this is a call to the backward function *)
                match e'.e with
                | App (app, v) when is_result_ty e3.ty && is_call_to_back app ->
                    register_back_call pat' v;
                    (self#visit_texpression env e3).e
                | _ -> super#visit_Let env monadic' pat' e' e3

              method! visit_App env app x =
                (* Look for: [ok (back x)] *)
                match app.e with
                | Qualif
                    {
                      id =
                        AdtCons
                          {
                            adt_id = TBuiltin TResult;
                            variant_id = Some variant_id;
                          };
                      _;
                    }
                  when variant_id = result_ok_id -> begin
                    match x.e with
                    | App (app', v) when is_call_to_back app' ->
                        let id = fresh_fvar_id () in
                        let var : fvar = { id; basename = None; ty = x.ty } in
                        register_back_call
                          (mk_typed_pattern_from_fvar var None)
                          v;
                        super#visit_App env app (mk_texpression_from_fvar var)
                    | _ -> super#visit_App env app x
                  end
                | _ -> super#visit_App env app x
            end
          in
          let e' = updt_visitor1#visit_texpression () e2 in
          [%ldebug "e':\n" ^ texpression_to_string ctx e'];

          (* Should we keep the change? *)
          if !count = 1 && Option.is_some !back_call then (
            [%ldebug "keeping the change"];
            let pat, arg = Option.get !back_call in
            let call = mk_call_to_update arg in
            (* Recurse on the updated expression *)
            super#visit_expression env (Let (true, pat, call, e')))
          else
            (* Sometimes the call to the backward function needs to
                 use fresh variables which are introduced *after* the
                 call to the backward function, but the call itself happens
                 quite late (because we end region abstractions in a lazy manner),
                 while we could introduce it earlier.
                 If it is the case, we insert the call to the backward function
                 as close as possible to the position of the call to the forward
                 function, that is: as soon as all the variables needed for its
                 arguments have been introduced.
              *)
            let _ = [%ldebug "not keeping the change"] in
            let e'' =
              if !count = 1 then (
                let back_pat, back_arg = Option.get !back_call_with_fresh in
                let fresh_vars =
                  FVarId.Set.inter !fresh_vars (texpression_get_fvars back_arg)
                in
                let rec insert_call_below (fresh_vars : FVarId.Set.t) e =
                  [%ldebug
                    "insert_call_below:" ^ "\n- fresh_vars:\n"
                    ^ FVarId.Set.to_string None fresh_vars
                    ^ "\n- e:\n"
                    ^ texpression_to_string ctx e];
                  match e.e with
                  | Let (monadic, pat, e1, e2) ->
                      let fresh_vars =
                        FVarId.Set.diff fresh_vars (typed_pattern_get_fvars pat)
                      in
                      if FVarId.Set.is_empty fresh_vars then
                        let call = mk_call_to_update back_arg in
                        let e' = Let (true, back_pat, call, e2) in
                        let e' = { e = e'; ty = e.ty } in
                        (true, { e = Let (monadic, pat, e1, e'); ty = e.ty })
                      else
                        let ok, e2 = insert_call_below fresh_vars e2 in
                        (ok, { e = Let (monadic, pat, e1, e2); ty = e.ty })
                  | _ -> (false, e)
                in
                [%ldebug "insert_call_below: START"];
                let ok, e'' = insert_call_below fresh_vars e' in
                if ok then Some e''.e else None)
              else None
            in
            if Option.is_some e'' then Option.get e''
            else
              (* Attempt 1. didn't work: perform attempt 2. (see above) *)
              let ok = ref true in
              let updt_visitor2 =
                object
                  inherit [_] map_expression as super

                  method! visit_FVar env var_id =
                    (* If we find a use of the backward function which was not
                         replaced then we set the [ok] boolean to false, meaning
                         we should not remove the call to the index function. *)
                    if var_id = back_var.id then ok := false else ();
                    super#visit_FVar env var_id

                  method! visit_Let env monadic' pat' e' e3 =
                    (* Check if this is a call to the backward function*)
                    match e'.e with
                    | App (app, v)
                      when is_result_ty e3.ty && is_call_to_back app ->
                        super#visit_expression env
                          (Let (true, pat', mk_call_to_update v, e3))
                    | _ -> super#visit_Let env monadic' pat' e' e3

                  method! visit_App env app x =
                    (* Look for: [ok (back x)] *)
                    match app.e with
                    | Qualif
                        {
                          id =
                            AdtCons
                              {
                                adt_id = TBuiltin TResult;
                                variant_id = Some variant_id;
                              };
                          _;
                        }
                      when variant_id = result_ok_id -> begin
                        match x.e with
                        | App (app, back_v) when is_call_to_back app ->
                            (super#visit_texpression env
                               (mk_call_to_update back_v))
                              .e
                        | _ -> super#visit_App env app x
                      end
                    | _ -> super#visit_App env app x
                end
              in
              let e' = updt_visitor2#visit_texpression () e2 in

              (* Should we keep the change? *)
              if !ok then (self#visit_texpression env e').e
              else super#visit_Let env monadic pat e1 e2
      | _ -> super#visit_Let env monadic pat e1 e2
  end

let simplify_array_slice_update =
  lift_expr_map_visitor simplify_array_slice_update_visitor

(** Decompose let-bindings by introducing intermediate let-bindings.

    This is a utility function: see {!decompose_monadic_let_bindings} and
    {!decompose_nested_let_patterns}.

    [decompose_monadic]: always decompose a monadic let-binding
    [decompose_nested_pats]: decompose the nested patterns *)
let decompose_let_bindings_visitor (decompose_monadic : bool)
    (decompose_nested_pats : bool) (_ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in

  (* Set up the var id generator *)
  let mk_fresh (ty : ty) : typed_pattern * texpression =
    let vid = fresh_fvar_id () in
    let tmp : fvar = { id = vid; basename = None; ty } in
    let ltmp = mk_typed_pattern_from_fvar tmp None in
    let rtmp = mk_texpression_from_fvar tmp in
    (ltmp, rtmp)
  in

  (* Utility function - returns the patterns to introduce, from the last to
     the first.

     For instance, if it returns:
     {[
       ([
         ((x3, x4), x1);
         ((x1, x2), tmp)
       ],
         (x0, tmp))
     ]}
     then we need to introduce:
     {[
       let (x0, tmp) = original_term in
       let (x1, x2) = tmp in
       let (x3, x4) = x1 in
       ...
     }]
  *)
  let decompose_pat (lv : typed_pattern) :
      (typed_pattern * texpression) list * typed_pattern =
    let patterns = ref [] in

    (* We decompose patterns *inside* other patterns.
       The boolean [inside] allows us to remember if we dived into a
       pattern already *)
    let visit_pats =
      object
        inherit [_] map_typed_pattern as super

        method! visit_typed_pattern (inside : bool) (pat : typed_pattern) :
            typed_pattern =
          match pat.value with
          | PatConstant _ | PatOpen _ | PatDummy -> pat
          | PatBound _ -> [%internal_error] span
          | PatAdt _ ->
              if not inside then super#visit_typed_pattern true pat
              else
                let ltmp, rtmp = mk_fresh pat.ty in
                let pat = super#visit_typed_pattern false pat in
                patterns := (pat, rtmp) :: !patterns;
                ltmp
      end
    in

    let inside = false in
    let lv = visit_pats#visit_typed_pattern inside lv in
    (!patterns, lv)
  in

  (* It is a very simple map *)
  object (self)
    inherit [_] map_expression as super

    method! visit_Let env monadic lv re next_e =
      (* Decompose the monadic let-bindings *)
      let monadic, lv, re, next_e =
        if (not monadic) || not decompose_monadic then (monadic, lv, re, next_e)
        else
          (* If monadic, we need to check if the left-value is a variable:
           * - if yes, don't decompose
           * - if not, make the decomposition in two steps
           *)
          match lv.value with
          | PatOpen _ | PatDummy ->
              (* Variable: nothing to do *)
              (monadic, lv, re, next_e)
          | PatBound _ -> [%internal_error] span
          | _ ->
              (* Not a variable: decompose if required *)
              (* Introduce a temporary variable to receive the value of the
               * monadic binding *)
              let ltmp, rtmp = mk_fresh lv.ty in
              (* Visit the next expression *)
              let next_e = self#visit_texpression env next_e in
              (* Create the let-bindings *)
              (monadic, ltmp, re, mk_opened_let false lv rtmp next_e)
      in
      (* Decompose the nested let-patterns *)
      let lv, next_e =
        if not decompose_nested_pats then (lv, next_e)
        else
          let pats, first_pat = decompose_pat lv in
          let e =
            List.fold_left
              (fun next_e (lpat, rv) -> mk_opened_let false lpat rv next_e)
              next_e pats
          in
          (first_pat, e)
      in
      (* Continue *)
      super#visit_Let env monadic lv re next_e
  end

let decompose_let_bindings (decompose_monadic : bool)
    (decompose_nested_pats : bool) =
  lift_expr_map_visitor
    (decompose_let_bindings_visitor decompose_monadic decompose_nested_pats)

(** Decompose monadic let-bindings.

    See the explanations in {!val:Config.decompose_monadic_let_bindings} *)
let decompose_monadic_let_bindings (ctx : ctx) (def : fun_decl) : fun_decl =
  decompose_let_bindings true false ctx def

(** Decompose the nested let patterns.

    See the explanations in {!val:Config.decompose_nested_let_patterns} *)
let decompose_nested_let_patterns (ctx : ctx) (def : fun_decl) : fun_decl =
  decompose_let_bindings false true ctx def

(** Unfold the monadic let-bindings to explicit matches. *)
let unfold_monadic_let_bindings_visitors (_ctx : ctx) (def : fun_decl) =
  (* It is a very simple map *)
  object (_self)
    inherit [_] map_expression as super

    method! visit_Let env monadic lv re e =
      (* We simply do the following transformation:
         {[
           pat <-- re; e

             ~~>

             match re with
             | Fail err -> Fail err
             | Return pat -> e
         ]}
      *)
      (* TODO: we should use a monad "kind" instead of a boolean *)
      if not monadic then super#visit_Let env monadic lv re e
      else
        (* We don't do the same thing if we use a state-error monad or simply
           an error monad.
           Note that some functions always live in the error monad (arithmetic
           operations, for instance).
        *)
        (* TODO: this information should be computed in SymbolicToPure and
         * store in an enum ("monadic" should be an enum, not a bool). *)
        let re_ty = Option.get (opt_destruct_result def.item_meta.span re.ty) in
        [%sanity_check] def.item_meta.span (lv.ty = re_ty);
        let err_vid = fresh_fvar_id () in
        let err_var : fvar =
          {
            id = err_vid;
            basename = Some ConstStrings.error_basename;
            ty = mk_error_ty;
          }
        in
        let err_pat = mk_typed_pattern_from_fvar err_var None in
        let fail_pat = mk_result_fail_pattern err_pat.value lv.ty in
        let err_v = mk_texpression_from_fvar err_var in
        let fail_value =
          mk_result_fail_texpression def.item_meta.span err_v e.ty
        in
        let fail_branch = { pat = fail_pat; branch = fail_value } in
        let success_pat = mk_result_ok_pattern lv in
        let success_branch = { pat = success_pat; branch = e } in
        let switch_body = Match [ fail_branch; success_branch ] in
        let e = Switch (re, switch_body) in
        (* Continue *)
        super#visit_expression env e
  end

let unfold_monadic_let_bindings =
  lift_expr_map_visitor unfold_monadic_let_bindings_visitors

(** Perform the following transformation:

    {[
      let y <-- ok e

            ~~>

      let y <-- toResult e
    ]}

    We only do this on a specific set of pure functions calls - those functions
    are identified in the "builtin" information about external function calls.
*)
let lift_pure_function_calls_visitor (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in

  let try_lift_expr (super_visit_e : texpression -> texpression)
      (visit_e : texpression -> texpression) (app : texpression) :
      bool * texpression =
    (* Check if the function should be lifted *)
    let f, args = destruct_apps app in
    let f = super_visit_e f in
    let args = List.map visit_e args in
    (* *)
    let lift =
      match f.e with
      | Qualif { id = FunOrOp (Unop unop); _ } -> lift_unop unop
      | Qualif { id = FunOrOp (Binop (binop, _)); _ } -> lift_binop binop
      | Qualif { id = FunOrOp (Fun fun_id); _ } -> lift_fun ctx fun_id
      | _ -> false
    in
    let app = mk_apps span f args in
    if lift then (true, mk_to_result_texpression span app) else (false, app)
  in

  (* The map visitor *)
  object (self)
    inherit [_] map_expression as super

    method! visit_texpression env e0 =
      (* Check if this is an expression of the shape: [ok (f ...)] where
           `f` has been identified as a function which should be lifted. *)
      match destruct_apps e0 with
      | ( ({ e = Qualif { id = FunOrOp (Fun (Pure ToResult)); _ }; _ } as
           to_result_expr),
          [ app ] ) ->
          (* Attempt to lift the expression *)
          let lifted, app =
            try_lift_expr
              (super#visit_texpression env)
              (self#visit_texpression env)
              app
          in

          if lifted then app else mk_app span to_result_expr app
      | { e = Let (monadic, pat, bound, next); ty }, [] ->
          let next = self#visit_texpression env next in
          (* Attempt to lift only if the let-expression is not already monadic *)
          let lifted, bound =
            if monadic then (true, self#visit_texpression env bound)
            else
              try_lift_expr
                (super#visit_texpression env)
                (self#visit_texpression env)
                bound
          in
          { e = Let (lifted, pat, bound, next); ty }
      | f, args ->
          let f = super#visit_texpression env f in
          let args = List.map (self#visit_texpression env) args in
          mk_apps span f args
  end

let lift_pure_function_calls =
  lift_expr_map_visitor_with_state lift_pure_function_calls_visitor
    FVarId.Map.empty

(** Perform the following transformation:

    {[
      let y <-- f x   (* Must be an application, is not necessarily monadic *)
      let (a, b) := y (* Tuple decomposition *)
      ...
    ]}

    becomes:

    {[
      let (a, b) <-- f x
      ...
    ]} *)
let merge_let_app_then_decompose_tuple_visitor (_ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in
  object (self)
    inherit [_] map_expression

    method! visit_Let env monadic0 pat0 bound0 next0 =
      let bound0 = self#visit_texpression env bound0 in
      (* Check if we need to merge two let-bindings *)
      if is_pat_open pat0 then
        let var0, _ = as_pat_open span pat0 in
        match next0.e with
        | Let (false, pat1, { e = FVar var_id; _ }, next1) when var_id = var0.id
          -> begin
            (* Check if we are decomposing a tuple *)
            if is_pat_tuple pat1 then
              (* Introduce fresh variables for all the dummy variables
                   to make sure we can turn the pattern into an expression *)
              let pat1 =
                typed_pattern_replace_dummy_vars_with_free_vars fresh_fvar_id
                  pat1
              in
              let pat1_expr =
                Option.get (typed_pattern_to_texpression span pat1)
              in
              (* Register the mapping from the variable we remove to the expression *)
              let env = FVarId.Map.add var0.id pat1_expr env in
              (* Continue *)
              let next1 = self#visit_texpression env next1 in
              Let (monadic0, pat1, bound0, next1)
            else
              let next0 = self#visit_texpression env next0 in
              Let (monadic0, pat0, bound0, next0)
          end
        | _ ->
            let next0 = self#visit_texpression env next0 in
            Let (monadic0, pat0, bound0, next0)
      else
        let next0 = self#visit_texpression env next0 in
        Let (monadic0, pat0, bound0, next0)

    (* Replace the variables *)
    method! visit_FVar env var_id =
      match FVarId.Map.find_opt var_id env with
      | None -> FVar var_id
      | Some e -> e.e
  end

let merge_let_app_then_decompose_tuple =
  lift_expr_map_visitor_with_state merge_let_app_then_decompose_tuple_visitor
    FVarId.Map.empty

let end_passes : (bool ref option * string * (ctx -> fun_decl -> fun_decl)) list
    =
  [
    (* Convert the unit variables to [()] if they are used as right-values or
     * [_] if they are used as left values. *)
    (None, "unit_vars_to_unit", unit_vars_to_unit);
    (* Introduce [massert] - we do this early because it makes the AST nicer to
       read by removing indentation. *)
    (Some Config.intro_massert, "intro_massert", intro_massert);
    (* Simplify the let-bindings which bind the fields of ADTs
       which only have one variant (i.e., enumerations with one variant
       and structures). *)
    (None, "simplify_decompose_struct", simplify_decompose_struct);
    (* Introduce the special structure create/update expressions *)
    (None, "intro_struct_updates", intro_struct_updates);
    (* Simplify the let-bindings *)
    (None, "simplify_let_bindings", simplify_let_bindings);
    (* Inline the useless variable reassignments *)
    ( None,
      "inline_useless_var_assignments",
      inline_useless_var_assignments ~inline_named:true ~inline_const:true
        ~inline_pure:true ~inline_identity:true );
    (* Simplify the lambdas by applying beta-reduction *)
    (None, "apply_beta_reduction", apply_beta_reduction);
    (* Eliminate the box functions - note that the "box" types were eliminated
       during the symbolic to pure phase: see the comments for [eliminate_box_functions] *)
    (None, "eliminate_box_functions", eliminate_box_functions);
    (* Remove the duplicated function calls *)
    (None, "simplify_duplicate_calls", simplify_duplicate_calls);
    (* Merge let bindings which bind an expression then decompose a tuple *)
    ( Some Config.merge_let_app_decompose_tuple,
      "merge_let_app_then_decompose_tuple",
      merge_let_app_then_decompose_tuple );
    (* Filter the useless variables, assignments, function calls, etc. *)
    (None, "filter_useless", filter_useless);
    (* Simplify the lets immediately followed by a return.

       Ex.:
       {[
         x <-- f y;
         Return x

           ~~>

         f y
       ]}
    *)
    (None, "simplify_let_then_ok", simplify_let_then_ok);
    (* Simplify the aggregated ADTs.

       Ex.:
       {[
         (* type struct = { f0 : nat; f1 : nat; f2 : nat } *)

         Mkstruct x.f0 x.f1 x.f2                 ~~> x
         { f0 := x.f0; f1 := x.f1; f2 := x.f2 }  ~~> x
         { f0 := x.f0; f1 := x.f1; f2 := v }     ~~> { x with f2 = v }
       ]}
    *)
    (None, "simplify_aggregates", simplify_aggregates);
    (* Simplify the aggregated ADTs further. *)
    ( None,
      "simplify_aggregates_unchanged_fields",
      simplify_aggregates_unchanged_fields );
    (* Simplify the let-bindings - some simplifications may have been unlocked by
       the pass above (for instance, the lambda simplification) *)
    (None, "simplify_let_bindings", simplify_let_bindings);
    (* Inline the useless vars again *)
    ( None,
      "inline_useless_var_assignments (pass 2)",
      inline_useless_var_assignments ~inline_named:true ~inline_const:true
        ~inline_pure:false ~inline_identity:true );
    (* Filter the useless variables again *)
    (None, "filter_useless (pass 2)", filter_useless);
    (* Simplify the let-then return again (the lambda simplification may have
       unlocked more simplifications here) *)
    (None, "simplify_let_then_ok (pass 2)", simplify_let_then_ok);
    (* Simplify the array/slice manipulations by introducing calls to [array_update]
       [slice_update] *)
    (None, "simplify_array_slice_update", simplify_array_slice_update);
    (* Simplify the let-then return again (the array simplification may have
       unlocked more simplifications here) *)
    (None, "simplify_let_then_ok (pass 3)", simplify_let_then_ok);
    (* Decompose the monadic let-bindings - used by Coq *)
    ( Some Config.decompose_monadic_let_bindings,
      "decompose_monadic_let_bindings",
      decompose_monadic_let_bindings );
    (* Decompose nested let-patterns *)
    ( Some Config.decompose_nested_let_patterns,
      "decompose_nested_let_patterns",
      decompose_nested_let_patterns );
    (* Unfold the monadic let-bindings *)
    ( Some Config.unfold_monadic_let_bindings,
      "unfold_monadic_let_bindings",
      unfold_monadic_let_bindings );
    (* Introduce calls to [toResult] to lift pure function calls to monadic
       function calls *)
    ( Some Config.lift_pure_function_calls,
      "lift_pure_function_calls",
      lift_pure_function_calls );
  ]

(** Auxiliary function for {!apply_passes_to_def} *)
let apply_end_passes_to_def (ctx : ctx) (def : fun_decl) : fun_decl =
  List.fold_left
    (fun def (option, pass_name, pass) ->
      let apply =
        match option with
        | None -> true
        | Some option -> !option
      in

      if apply then (
        [%ltrace "About to apply: '" ^ pass_name ^ "'"];
        let def = pass ctx def in
        [%ltrace
          "After applying '" ^ pass_name ^ "'" ^ ":\n\n"
          ^ fun_decl_to_string ctx def];
        def)
      else (
        [%ltrace "Ignoring " ^ pass_name ^ " due to the configuration\n"];
        def))
    def end_passes

(** Small utility for {!filter_loop_inputs} *)
let filter_prefix (keep : bool list) (ls : 'a list) : 'a list =
  let ls0, ls1 = Collections.List.split_at ls (List.length keep) in
  let ls0 =
    List.filter_map
      (fun (b, x) -> if b then Some x else None)
      (List.combine keep ls0)
  in
  List.append ls0 ls1

type fun_loop_id = A.fun_id * LoopId.id option [@@deriving show, ord]

module FunLoopIdOrderedType = struct
  type t = fun_loop_id

  let compare = compare_fun_loop_id
  let to_string = show_fun_loop_id
  let pp_t = pp_fun_loop_id
  let show_t = show_fun_loop_id
end

module FunLoopIdMap = Collections.MakeMap (FunLoopIdOrderedType)

(** Helper for [filter_loop_inputs].

    Explore one loop body and compute the used information. *)
let filter_loop_inputs_explore_one_visitor (ctx : ctx)
    (used_map : bool list FunLoopIdMap.t ref) (decl : fun_decl) =
  let span = decl.item_meta.span in
  (* There should be a body *)
  let body = Option.get decl.body in
  (* Open the binders *)
  reset_fvar_id_counter ();
  let body = open_all_fun_body span body in
  [%ldebug "After opening binders:\n" ^ fun_body_to_string ctx body];
  let used =
    ref (List.map (fun v -> ((fst (as_pat_open span v)).id, false)) body.inputs)
  in
  let inputs =
    List.map
      (fun v ->
        let v, _ = as_pat_open span v in
        (v.id, mk_texpression_from_fvar v))
      body.inputs
  in
  [%ltrace
    "inputs:\n"
    ^ String.concat ", " (List.map (typed_pattern_to_string ctx) body.inputs)];
  let inputs_set =
    FVarId.Set.of_list
      (List.map
         (fun x ->
           let x, _ = as_pat_open span x in
           x.id)
         body.inputs)
  in
  [%sanity_check] decl.item_meta.span (Option.is_some decl.loop_id);

  let fun_id = (T.FRegular decl.def_id, decl.loop_id) in

  let set_used (vid : fvar_id) =
    used := List.map (fun (vid', b) -> (vid', b || vid = vid')) !used
  in

  (* Set the fuel as used *)
  let sg_info = decl.signature.fwd_info in
  let visitor =
    object (self : 'self)
      inherit [_] iter_expression as super

      (** Override the expression visitor, to look for loop function calls *)
      method! visit_texpression env e =
        match e.e with
        | App _ -> (
            (* If this is an app: destruct all the arguments, and check if
                 the leftmost expression is the loop function call *)
            let e_app, args = destruct_apps e in
            match e_app.e with
            | Qualif qualif -> (
                match qualif.id with
                | FunOrOp (Fun (FromLlbc (FunId fun_id', loop_id'))) ->
                    if (fun_id', loop_id') = fun_id then (
                      (* For each argument, check if it is exactly the original
                         input parameter. Note that there shouldn't be partial
                         applications of loop functions: the number of arguments
                         should be exactly the number of input parameters (i.e.,
                         we can use [combine])
                      *)
                      [%ltrace
                        "args:\n"
                        ^ String.concat ", "
                            (List.map (texpression_to_string ctx) args)];
                      let used_args = List.combine inputs args in
                      List.iter
                        (fun ((vid, var), arg) ->
                          if var <> arg then (
                            self#visit_texpression env arg;
                            set_used vid))
                        used_args)
                    else super#visit_texpression env e
                | _ -> super#visit_texpression env e)
            | _ -> super#visit_texpression env e)
        | _ -> super#visit_texpression env e

      (** If we visit a variable which is actually an input parameter, we set it
          as used. Note that we take care of ignoring some of those input
          parameters given in [visit_texpression]. *)
      method! visit_fvar_id _ id =
        if FVarId.Set.mem id inputs_set then set_used id
    end
  in

  (* Apply the visitor to the body *)
  visitor#visit_texpression () body.body;

  [%ltrace
    "- used variables: "
    ^ String.concat ", "
        (List.map (Print.pair_to_string FVarId.to_string string_of_bool) !used)];

  (* Save the filtering information, if there is anything to filter *)
  if List.exists (fun (_, b) -> not b) !used then
    let used = List.map snd !used in
    let used =
      match FunLoopIdMap.find_opt fun_id !used_map with
      | None -> used
      | Some used0 ->
          List.map (fun (b0, b1) -> b0 || b1) (List.combine used0 used)
    in
    used_map := FunLoopIdMap.add fun_id used !used_map

(** Helper for [filter_loop_inputs].

    Filter the inputs in one loop declaration. *)
let filter_loop_inputs_filter_in_one (_ctx : ctx)
    (used_map : bool list FunLoopIdMap.t) (decl : fun_decl) : fun_decl =
  (* Filter the function signature *)
  let fun_id = (T.FRegular decl.def_id, decl.loop_id) in
  let decl =
    match FunLoopIdMap.find_opt fun_id used_map with
    | None -> (* Nothing to filter *) decl
    | Some used_info ->
        let {
          generics;
          explicit_info = _;
          known_from_trait_refs = _;
          llbc_generics;
          preds;
          inputs;
          output;
          fwd_info;
          back_effect_info;
        } =
          decl.signature
        in
        let inputs = filter_prefix used_info inputs in
        let explicit_info = compute_explicit_info generics inputs in
        let known_from_trait_refs = compute_known_info explicit_info generics in
        let signature =
          {
            generics;
            explicit_info;
            known_from_trait_refs;
            llbc_generics;
            preds;
            inputs;
            output;
            fwd_info;
            back_effect_info;
          }
        in

        { decl with signature }
  in

  (* Filter the function body *)
  let filter_in_body (body : fun_body) : fun_body =
    (* Update the list of vars *)
    let { inputs; body } = body in

    let inputs =
      match FunLoopIdMap.find_opt fun_id used_map with
      | None -> (* Nothing to filter *) inputs
      | Some used_info ->
          let inputs = filter_prefix used_info inputs in
          inputs
    in

    (* Update the body expression *)
    let visitor =
      object (self)
        inherit [_] map_expression as super

        method! visit_texpression env e =
          match e.e with
          | App _ -> (
              let e_app, args = destruct_apps e in
              match e_app.e with
              | Qualif qualif -> (
                  match qualif.id with
                  | FunOrOp (Fun (FromLlbc (FunId fun_id, loop_id))) -> (
                      match
                        FunLoopIdMap.find_opt (fun_id, loop_id) used_map
                      with
                      | None -> super#visit_texpression env e
                      | Some used_info ->
                          (* Filter the types in the arrow type *)
                          let tys, ret_ty = destruct_arrows e_app.ty in
                          let tys = filter_prefix used_info tys in
                          let ty = mk_arrows tys ret_ty in
                          let e_app = { e_app with ty } in

                          (* Filter the arguments *)
                          let args = filter_prefix used_info args in

                          (* Explore the arguments *)
                          let args =
                            List.map (self#visit_texpression env) args
                          in

                          (* Rebuild *)
                          mk_apps decl.item_meta.span e_app args)
                  | _ ->
                      let e_app = self#visit_texpression env e_app in
                      let args = List.map (self#visit_texpression env) args in
                      mk_apps decl.item_meta.span e_app args)
              | _ ->
                  let e_app = self#visit_texpression env e_app in
                  let args = List.map (self#visit_texpression env) args in
                  mk_apps decl.item_meta.span e_app args)
          | _ -> super#visit_texpression env e
      end
    in
    let body = visitor#visit_texpression () body in
    { inputs; body }
  in
  map_open_fun_decl_body filter_in_body decl

(** Filter the useless loop input parameters. *)
let filter_loop_inputs (ctx : ctx) (transl : pure_fun_translation list) :
    pure_fun_translation list =
  (* We need to explore groups of mutually recursive functions. In order
     to compute which parameters are useless, we need to explore the
     functions by groups of mutually recursive definitions.

     Because every Rust function is translated to a list of functions (forward
     function, backward functions, loop functions, etc.), and those functions
     might depend on each others in different ways, we recompute the SCCs of
     the whole module.

     Rem.: we also redo this computation, on a smaller scale, in {!Translate}.
     Maybe we can factor out the two.
  *)
  let all_decls =
    List.concat
      (List.concat (List.map (fun { f; loops } -> [ f :: loops ]) transl))
  in
  let subgroups = ReorderDecls.group_reorder_fun_decls all_decls in

  [%ltrace
    "all_decls:\n\n"
    ^ String.concat "\n\n" (List.map (fun_decl_to_string ctx) all_decls)];

  (* Explore the subgroups one by one.

     For now, we only filter the parameters of loop functions which are simply
     recursive.

     Rem.: there is a bit of redundancy in computing the useless parameters
     for the loop forward *and* the loop backward functions.
  *)
  (* The [filtered] map: maps function identifiers to filtering information. *)
  let used_map : bool list FunLoopIdMap.t ref = ref FunLoopIdMap.empty in

  (* We start by computing the filtering information, for each function *)
  List.iter
    (fun (_, fl) ->
      match fl with
      | [ f ] ->
          (* Group made of one function: check if it is a loop. If it is the
             case, explore it. *)
          [%ltrace "singleton:\n\n" ^ fun_decl_to_string ctx f];

          if Option.is_some f.loop_id then
            filter_loop_inputs_explore_one_visitor ctx used_map f
          else ()
      | _ ->
          (* Group of mutually recursive functions: ignore for now *)
          ())
    subgroups;

  (* We then apply the filtering to all the function definitions at once *)
  let filter_in_one = filter_loop_inputs_filter_in_one ctx !used_map in
  let transl =
    List.map
      (fun f ->
        { f = filter_in_one f.f; loops = List.map filter_in_one f.loops })
      transl
  in

  (* Return *)
  transl

(** Update the [reducible] attribute.

    For now we mark a function as reducible when its body is only a call to a
    loop function. This situation often happens for simple functions whose body
    contains a loop: we introduce an intermediate function for the loop body,
    and the translation of the function itself simply calls the loop body. By
    marking the function as reducible, we allow tactics like [simp] or
    [progress] to see through the definition. *)
let compute_reducible (_ctx : ctx) (transl : pure_fun_translation list) :
    pure_fun_translation list =
  let update_one (trans : pure_fun_translation) : pure_fun_translation =
    match trans.f.body with
    | None -> trans
    | Some body -> (
        let app, _ = destruct_apps body.body in
        match app.e with
        | Qualif
            {
              id = FunOrOp (Fun (FromLlbc (FunId fid, Some _lp_id)));
              generics = _;
            }
          when fid = FRegular trans.f.def_id ->
            let f =
              { trans.f with backend_attributes = { reducible = true } }
            in
            { trans with f }
        | _ -> trans)
  in
  List.map update_one transl

(** Apply all the micro-passes to a function.

    As loops are initially directly integrated into the function definition,
    {!apply_passes_to_def extracts those loops definitions from the body; it
    thus returns the pair: (function def, loop defs). See {!decompose_loops}
    for more information.

    [ctx]: used only for printing. *)
let apply_passes_to_def (ctx : ctx) (def : fun_decl) : fun_and_loops =
  (* Debug *)
  [%ltrace def.name];
  [%ltrace "Original decl:\n\n" ^ fun_decl_to_string ctx def];

  (* First, find names for the variables which are unnamed *)
  [%ltrace "About to apply 'compute_pretty_names'"];
  let def = compute_pretty_names ctx def in
  [%ltrace "After 'compute_pretty_name':\n\n" ^ fun_decl_to_string ctx def];

  (* TODO: we might want to leverage more the assignment meta-data, for
   * aggregates for instance. *)

  (* TODO: reorder the branches of the matches/switches *)

  (* The meta-information is now useless: remove it.
   * Rk.: some passes below use the fact that we removed the meta-data
   * (otherwise we would have to "unmeta" expressions before matching) *)
  let def = remove_meta def in
  [%ltrace "Remove_meta:\n\n" ^ fun_decl_to_string ctx def];

  (* Extract the loop definitions by removing the {!Loop} node *)
  let def, loops = decompose_loops ctx def in
  [%ltrace
    let funs = def :: loops in
    "After decomposing loops:\n\n"
    ^ String.concat "\n\n" (List.map (fun_decl_to_string ctx) funs)];

  (* Apply the remaining passes *)
  let f = apply_end_passes_to_def ctx def in
  let loops = List.map (apply_end_passes_to_def ctx) loops in
  { f; loops }

(** Introduce type annotations.

    See [add_type_annotations].

    Note that we use the context only for printing. *)
let add_type_annotations_to_fun_decl (trans_ctx : trans_ctx)
    (trans_funs : pure_fun_translation FunDeclId.Map.t)
    (builtin_sigs : fun_sig Builtin.BuiltinFunIdMap.t)
    (type_decls : type_decl TypeDeclId.Map.t) (def : fun_decl) : fun_decl =
  let span = def.item_meta.span in
  let fmt = trans_ctx_to_pure_fmt_env trans_ctx in
  let texpression_to_string (x : texpression) : string =
    PrintPure.texpression_to_string fmt false "" "  " x
  in
  let ty_to_string (x : ty) : string = PrintPure.ty_to_string fmt false x in
  let generic_params_to_string (generics : generic_params) : string =
    "["
    ^ String.concat ", " (PrintPure.generic_params_to_strings fmt generics)
    ^ "]"
  in
  let generic_args_to_string (generics : generic_args) : string =
    "["
    ^ String.concat ", " (PrintPure.generic_args_to_strings fmt false generics)
    ^ "]"
  in
  let fun_sig_to_string (sg : fun_sig) : string =
    PrintPure.fun_sig_to_string fmt sg
  in

  (* The map visitor.

     For every sub-expression we track a "type with holes", where the holes
     are types which are not explicitly known (either because we can't directly
     know the type from the context, or because some type variables are implicit).

     If at some point the type is not known and the type of the expression is
     ambiguous, we introduce a type annotation.

     We encode types with holes in a simple manner: the unknown holes are type
     variables with id = -1.
  *)
  let hole : ty = TVar (T.Free (TypeVarId.of_int (-1))) in
  (* The const generic holes are not really useful, but while we're at it we
     can keep track of them *)
  let cg_hole : const_generic =
    T.CgVar (T.Free (ConstGenericVarId.of_int (-1)))
  in

  (* Small helper to add a type annotation *)
  let mk_type_annot (e : texpression) : texpression =
    { e = Meta (TypeAnnot, e); ty = e.ty }
  in

  let rec visit (ty : ty) (e : texpression) : texpression =
    match e.e with
    | FVar _ | CVar _ | Const _ | EError _ | Qualif _ -> e
    | BVar _ -> [%internal_error] span
    | App _ -> visit_App ty e
    | Lambda (pat, e') ->
        (* Decompose the type *)
        let ty' =
          match ty with
          | TArrow (_, ty) -> ty
          | _ -> hole
        in
        { e with e = Lambda (pat, visit ty' e') }
    | Let (monadic, pat, bound, next) ->
        (* The type of the bound expression is considered as unknown *)
        let bound = visit hole bound in
        let next = visit ty next in
        { e with e = Let (monadic, pat, bound, next) }
    | Switch (discr, body) ->
        (* We consider that the type of the discriminant is unknown *)
        let discr = visit hole discr in
        let body = visit_switch_body ty body in
        { e with e = Switch (discr, body) }
    | Loop _ ->
        (* Loops should have been eliminated *)
        [%internal_error] span
    | StructUpdate supd ->
        [%ldebug "exploring: " ^ texpression_to_string e];
        (* Some backends need a type annotation here if we create a new structure
           and if the type is unknown.
           TODO: actually we may change the type of the structure by changing
           one of its fields (it happens when we do an unsized cast in Rust).
           We ignore this case here. *)
        let ty =
          match supd.init with
          | None -> ty
          | Some _ ->
              (* We update a structure (we do not create a new one): we consider that the type is known *)
              e.ty
        in
        begin
          match ty with
          | TAdt (adt_id, generics) ->
              (* The type is known: let's compute the type of the fields and recurse *)
              let field_tys =
                (* There are two cases: the ADT may be an array (it happens when
                   initializing an array) *)
                match adt_id with
                | TBuiltin TArray ->
                    [%sanity_check] span (List.length generics.types = 1);
                    Collections.List.repeat (List.length supd.updates)
                      (List.nth generics.types 0)
                | _ ->
                    PureTypeCheck.get_adt_field_types span type_decls adt_id
                      None generics
              in
              (* Update the fields *)
              let updates =
                List.map
                  (fun ((fid, fe) : _ * texpression) ->
                    let field_ty = FieldId.nth field_tys fid in
                    (fid, visit field_ty fe))
                  supd.updates
              in
              { e with e = StructUpdate { supd with updates } }
          | _ ->
              (* The type of the structure is unknown: we add a type annotation.
                 From there, the type of the field updates is known *)
              let updates =
                List.map
                  (fun ((fid, fe) : _ * texpression) -> (fid, visit fe.ty fe))
                  supd.updates
              in
              let e = { e with e = StructUpdate { supd with updates } } in
              (* Add the type annotation, if the backend is Lean *)
              if Config.backend () = Lean then mk_type_annot e else e
        end
    | Meta (meta, e') ->
        let ty = if meta = TypeAnnot then e'.ty else ty in
        { e with e = Meta (meta, visit ty e') }
  and visit_App (ty : ty) (e : texpression) : texpression =
    [%ldebug
      "visit_App:\n- ty: " ^ ty_to_string ty ^ "\n- e: "
      ^ texpression_to_string e];
    (* Deconstruct the app *)
    let f, args = destruct_apps e in
    (* Compute the types of the arguments: it depends on the function *)
    let mk_holes () = List.map (fun _ -> hole) args in
    let mk_known () = List.map (fun (e : texpression) -> e.ty) args in
    let known_f_ty, known_args_tys =
      let rec compute_known_tys known_ty args =
        match args with
        | [] -> (known_ty, [])
        | _ :: args -> (
            match known_ty with
            | TArrow (ty0, ty1) ->
                let fty, args_tys = compute_known_tys ty1 args in
                (fty, ty0 :: args_tys)
            | _ ->
                let fty, args_tys = compute_known_tys hole args in
                (fty, hole :: args_tys))
      in
      compute_known_tys ty args
    in
    let compute_known_tys_from_fun_id (qualif : qualif) (fid : fun_id) :
        ty * ty list * bool =
      match fid with
      | Pure fid -> begin
          match fid with
          | Return | ToResult -> begin
              match known_args_tys with
              | [ ty ] ->
                  if ty = hole && Config.backend () = Lean then
                    (hole, mk_holes (), true)
                  else (known_f_ty, known_args_tys, false)
              | _ -> (known_f_ty, known_args_tys, false)
            end
          | Fail | Assert | FuelDecrease | FuelEqZero ->
              (f.ty, mk_known (), false)
          | UpdateAtIndex _ -> (known_f_ty, known_args_tys, false)
        end
      | FromLlbc (fid, lp_id) -> begin
          (* Lookup the signature *)
          let sg =
            match fid with
            | FunId (FRegular fid) ->
                let trans_fun =
                  [%silent_unwrap] span
                    (LlbcAst.FunDeclId.Map.find_opt fid trans_funs)
                in
                let trans_fun =
                  match lp_id with
                  | None -> trans_fun.f
                  | Some lp_id -> Pure.LoopId.nth trans_fun.loops lp_id
                in
                [%ldebug "function name: " ^ trans_fun.name];
                trans_fun.signature
            | TraitMethod (tref, method_name, method_decl_id) ->
                [%ldebug "method name: " ^ method_name];
                if Option.is_some lp_id then
                  [%craise] span
                    "Trying to get a loop subfunction from a method call";
                let method_sig =
                  [%silent_unwrap] span
                    (Charon.Substitute.lookup_flat_method_sig trans_ctx.crate
                       tref.trait_decl_ref.trait_decl_id method_name)
                in
                (* TODO: we shouldn't call `SymbolicToPure` here, there should
                   be a way to translate these signatures earlier. *)
                SymbolicToPureTypes.translate_fun_sig trans_ctx
                  (FRegular method_decl_id) method_name method_sig
                  (List.map (fun _ -> None) method_sig.inputs)
            | FunId (FBuiltin aid) ->
                Builtin.BuiltinFunIdMap.find aid builtin_sigs
          in
          [%ldebug "signature: " ^ fun_sig_to_string sg];
          (* In case this is a trait method, we need to concatenate the generics
             args of the trait ref with the generics args of the method call itself *)
          let generics =
            match fid with
            | TraitMethod (trait_ref, _, _) ->
                append_generic_args trait_ref.trait_decl_ref.decl_generics
                  qualif.generics
            | _ -> qualif.generics
          in
          let tr_self =
            match fid with
            | TraitMethod (trait_ref, _, _) -> trait_ref.trait_id
            (* Dummy, won't be used since we're not substituting for a trait. *)
            | _ -> UnknownTrait "add_type_annotations_to_fun_decl"
          in
          (* Replace all the unknown implicit type variables with holes.
             Note that we assume that all the trait refs are there, meaning
             we can use them to infer some implicit variables.
          *)
          let known = sg.known_from_trait_refs in
          let types =
            List.map
              (fun (known, ty) ->
                match known with
                | Known -> ty
                | Unknown -> hole)
              (List.combine known.known_types generics.types)
          in
          let const_generics =
            List.map
              (fun (known, cg) ->
                match known with
                | Known -> cg
                | Unknown -> cg_hole)
              (List.combine known.known_const_generics generics.const_generics)
          in
          let generics = { qualif.generics with types; const_generics } in
          (* Compute the types of the arguments *)
          [%ldebug
            "- sg.generics: "
            ^ generic_params_to_string sg.generics
            ^ "\n- generics: "
            ^ generic_args_to_string generics];
          let subst =
            make_subst_from_generics_for_trait sg.generics tr_self generics
          in
          let sg = fun_sig_substitute subst sg in
          (known_f_ty, sg.inputs, false)
        end
    in
    let f_ty, args_tys, need_annot =
      match f.e with
      | Qualif qualif -> begin
          match qualif.id with
          | FunOrOp fop -> begin
              match fop with
              | Fun fid -> begin compute_known_tys_from_fun_id qualif fid end
              | Unop unop -> begin
                  match unop with
                  | Not _ | Neg _ | Cast _ | ArrayToSlice ->
                      (known_f_ty, known_args_tys, false)
                end
              | Binop _ -> (known_f_ty, known_args_tys, false)
            end
          | Global _ -> (f.ty, mk_known (), false)
          | AdtCons adt_cons_id -> begin
              (* We extract the type of the arguments from the known type *)
              match ty with
              | TAdt (adt_id, generics)
              (* TODO: there are type-checking errors that we need to take into account (otherwise
                 [get_adt_field_types] sometimes crashes) *)
                when adt_id = adt_cons_id.adt_id ->
                  (* The type is known: let's compute the type of the fields and recurse *)
                  let field_tys =
                    PureTypeCheck.get_adt_field_types span type_decls adt_id
                      adt_cons_id.variant_id generics
                  in
                  (* We shouldn't need to know the type of the constructor - just leaving
                     a hole for now *)
                  (hole, field_tys, false)
              | _ ->
                  (* The type is unknown, but if the constructor is an enumeration
                     constructor, we can retrieve information from it *)
                  if Option.is_some adt_cons_id.variant_id then
                    let args_tys =
                      match e.ty with
                      | TAdt (adt_id, generics) ->
                          (* Replace the generic arguments with holes *)
                          let generics =
                            {
                              generics with
                              types = List.map (fun _ -> hole) generics.types;
                              const_generics =
                                List.map
                                  (fun _ -> cg_hole)
                                  generics.const_generics;
                            }
                          in
                          PureTypeCheck.get_adt_field_types span type_decls
                            adt_id adt_cons_id.variant_id generics
                      | _ -> mk_holes ()
                    in
                    (hole, args_tys, false)
                  else (hole, mk_holes (), false)
            end
          | Proj _ | TraitConst _ ->
              (* Being conservative here *)
              (hole, mk_holes (), false)
        end
      | FVar _ ->
          (* We consider that the full type of the function should be known,
             so the type of the arguments should be known *)
          (f.ty, mk_known (), false)
      | BVar _ -> [%internal_error] span
      | _ ->
          (* Being conservative: the type is unknown (we actually shouldn't
             get here) *)
          (hole, mk_holes (), false)
    in
    (* The application may be partial *)
    let args_tys = Collections.List.prefix (List.length args) args_tys in
    let args =
      List.map (fun (ty, arg) -> visit ty arg) (List.combine args_tys args)
    in
    let f = visit f_ty f in
    let e = mk_apps span f args in
    if need_annot then mk_type_annot e else e
  and visit_switch_body (ty : ty) (body : switch_body) : switch_body =
    match body with
    | If (e1, e2) -> If (visit ty e1, visit ty e2)
    | Match branches ->
        let branches =
          List.map
            (fun (b : match_branch) -> { b with branch = visit ty b.branch })
            branches
        in
        Match branches
  in

  (* Update the body *)
  map_open_fun_decl_body_expr
    (fun (body : texpression) -> visit body.ty body)
    def

(** Introduce type annotations.

    See [add_type_annotations]

    We need to do this in some backends in particular for the expressions which
    create structures, as the target structure may be ambiguous from the
    context.

    Note that we use the context only for printing. *)
let add_type_annotations (trans_ctx : trans_ctx)
    (trans_funs : pure_fun_translation list)
    (builtin_sigs : fun_sig Builtin.BuiltinFunIdMap.t)
    (type_decls : type_decl TypeDeclId.Map.t) : pure_fun_translation list =
  let trans_funs_map =
    FunDeclId.Map.of_list
      (List.map
         (fun (fl : pure_fun_translation) -> (fl.f.def_id, fl))
         trans_funs)
  in
  let add_annot =
    add_type_annotations_to_fun_decl trans_ctx trans_funs_map builtin_sigs
      type_decls
  in
  List.map
    (fun (fl : pure_fun_translation) ->
      let f = add_annot fl.f in
      let loops = List.map add_annot fl.loops in
      { f; loops })
    trans_funs

(** Apply the micro-passes to a list of forward/backward translations.

    This function also extracts the loop definitions from the function body (see
    {!decompose_loops}).

    It also returns a boolean indicating whether the forward function should be
    kept or not at extraction time ([true] means we need to keep the forward
    function).

    Note that we don't "filter" the forward function and return a boolean
    instead, because this function contains useful information to extract the
    backward functions. Note that here, keeping the forward function it is not
    *necessary* but convenient. *)
let apply_passes_to_pure_fun_translations (trans_ctx : trans_ctx)
    (builtin_sigs : fun_sig Builtin.BuiltinFunIdMap.t)
    (type_decls : type_decl list) (transl : fun_decl list) :
    pure_fun_translation list =
  let fun_decls =
    FunDeclId.Map.of_list
      (List.map (fun (f : fun_decl) -> (f.def_id, f)) transl)
  in
  let type_decls =
    TypeDeclId.Map.of_list
      (List.map (fun (d : type_decl) -> (d.def_id, d)) type_decls)
  in
  let ctx = { trans_ctx; fun_decls } in

  (* Apply the micro-passes *)
  let transl = List.map (apply_passes_to_def ctx) transl in

  (* Filter the useless inputs in the loop functions (loops are initially
     parameterized by *all* the symbolic values in the context, because
     they may access any of them). *)
  let transl = filter_loop_inputs ctx transl in

  (* Add the type annotations - we add those only now because we need
     to use the final types of the functions (in particular, we introduce
     loop functions and modify their types above) *)
  let transl = add_type_annotations trans_ctx transl builtin_sigs type_decls in

  (* Update the "reducible" attribute *)
  compute_reducible ctx transl
