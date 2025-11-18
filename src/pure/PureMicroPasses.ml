(** The following module defines micro-passes which operate on the pure AST *)

open Pure
open PureUtils
open TranslateCore

(** The local logger *)
let log = Logging.pure_micro_passes_log

type ctx = {
  fun_decls : fun_decl FunDeclId.Map.t;
  type_decls : type_decl TypeDeclId.Map.t;
  trans_ctx : trans_ctx;
  fresh_fvar_id : unit -> fvar_id;
}

let fun_decl_to_string (ctx : ctx) (def : fun_decl) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.fun_decl_to_string fmt def

let loop_body_to_string (ctx : ctx) (x : loop_body) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.loop_body_to_string fmt "" "  " x

let loop_to_string (ctx : ctx) (x : loop) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.loop_to_string fmt "" "  " x

let fun_id_to_string (ctx : ctx) (fid : fun_id) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.regular_fun_id_to_string fmt fid

let fun_sig_to_string (ctx : ctx) (sg : fun_sig) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.fun_sig_to_string fmt sg

let var_to_string (ctx : ctx) (v : var) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.var_to_string fmt v

let texpr_to_string (ctx : ctx) (x : texpr) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.texpr_to_string fmt false "" "  " x

let fvar_to_string (ctx : ctx) (x : fvar) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.fvar_to_string fmt x

let generic_params_to_string (ctx : ctx) (x : generic_params) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.generic_params_to_string fmt x

let ty_to_string (ctx : ctx) (x : ty) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.ty_to_string fmt false x

let let_to_string (ctx : ctx) monadic lv re next : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.let_to_string fmt "" "  " monadic lv re next

let fun_body_to_string (ctx : ctx) (x : fun_body) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.fun_body_to_string fmt x

let switch_to_string (ctx : ctx) scrut (x : switch_body) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.switch_to_string fmt "" "  " scrut x

let struct_update_to_string (ctx : ctx) supd : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.struct_update_to_string fmt "" "  " supd

let tpat_to_string (ctx : ctx) pat : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.tpat_to_string fmt pat

let lift_map_fun_decl_body (f : ctx -> fun_decl -> fun_body -> fun_body)
    (ctx : ctx) (def : fun_decl) : fun_decl =
  (* We open all the bound variables in the body before exploring it, then
     close them all after performing the updates - this makes it easier to
     deal with variables *)
  map_open_all_fun_decl_body ctx.fresh_fvar_id (f ctx def) def

(** Lift a visitor of expressions to a function which updates a function body *)
let lift_expr_map_visitor_with_state
    (obj : ctx -> fun_decl -> < visit_texpr : 'a -> texpr -> texpr ; .. >)
    (state : 'a) (ctx : ctx) (def : fun_decl) : fun_decl =
  (* We open all the bound variables in the body before exploring it, then
     close them all after performing the updates - this makes it easier to
     deal with variables *)
  map_open_all_fun_decl_body_expr ctx.fresh_fvar_id
    ((obj ctx def)#visit_texpr state)
    def

(** Lift a visitor of expressions to a function which updates a function body *)
let lift_expr_map_visitor
    (obj : ctx -> fun_decl -> < visit_texpr : unit -> texpr -> texpr ; .. >)
    (ctx : ctx) (def : fun_decl) : fun_decl =
  lift_expr_map_visitor_with_state obj () ctx def

let lift_iter_fun_decl_body (f : ctx -> fun_decl -> fun_body -> unit)
    (ctx : ctx) (def : fun_decl) : unit =
  (* We open all the bound variables in the body before exploring it, then
     close them all after performing the updates - this makes it easier to
     deal with variables *)
  iter_open_all_fun_decl_body ctx.fresh_fvar_id (f ctx def) def

(** Lift a visitor of expressions to a function which updates a function body *)
let lift_expr_iter_visitor_with_state
    (obj : ctx -> fun_decl -> < visit_texpr : 'a -> texpr -> unit ; .. >)
    (state : 'a) (ctx : ctx) (def : fun_decl) : unit =
  (* We open all the bound variables in the body before exploring it, then
     close them all after performing the updates - this makes it easier to
     deal with variables *)
  iter_open_all_fun_decl_body_expr ctx.fresh_fvar_id
    ((obj ctx def)#visit_texpr state)
    def

(** Lift a visitor of expressions to a function which updates a function body *)
let lift_expr_iter_visitor
    (obj : ctx -> fun_decl -> < visit_texpr : unit -> texpr -> unit ; .. >)
    (ctx : ctx) (def : fun_decl) : unit =
  lift_expr_iter_visitor_with_state obj () ctx def

let open_fun_body ctx = open_fun_body ctx.fresh_fvar_id
let open_all_fun_body ctx = open_all_fun_body ctx.fresh_fvar_id
let open_lambdas ctx = open_lambdas ctx.fresh_fvar_id
let open_binder ctx = open_binder ctx.fresh_fvar_id
let open_binders ctx = open_binders ctx.fresh_fvar_id
let open_lets ctx = open_lets ctx.fresh_fvar_id
let open_loop_body ctx = open_loop_body ctx.fresh_fvar_id
let mk_fresh_fvar ctx = mk_fresh_fvar ctx.fresh_fvar_id
let open_all_texpr ctx = open_all_texpr ctx.fresh_fvar_id

let opt_destruct_loop_result_decompose_outputs ctx =
  opt_destruct_loop_result_decompose_outputs ctx.fresh_fvar_id

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

let rec decompose_tpat span (x : tpat) : (fvar * int) option =
  match x.pat with
  | PBound _ -> [%internal_error] span
  | POpen (v, _) -> Some (v, 0)
  | PAdt { variant_id = None; fields = [ x ] } -> begin
      Option.map (fun (vid, depth) -> (vid, depth + 1)) (decompose_tpat span x)
    end
  | PConstant _ | PIgnored | PAdt _ -> None

let rec decompose_texpr span (x : texpr) : (fvar_id * int) option =
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
              (decompose_texpr span x)
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
  | Meta (_, x) -> decompose_texpr span x

type loop_info = {
  inputs : tpat list;  (** The inputs bound by the loop *)
  outputs : tpat list;
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
  let register_assign (lv : tpat) (rv : texpr) =
    match (decompose_tpat span lv, decompose_texpr span rv) with
    | Some (lhs, lhs_depth), Some (rhs_id, rhs_depth) ->
        if lhs_depth + rhs_depth = 0 then
          register_edge (Pure lhs.id) 0 (Pure rhs_id)
    | _ -> ()
  in
  let register_expr_eq (lv : texpr) (rv : texpr) =
    match (decompose_texpr span lv, decompose_texpr span rv) with
    | Some (lhs_id, lhs_depth), Some (rhs_id, rhs_depth) ->
        if lhs_depth + rhs_depth = 0 then
          register_edge (Pure lhs_id) 0 (Pure rhs_id)
    | _ -> ()
  in
  let register_texpr_has_name (e : texpr) (name : string) (depth : int) =
    match decompose_texpr span e with
    | Some (id, depth') -> register_node (Pure id) name (depth + depth')
    | _ -> ()
  in
  let register_texpr_at_place (e : texpr) (mp : mplace) =
    match (decompose_texpr span e, decompose_mplace_to_local mp) with
    | Some (fid, 0), Some (lid, _, []) -> register_edge (Pure fid) 0 (Llbc lid)
    | _ -> ()
  in

  let visitor =
    object
      inherit [_] iter_expr as super
      method! visit_fvar _ v = register_var v

      method! visit_Let env monadic lv re e =
        (* There might be meta information wrapped around the RHS *)
        Option.iter
          (fun mp ->
            match (decompose_tpat span lv, decompose_mplace_to_local mp) with
            | Some (lhs, 0), Some (lid, _, []) ->
                register_edge (Pure lhs.id) 0 (Llbc lid)
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

      method! visit_PBound _ _ _ = [%internal_error] span

      method! visit_POpen env lv mp =
        register_var_at_place lv mp;
        super#visit_POpen env lv mp

      method! visit_Meta env meta e =
        begin
          match meta with
          | Assignment (mp, rvalue, rmp) ->
              register_texpr_at_place rvalue mp;
              Option.iter (register_texpr_at_place rvalue) rmp
          | SymbolicAssignments infos ->
              List.iter (fun (var, rvalue) -> register_expr_eq var rvalue) infos
          | SymbolicPlaces infos ->
              List.iter
                (fun (var, name) -> register_texpr_has_name var name 1)
                infos
          | MPlace mp -> register_texpr_at_place e mp
          | Tag _ | TypeAnnot -> ()
        end;
        super#visit_Meta env meta e

      method! visit_loop env loop =
        let info : loop_info =
          { inputs = loop.loop_body.inputs; outputs = [] }
        in
        loop_infos := LoopId.Map.add loop.loop_id info !loop_infos;
        (* The body should be wrapped in "sym places" meta information: we want to use
           it with priority 0 (rather than 1 as is done by default in visit_Meta). *)
        (match loop.loop_body.loop_body.e with
        | Meta (SymbolicPlaces infos, _) ->
            List.iter
              (fun (var, name) -> register_texpr_has_name var name 0)
              infos
        | _ -> ());
        (* Also link the loop bound variables to the input arguments *)
        List.iter
          (fun (pat, arg) -> register_assign pat arg)
          (List.combine loop.loop_body.inputs loop.inputs);
        (* Recurse *)
        super#visit_loop env loop

      method! visit_mplace _ mp =
        match decompose_mplace_to_local mp with
        | Some (vid, name, _) -> register_local vid name
        | _ -> ()
    end
  in
  List.iter (visitor#visit_tpat ()) body.inputs;
  visitor#visit_texpr () body.body;

  (* Equate the loop outputs *)
  let rec equate (out0 : tpat) (out1 : tpat) : unit =
    match (out0.pat, out1.pat) with
    | POpen (v0, _), POpen (v1, _) -> register_edge (Pure v0.id) 0 (Pure v1.id)
    | PAdt adt0, PAdt adt1 ->
        if
          adt0.variant_id = adt1.variant_id
          && List.length adt0.fields = List.length adt1.fields
        then
          List.iter
            (fun (x, y) -> equate x y)
            (List.combine adt0.fields adt1.fields)
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
            go_inner outputs;
            go outputs
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
      inherit [_] map_expr
      method! visit_POpen _ v mp = POpen (update_var v, mp)
      method! visit_PBound _ _ _ = [%internal_error] span
    end
  in

  (* Apply *)
  let { inputs; body } = body in
  let inputs = List.map (visitor#visit_tpat ()) inputs in
  let body = visitor#visit_texpr () body in
  { inputs; body }

(** This function computes pretty names for the variables in the pure AST. It
    relies on the "meta"-place information in the AST to generate naming
    constraints, and then uses those to compute the names. *)
let compute_pretty_names (ctx : ctx) (def : fun_decl) : fun_decl =
  (* We open all the bound variables in the body before exploring it, then
     close them all after performing the updates - this makes it easier to
     deal with variables *)
  map_open_all_fun_decl_body ctx.fresh_fvar_id
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
let remove_meta (ctx : ctx) (def : fun_decl) : fun_decl =
  map_open_all_fun_decl_body_expr ctx.fresh_fvar_id PureUtils.remove_meta def

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
    inherit [_] map_expr as super

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
            let massert = [%add_loc] mk_app span massert scrut in
            (* Introduce the let-binding *)
            let monadic = true in
            let pat = mk_ignored_pat mk_unit_ty in
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
    inherit [_] map_expr as super

    method! visit_Let env (monadic : bool) (lv : tpat) (scrutinee : texpr)
        (next : texpr) =
      match (lv.pat, lv.ty) with
      | PAdt adt_pat, TAdt (TAdtId adt_id, generics) ->
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
            let gen_field_proj (field_id : FieldId.id) (dest : tpat) : texpr =
              let proj_kind = { adt_id = TAdtId adt_id; field_id } in
              let qualif = { id = Proj proj_kind; generics } in
              let proj_e = Qualif qualif in
              let proj_ty = mk_arrow scrutinee.ty dest.ty in
              let proj = { e = proj_e; ty = proj_ty } in
              [%add_loc] mk_app span proj scrutinee
            in
            let id_var_pairs =
              FieldId.mapi (fun fid v -> (fid, v)) adt_pat.fields
            in
            let monadic = false in
            let e =
              List.fold_right
                (fun (fid, pat) e ->
                  let field_proj = gen_field_proj fid pat in
                  mk_opened_let monadic pat field_proj e)
                id_var_pairs next
            in
            (super#visit_texpr env e).e
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
  let update_app visit_texpr (e : texpr) =
    [%ldebug "- e:\n" ^ texpr_to_string ctx e];
    let app, args = destruct_apps e in
    [%ldebug
      "- app: " ^ texpr_to_string ctx app ^ "\n- app.ty: "
      ^ ty_to_string ctx app.ty ^ "\n- args:\n"
      ^ String.concat "\n" (List.map (texpr_to_string ctx) args)];
    let ignore () =
      let app = visit_texpr app in
      let args = List.map visit_texpr args in
      [%ldebug
        "Ignoring and recomposing the application:\n" ^ "- app': "
        ^ texpr_to_string ctx app ^ "\n- app'.ty: " ^ ty_to_string ctx app.ty
        ^ "\n- args':\n"
        ^ String.concat "\n\n" (List.map (texpr_to_string ctx) args)];
      [%add_loc] mk_apps def.item_meta.span app args
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
                FieldId.mapi (fun fid fe -> (fid, visit_texpr fe)) args
              in
              let ne = { struct_id; init; updates } in
              let nty = e.ty in
              { e = StructUpdate ne; ty = nty }
            else ignore ()
          else ignore ()
    | _ -> ignore ()
  in

  object (self)
    inherit [_] map_expr as super

    method! visit_texpr env (e : texpr) =
      match e.e with
      | App _ -> update_app (self#visit_texpr env) e
      | _ -> super#visit_texpr env e
  end

let intro_struct_updates = lift_expr_map_visitor intro_struct_updates_visitor

(** This performs the following simplifications:
    {[
      fun x1 ... xn => g x1 ... xn
      ...
        ~~>
      g
      ...
    ]} *)
let simplify_lambdas_visitor (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in
  object (self)
    inherit [_] map_expr as super

    method! visit_texpr env e =
      match e.e with
      | Lambda _ ->
          (* Arrow case *)
          let pats, e = raw_destruct_lambdas e in
          let g, args = destruct_apps e in
          let default () =
            let e = self#visit_texpr env e in
            mk_opened_lambdas span pats e
          in
          if List.length pats = List.length args then
            (* Check if the arguments are exactly the lambdas *)
            let check_pat_arg ((pat, arg) : tpat * texpr) =
              match (pat.pat, arg.e) with
              | POpen (v, _), FVar vid -> v.id = vid
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
              if simplify then self#visit_texpr env g else default ()
            else default ()
          else default ()
      | _ -> super#visit_texpr env e
  end

let simplify_lambdas = lift_expr_map_visitor simplify_lambdas_visitor

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

    Simplify identity functions:
    {[
      let f := fun x => x
      ...
      f x
        ~~>
      let f := fun x => x
      ...
      x
    ]} *)
let simplify_let_bindings_visitor (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in
  object (self)
    inherit [_] map_expr as super

    method! visit_Let env monadic lv rv next =
      [%ldebug "Visiting let:\n" ^ let_to_string ctx monadic lv rv next];
      match rv.e with
      | Let (rmonadic, rlv, rrv, rnext) ->
          [%ldebug "Case: inner let"];
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
          [%ldebug "Case: result"];
          (* return/fail case *)
          if variant_id = result_ok_id then
            (* Return case - note that the simplification we just perform
                 might have unlocked the tuple simplification below *)
            self#visit_Let env false lv x next
          else if variant_id = result_fail_id then
            (* Fail case *)
            self#visit_expr env rv.e
          else [%craise] def.item_meta.span "Unexpected"
      | App _ ->
          [%ldebug "Case: app"];
          (* This might be the tuple case *)
          if not monadic then
            match (opt_dest_struct_pat lv, opt_dest_tuple_texpr rv) with
            | Some pats, Some vals ->
                (* Tuple case *)
                let pat_vals = List.combine pats vals in
                let e =
                  List.fold_right
                    (fun (pat, v) next -> mk_opened_let false pat v next)
                    pat_vals next
                in
                super#visit_expr env e.e
            | _ -> super#visit_Let env monadic lv rv next
          else super#visit_Let env monadic lv rv next
      | Lambda (pat, body) ->
          [%ldebug "Case: lambda"];
          (* Simplify:
             {[
               let f := fun x => x
               ...
               f x
                 ~~>
               let f := fun x => x
               ...
               x
             ]}
          *)
          begin
            match (pat.pat, body.e) with
            | POpen (fv, _), FVar fid when fv.id = fid ->
                [%ldebug "Simplifying the lambda"];
                let next =
                  let env = FVarId.Set.add fid env in
                  self#visit_texpr env next
                in
                (mk_opened_let monadic lv rv next).e
            | _ ->
                [%ldebug "Not simplifying the lambda"];
                super#visit_Let env monadic lv rv next
          end
      | _ -> super#visit_Let env monadic lv rv next

    method! visit_App env f arg =
      [%ldebug
        "Visiting app: " ^ texpr_to_string ctx ([%add_loc] mk_app span f arg)];
      (* Check if this is the identity case *)
      match f.e with
      | FVar fid when FVarId.Set.mem fid env -> arg.e
      | _ -> super#visit_App env f arg
  end

let simplify_let_bindings =
  lift_expr_map_visitor_with_state simplify_let_bindings_visitor
    FVarId.Set.empty

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

    This micro pass removes those duplicate function calls.

    TODO: this micro-pass will not be sound anymore once we allow stateful
    (backward) functions. *)
let simplify_duplicate_calls_visitor (_ctx : ctx) (def : fun_decl) =
  object (self)
    inherit [_] map_expr as super

    method! visit_Let env monadic pat bound next =
      let bound = self#visit_texpr env bound in
      (* Register the function call if the pattern doesn't contain ignored
         variables *)
      let env =
        let factor =
          monadic
          ||
          match destruct_apps bound with
          | { e = FVar _; _ }, _ :: _ ->
              (* May be a backward function call *)
              true
          | _ -> false
        in
        if factor then
          match tpat_to_texpr def.item_meta.span pat with
          | None -> env
          | Some pat_expr -> TExprMap.add bound (monadic, pat_expr) env
        else env
      in
      let next = self#visit_texpr env next in
      Let (monadic, pat, bound, next)

    method! visit_texpr env e =
      let e =
        match TExprMap.find_opt e env with
        | None -> e
        | Some (monadic, e) ->
            if monadic then mk_result_ok_texpr def.item_meta.span e else e
      in
      super#visit_texpr env e
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

type inline_env = { subst : texpr FVarId.Map.t; loop_back_funs : FVarId.Set.t }

let empty_inline_env : inline_env =
  { subst = FVarId.Map.empty; loop_back_funs = FVarId.Set.empty }

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

    [inline_loop_back_calls]: inline calls to loop backward functions. This is
    useful to trigger simplifications, for instance in [loop_to_recursive].

    TODO: we have a smallish issue which is that rvalues should be merged with
    expressions... For now, this forces us to substitute whenever we can, but
    leave the let-bindings where they are, and eliminated them in a subsequent
    pass (if they are useless). *)
let inline_useless_var_assignments_visitor ~(inline_named : bool)
    ~(inline_const : bool) ~(inline_pure : bool) ~(inline_identity : bool)
    ?(inline_loop_back_calls : bool = false) (ctx : ctx) (def : fun_decl) =
  object (self)
    inherit [_] map_expr as super

    (** Visit the let-bindings to filter the useless ones (and update the
        substitution map while doing so *)
    method! visit_Let (env : inline_env) monadic lv re e =
      (* In order to filter, we need to check first that:
           - the let-binding is not monadic
           - the left-value is a variable

           We also inline if the binding decomposes a structure that is to be
           extracted as a tuple, and the right value is a variable.
        *)
      match (monadic, lv.pat) with
      | false, POpen (lv_var, _) ->
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

            (* Or:
               1.3 the right-expression is a call to a loop backward function,
               and [inline_loop_back_calls] is [true] *)
            let back_call =
              inline_loop_back_calls
              &&
              let f, _ = destruct_apps re in
              match f.e with
              | FVar fid -> FVarId.Set.mem fid env.loop_back_funs
              | _ -> false
            in

            filter_left && (var_or_global || const_re || pure_re || back_call)
          in

          (* Or if: 2. the let-binding bounds the identity function *)
          let filter_id =
            inline_identity
            &&
            match re.e with
            | Lambda ({ pat = POpen (v0, _); _ }, { e = FVar v1; _ }) ->
                v0.id = v1
            | _ -> false
          in

          let filter = filter_pure || filter_id in

          (* Update the rhs (we may perform substitutions inside, and it is
           * better to do them *before* we inline it *)
          let re = self#visit_texpr env re in
          (* Update the substitution environment *)
          let env =
            if filter then
              { env with subst = FVarId.Map.add lv_var.id re env.subst }
            else env
          in
          (* Update the next expression *)
          let e = self#visit_texpr env e in
          (* Reconstruct the [let], only if the binding is not filtered *)
          if filter then e.e else Let (monadic, lv, re, e)
      | ( false,
          PAdt
            {
              variant_id = None;
              fields = [ { pat = POpen (lv_var, _); ty = _ } ];
            } ) ->
          (* Second case: we deconstruct a structure with one field that we will
               extract as tuple. *)
          let adt_id, _ = PureUtils.ty_as_adt def.item_meta.span re.ty in
          (* Update the rhs (we may perform substitutions inside, and it is
           * better to do them *before* we inline it *)
          let re = self#visit_texpr env re in
          if
            PureUtils.is_fvar re
            && type_decl_from_type_id_is_tuple_struct
                 ctx.trans_ctx.type_ctx.type_infos adt_id
          then
            (* Update the substitution environment *)
            let env =
              { env with subst = FVarId.Map.add lv_var.id re env.subst }
            in
            (* Update the next expression *)
            let e = self#visit_texpr env e in
            (* We filter the [let], and thus do not reconstruct it *)
            e.e
          else (* Nothing to do *)
            super#visit_Let env monadic lv re e
      | _ -> super#visit_Let env monadic lv re e

    (** Substitute the variables *)
    method! visit_FVar (env : inline_env) (vid : FVarId.id) =
      match FVarId.Map.find_opt vid env.subst with
      | None -> (* No substitution *) super#visit_FVar env vid
      | Some ne ->
          (* Substitute - note that we need to reexplore, because
           * there may be stacked substitutions, if we have:
           * var0 --> var1
           * var1 --> var2.
           *)
          self#visit_expr env ne.e

    method! visit_loop_body (env : inline_env) (body : loop_body) =
      (* Register the loop inputs.

         TODO: for now we register all the inputs, but we should only register
         the backward functions. *)
      let { inputs; loop_body } = body in
      let fvars = tpats_get_fvars inputs in
      let env =
        { env with loop_back_funs = FVarId.Set.union env.loop_back_funs fvars }
      in
      { inputs; loop_body = self#visit_texpr env loop_body }
  end

let inline_useless_var_assignments ~inline_named ~inline_const ~inline_pure
    ~inline_identity ?(inline_loop_back_calls = false) =
  lift_expr_map_visitor_with_state
    (inline_useless_var_assignments_visitor ~inline_named ~inline_const
       ~inline_pure ~inline_identity ~inline_loop_back_calls)
    empty_inline_env

(** Simplify let-bindings which bind tuples and which contain ignored patterns.

    Ex.:
    {[
      let (_, x) = if b then (true, 1) else (false, 0) in …

          ~>

      let x = if b then 1 else 0 in …
    ]} *)
let simplify_let_tuple span (ctx : ctx) (monadic : bool) (pat : tpat)
    (bound : texpr) : tpat * texpr * bool =
  let span = span in
  (* We attempt to filter only if:
     - the pattern is a tuple containing ignored patterns
     - the bound expression is "non trivial" (for instance, not just a
       function call) *)
  let pats = opt_destruct_tuple_tpat span pat in
  let has_ignored_pats =
    match pats with
    | None -> false
    | Some pats -> List.exists is_ignored_pat pats
  in
  let bound_non_trivial =
    match bound.e with
    | Lambda _ | Let _ | Switch _ -> true
    | _ -> false
  in

  if has_ignored_pats && bound_non_trivial then (
    (* Update *)
    let pats = Option.get pats in
    let keep = List.map (fun p -> not (is_ignored_pat p)) pats in
    [%ldebug "keep: " ^ Print.list_to_string Print.bool_to_string keep];
    let tys = List.map (fun (p : tpat) -> p.ty) pats in
    let num_nonfiltered_pats = List.length pats in
    let pats = List.filter (fun p -> not (is_ignored_pat p)) pats in
    let pats = mk_simpl_tuple_pat pats in
    let new_ty = if monadic then mk_result_ty pats.ty else pats.ty in

    (* Update an expression to filter its outputs *)
    let rec update (e : texpr) : texpr =
      [%ldebug "e:\n" ^ texpr_to_string ctx e];
      match e.e with
      | FVar _ | App _ | Loop _ | Const _ ->
          [%ldebug "expression is FVar, App, Loop, Const"];
          let tuple_size = get_tuple_size e in
          [%sanity_check] span
            (tuple_size = None || tuple_size = Some num_nonfiltered_pats);
          (* If this is a panic/break/continue, we do nothing *)
          if is_result_fail e || is_loop_result_fail_break_continue e then (
            [%ldebug "expression is a fail, break or a continue"];
            let f, args = destruct_qualif_apps e in
            [%add_loc] mk_qualif_apps span f args new_ty)
          else if is_result_ok e then (
            (* If this is an [ok] we update the inner expression *)
            [%ldebug "expression is an ok"];
            let f, args = destruct_qualif_apps e in
            match args with
            | [ x ] ->
                let x = update x in
                [%add_loc] mk_qualif_apps span f [ x ] new_ty
            | _ -> [%internal_error] span
            (* If this is a tuple we filter the arguments *))
          else if tuple_size = Some num_nonfiltered_pats then (
            [%ldebug "expression is a tuple"];
            let args = [%add_loc] destruct_tuple_texpr span e in
            [%ldebug
              "args:\n"
              ^ Print.list_to_string ~sep:"\n" (texpr_to_string ctx) args];
            let args =
              List.filter_map
                (fun (keep, arg) -> if keep then Some arg else None)
                (List.combine keep args)
            in
            mk_simpl_tuple_texpr span args)
          else (
            [%ldebug "expression is of an unknown kind"];
            (* We need to introduce an intermediate let-binding *)
            let pats, out =
              List.split
                (List.map
                   (fun (keep, ty) ->
                     if keep then
                       let fv = mk_fresh_fvar ctx ty in
                       (mk_tpat_from_fvar None fv, Some (mk_texpr_from_fvar fv))
                     else (mk_ignored_pat ty, None))
                   (List.combine keep tys))
            in
            let pats = mk_simpl_tuple_pat pats in
            let out = List.filter_map (fun x -> x) out in
            let out = mk_simpl_tuple_texpr span out in

            let monadic = is_result_ty e.ty in
            let out = if monadic then mk_result_ok_texpr span out else out in
            mk_opened_let monadic pats e out)
      | BVar _ | CVar _ | Qualif _ | StructUpdate _ -> [%internal_error] span
      | Lambda (pat, inner) -> mk_opened_lambda span pat (update inner)
      | Let (monadic, pat, bound, next) ->
          mk_opened_let monadic pat bound (update next)
      | Switch (scrut, body) ->
          let switch =
            match body with
            | If (e0, e1) -> If (update e0, update e1)
            | Match branches ->
                let branches =
                  List.map
                    (fun (br : match_branch) ->
                      { br with branch = update br.branch })
                    branches
                in
                Match branches
          in
          let ty = get_switch_body_ty switch in
          { e = Switch (scrut, switch); ty }
      | Meta (m, inner) -> mk_emeta m (update inner)
      | EError _ -> { e with ty = new_ty }
    in

    let bound = update bound in
    (pats, bound, true))
  else (pat, bound, false)

(** Filter the useless assignments (removes the useless variables, filters the
    function calls) *)
let filter_useless (ctx : ctx) (def : fun_decl) : fun_decl =
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
      inherit [_] mapreduce_tpat
      method zero _ = true
      method plus b0 b1 _ = b0 () && b1 ()

      method! visit_POpen env v mp =
        if FVarId.Set.mem v.id env then (POpen (v, mp), fun _ -> false)
        else (PIgnored, fun _ -> true)

      method! visit_PBound _ _ _ = [%internal_error] span
    end
  in
  let filter_tpat (used_vars : FVarId.Set.t) (lv : tpat) : tpat * bool =
    let lv, all_dummies = lv_visitor#visit_tpat used_vars lv in
    (lv, all_dummies ())
  in

  (* We then implement the transformation on *expressions* through a mapreduce.
     Note that the transformation is bottom-up.
     The map filters the useless assignments, the reduce computes the set of
     used variables. *)
  let expr_visitor =
    object (self)
      inherit [_] mapreduce_expr as super
      method zero _ = FVarId.Set.empty
      method plus s0 s1 _ = FVarId.Set.union (s0 ()) (s1 ())

      (** Whenever we visit a variable, we need to register the used variable *)
      method! visit_FVar _ vid = (FVar vid, fun _ -> FVarId.Set.singleton vid)

      method! visit_expr env e =
        match e with
        | BVar _ -> [%internal_error] span
        | FVar _ | CVar _ | Const _ | App _ | Qualif _
        | Meta (_, _)
        | StructUpdate _ | Lambda _
        | EError (_, _) -> super#visit_expr env e
        | Switch (scrut, switch) -> (
            match switch with
            | If (_, _) -> super#visit_expr env e
            | Match branches ->
                (* Simplify the branches *)
                let simplify_branch (br : match_branch) =
                  (* Compute the set of values used inside the branch *)
                  let branch, used = self#visit_texpr env br.branch in
                  (* Simplify the pattern *)
                  let pat, _ = filter_tpat (used ()) br.pat in
                  { pat; branch }
                in
                super#visit_expr env
                  (Switch (scrut, Match (List.map simplify_branch branches))))
        | Let (monadic, lv, re, e) ->
            (* Compute the set of values used in the next expression *)
            let e, used = self#visit_texpr env e in
            let used = used () in
            (* Filter the left values *)
            let lv, all_dummies = filter_tpat used lv in
            (* Small utility - called if we can't filter the let-binding *)
            let dont_filter () =
              let re, used_re = self#visit_texpr env re in
              let used = FVarId.Set.union used (used_re ()) in
              (* Simplify the left pattern if it only contains ignored variables *)
              let lv =
                if all_dummies then
                  let ty = lv.ty in
                  let pat = PIgnored in
                  { pat; ty }
                else lv
              in
              (* If there are ignored patterns, attempt to simplify
                 the binding and the right expression. *)
              let lv, re, updated = simplify_let_tuple span ctx monadic lv re in

              (* We may need to revisited the bound expression if we modified it:
                 some values may now be unused. *)
              let re = if updated then fst (self#visit_texpr env re) else re in

              (* Put everything together *)
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
            let {
              loop_id = _;
              span = _;
              output_tys = _;
              num_output_values = _;
              inputs;
              num_input_conts = _;
              loop_body;
            } =
              loop
            in
            let loop_body, used =
              let { inputs; loop_body } = loop_body in
              let loop_body, used = self#visit_texpr () loop_body in
              (({ inputs; loop_body } : loop_body), used)
            in
            let used, inputs =
              List.fold_left_map
                (fun used input ->
                  let input, used' = self#visit_texpr () input in
                  (self#plus used used', input))
                used inputs
            in
            (Loop { loop with inputs; loop_body }, used)
    end
    (* We filter only inside of transparent (i.e., non-opaque) definitions *)
  in
  map_open_all_fun_decl_body ctx.fresh_fvar_id
    (fun body ->
      (* Visit the body *)
      let body_exp, used_vars = expr_visitor#visit_texpr () body.body in
      (* Visit the parameters - TODO: update: we can filter only if the definition
         is not recursive (otherwise it might mess up with the decrease clauses:
         the decrease clauses uses all the inputs given to the function, if some
         inputs are replaced by '_' we can't give it to the function used in the
         decreases clause).
         For now we deactivate the filtering. *)
      let used_vars = used_vars () in
      let inputs =
        if false then
          List.map (fun lv -> fst (filter_tpat used_vars lv)) body.inputs
        else body.inputs
      in
      (* Return *)
      { body = body_exp; inputs })
    def

(** Simplify let bindings which bind expressions containing a branching.

    This micro-pass does transformations of the following kind:
    {[
      let (b', x) := if b then (true, 1) else (false, 0) in
      ...

        ~~>

      let x := if b then 1 else 0 in
      let b' := b in // inlined afterwards by [inline_useless_var_assignments]
      ...
    ]}

    Expressions like the above one are often introduced when merging contexts
    after a branching. *)
let simplify_let_branching (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in
  (* Helper to compute the output *)
  let simplify_aux (monadic : bool) (pats : tpat list) (bound : texpr)
      (next : texpr) : tpat * texpr * texpr =
    let num_outs = List.length pats in
    (* We will accumulate the outputs we find in this array *)
    let outs = Array.init num_outs (fun _ -> []) in
    let push_to_outs i el =
      Array.set outs i (TExprSet.of_list el :: Array.get outs i)
    in

    (* Compute the set of variables which are bound inside the bound expression
       (we will ignored those, as they were not introduced before) *)
    let bound_fvars = texpr_get_bound_fvars bound in

    (* Small helper.

       When exploring expressions, we keep track of the variables we branched
       upon together with the values they were expanded to, whenever we dive into a branch.

       For instance:
       {[
         if b then
           // here we remember: b -> true
           ...
         else
           // here we remember: b -> false
           ...
       ]}

       This small helper allows, given an expression [e], to retrieve the
       list of variables that it may be equal to, in the current branch.
       For instance, in the branch [then] of the example above, [true] might
       be equal to [b]. *)
    let get_equal_values (branchings : fvar_id list TExprMap.t) (e : texpr) :
        texpr list =
      (* For now we do something simple: we simply check if there is
         exactly [e] which appears as a key in the map. We could recursively
         explore the sub-expressions of [e] instead. *)
      match TExprMap.find_opt e branchings with
      | None -> []
      | Some el -> List.map (fun id -> ({ e = FVar id; ty = e.ty } : texpr)) el
    in

    (* When we can't compute the exact list of values an expression evaluates
           to, we store an empty set of possible values for all the outputs, meaning
           we will not simplify anything. *)
    let push_empty_possibilities () =
      for i = 0 to num_outs - 1 do
        push_to_outs i []
      done
    in

    (* Is this expression a free variable which was bound before (we ignore
       the variables bound inside the bound expression of the let, as we
       can't refer to them from outside the let-binding) *)
    let is_bound_before_fvar (e : texpr) : bool =
      match e.e with
      | FVar id -> not (FVarId.Set.mem id bound_fvars)
      | _ -> false
    in

    (* Explore the bound expression. *)
    let rec explore (branchings : fvar_id list TExprMap.t) (e : texpr) : unit =
      match e.e with
      | FVar _ | CVar _ | Const _ | StructUpdate _ | Qualif _ | Lambda _ ->
          [%sanity_check] span (num_outs = 1);
          push_to_outs 0 (e :: get_equal_values branchings e)
      | BVar _ -> [%internal_error] span
      | App _ ->
          (* *)
          if is_result_fail e || is_loop_result_fail_break_continue e then ()
          else if is_result_ok e then
            let _, args = destruct_apps e in
            match args with
            | [ x ] -> explore branchings x
            | _ -> [%internal_error] span
          else if get_tuple_size e = Some num_outs then
            let args = [%add_loc] destruct_tuple_texpr span e in
            List.iteri
              (fun i arg ->
                let vl = get_equal_values branchings arg in
                push_to_outs i (arg :: vl))
              args
          else push_empty_possibilities ()
      | Let (_, _, _, next) -> explore branchings next
      | Switch (scrut, switch) -> (
          if
            (* Remember the branching, in case we branch over a variable that
               we shouldn't ignore *)
            is_bound_before_fvar scrut
          then
            let scrut_id = as_fvar span scrut in
            match switch with
            | If (e0, e1) ->
                let branchings0 =
                  TExprMap.add_to_list mk_true scrut_id branchings
                in
                explore branchings0 e0;
                let branchings1 =
                  TExprMap.add_to_list mk_false scrut_id branchings
                in
                explore branchings1 e1
            | Match branches ->
                List.iter
                  (fun ({ pat; branch } : match_branch) ->
                    let branchings =
                      match tpat_to_texpr span pat with
                      | None -> branchings
                      | Some e -> TExprMap.add_to_list e scrut_id branchings
                    in
                    explore branchings branch)
                  branches
          else
            match switch with
            | If (e0, e1) ->
                explore branchings e0;
                explore branchings e1
            | Match branches ->
                List.iter
                  (fun ({ pat = _; branch } : match_branch) ->
                    explore branchings branch)
                  branches)
      | Loop _ -> push_empty_possibilities ()
      | Meta (_, e) -> explore branchings e
      | EError _ -> ()
    in
    explore TExprMap.empty bound;

    (* Check if some of the outputs can be mapped to the same value.
       We simply check if the potential outputs have a non empty intersection
       for all the branches. *)
    let possible_outputs =
      Array.map
        (fun (ls : TExprSet.t list) ->
          match ls with
          | [] -> TExprSet.empty
          | s :: ls -> List.fold_left (fun s s' -> TExprSet.inter s s') s ls)
        outs
    in
    [%ldebug
      "possible_outputs:\n"
      ^ String.concat ",\n\n"
          ((List.map (fun s ->
                "["
                ^ String.concat ", "
                    (List.map (texpr_to_string ctx) (TExprSet.to_list s))
                ^ "]"))
             (Array.to_list possible_outputs))];

    (* Pick outputs whenever possible *)
    let keep, outputs =
      List.split
        (List.map
           (fun s ->
             (* For now, we simply pick the first output which works *)
             match TExprSet.to_list s with
             | [] -> (true, None)
             | x :: _ -> (false, Some x))
           (Array.to_list possible_outputs))
    in
    let apply_update = List.exists Option.is_some outputs in
    [%ldebug
      "chosen outputs:\n"
      ^ String.concat ",\n\n"
          (List.map (Print.option_to_string (texpr_to_string ctx)) outputs)];

    let new_ty =
      mk_simpl_tuple_ty
        (List.map
           (fun (e : texpr) -> e.ty)
           (List.filter_map (fun x -> x) outputs))
    in
    let new_ty = if monadic then mk_result_ty new_ty else new_ty in

    (* Update the bound expression *)
    let rec update (e : texpr) : texpr =
      [%ldebug "About to update expression:\n" ^ texpr_to_string ctx e];
      match e.e with
      | FVar _ | CVar _ | Const _ | StructUpdate _ | Qualif _ | Lambda _ -> (
          [%sanity_check] span (num_outs = 1);
          match List.hd outputs with
          | None -> e
          | Some e -> e)
      | BVar _ -> [%internal_error] span
      | App _ ->
          [%ldebug "is app"];
          (* *)
          let tuple_size = get_tuple_size e in
          [%sanity_check] span (tuple_size = None || tuple_size = Some num_outs);
          if is_result_fail e || is_loop_result_fail_break_continue e then (
            [%ldebug "is fail, break or continue"];
            let f, args = destruct_qualif_apps e in
            [%add_loc] mk_qualif_apps span f args new_ty)
          else if is_result_ok e then (
            [%ldebug "is ok"];
            let _, args = destruct_apps e in
            let e =
              match args with
              | [ x ] -> mk_result_ok_texpr span (update x)
              | _ -> [%internal_error] span
            in
            [%ldebug
              "result::ok expression after update:\n" ^ texpr_to_string ctx e];
            e)
          else if tuple_size = Some num_outs then (
            [%ldebug "is tuple"];
            let args = [%add_loc] destruct_tuple_texpr span e in
            [%ldebug
              "args:\n"
              ^ String.concat ",\n" (List.map (texpr_to_string ctx) args)];

            let args =
              List.filter_map
                (fun (arg, out) ->
                  match out with
                  | None -> Some arg
                  | Some _ -> None)
                (List.combine args outputs)
            in
            let e = mk_simpl_tuple_texpr span args in
            [%ldebug "Tuple after update:\n" ^ texpr_to_string ctx e];
            e)
          else (
            [%ldebug "unknown kind of expression"];
            (* TODO: we may have issues if we can't properly update the type *)
            [%internal_error] span)
      | Let (monadic, bound, pat, next) ->
          mk_opened_let monadic bound pat (update next)
      | Switch (scrut, switch) ->
          let switch =
            match switch with
            | If (e0, e1) -> If (update e0, update e1)
            | Match branches ->
                Match
                  (List.map
                     (fun (br : match_branch) ->
                       { br with branch = update br.branch })
                     branches)
          in
          { e = Switch (scrut, switch); ty = new_ty }
      | Loop _ ->
          (* TODO: we may have issues if we can't properly update the type *)
          [%internal_error] span
      | Meta (m, inner) -> mk_emeta m (update inner)
      | EError _ -> { e = e.e; ty = new_ty }
    in
    let bound = if apply_update then update bound else bound in

    (* Update the pattern *)
    let pat =
      let pats =
        List.filter_map
          (fun (keep, pat) -> if keep then Some pat else None)
          (List.combine keep pats)
      in
      mk_simpl_tuple_pat pats
    in

    (* Introduce let-bindings for the outputs we removed *)
    let next =
      mk_opened_lets false
        (List.filter_map
           (fun (pat, out) ->
             match out with
             | None -> None
             | Some out -> Some (pat, out))
           (List.combine pats outputs))
        next
    in

    (* Create the let-binding *)
    (pat, bound, next)
  in

  (* Helper to compute the output *)
  let simplify (monadic : bool) (pat : tpat) (bound : texpr) (next : texpr) :
      tpat * texpr * texpr =
    match opt_destruct_tuple_tpat span pat with
    | None -> (pat, bound, next)
    | Some pats -> simplify_aux monadic pats bound next
  in

  let visitor =
    object
      inherit [_] map_expr as super

      method! visit_Let env monadic pat bound next =
        (* Only attempt to simplify if there is a branching in the bound expression *)
        match bound.e with
        | Switch _ ->
            let pat, bound, next = simplify monadic pat bound next in
            super#visit_Let env monadic pat bound next
        | _ -> super#visit_Let env monadic pat bound next
    end
  in

  map_open_all_fun_decl_body ctx.fresh_fvar_id
    (fun body -> { body with body = visitor#visit_texpr () body.body })
    def

(** Simplify the lets immediately followed by an ok.

    Ex.:
    {[
      x <-- f y;
      Ok x

        ~~>

      f y
    ]}

    If [ignore_loops] is true, we do not apply this transformation binds a loop
    (this is useful to simplify some other micro-passes). *)
let simplify_let_then_ok_visitor ~(ignore_loops : bool) _ctx (def : fun_decl) =
  (* Match a pattern and an expression: evaluates to [true] if the expression
     is actually exactly the pattern *)
  let rec match_pat_and_expr (pat : tpat) (e : texpr) : bool =
    match (pat.pat, e.e) with
    | PConstant plit, Const lit -> plit = lit
    | POpen (pv, _), FVar vid -> pv.id = vid
    | PIgnored, _ ->
        (* It is ok only if we ignore the unit value *)
        pat.ty = mk_unit_ty && e = mk_unit_texpr
    | PAdt padt, _ -> (
        let qualif, args = destruct_apps e in
        match qualif.e with
        | Qualif { id = AdtCons cons_id; generics = _ } ->
            if
              pat.ty = e.ty
              && padt.variant_id = cons_id.variant_id
              && List.length padt.fields = List.length args
            then
              List.for_all
                (fun (p, e) -> match_pat_and_expr p e)
                (List.combine padt.fields args)
            else false
        | _ -> false)
    | _ -> false
  in

  object (self)
    inherit [_] map_expr

    method! visit_Let env monadic lv rv next_e =
      (* We do a bottom up traversal (simplifying in the children nodes
         can allow simplifying in the parent nodes) *)
      let rv = self#visit_texpr env rv in
      let next_e = self#visit_texpr env next_e in
      let not_simpl_e = Let (monadic, lv, rv, next_e) in
      match next_e.e with
      | Switch _ | Loop _ | Let _ ->
          (* Small shortcut to avoid doing the check on every let-binding *)
          not_simpl_e
      | _ -> (
          (* Ignore loops if the user instructs to do so *)
          match rv.e with
          | Loop _ when ignore_loops -> not_simpl_e
          | _ -> (
              if
                (* Do the check *)
                monadic
              then
                (* The first let-binding is monadic *)
                match opt_destruct_ret next_e with
                | Some e ->
                    if match_pat_and_expr lv e then rv.e else not_simpl_e
                | None -> not_simpl_e
              else
                (* The first let-binding is not monadic *)
                match opt_destruct_ret next_e with
                | Some e ->
                    if match_pat_and_expr lv e then
                      (* We need to wrap the right-value in a ret *)
                      (mk_result_ok_texpr def.item_meta.span rv).e
                    else not_simpl_e
                | None ->
                    if match_pat_and_expr lv next_e then rv.e else not_simpl_e))
  end

let simplify_let_then_ok ~(ignore_loops : bool) =
  lift_expr_map_visitor (simplify_let_then_ok_visitor ~ignore_loops)

(** Simplify the aggregated ADTs. Ex.:
    {[
      type struct = { f0 : nat; f1 : nat; f2 : nat }

      Mkstruct x.f0 x.f1 x.f2 ~~> x
    ]} *)
let simplify_aggregates_visitor (ctx : ctx) (def : fun_decl) =
  object
    inherit [_] map_expr as super

    (* Look for a type constructor applied to arguments *)
    method! visit_texpr env e =
      (* First simplify the sub-expressions *)
      let e = super#visit_texpr env e in
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
                let to_var_proj (i : int) (arg : texpr) :
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
          let to_expr_proj ((fid, arg) : FieldId.id * texpr) : texpr option =
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

(** Helper: flatten nested struct updates and projections of struct updates.

    Ex.:
    [
      { { x with field0 = 0 } with field0 = 1; field1 = 2 }

        ~~>

      { x with field1 = 1; field1 = 2 }
    ]

    [
      { x with field1 = 1 }.field1 ~> 1
      { x with field1 = 1 }.field2 ~> x.field1
    ]
*)
let flatten_struct_updates (ctx : ctx) (def : fun_decl) : fun_decl =
  let span = def.item_meta.span in
  let visitor =
    object (self)
      inherit [_] map_expr as super

      method! visit_StructUpdate env { struct_id; init; updates } =
        (* Flatten nested struct updates *)
        match init with
        | None -> super#visit_StructUpdate env { struct_id; init; updates }
        | Some init -> (
            let init = self#visit_texpr env init in
            let visit_update (fid, e) = (fid, self#visit_texpr env e) in
            let updates = List.map visit_update updates in
            match init.e with
            | StructUpdate
                { struct_id = struct_id'; init = init'; updates = updates' } ->
                [%sanity_check] span (struct_id = struct_id');
                let fids = FieldId.Set.of_list (List.map fst updates) in
                let updates' =
                  List.filter
                    (fun (fid, _) -> not (FieldId.Set.mem fid fids))
                    updates'
                in
                let updates' = List.map visit_update updates' in
                let updates = updates' @ updates in
                StructUpdate { struct_id; init = init'; updates }
            | _ -> StructUpdate { struct_id; init = Some init; updates })

      method! visit_App env f arg =
        let f = self#visit_texpr env f in
        let arg = self#visit_texpr env arg in
        match f.e with
        | Qualif { id = Proj { field_id; _ }; _ } -> (
            match arg.e with
            | StructUpdate { struct_id = _; init; updates } -> (
                (* Simplify projections.

                Check if the field we project is listed in the updates. *)
                match
                  List.find_opt (fun (fid, _) -> fid = field_id) updates
                with
                | Some (_, field) ->
                    (* We found the field: simply evaluate to the updated expression *)
                    field.e
                | None -> (
                    (* Could not find the field: there *must* be an init value *)
                    match init with
                    | None -> [%internal_error] span
                    | Some init ->
                        (* Project directly the init value *)
                        ([%add_loc] mk_app span f init).e))
            | App _ -> (
                let f, args = destruct_apps f in
                (* Check if this is a call to a constructor *)
                match f.e with
                | Qualif { id = AdtCons _; _ } -> (
                    (* Let's select the proper argument *)
                    match FieldId.nth_opt args field_id with
                    | Some e -> e.e
                    | None -> [%internal_error] span)
                | _ -> ([%add_loc] mk_app span f arg).e)
            | _ -> ([%add_loc] mk_app span f arg).e)
        | _ -> ([%add_loc] mk_app span f arg).e
    end
  in
  map_open_all_fun_decl_body_expr ctx.fresh_fvar_id (visitor#visit_texpr ()) def

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
  expand_map : expr ExprMap.t;
  (* The list of values which were expanded through matches or let-bindings.

     For instance, if we see the expression [let (x, y) = p in ...] we push
     the expression [p].
  *)
  expanded : expr list;
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
  let add_pat_eqs (bound_adt : texpr) (pat : tpat) (env : simp_aggr_env) :
      simp_aggr_env =
    (* Register the pattern - note that we may not be able to convert the
       pattern to an expression if, for instance, it contains [_] *)
    let env =
      match tpat_to_texpr span pat with
      | Some pat_expr -> add_expand bound_adt.e pat_expr.e env
      | None -> env
    in
    (* Register the fact that the scrutinee got expanded *)
    let env = add_expanded bound_adt.e env in
    (* Check if we are decomposing an ADT to introduce variables for its fields *)
    match pat.pat with
    | PAdt adt ->
        (* Check if the fields are all variables, and compute the tuple:
           (variable introduced for the field, projection) *)
        let fields = FieldId.mapi (fun id x -> (id, x)) adt.fields in
        let vars_to_projs =
          Collections.List.filter_map
            (fun ((fid, f) : _ * tpat) ->
              match f.pat with
              | POpen (var, _) ->
                  let proj = mk_adt_proj span bound_adt fid f.ty in
                  let var = { e = FVar var.id; ty = f.ty } in
                  Some (var.e, proj.e)
              | PBound _ -> [%internal_error] span
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
  let expand_expr simp_env (v : expr) : expr =
    let visitor =
      object
        inherit [_] map_expr as super

        method! visit_expr env e =
          match get_expand e simp_env with
          | None -> super#visit_expr env e
          | Some e -> super#visit_expr env e
      end
    in
    visitor#visit_expr () v
  in

  (* The visitor *)
  object (self)
    inherit [_] map_expr as super

    method! visit_Switch env scrut switch =
      [%ltrace "Visiting switch: " ^ switch_to_string ctx scrut switch];
      (* Update the scrutinee *)
      let scrut = self#visit_texpr env scrut in
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
              self#visit_texpr (add_expand scrut.e (mk_bool_value v).e env) st
            in
            let b0 = update true b0 in
            let b1 = update false b1 in
            If (b0, b1)
        | Match branches ->
            let update_branch (b : match_branch) =
              (* Register the information introduced by the patterns *)
              let env = add_pat_eqs scrut b.pat env in
              { b with branch = self#visit_texpr env b.branch }
            in
            let branches = List.map update_branch branches in
            Match branches
      in
      Switch (scrut, switch)

    (* We need to detect patterns of the shape: [let (x, y) = t in ...] *)
    method! visit_Let env monadic pat bound next =
      (* Register the pattern if it is not a monadic let binding *)
      let env = if monadic then env else add_pat_eqs bound pat env in
      (* Continue *)
      super#visit_Let env monadic pat bound next

    (* Update the ADT values *)
    method! visit_texpr env e0 =
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
                  let update_field ((fid, e) : field_id * texpr) :
                      (field_id * texpr) option =
                    (* Recursively expand the value of the field, to check if it is
                         equal to the updated value: if it is the case, we can omit
                         the update. *)
                    let adt = init in
                    let field_value = mk_adt_proj span adt fid e.ty in
                    let field_value = expand_expr env field_value.e in
                    (* If this value is equal to the value we update the field
                         with, we can simply ignore the update *)
                    if field_value = expand_expr env e.e then (
                      [%ltrace "Simplifying field: " ^ texpr_to_string ctx e];
                      None)
                    else (
                      [%ltrace
                        "Not simplifying field: " ^ texpr_to_string ctx e];
                      Some (fid, e))
                  in
                  let updates = List.filter_map update_field updt.updates in
                  if updates = [] then (
                    [%ltrace
                      "StructUpdate: " ^ texpr_to_string ctx e0 ^ " ~~> "
                      ^ texpr_to_string ctx init];
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
            [%ltrace "Visiting app: " ^ texpr_to_string ctx e0];
            (* It may be an ADT expr (e.g., [Cons x y] or [(x, y)]):
                 check if it is the case, and if it is, compute the expansion
                 of all the values expanded so far, and see if exactly one of
                 those is equal to the current expression *)
            let e1 = super#visit_texpr env e0 in
            let e1_exp = expand_expr env e1.e in
            let f, _ = destruct_apps e1 in
            if is_adt_cons f then
              let expanded =
                List.filter_map
                  (fun e ->
                    let e' = expand_expr env e in
                    if e1_exp = e' then Some e else None)
                  env.expanded
              in
              begin
                match expanded with
                | [ e2 ] ->
                    [%ltrace
                      "Simplified: " ^ texpr_to_string ctx e1 ^ " ~~> "
                      ^ texpr_to_string ctx { e1 with e = e2 }];
                    e2
                | _ -> e1.e
              end
            else e1.e
        | _ -> super#visit_expr env e0.e
      in
      { e0 with e }
  end

let simplify_aggregates_unchanged_fields =
  lift_expr_map_visitor_with_state simplify_aggregates_unchanged_fields_visitor
    { expand_map = ExprMap.empty; expanded = [] }

(** Helper for [decompose_loops]: update the occurrences of continue and break
*)
let update_continue_breaks (ctx : ctx) (def : fun_decl) (loop_func : texpr)
    (constant_inputs : texpr list) (e : texpr) : texpr =
  let span = def.item_meta.span in

  let rec update (e : texpr) : texpr =
    [%ldebug "e:\n" ^ texpr_to_string ctx e];
    match e.e with
    | FVar _ | BVar _ | CVar _ | Const _ -> e
    | App _ | Qualif _ -> (
        (* Check if this is a continue, break, or a recLoopCall *)
        match
          opt_destruct_loop_result_decompose_outputs ctx span ~intro_let:true e
        with
        | Some ({ variant_id; args; break_ty; _ }, rebind) ->
            if variant_id = loop_result_continue_id then (
              [%ldebug "continue expression: introducing a recursive call"];
              [%ldebug
                "- loop_func: "
                ^ texpr_to_string ctx loop_func
                ^ "\n- loop_func.ty: "
                ^ ty_to_string ctx loop_func.ty
                ^ "\n- num args: "
                ^ string_of_int (List.length args)
                ^ "\n- args:\n"
                ^ String.concat "\n\n" (List.map (texpr_to_string ctx) args)];
              let args = constant_inputs @ args in
              rebind ([%add_loc] mk_apps span loop_func args))
            else if variant_id = loop_result_break_id then (
              [%ldebug "break expression: introducing an ok expression"];
              let arg = mk_simpl_tuple_texpr span args in
              rebind (mk_result_ok_texpr span arg))
            else if variant_id = loop_result_fail_id then
              let arg = mk_simpl_tuple_texpr span args in
              rebind (mk_result_fail_texpr span arg break_ty)
            else [%internal_error] span
        | _ -> (
            (* Not a continue or a break: might be a recLoopCall *)
            match opt_destruct_rec_loop_call span e with
            | Some { args; _ } ->
                let args = constant_inputs @ args in
                [%add_loc] mk_apps span loop_func args
            | None -> e))
    | Lambda (pat, body) ->
        let body = update body in
        mk_opened_lambda span pat body
    | Let (monadic, pat, bound, next) ->
        let bound = update bound in
        let next = update next in
        mk_opened_let monadic pat bound next
    | Switch (scrut, body) ->
        let scrut = update scrut in
        let body, ty =
          match body with
          | If (e0, e1) ->
              let e0 = update e0 in
              let e1 = update e1 in
              (If (e0, e1), e0.ty)
          | Match branches ->
              let branches =
                List.map
                  (fun ({ pat; branch } : match_branch) ->
                    { pat; branch = update branch })
                  branches
              in
              let ty =
                match branches with
                | [] -> [%internal_error] span
                | { branch = b; _ } :: _ -> b.ty
              in
              (Match branches, ty)
        in
        { e = Switch (scrut, body); ty }
    | Loop _ -> [%internal_error] span
    | StructUpdate { struct_id; init; updates } ->
        let init = Option.map update init in
        let updates = List.map (fun (fid, e) -> (fid, update e)) updates in
        { e with e = StructUpdate { struct_id; init; updates } }
    | Meta (m, e) -> mk_emeta m (update e)
    | EError _ ->
        let ty =
          match try_unwrap_loop_result e.ty with
          | None -> e.ty
          | Some (_, break) -> mk_result_ty break
        in
        { e with ty }
  in
  update e

(** Retrieve the loop definitions from the function definition.

    Introduce auxiliary definitions for the loops. *)
let decompose_loops_aux (ctx : ctx) (def : fun_decl) (body : fun_body) :
    fun_decl * fun_decl list =
  let span = def.item_meta.span in

  let fvars, body = open_all_fun_body ctx span body in

  (* Count the number of loops *)
  let loops = ref LoopId.Set.empty in
  let expr_visitor =
    object
      inherit [_] iter_expr as super

      method! visit_Loop env loop =
        [%sanity_check] span (not (LoopId.Set.mem loop.loop_id !loops));
        loops := LoopId.Set.add loop.loop_id !loops;
        super#visit_Loop env loop
    end
  in
  expr_visitor#visit_texpr () body.body;
  let num_loops = LoopId.Set.cardinal !loops in

  (* Store the loops here *)
  let loops = ref LoopId.Map.empty in

  let compute_loop_fun_expr (loop : loop) (generics_filter : generics_filter)
      (constant_inputs : ty list) : texpr =
    let generic_args = generic_args_of_params def.signature.generics in
    let { types; const_generics; trait_refs } : generic_args = generic_args in
    let types =
      List.filter_map
        (fun (b, x) -> if b then Some x else None)
        (List.combine generics_filter.types types)
    in
    let const_generics =
      List.filter_map
        (fun (b, x) -> if b then Some x else None)
        (List.combine generics_filter.const_generics const_generics)
    in
    let trait_refs =
      List.filter_map
        (fun (b, x) -> if b then Some x else None)
        (List.combine generics_filter.trait_clauses trait_refs)
    in
    let generics : generic_args = { types; const_generics; trait_refs } in

    let output_ty = mk_result_ty (mk_simpl_tuple_ty loop.output_tys) in
    let input_tys = List.map (fun (e : texpr) -> e.ty) loop.inputs in
    let input_tys = constant_inputs @ input_tys in
    let func_ty = mk_arrows input_tys output_ty in
    let func =
      Qualif
        {
          id =
            FunOrOp
              (Fun (FromLlbc (FunId (FRegular def.def_id), Some loop.loop_id)));
          generics;
        }
    in
    { e = func; ty = func_ty }
  in

  (* Generate a function declaration from a loop body.

     We return:
     - the new declaration for the loop
     - the additional constant inputs (constants refered to by the loop but not
       bound by the loop body)
     - the expression representing a call to the loop function (without any arguments)
  *)
  let generate_loop_def visit_loop_body (loop : loop) :
      fun_decl * fvar list * texpr =
    let { output_tys; loop_body; _ } = loop in
    let output_ty = mk_simpl_tuple_ty output_tys in

    (* First decompose the inner loops *)
    let loop_body = visit_loop_body loop_body in

    (* Compute the list of *constant* inputs: those are variables used
       by the loop but not bound by the loop itself (because they are
       not modified through the loop iterations). *)
    let constant_inputs =
      let used_in_body = texpr_get_fvars loop_body.loop_body in
      let bound_in_body = loop_body_get_bound_fvars loop_body in
      let constant_inputs =
        List.filter_map
          (fun fid ->
            if FVarId.Set.mem fid bound_in_body then None
            else Some (FVarId.Map.find fid fvars))
          (FVarId.Set.elements used_in_body)
      in
      [%ldebug
        "- body:\n"
        ^ loop_body_to_string ctx loop_body
        ^ "\n\n- used_in_body: "
        ^ FVarId.Set.to_string None used_in_body
        ^ "\n- bound_in_body: "
        ^ FVarId.Set.to_string None bound_in_body
        ^ "\n- constant_inputs: "
        ^ Print.list_to_string (fvar_to_string ctx) constant_inputs];
      constant_inputs
    in
    let constant_input_tys =
      List.map (fun (e : fvar) -> e.ty) constant_inputs
    in

    (* Compute the generic params - note that the indices are not updated,
       meaning we do not need to update those in the body *)
    let generics, generics_filter =
      filter_generic_params_used_in_texpr def.signature.generics
        loop_body.loop_body
    in
    [%ldebug
      "- generic_params:\n"
      ^ generic_params_to_string ctx generics
      ^ "\n- generics_filter:\n"
      ^ show_generics_filter generics_filter];
    let loop_func =
      compute_loop_fun_expr loop generics_filter constant_input_tys
    in

    (* Update the loop body to introduce recursive calls *)
    let body =
      update_continue_breaks ctx def loop_func
        (List.map mk_texpr_from_fvar constant_inputs)
        loop_body.loop_body
    in

    (* Update the inputs and close the loop body *)
    let loop_body =
      let inputs =
        List.map (mk_tpat_from_fvar None) constant_inputs @ loop_body.inputs
      in
      let body : fun_body = { inputs; body } in
      [%ldebug
        "body before closing the free variables:\n"
        ^ fun_body_to_string ctx body];
      close_all_fun_body loop.span body
    in

    (* *)
    let fun_sig = def.signature in
    let fwd_info = fun_sig.fwd_info in
    let fwd_effect_info = fwd_info.effect_info in
    let ignore_output = fwd_info.ignore_output in

    (* Generate the loop definition *)
    let loop_fwd_effect_info =
      { fwd_effect_info with is_rec = !Config.loops_to_recursive_functions }
    in

    let loop_fwd_sig_info : fun_sig_info =
      { effect_info = loop_fwd_effect_info; ignore_output }
    in

    (* Note that the loop body already binds the "constant" inputs: we don't
       need to add them anymore *)
    let input_tys = List.map (fun (v : tpat) -> v.ty) loop_body.inputs in
    let output = output_ty in

    let llbc_generics : T.generic_params =
      let { types; const_generics; trait_clauses; _ } : T.generic_params =
        fun_sig.llbc_generics
      in
      let types =
        List.filter_map
          (fun (b, x) -> if b then Some x else None)
          (List.combine generics_filter.types types)
      in
      let const_generics =
        List.filter_map
          (fun (b, x) -> if b then Some x else None)
          (List.combine generics_filter.const_generics const_generics)
      in
      let trait_clauses =
        List.filter_map
          (fun (b, x) -> if b then Some x else None)
          (List.combine generics_filter.trait_clauses trait_clauses)
      in
      {
        types;
        const_generics;
        trait_clauses;
        regions = [];
        regions_outlive = [];
        types_outlive = [];
        trait_type_constraints = [];
      }
    in

    let explicit_info = compute_explicit_info generics input_tys in
    let known_from_trait_refs = compute_known_info explicit_info generics in
    let loop_sig : fun_sig =
      {
        generics;
        explicit_info;
        known_from_trait_refs;
        llbc_generics;
        preds = { trait_type_constraints = [] };
        inputs = input_tys;
        output = mk_result_ty output;
        fwd_info = loop_fwd_sig_info;
        back_effect_info = fun_sig.back_effect_info;
      }
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
        src = def.src;
        backend_attributes = def.backend_attributes;
        num_loops;
        loop_id = Some loop.loop_id;
        name = def.name;
        signature = loop_sig;
        is_global_decl_body = def.is_global_decl_body;
        body = Some loop_body;
      }
    in

    (loop_def, constant_inputs, loop_func)
  in

  let decompose_visitor =
    object (self)
      inherit [_] map_expr

      method! visit_Loop env loop =
        (* Update the definition *)
        let loop_def, constant_inputs, func =
          generate_loop_def (self#visit_loop_body env) loop
        in

        (* Store the loop definition *)
        loops := LoopId.Map.add_strict loop.loop_id loop_def !loops;

        let inputs =
          List.map mk_texpr_from_fvar constant_inputs @ loop.inputs
        in
        let loop = [%add_loc] mk_apps span func inputs in
        loop.e
    end
  in

  let body_expr = decompose_visitor#visit_texpr () body.body in
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
let unit_vars_to_unit (ctx : ctx) (def : fun_decl) : fun_decl =
  let span = def.item_meta.span in

  (* The map visitor *)
  let obj =
    object
      inherit [_] map_expr as super

      (** Replace in patterns *)
      method! visit_POpen _ v mp =
        if v.ty = mk_unit_ty then PIgnored else POpen (v, mp)

      method! visit_PBound _ _ _ = [%internal_error] span

      (** Replace in "regular" expressions - note that we could limit ourselves
          to variables, but this is more powerful *)
      method! visit_texpr env e =
        if e.ty = mk_unit_ty then mk_unit_texpr else super#visit_texpr env e
    end
  in
  (* Update the body *)
  map_open_all_fun_decl_body ctx.fresh_fvar_id
    (fun body ->
      let body_exp = obj#visit_texpr () body.body in
      (* Update the input parameters *)
      let inputs = List.map (obj#visit_tpat ()) body.inputs in
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
    inherit [_] map_expr as super

    method! visit_texpr env e =
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
                  [%add_loc] mk_apps def.item_meta.span arg args
              | Index _
              | ArrayToSliceShared
              | ArrayToSliceMut
              | ArrayRepeat
              | PtrFromParts _ -> super#visit_texpr env e)
          | _ -> super#visit_texpr env e)
      | _ -> super#visit_texpr env e
  end

let eliminate_box_functions =
  lift_expr_map_visitor eliminate_box_functions_visitor

(** Simplify the lambdas by applying beta-reduction *)
let apply_beta_reduction_visitor (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in

  object (self)
    inherit [_] map_expr as super

    method! visit_FVar env vid =
      match FVarId.Map.find_opt vid env with
      | None -> FVar vid
      | Some e -> e.e

    method! visit_texpr env e =
      [%ldebug "e:\n" ^ texpr_to_string ctx e];
      let f, args = destruct_apps e in
      let args = List.map (self#visit_texpr env) args in
      let pats, body = raw_destruct_lambdas f in
      [%ldebug
        "After decomposing:\n- pats: "
        ^ Print.list_to_string (tpat_to_string ctx) pats
        ^ "\n- body: " ^ texpr_to_string ctx body ^ "\n- args: "
        ^ Print.list_to_string (texpr_to_string ctx) args];
      if args <> [] && pats <> [] then (
        [%ldebug "Can simplify:\n" ^ texpr_to_string ctx e];
        (* Apply the beta-reduction

           First split the arguments/patterns between those that
           will disappear and those we have to preserve. *)
        let min = Int.min (List.length args) (List.length pats) in
        let pats, kept_pats = Collections.List.split_at pats min in
        let args, kept_args = Collections.List.split_at args min in
        (* Substitute *)
        let vars =
          List.map (fun v -> (fst ([%add_loc] as_pat_open span v)).id) pats
        in
        let body =
          let env = FVarId.Map.add_list (List.combine vars args) env in
          self#visit_texpr env body
        in
        (* Reconstruct the term *)
        [%add_loc] mk_apps span
          (mk_opened_lambdas span kept_pats body)
          kept_args)
      else
        (* We may be exploring an expression of the shape:
           [(fun y -> (fun x -> e) y))]
           in which case we need to make sure we simplify the body:
           [(fun x -> e) y ~> e[x/y]]

           We also have to be careful about not infinitely looping.
        *)
        let body =
          if pats <> [] then self#visit_texpr env body
          else super#visit_texpr env body
        in
        [%add_loc] mk_apps span (mk_opened_lambdas span pats body) args
  end

let apply_beta_reduction =
  lift_expr_map_visitor_with_state apply_beta_reduction_visitor FVarId.Map.empty

(** This pass simplifies uses of array/slice index operations.

    We perform the following transformations:
    [
      let (_, back) = Array.index_mut_usize a i in
      let a' = back x in
      ...

       ~~>

      let a' = Array.update a i x in
      ...
    ]

    [
      let _, back = Array.index_mut_usize a i in
      ok (back x)

         ~~>

       Array.update a i x
    ] *)
let simplify_array_slice_update_visitor (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in

  (* The difficulty is that the let-binding which uses the backward function
     may not appear immediately after the let-binding which introduces it.

     The micro-pass is written in a general way: for instance we do not leverage
     the fact that a backward function should be used only once.
  *)

  (* Small helper: given an expression:
     [let (_, back) = index_mut a i in e2]
     attempt to simplify the let-binding.
   *)
  let try_simplify (monadic : bool) (pat : tpat) (e1 : texpr) (e2 : texpr)
      (back_var : fvar) (is_array : bool) (index_generics : generic_args)
      (a : texpr) (i : texpr) : texpr =
    (* Helper: outputs the input argument if this is a call to the backward function *)
    let is_call_to_back (e : texpr) : texpr option =
      let f, args = destruct_apps e in
      match (f.e, args) with
      | FVar id, [ v ] when id = back_var.id -> Some v
      | _ -> None
    in
    (* Helper to introduce a call to the proper update function *)
    let mk_call_to_update (v : texpr) =
      let array_or_slice = if is_array then Array else Slice in
      let qualif =
        Qualif
          {
            id = FunOrOp (Fun (Pure (UpdateAtIndex array_or_slice)));
            generics = index_generics;
          }
      in
      let qualif = { e = qualif; ty = mk_arrows [ a.ty; i.ty; v.ty ] e2.ty } in
      [%add_loc] mk_apps span qualif [ a; i; v ]
    in

    (* We repeteadly destruct the let-bindings in the next expression until
       the moment we find the call to the backward function. We remove this
       call and insert instead a call to [update]. As the call to the backward
       function may use variables introduced *after* the call to [index_mut]
       we do not necessarily insert it at the position of the backward call
       and may have to introduce it before: we try to introduce it as close
       as possible to the call to [index_mut].

       For instance:
       [
         let (_, back) = index_mut a i in
         let v1 = v + 1 in
         let i1 = i + 1 in
         let a1 = back v1 in
         ...

           ~>

         let v1 = v + 1 in
         let a1 = update a i v1 in (* HERE *)
         let i1 = i + 1 in
         ...
       ]

       In order to do this, we keep track of the fresh variables introduced since
       the call to [index_mut].
    *)
    let rec update (fresh_vars : FVarId.Set.t) (next : texpr) :
        (tpat * texpr * FVarId.Set.t) option * bool * texpr =
      match next.e with
      | Let (monadic', pat', bound, next') -> (
          (* Check if we are calling the backward function *)
          match is_call_to_back bound with
          | None -> (
              (* Continue *)
              let tpat_fvars = tpat_get_fvars pat' in
              let fresh_vars' = FVarId.Set.union fresh_vars tpat_fvars in
              let back_call, updated, next' = update fresh_vars' next' in
              (* Check if we already updated *)
              if updated then
                (back_call, updated, mk_opened_let monadic' pat' bound next')
              else
                (* Check if we found the backward call *)
                match back_call with
                | None ->
                    (* Nothing to do *)
                    (back_call, updated, mk_opened_let monadic' pat' bound next')
                | Some (back_pat, v, v_vars) ->
                    (* Check if the input value given to the backward call requires
                       variables that were introduced in this let-binding:
                       if yes, we insert it here, otherwise we insert it higher up *)
                    if
                      not
                        (FVarId.Set.is_empty
                           (FVarId.Set.inter v_vars tpat_fvars))
                    then
                      (* Insert here *)
                      let next' =
                        mk_opened_let true back_pat (mk_call_to_update v) next'
                      in
                      (back_call, true, mk_opened_let monadic' pat' bound next')
                    else
                      (* Do not insert here *)
                      ( back_call,
                        updated,
                        mk_opened_let monadic' pat' bound next' ))
          | Some v ->
              (* Ignore this let-binding and return information about the backward
               call, so that we can insert it before *)
              (Some (pat', v, texpr_get_fvars v), false, next'))
      | App (f, arg) -> (
          (* Check if this is the [ok (back v)] case *)
          match f.e with
          | Qualif
              {
                id =
                  AdtCons
                    { adt_id = TBuiltin TResult; variant_id = Some variant_id };
                _;
              }
            when variant_id = result_ok_id -> (
              (* Check if we are calling the backward function *)
              match is_call_to_back arg with
              | Some v ->
                  (* Introduce the backward call here (there is no point in moving it up higher).
                     Note that it's ok to output [None] for the information about the backward
                     call: the option will be matched on only if the boolean [updated] is false. *)
                  (None, true, mk_call_to_update v)
              | None -> (None, false, next))
          | _ -> (None, false, next))
      | _ ->
          (* Stop *)
          (None, false, next)
    in
    (* Update *)
    let back_call, updated, next = update FVarId.Set.empty e2 in
    (* Check if we managed to update: if no, we need to insert the call to [update] here *)
    if updated then next
    else
      match back_call with
      | None ->
          (* Could not find the call to the backward function: reconstruct the expression *)
          mk_opened_let monadic pat e1 e2
      | Some (back_pat, back_v, _) ->
          mk_opened_let true back_pat (mk_call_to_update back_v) next
  in

  object (self)
    inherit [_] map_expr

    method! visit_Let env monadic pat e1 e2 =
      (* Update the first expression *)
      let e1 = self#visit_texpr env e1 in
      (* Update the second expression *)
      let e2 = self#visit_texpr env e2 in
      (* Check if the current let-binding is a call to an index function *)
      let e1_app, e1_args = destruct_apps e1 in
      match (pat.pat, e1_app.e, e1_args) with
      | ( (* let (_, back) = ... *)
          PAdt
            {
              variant_id = None;
              fields =
                [ { pat = PIgnored; _ }; { pat = POpen (back_var, _); _ } ];
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
            ^ texpr_to_string ctx { e = Let (monadic, pat, e1, e2); ty = e2.ty }];

          (* Attempt to simplify the let-binding.

             We first check that there is only a single use of the backward
             function. TODO: generalize
          *)
          let count = ref 0 in
          let count_visitor =
            object
              inherit [_] iter_expr

              method! visit_fvar_id _ fid =
                if fid = back_var.id then count := !count + 1 else ()
            end
          in
          count_visitor#visit_texpr () e2;
          if !count = 1 then
            (try_simplify monadic pat e1 e2 back_var is_array index_generics a i)
              .e
          else (mk_opened_let monadic pat e1 e2).e
      | _ -> (mk_opened_let monadic pat e1 e2).e
  end

let simplify_array_slice_update =
  lift_expr_map_visitor simplify_array_slice_update_visitor

(** Decompose let-bindings by introducing intermediate let-bindings.

    This is a utility function: see {!decompose_monadic_let_bindings} and
    {!decompose_nested_let_patterns}.

    [decompose_monadic]: always decompose a monadic let-binding
    [decompose_nested_patterns]: decompose the nested patterns *)
let decompose_let_bindings_visitor (decompose_monadic : bool)
    (decompose_nested_patterns : bool) (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in

  (* Set up the var id generator *)
  let mk_fresh (ty : ty) : tpat * texpr =
    let vid = ctx.fresh_fvar_id () in
    let tmp : fvar = { id = vid; basename = None; ty } in
    let ltmp = mk_tpat_from_fvar None tmp in
    let rtmp = mk_texpr_from_fvar tmp in
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
  let decompose_pat (lv : tpat) : (tpat * texpr) list * tpat =
    let patterns = ref [] in

    (* We decompose patterns *inside* other patterns.
       The boolean [inside] allows us to remember if we dived into a
       pattern already *)
    let visit_pats =
      object
        inherit [_] map_tpat as super

        method! visit_tpat (inside : bool) (pat : tpat) : tpat =
          match pat.pat with
          | PConstant _ | POpen _ | PIgnored -> pat
          | PBound _ -> [%internal_error] span
          | PAdt _ ->
              if not inside then super#visit_tpat true pat
              else
                let ltmp, rtmp = mk_fresh pat.ty in
                let pat = super#visit_tpat false pat in
                patterns := (pat, rtmp) :: !patterns;
                ltmp
      end
    in

    let inside = false in
    let lv = visit_pats#visit_tpat inside lv in
    (!patterns, lv)
  in

  (* It is a very simple map *)
  object (self)
    inherit [_] map_expr as super

    method! visit_Let env monadic lv re next_e =
      (* Decompose the monadic let-bindings *)
      let monadic, lv, re, next_e =
        if (not monadic) || not decompose_monadic then (monadic, lv, re, next_e)
        else
          (* If monadic, we need to check if the left-value is a variable:
           * - if yes, don't decompose
           * - if not, make the decomposition in two steps
           *)
          match lv.pat with
          | POpen _ | PIgnored ->
              (* Variable: nothing to do *)
              (monadic, lv, re, next_e)
          | PBound _ -> [%internal_error] span
          | _ ->
              (* Not a variable: decompose if required *)
              (* Introduce a temporary variable to receive the value of the
               * monadic binding *)
              let ltmp, rtmp = mk_fresh lv.ty in
              (* Visit the next expression *)
              let next_e = self#visit_texpr env next_e in
              (* Create the let-bindings *)
              (monadic, ltmp, re, mk_opened_let false lv rtmp next_e)
      in
      (* Decompose the nested let-patterns *)
      let lv, next_e =
        if not decompose_nested_patterns then (lv, next_e)
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
    (decompose_nested_patterns : bool) =
  lift_expr_map_visitor
    (decompose_let_bindings_visitor decompose_monadic decompose_nested_patterns)

(** Decompose monadic let-bindings.

    See the explanations in {!val:Config.decompose_monadic_let_bindings} *)
let decompose_monadic_let_bindings (ctx : ctx) (def : fun_decl) : fun_decl =
  decompose_let_bindings true false ctx def

(** Decompose the nested let patterns.

    See the explanations in {!val:Config.decompose_nested_let_patterns} *)
let decompose_nested_let_patterns (ctx : ctx) (def : fun_decl) : fun_decl =
  decompose_let_bindings false true ctx def

(** Unfold the monadic let-bindings to explicit matches. *)
let unfold_monadic_let_bindings_visitors (ctx : ctx) (def : fun_decl) =
  (* It is a very simple map *)
  object (_self)
    inherit [_] map_expr as super

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
        let err_vid = ctx.fresh_fvar_id () in
        let err_var : fvar =
          {
            id = err_vid;
            basename = Some ConstStrings.error_basename;
            ty = mk_error_ty;
          }
        in
        let err_pat = mk_tpat_from_fvar None err_var in
        let fail_pat = mk_result_fail_pat err_pat.pat lv.ty in
        let err_v = mk_texpr_from_fvar err_var in
        let fail_value = mk_result_fail_texpr def.item_meta.span err_v e.ty in
        let fail_branch = { pat = fail_pat; branch = fail_value } in
        let success_pat = mk_result_ok_pat lv in
        let success_branch = { pat = success_pat; branch = e } in
        let switch_body = Match [ fail_branch; success_branch ] in
        let e = Switch (re, switch_body) in
        (* Continue *)
        super#visit_expr env e
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

  let try_lift_expr (super_visit_e : texpr -> texpr) (visit_e : texpr -> texpr)
      (app : texpr) : bool * texpr =
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
    let app = [%add_loc] mk_apps span f args in
    if lift then (true, mk_to_result_texpr span app) else (false, app)
  in

  (* The map visitor *)
  object (self)
    inherit [_] map_expr as super

    method! visit_texpr env e0 =
      (* Check if this is an expression of the shape: [ok (f ...)] where
           `f` has been identified as a function which should be lifted. *)
      match destruct_apps e0 with
      | ( ({ e = Qualif { id = FunOrOp (Fun (Pure ToResult)); _ }; _ } as
           to_result_expr),
          [ app ] ) ->
          (* Attempt to lift the expression *)
          let lifted, app =
            try_lift_expr (super#visit_texpr env) (self#visit_texpr env) app
          in

          if lifted then app else [%add_loc] mk_app span to_result_expr app
      | { e = Let (monadic, pat, bound, next); ty }, [] ->
          let next = self#visit_texpr env next in
          (* Attempt to lift only if the let-expression is not already monadic *)
          let lifted, bound =
            if monadic then (true, self#visit_texpr env bound)
            else
              try_lift_expr (super#visit_texpr env) (self#visit_texpr env) bound
          in
          { e = Let (lifted, pat, bound, next); ty }
      | f, args ->
          let f = super#visit_texpr env f in
          let args = List.map (self#visit_texpr env) args in
          [%add_loc] mk_apps span f args
  end

let lift_pure_function_calls =
  lift_expr_map_visitor_with_state lift_pure_function_calls_visitor
    FVarId.Map.empty

let mk_fresh_fuel_var (ctx : ctx) : fvar =
  let id = ctx.fresh_fvar_id () in
  { id; basename = Some ConstStrings.fuel_basename; ty = mk_fuel_ty }

(** Add the fuel parameter, if necessary *)
let add_fuel_one (ctx : ctx) (loops : fun_decl LoopId.Map.t) (def : fun_decl) :
    fun_decl =
  [%ldebug fun_decl_to_string ctx def];
  let span = def.item_meta.span in
  (* Open the binders - this is more convenient *)
  let body =
    Option.map (fun b -> snd (open_all_fun_body ctx span b)) def.body
  in

  (* Introduce variables for the fuel and the state *)
  let effekt = def.signature.fwd_info.effect_info in
  let fuel0 =
    if effekt.can_diverge && !Config.use_fuel then Some (mk_fresh_fuel_var ctx)
    else None
  in
  let fuel =
    if effekt.can_diverge && !Config.use_fuel then Some (mk_fresh_fuel_var ctx)
    else None
  in
  let fuel_expr = Option.map mk_texpr_from_fvar fuel in
  let fuel_ty = Option.map (fun (v : fvar) -> v.ty) fuel in

  (* Update the signature *)
  let sg = def.signature in
  let sg =
    { sg with inputs = Option.to_list fuel_ty @ sg.inputs; output = sg.output }
  in
  let def = { def with signature = sg } in

  (* Small helper: update a call by adding the fuel and state parameters, return
     the updated expession together with the new state *)
  let update_call (f : texpr) (args : texpr list) (fuel : texpr option) : texpr
      =
    (* We need to update the type of the function *)
    let inputs, output = destruct_arrows f.ty in
    let fuel_ty = Option.map (fun (v : texpr) -> v.ty) fuel in
    let inputs = Option.to_list fuel_ty @ inputs in
    let f = { f with ty = mk_arrows inputs output } in

    (* Put everything together *)
    let e = [%add_loc] mk_apps span f (Option.to_list fuel @ args) in

    (* Return *)
    e
  in

  (* Update the body *)
  let rec update (fuel : texpr option) (e : texpr) : texpr =
    [%ldebug "e:\n" ^ texpr_to_string ctx e];
    match e.e with
    | FVar _ | BVar _ | CVar _ | Const _ -> e
    | App _ | Qualif _ ->
        (* We treat function calls, [Result::ok], [Result::fail] here *)
        let f, args = destruct_apps e in
        (* The arguments *must* be pure (which means they can not be stateful
         nor divergent) *)
        let args = List.map (update None) args in
        [%ldebug
          "- f: " ^ texpr_to_string ctx f ^ "\n- args:\n"
          ^ Print.list_to_string (texpr_to_string ctx) args];
        (* *)
        begin
          match f.e with
          | Qualif
              {
                id = FunOrOp (Fun (FromLlbc (FunId (FRegular fid'), lp_id)));
                _;
              } ->
              (* Lookup the decl *)
              let def' : fun_decl =
                match lp_id with
                | None -> FunDeclId.Map.find fid' ctx.fun_decls
                | Some lp_id ->
                    [%sanity_check] span (fid' = def.def_id);
                    LoopId.Map.find lp_id loops
              in
              [%ldebug
                "def'.signature.inputs:\n"
                ^ Print.list_to_string (ty_to_string ctx) def'.signature.inputs];
              (* This should be a full application *)
              [%sanity_check] span
                (List.length args = List.length def'.signature.inputs);

              (* Add the fuel and the state parameters. *)
              let effect' = def'.signature.fwd_info.effect_info in
              [%sanity_check] span
                ((not effect'.can_diverge) || (not !Config.use_fuel)
               || Option.is_some fuel);
              let fuel = if effect'.can_diverge then fuel else None in
              let call = update_call f args fuel in
              call
          | _ -> [%add_loc] mk_apps span f args
        end
    | Lambda _ -> e
    | Let (monadic, lv, re, next) ->
        (* Is it a function/loop call? *)
        let f, args = destruct_apps re in
        begin
          match f.e with
          | Qualif
              {
                id = FunOrOp (Fun (FromLlbc (FunId (FRegular fid'), lp_id)));
                _;
              } ->
              (* Lookup the decl *)
              let def' : fun_decl =
                match lp_id with
                | None -> FunDeclId.Map.find fid' ctx.fun_decls
                | Some lp_id ->
                    [%sanity_check] span (fid' = def.def_id);
                    LoopId.Map.find lp_id loops
              in
              (* This should be a full application *)
              [%sanity_check] span
                (List.length args = List.length def'.signature.inputs);

              (* Add the fuel and the state parameters. *)
              let call =
                let effect' = def'.signature.fwd_info.effect_info in
                let fuel' = if effect'.can_diverge then fuel else None in

                [%sanity_check] span
                  ((not effect'.can_diverge) || (not !Config.use_fuel)
                 || Option.is_some fuel');

                update_call f args fuel'
              in

              (* Update the let binding *)
              let next = update fuel next in
              mk_opened_let monadic lv call next
          | _ ->
              let re = update fuel re in
              let next = update fuel next in
              mk_opened_let monadic lv re next
        end
    | Switch (scrut, If (e1, e2)) ->
        (* The scrutinee must be pure *)
        let scrut = update None scrut in
        (* *)
        let e1 = update fuel e1 in
        let e2 = update fuel e2 in
        { e = Switch (scrut, If (e1, e2)); ty = e1.ty }
    | Switch (scrut, Match branches) ->
        (* The scrutinee must be pure *)
        let scrut = update None scrut in
        (* *)
        let branches =
          List.map
            (fun (b : match_branch) -> { b with branch = update fuel b.branch })
            branches
        in
        (* *)
        {
          e = Switch (scrut, Match branches);
          ty = (List.hd branches).branch.ty;
        }
    | Loop _ ->
        (* Loops should have been eliminated by then *)
        [%internal_error] span
    | StructUpdate _ -> e
    | Meta (m, e') -> mk_emeta m e'
    | EError _ -> e
  in
  let body =
    Option.map
      (fun (body : fun_body) ->
        let { body; inputs } = body in
        (* Update the body *)
        let body = update fuel_expr body in
        (* Wrap it in a match over the fuel if necessary *)
        let body, fuel_input =
          if effekt.is_rec && !Config.use_fuel then
            ( wrap_in_match_fuel span (Option.get fuel0).id (Option.get fuel).id
                ~close:false body,
              fuel0 )
          else (body, fuel)
        in
        (* Update the inputs *)
        let inputs =
          let fuel_pat = Option.map (mk_tpat_from_fvar None) fuel_input in
          Option.to_list fuel_pat @ inputs
        in
        (* *)
        { body; inputs })
      body
  in

  (* Close the binders *)
  let body = Option.map (close_all_fun_body span) body in
  { def with body }

let add_fuel (ctx : ctx) (trans : pure_fun_translation) : pure_fun_translation =
  let loops_map =
    LoopId.Map.of_list
      (List.map (fun (f : fun_decl) -> (Option.get f.loop_id, f)) trans.loops)
  in

  (* Add the fuel and the state *)
  let f = add_fuel_one ctx loops_map trans.f in
  let loops = List.map (add_fuel_one ctx loops_map) trans.loops in

  (* Decompose the monadic let-bindings if necessary (Coq needs this) *)
  let f, loops =
    if !Config.decompose_monadic_let_bindings then
      let f = decompose_monadic_let_bindings ctx f in
      let loops = List.map (decompose_monadic_let_bindings ctx) loops in
      (f, loops)
    else (f, loops)
  in

  (* *)
  { f; loops }

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
let merge_let_app_then_decompose_tuple_visitor (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in
  object (self)
    inherit [_] map_expr

    method! visit_Let env monadic0 pat0 bound0 next0 =
      let bound0 = self#visit_texpr env bound0 in
      (* Check if we need to merge two let-bindings *)
      if is_pat_open pat0 then
        let var0, _ = [%add_loc] as_pat_open span pat0 in
        match next0.e with
        | Let (false, pat1, { e = FVar var_id; _ }, next1) when var_id = var0.id
          -> begin
            (* Check if we are decomposing a tuple *)
            if is_pat_tuple pat1 then
              (* Introduce fresh variables for all the ignored variables
                   to make sure we can turn the pattern into an expression *)
              let pat1 =
                tpat_replace_ignored_vars_with_free_vars ctx.fresh_fvar_id pat1
              in
              let pat1_expr = Option.get (tpat_to_texpr span pat1) in
              (* Register the mapping from the variable we remove to the expression *)
              let env = FVarId.Map.add var0.id pat1_expr env in
              (* Continue *)
              let next1 = self#visit_texpr env next1 in
              Let (monadic0, pat1, bound0, next1)
            else
              let next0 = self#visit_texpr env next0 in
              Let (monadic0, pat0, bound0, next0)
          end
        | _ ->
            let next0 = self#visit_texpr env next0 in
            Let (monadic0, pat0, bound0, next0)
      else
        let next0 = self#visit_texpr env next0 in
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

(** Returns true if the continuations listed in [loop_conts] are used in a
    chained manner.

    For instance, given [loop_conts = {f0, f1}], they are in:
    {[
      let x1 = f0 x0 in
      f1 x1
    ]}
    but not in:
    {[
      f0 x0, f1 x1
    ]}

    We do this by doing a (slightly imprecise) control-flow analysis. *)
let expr_chains_loop_conts span (ctx : ctx) (loop_vars : FVarId.Set.t)
    (e : texpr) : bool =
  let flatten_set_list (s : FVarId.Set.t list) : FVarId.Set.t =
    List.fold_left (fun s0 s1 -> FVarId.Set.union s0 s1) FVarId.Set.empty s
  in
  let flatten_set_list_opt (sl : FVarId.Set.t list option) : FVarId.Set.t =
    match sl with
    | None -> FVarId.Set.empty
    | Some sl -> flatten_set_list sl
  in
  let flatten_set_list_opt_list (sl : FVarId.Set.t list option list) :
      FVarId.Set.t =
    let sl = List.flatten (List.filter_map (fun x -> x) sl) in
    flatten_set_list sl
  in
  let merge_sets_lists (sl : FVarId.Set.t list list) : FVarId.Set.t list =
    (* Attempt to combine the sets if the lists all have the same length,
       otherwise group everything in a single set *)
    match sl with
    | [] -> [ FVarId.Set.empty ]
    | s :: sl ->
        let n = List.length s in
        if List.for_all (fun s -> List.length s = n) sl then
          let rec merge sl =
            match sl with
            | [] -> s
            | s :: sl ->
                let s' = merge sl in
                List.map
                  (fun (s, s') -> FVarId.Set.union s s')
                  (List.combine s s')
          in
          merge sl
        else [ flatten_set_list (List.flatten (s :: sl)) ]
  in
  let merge_sets_opt_lists (sl : FVarId.Set.t list option list) :
      FVarId.Set.t list option =
    let sl = List.filter_map (fun x -> x) sl in
    if sl = [] then None else Some (merge_sets_lists sl)
  in
  let extend_env (env : FVarId.Set.t FVarId.Map.t) (pat : tpat)
      (deps : FVarId.Set.t) : FVarId.Set.t FVarId.Map.t =
    let fvars = tpat_get_fvars pat in
    FVarId.Map.add_list
      (List.map (fun fid -> (fid, deps)) (FVarId.Set.elements fvars))
      env
  in
  let rec check (env : FVarId.Set.t FVarId.Map.t) (e : texpr) :
      FVarId.Set.t list option =
    match e.e with
    | FVar fid -> (
        if FVarId.Set.mem fid loop_vars then Some [ FVarId.Set.singleton fid ]
        else
          match FVarId.Map.find_opt fid env with
          | None -> Some [ FVarId.Set.empty ]
          | Some deps -> Some [ deps ])
    | BVar _ -> [%internal_error] span
    | CVar _ | Const _ | Qualif _ | EError _ -> Some [ FVarId.Set.empty ]
    | App _ -> (
        (* Ignore the continues, pay attention to structures *)
        let f, args = destruct_apps e in
        match f.e with
        | Qualif
            {
              id =
                AdtCons { adt_id = TBuiltin TLoopResult; variant_id = Some id };
              _;
            }
          when id = loop_result_continue_id -> None
        | Qualif { id = AdtCons { adt_id = _; variant_id = None }; _ } ->
            let args = List.map (check env) args in
            if List.for_all Option.is_some args then
              Some (List.map (fun x -> flatten_set_list (Option.get x)) args)
            else Some [ flatten_set_list_opt_list args ]
        | _ ->
            let f = check env f in
            let args = List.map (check env) args in
            Some [ flatten_set_list_opt_list (f :: args) ])
    | Lambda _ ->
        let _, _, body = open_lambdas ctx span e in
        check env body
    | Let (_, pat, bound, next) ->
        let bound = flatten_set_list_opt (check env bound) in
        let _, pat, next = open_binder ctx span pat next in
        (* Update the environment - this is not very precise *)
        let env = extend_env env pat bound in
        check env next
    | Switch (scrut, switch) -> (
        let scrut = flatten_set_list_opt (check env scrut) in
        match switch with
        | If (e0, e1) ->
            let e0 = check env e0 in
            let e1 = check env e1 in
            merge_sets_opt_lists [ e0; e1 ]
        | Match branches ->
            let branches =
              List.map
                (fun ({ pat; branch } : match_branch) ->
                  let _, pat, branch = open_binder ctx span pat branch in
                  let env = extend_env env pat scrut in
                  check env branch)
                branches
            in
            merge_sets_opt_lists branches)
    | Loop { inputs; loop_body = { inputs = input_pats; loop_body }; _ } ->
        let inputs = List.map (check env) inputs in
        let _, input_pats, loop_body =
          open_binders ctx span input_pats loop_body
        in
        let env =
          List.fold_left2
            (fun env pat bound ->
              match bound with
              | None -> env
              | Some bound -> extend_env env pat (flatten_set_list bound))
            env input_pats inputs
        in
        check env loop_body
    | StructUpdate { struct_id = _; init; updates } ->
        let init =
          match init with
          | None -> None
          | Some init -> check env init
        in
        let updates = List.map (fun (_, x) -> check env x) updates in
        Some [ flatten_set_list_opt_list (init :: updates) ]
    | Meta (_, e) -> check env e
  in
  let outputs = check FVarId.Map.empty e in
  match outputs with
  | None -> false
  | Some outputs -> List.for_all (fun s -> FVarId.Set.cardinal s > 1) outputs

(** Simplify the outputs of a loop. *)
let simplify_loop_output_conts (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in

  (* Small helper to update the expression *after* the loop while detecting
     which simplifications should be done on the outputs.

     Returns the updated expression and a map from the freshly introduced
     fvar ids to their expressions. Those fresh fvars are continuations that
     should be added to the loop output.

     For now we do something simple and we don't check whether we're introducing
     continuations which collide each other: this is sound, but doesn't lead to
     the best output in the presence of branching after the loop.
  *)
  let simplify_in (before_loop_vars : FVarId.Set.t) (loop_vars : FVarId.Set.t)
      (loop_conts : FVarId.Set.t) (e : texpr) :
      (FVarId.id * texpr) list * (FVarId.id * texpr) list * texpr =
    let all_loop_outputs = FVarId.Set.union loop_vars loop_conts in
    let all_vars = FVarId.Set.union before_loop_vars all_loop_outputs in
    let fresh_values = ref [] in
    let fresh_conts = ref [] in
    let fresh_output_var ~(is_value : bool) (e : texpr) : texpr =
      let fid = ctx.fresh_fvar_id () in
      let fv : texpr = { e = FVar fid; ty = e.ty } in
      let fresh = if is_value then fresh_values else fresh_conts in
      fresh := (fid, e) :: !fresh;
      fv
    in
    let rec simplify (e : texpr) : texpr =
      match e.e with
      | FVar _
      | BVar _
      | CVar _
      | Const _
      | EError _
      | StructUpdate _
      | Qualif _
      | Switch _ (* let's ignore those for now *)
      | Loop _ -> e
      | Let (monadic, pat, bound, next) ->
          let bound = simplify bound in
          let _, pat, next = open_binder ctx span pat next in
          let next = simplify next in
          mk_closed_let span monadic pat bound next
      | Meta (m, e) -> mk_emeta m (simplify e)
      | Lambda _ ->
          (* One of the important cases: this might be the composition of a
             backward function. We check if all the free variables appearing
             in its body are loop outputs: if yes, it is likely a backward
             function which composes loop outputs

             We also check whether it's worth merging the outputs.
             For instance, if we have something like this:
             {[
               let (..., y, back0, back1) <- loop ...
               let back := fun x ->
                 back1 (Cons (y, back0 x))
               ...
             ]}
             then we introduce an output for [back] because it allows merging
             [back0], [back1] and [y] in a single output.

             However, if we have something like this:
             {[
               let (..., back0, back1) <- loop ...
               let back := fun (x, y) ->
                 (back0 x, back1 y)
               ...
             ]}
             then we don't merge anything, because it would only group
             several backward functions into a single backward functions,
             potentially limiting further optimizations like in
             [loop_to_recursive].

             We detect this by doing a flow analysis.
          *)
          if expr_chains_loop_conts span ctx all_loop_outputs e then (
            (* It is a subset: introduce a fresh output var *)
            [%ldebug
              "Simplifying output:\n" ^ texpr_to_string ctx e ^ "\n- ty: "
              ^ ty_to_string ctx e.ty];
            fresh_output_var ~is_value:false e)
          else
            (* No: dive into the lambda as there might be sub-expressions we can isolate *)
            let _, patl, body = open_lambdas ctx span e in
            let body = simplify body in
            close_lambdas span patl body
      | App _ -> (
          (* Other important case: try to simplify calls to backward functions *)
          let f, args = destruct_apps e in
          (* Is it a call to a backward function? *)
          match f.e with
          | FVar fid when FVarId.Set.mem fid loop_conts ->
              (* Check if all the free variables which appear in the call
                 are loop outputs or were introduced before the loop: if yes,
                 simplify. *)
              let fvars = texpr_get_fvars e in
              if FVarId.Set.subset fvars all_vars then (
                (* Simplify: introduce a fresh output var *)
                [%ldebug
                  "Simplifying call to backward function:\n"
                  ^ texpr_to_string ctx e ^ "\n- ty: " ^ ty_to_string ctx e.ty];
                fresh_output_var ~is_value:true e)
              else [%add_loc] mk_apps span (simplify f) (List.map simplify args)
          | _ -> [%add_loc] mk_apps span (simplify f) (List.map simplify args))
    in
    let e = simplify e in
    (List.rev !fresh_values, List.rev !fresh_conts, e)
  in

  let update_loop_body (num_filtered_outputs : int)
      (keep_outputs : (bool * FVarId.id option) list)
      (fresh_output_values : texpr list) (fresh_output_conts : texpr list)
      (continue_ty : ty) (break_ty : ty) (body : loop_body) : loop_body =
    let _, body = open_loop_body ctx span body in

    (* Introduce an intermediate let-binding for a loop.

       TODO: is this really useful? Can it happen that we find an loop
       which is not bound by a let-binding? If useful, we should also use
       it elsewhere.
    *)
    let rebind_loop (loop : loop) : texpr =
      let fvars = List.map (mk_fresh_fvar ctx) loop.output_tys in
      let pats = List.map (mk_tpat_from_fvar None) fvars in
      let pat = mk_simpl_tuple_pat pats in
      let outputs = List.map mk_texpr_from_fvar fvars in
      let output = mk_simpl_tuple_texpr span outputs in
      let bound : texpr = { e = Loop loop; ty = mk_result_ty output.ty } in
      mk_closed_let span true pat bound (mk_break_texpr span continue_ty output)
    in

    let rec update (e : texpr) : texpr =
      match e.e with
      | FVar _ | BVar _ | CVar _ | Const _ | Lambda _ | StructUpdate _ ->
          (* Shouldn't happen *)
          [%internal_error] span
      | Loop loop ->
          (* Introduce a let-binding and simplify (the simplification is implemented
             for the App case, below). *)
          update (rebind_loop loop)
      | EError _ -> e
      | App _ | Qualif _ ->
          (* This might be a break or a continue *)
          begin
            match
              opt_destruct_loop_result_decompose_outputs ctx span
                ~intro_let:true e
            with
            | None -> e
            | Some ({ variant_id; args = outputs; _ }, rebind) ->
                if variant_id = loop_result_break_id then
                  (* Filter while computing the map from output var index to output expression *)
                  let outputs, map =
                    List.split
                      (List.map
                         (fun (o, (keep, fid)) ->
                           let b =
                             match fid with
                             | Some fid -> Some (fid, o)
                             | None -> None
                           in
                           let o = if keep then Some o else None in
                           (o, b))
                         (List.combine outputs keep_outputs))
                  in
                  let outputs = List.filter_map (fun x -> x) outputs in
                  let output_values, output_conts =
                    Collections.List.split_at outputs num_filtered_outputs
                  in

                  (* Compute the additional outputs: we need to update the free variables which
                     appear in the continuation (and are output by the loop) with their actual
                     expression. *)
                  let map =
                    FVarId.Map.of_list (List.filter_map (fun x -> x) map)
                  in
                  let visitor =
                    object
                      inherit [_] map_expr

                      method! visit_FVar _ fid =
                        match FVarId.Map.find_opt fid map with
                        | None -> FVar fid
                        | Some e -> e.e
                    end
                  in
                  let fresh_output_values =
                    List.map (visitor#visit_texpr ()) fresh_output_values
                  in
                  let fresh_output_conts =
                    List.map (visitor#visit_texpr ()) fresh_output_conts
                  in

                  let outputs =
                    mk_simpl_tuple_texpr span
                      (output_values @ fresh_output_values @ output_conts
                     @ fresh_output_conts)
                  in
                  rebind (mk_break_texpr span continue_ty outputs)
                else if variant_id = loop_result_continue_id then
                  (* We leave the expression unchanged but have to modify its type *)
                  rebind
                    (mk_continue_texpr span
                       (mk_simpl_tuple_texpr span outputs)
                       break_ty)
                else (
                  [%sanity_check] span (variant_id = loop_result_fail_id);
                  let arg = mk_simpl_tuple_texpr span outputs in
                  rebind
                    (mk_loop_result_fail_texpr span continue_ty break_ty arg))
          end
      | Let (monadic, pat, bound, next) ->
          (* No need to update the bound expression *)
          let _, pat, next = open_binder ctx span pat next in
          let next = update next in
          mk_closed_let span monadic pat bound next
      | Switch (scrut, switch) ->
          (* No need to update the scrutinee *)
          let switch =
            match switch with
            | If (e0, e1) -> If (update e0, update e1)
            | Match branches ->
                let branches =
                  List.map
                    (fun ({ pat; branch } : match_branch) ->
                      let _, pat, branch = open_binder ctx span pat branch in
                      let branch = update branch in
                      let pat, branch = close_binder span pat branch in
                      { pat; branch })
                    branches
                in
                Match branches
          in
          [%add_loc] mk_switch span scrut switch
      | Meta (m, e) -> mk_emeta m (update e)
    in

    let body = { body with loop_body = update body.loop_body } in
    close_loop_body span body
  in

  let fvarset_union (vars : FVarId.Set.t) (vars' : fvar FVarId.Map.t) :
      FVarId.Set.t =
    FVarId.Set.union vars (FVarId.Set.of_list (FVarId.Map.keys vars'))
  in

  let rec update (vars : FVarId.Set.t) (e : texpr) : texpr =
    match e.e with
    | FVar _
    | BVar _
    | CVar _
    | Const _
    | App _
    | Qualif _
    | StructUpdate _
    | EError _ -> e
    | Loop _ ->
        (* A loop should always be bound by a let *)
        [%internal_error] span
    | Lambda _ ->
        let vars', pats, body = open_lambdas ctx span e in
        let vars = fvarset_union vars vars' in
        let body = update vars body in
        mk_closed_lambdas span pats body
    | Meta (meta, inner) -> mk_emeta meta (update vars inner)
    | Switch (scrut, switch) ->
        let scrut = update vars scrut in
        let switch, ty =
          match switch with
          | If (e0, e1) ->
              let e0 = update vars e0 in
              let e1 = update vars e1 in
              (If (e0, e1), e0.ty)
          | Match branches ->
              let branches =
                List.map
                  (fun ({ pat; branch } : match_branch) ->
                    let vars', pat, branch = open_binder ctx span pat branch in
                    let vars = fvarset_union vars vars' in
                    let branch = update vars branch in
                    let pat, branch = close_binder span pat branch in
                    { pat; branch })
                  branches
              in
              let ty = (List.hd branches).branch.ty in
              (Match branches, ty)
        in
        { e = Switch (scrut, switch); ty }
    | Let (monadic, pat, bound, next) -> (
        [%ldebug "About to simplify the outputs of:\n" ^ texpr_to_string ctx e];
        let vars', pat, next = open_binder ctx span pat next in
        let vars = fvarset_union vars vars' in
        [%ldebug
          "After opening the binders in the let:\n"
          ^ texpr_to_string ctx { e with e = Let (monadic, pat, bound, next) }];
        (* Check if we are binding a loop *)
        match bound.e with
        | Loop loop ->
            (* The output should be a tuple containing first the output values,
               then the output continuations *)
            let pats = try_destruct_tuple_tpat span pat in
            let as_pat_open_or_ignored (pat : tpat) : fvar option =
              match pat.pat with
              | POpen (fv, _) -> Some fv
              | PIgnored -> None
              | _ -> [%internal_error] span
            in
            let pvars = List.map as_pat_open_or_ignored pats in
            let to_set pvars =
              FVarId.Set.of_list
                (List.filter_map (Option.map (fun (v : fvar) -> v.id)) pvars)
            in
            let loop_varset = to_set pvars in
            [%ldebug
              "\n- loop.num_output_values: "
              ^ string_of_int loop.num_output_values
              ^ "- pats: "
              ^ Print.list_to_string (tpat_to_string ctx) pats];
            [%sanity_check] span (loop.num_output_values <= List.length pvars);
            let loop_conts =
              to_set (Collections.List.drop loop.num_output_values pvars)
            in

            (* Analyze the next expression to detect potential simplifications *)
            let fresh_output_values, fresh_output_conts, next =
              simplify_in vars loop_varset loop_conts next
            in
            let fresh_outputs = fresh_output_values @ fresh_output_conts in
            [%ldebug
              "After calling simplify_in:" ^ "\n- fresh_output_values:\n"
              ^ Print.list_to_string ~sep:"\n" (texpr_to_string ctx)
                  (List.map snd fresh_output_values)
              ^ "\n- fresh_output_conts:\n"
              ^ Print.list_to_string ~sep:"\n" (texpr_to_string ctx)
                  (List.map snd fresh_output_conts)];

            (* Filter the output variables which are now useless *)
            let used_vars = texpr_get_fvars next in
            let keep_varsl =
              List.map
                (fun (v : fvar option) ->
                  match v with
                  | None -> (false, None)
                  | Some v ->
                      let keep = FVarId.Set.mem v.id used_vars in
                      (keep, Some v.id))
                pvars
            in

            (* Update the loop body *)
            let continue_ty =
              mk_simpl_tuple_ty (List.map (fun (e : texpr) -> e.ty) loop.inputs)
            in
            let filter outputs =
              List.filter_map
                (fun (keep, ty) -> if keep then Some ty else None)
                outputs
            in
            let output_value_tys, output_conts_tys =
              Collections.List.split_at
                (List.combine (List.map fst keep_varsl) loop.output_tys)
                loop.num_output_values
            in
            let filt_output_value_tys = filter output_value_tys in
            let output_tys =
              let tys =
                filt_output_value_tys
                @ List.map
                    (fun ((_, e) : _ * texpr) -> e.ty)
                    fresh_output_values
                @ filter output_conts_tys
                @ List.map (fun ((_, e) : _ * texpr) -> e.ty) fresh_output_conts
              in
              (* There may be only one remaining output, which has type tuple:
                 if it is the case we need to simplify it *)
              match tys with
              | [ ty ] -> try_destruct_tuple span ty
              | _ -> tys
            in

            let break_ty = mk_simpl_tuple_ty output_tys in
            let loop_body =
              let num_filtered_outputs = List.length filt_output_value_tys in
              let fresh_output_values = List.map snd fresh_output_values in
              let fresh_output_conts = List.map snd fresh_output_conts in
              [%ldebug
                "About to update the loop body:" ^ "\n- keep_varsl: "
                ^ Print.list_to_string
                    (Print.pair_to_string Print.bool_to_string
                       (Print.option_to_string FVarId.to_string))
                    keep_varsl
                ^ "\n- fresh_output_values:\n"
                ^ Print.list_to_string ~sep:"\n" (texpr_to_string ctx)
                    fresh_output_values
                ^ "\n- fresh_output_conts:\n"
                ^ Print.list_to_string ~sep:"\n" (texpr_to_string ctx)
                    fresh_output_conts];
              update_loop_body num_filtered_outputs keep_varsl
                fresh_output_values fresh_output_conts continue_ty break_ty
                loop.loop_body
            in

            (* Update the signature *)
            let num_output_values =
              List.length
                (List.filter fst
                   (Collections.List.prefix loop.num_output_values keep_varsl))
            in
            let loop = { loop with num_output_values; output_tys; loop_body } in
            let loop : texpr =
              { e = Loop loop; ty = mk_loop_result_ty continue_ty break_ty }
            in

            (* Reconstruct the let-binding *)
            let filtered_pats =
              List.filter_map
                (fun ((keep, _), pat) -> if keep then Some pat else None)
                (List.combine keep_varsl pats)
            in
            let new_pats =
              List.map
                (fun ((id, e) : _ * texpr) ->
                  ({ id; basename = Some "back"; ty = e.ty } : fvar))
                fresh_outputs
            in
            let new_pats = List.map (mk_tpat_from_fvar None) new_pats in
            let pats = filtered_pats @ new_pats in
            let pat = mk_simpl_tuple_pat pats in
            mk_closed_let span monadic pat loop next
        | _ ->
            (* No need to update the bound expression *)
            let next = update vars next in
            mk_closed_let span monadic pat bound next)
  in
  let body =
    Option.map
      (fun body ->
        let fvars, body = open_fun_body ctx span body in
        let fvars = FVarId.Set.of_list (FVarId.Map.keys fvars) in
        let body = { body with body = update fvars body.body } in
        close_fun_body span body)
      def.body
  in
  { def with body }

type loop_rel = {
  inputs : texpr list list;
  outputs : texpr list list;
  used_fvars : FVarId.Set.t;
      (** The set of fvars which are actually used by the loop (not simply
          transmitted to the continues *)
}

let loop_rel_to_string (ctx : ctx) (rel : loop_rel) : string =
  let { inputs; outputs; used_fvars } = rel in
  "{\n  inputs = "
  ^ Print.list_to_string (Print.list_to_string (texpr_to_string ctx)) inputs
  ^ ";\n  outputs = "
  ^ Print.list_to_string (Print.list_to_string (texpr_to_string ctx)) outputs
  ^ ";\n  used_fvars = "
  ^ FVarId.Set.to_string None used_fvars
  ^ "\n}"

(** Analyze a loop body to compute the relationship between its input and its
    outputs.

    Remark: we expect the loop body to have been opened (only the *inputs* of
    the loop body, it is fine if the other variables are bound). *)
let compute_loop_input_output_rel (span : Meta.span) (ctx : ctx) (loop : loop) :
    loop_rel =
  [%sanity_check] span (List.for_all tpat_is_open loop.loop_body.inputs);

  let body = loop.loop_body in
  let inputs = List.map (fun _ -> ref []) body.inputs in
  let outputs = List.map (fun _ -> ref []) loop.output_tys in
  let used_fvars = ref FVarId.Set.empty in
  let inputs_fvars = tpats_get_fvars body.inputs in

  let visitor =
    object (self)
      inherit [_] iter_expr as super

      method! visit_texpr env e =
        match e.e with
        | Loop loop ->
            (* We do not visit the inner loops *)
            List.iter (self#visit_texpr env) loop.inputs
        | App _ -> begin
            [%ldebug
              "- e.ty: " ^ ty_to_string ctx e.ty ^ "\n- e:\n"
              ^ texpr_to_string ctx e];
            match
              opt_destruct_loop_result_decompose_outputs ctx span
                ~intro_let:false e
            with
            | None ->
                (* We need to visit the sub-expressions *)
                super#visit_texpr env e
            | Some ({ variant_id; args; _ }, _) ->
                [%ldebug
                  "- outputs:\n"
                  ^ Print.list_to_string ~sep:"\n"
                      (fun el -> Print.list_to_string (texpr_to_string ctx) !el)
                      outputs
                  ^ "\n\n- args:\n"
                  ^ Print.list_to_string ~sep:"\n" (texpr_to_string ctx) args];

                if variant_id = loop_result_break_id then (
                  [%sanity_check] span (List.length outputs = List.length args);
                  (* Update the output map *)
                  List.iter
                    (fun (l, arg) -> l := arg :: !l)
                    (List.combine outputs args);
                  (* Also visit the arguments: we want to register the used variables *)
                  List.iter (self#visit_texpr env) args)
                else if variant_id = loop_result_continue_id then (
                  [%ldebug
                    "- inputs:\n"
                    ^ Print.list_to_string ~sep:"\n"
                        (fun el ->
                          Print.list_to_string (texpr_to_string ctx) !el)
                        inputs
                    ^ "\n\n- args:\n"
                    ^ Print.list_to_string ~sep:"\n" (texpr_to_string ctx) args];

                  (* There is a special case if the loop has a single input of type
                     unit *)
                  match loop.inputs with
                  | [ input ] when input.ty = mk_unit_ty ->
                      List.iter (fun l -> l := mk_unit_texpr :: !l) inputs
                  | _ ->
                      [%sanity_check] span
                        (List.length inputs = List.length args);
                      (* Update the input map *)
                      List.iter
                        (fun (l, arg) -> l := arg :: !l)
                        (List.combine inputs args))
                else (
                  [%sanity_check] span (variant_id = loop_result_fail_id);
                  (* Also visit the arguments: we want to register the used variables *)
                  List.iter (self#visit_texpr env) args)
          end
        | _ -> super#visit_texpr env e

      method! visit_fvar_id _ fid = used_fvars := FVarId.Set.add fid !used_fvars
    end
  in
  visitor#visit_texpr () body.loop_body;

  let inputs = List.map (fun l -> List.rev !l) inputs in
  let outputs = List.map (fun l -> List.rev !l) outputs in
  [%ldebug
    "About to explore inputs/outputs to compute the used variables:"
    ^ "\n- inputs: "
    ^ Print.list_to_string (Print.list_to_string (texpr_to_string ctx)) inputs
    ^ "\n- outputs: "
    ^ Print.list_to_string (Print.list_to_string (texpr_to_string ctx)) outputs];

  (* We took care to not explore the outputs when registering the used variables,
     but it is actually too restrictice, because some inputs might be used in
     backward functions.

     For instance:
     loop (fun x y ->
       if b then
         ...
         let y' = ... y in // we mark y as marked because of this
         ...
         continue (x, y')
       else
         ...
         break (fun tl -> Cons (x, tl)) // we want to mark x as used because of this

     For this reason we explore the outputs. If we find an expression which is
     stricly more complex than simply a variable, we register the variables it
     contains as used.
  *)
  let visitor =
    object
      inherit [_] iter_expr
      method! visit_fvar_id _ fid = used_fvars := FVarId.Set.add fid !used_fvars
    end
  in
  let rec explore (e : texpr) =
    match e.e with
    | FVar _ | BVar _ | CVar _ | Const _ | EError _ -> ()
    | App _ | Lambda _ | Qualif _ | Let _ | Switch _ | StructUpdate _ ->
        visitor#visit_texpr () e
    | Loop _ -> [%internal_error] span
    | Meta (_, inner) -> explore inner
  in
  List.iter (List.iter explore) inputs;
  List.iter (List.iter explore) outputs;

  (* Filter the used variables to only preserve the inputs *)
  let used_fvars =
    FVarId.Set.filter (fun fid -> FVarId.Set.mem fid inputs_fvars) !used_fvars
  in

  (* *)
  { inputs; outputs; used_fvars }

(** Small helper: decompose a pattern if it is a variable or an ignored pattern
    of type tuple. Returns an optional substitution (if the pattern was a
    variable) *)
let decompose_tuple_pat span (ctx : ctx) (pat : tpat) :
    bool * tpat * (FVarId.id * texpr) option =
  if (is_pat_open pat || is_ignored_pat pat) && is_tuple_ty pat.ty then
    (* Decompose the pattern *)
    let pat, subst =
      let tys = [%add_loc] as_tuple_ty span pat.ty in
      if is_pat_open pat then
        (* Introduce auxiliary variables *)
        let fv, _ = [%add_loc] as_pat_open span pat in
        let fvars = List.map (mk_fresh_fvar ctx) tys in
        let pat =
          mk_simpl_tuple_pat (List.map (mk_tpat_from_fvar None) fvars)
        in
        let tuple =
          mk_simpl_tuple_texpr span (List.map mk_texpr_from_fvar fvars)
        in
        (pat, Some (fv.id, tuple))
      else
        (* Simply decompose into a tuple of ignored patterns *)
        (mk_simpl_tuple_pat (List.map mk_ignored_pat tys), None)
    in
    (true, pat, subst)
  else (false, pat, None)

let decompose_loop_outputs (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in
  let visitor =
    object (self)
      inherit [_] map_expr as super

      method! visit_Let env monadic pat bound next =
        match bound.e with
        | Loop _ ->
            (* Attempt to decompose the pattern *)
            let decompose, pat, subst = decompose_tuple_pat span ctx pat in
            if decompose then
              (* Update the bound expression first *)
              let bound = self#visit_texpr env bound in
              (* Register the substitution *)
              let env =
                match subst with
                | None -> env
                | Some (fid, tuple) -> FVarId.Map.add fid tuple env
              in
              (* Update the next expression *)
              let next = self#visit_texpr env next in
              (* Recreate the let-binding *)
              (mk_opened_let monadic pat bound next).e
            else super#visit_Let env monadic pat bound next
        | _ -> super#visit_Let env monadic pat bound next

      method! visit_FVar env fid =
        match FVarId.Map.find_opt fid env with
        | None -> FVar fid
        | Some e -> e.e
    end
  in

  let body =
    Option.map
      (fun body ->
        let _, body = open_all_fun_body ctx span body in
        let body =
          { body with body = visitor#visit_texpr FVarId.Map.empty body.body }
        in
        close_all_fun_body span body)
      def.body
  in
  { def with body }

(** We do several things.

    1. We filter the loop outputs which are not used.

    2. We filter the loop outputs which are actually equal to some of its
    inputs, while filtering the inputs which are equal throughout the execution
    of the loop (we do the latter only if [filter_constant_inputs] is [true] or
    if the input is actually not used within the loop body - we have this option
    because we want to filter those inputs *after* introducing auxiliary
    functions, if there are).

    For instance:
    {[
      let (i, y) =
        loop (fun i x ->
          if i < n then continue ((i + 1), y)
          else break (i, y)) i0 y0
      in
      ...

        ~>

      let i =
        loop (fun i x ->
          if i < n then continue (i + 1)
          else break i) i0
      in
      let y = y0 in
      ...
    ]}

    3. We filter the loop output backward functions which are the identity. *)
let filter_loop_useless_inputs_outputs (ctx : ctx)
    ~(filter_constant_inputs : bool) (def : fun_decl) =
  let span = def.item_meta.span in

  (* Helper to substitute the unchanged variables with their (constant)
     values in the loop body. *)
  let substitute_in_loop_body (subst : texpr FVarId.Map.t) (body : loop_body) :
      loop_body =
    let visitor =
      object
        inherit [_] map_expr

        method! visit_FVar _ fid =
          match FVarId.Map.find_opt fid subst with
          | None -> FVar fid
          | Some e -> e.e
      end
    in
    visitor#visit_loop_body () body
  in

  (* Helper to update the continue/breaks in a loop body *)
  let update_continue_break (keep_outputs : bool list) (keep_inputs : bool list)
      (continue_ty : ty) (break_ty : ty) (body : loop_body) : loop_body =
    let rec update (e : texpr) : texpr =
      match e.e with
      | FVar _ | BVar _ | CVar _ | Const _ | Lambda _ | StructUpdate _ | Loop _
        ->
          (* Shouldn't happen *)
          [%internal_error] span
      | EError _ -> e
      | App _ | Qualif _ ->
          (* This might be a break or a continue *)
          begin
            match
              opt_destruct_loop_result_decompose_outputs ctx span
                ~intro_let:true e
            with
            | None -> e
            | Some ({ variant_id; args = outputs; _ }, rebind) ->
                let filter keep el =
                  let el =
                    (* There is a special case if the loop has a single input of type unit *)
                    match body.inputs with
                    | [ pat ] when pat.ty = mk_unit_ty -> []
                    | _ ->
                        [%sanity_check] span (List.length keep = List.length el);
                        List.filter_map
                          (fun (keep, x) -> if keep then Some x else None)
                          (List.combine keep el)
                  in
                  mk_simpl_tuple_texpr span el
                in
                if variant_id = loop_result_break_id then
                  (* Filter *)
                  let outputs = filter keep_outputs outputs in
                  rebind (mk_break_texpr span continue_ty outputs)
                else if variant_id = loop_result_continue_id then
                  (* We leave the expression unchanged but have to modify its type *)
                  let inputs = filter keep_inputs outputs in
                  rebind (mk_continue_texpr span inputs break_ty)
                else (
                  [%sanity_check] span (variant_id = loop_result_fail_id);
                  let arg = mk_simpl_tuple_texpr span outputs in
                  rebind
                    (mk_loop_result_fail_texpr span continue_ty break_ty arg))
          end
      | Let (monadic, pat, bound, next) ->
          (* No need to update the bound expression *)
          let _, pat, next = open_binder ctx span pat next in
          let next = update next in
          mk_closed_let span monadic pat bound next
      | Switch (scrut, switch) ->
          (* No need to update the scrutinee *)
          let switch =
            match switch with
            | If (e0, e1) -> If (update e0, update e1)
            | Match branches ->
                let branches =
                  List.map
                    (fun ({ pat; branch } : match_branch) ->
                      let _, pat, branch = open_binder ctx span pat branch in
                      let branch = update branch in
                      let pat, branch = close_binder span pat branch in
                      { pat; branch })
                    branches
                in
                Match branches
          in
          [%add_loc] mk_switch span scrut switch
      | Meta (m, e) -> mk_emeta m (update e)
    in

    let inputs =
      List.filter_map
        (fun (keep, input) -> if keep then Some input else None)
        (List.combine keep_inputs body.inputs)
    in
    { inputs; loop_body = update body.loop_body }
  in

  (* Small helper: filter the variables which appear in [pat] and not in [next] *)
  let filter_useless (next : texpr) (pat : tpat) : tpat =
    let fvars = texpr_get_fvars next in

    let visitor =
      object
        inherit [_] map_tpat

        method! visit_POpen _ v mp =
          if FVarId.Set.mem v.id fvars then POpen (v, mp) else PIgnored

        method! visit_PBound _ _ _ = [%internal_error] span
      end
    in
    visitor#visit_tpat () pat
  in

  (* Small helper: update a loop body *)
  let update_loop (pat : tpat) (loop : loop) (next : texpr) :
      tpat * loop * texpr =
    let body = loop.loop_body in

    (* Analyze the body *)
    let rel = compute_loop_input_output_rel span ctx loop in

    [%ldebug
      "- used_inputs: "
      ^ FVarId.Set.to_string None rel.used_fvars
      ^ "\n- pat: " ^ tpat_to_string ctx pat ^ "\n- loop:\n"
      ^ loop_to_string ctx loop ^ "\n- next:\n" ^ texpr_to_string ctx next];

    (* We need to decompose the pattern, if it is a tuple, before attempting
       to destruct it below. *)
    let pat, next =
      let _, pat, subst = decompose_tuple_pat span ctx pat in
      let next =
        match subst with
        | None -> next
        | Some (fid, e) ->
            (* We need to update the next expression *)
            let visitor =
              object
                inherit [_] map_expr

                method! visit_FVar _ fid' =
                  if fid' = fid then e.e else FVar fid'
              end
            in
            visitor#visit_texpr () next
      in
      (pat, next)
    in

    (* We go through the inputs and identify those which are
       mapped to exactly themselves (i.e., remain unchanged throughout
       the loop). If [filter_constant_inputs] is [true] we filter them.
       Otherwise, we filter only the inputs which are actually not used
       within the loop (and are just passed throughout the recursive calls).

       We then go through the outputs: for a given output, if all the expressions
       it is mapped to are actually the same, and this expression doesn't
       contain variables which are locally bound in the loop, it means that
       this output can be computed from the inputs of the loop only. If
       those inputs were filtered above, it means they are left unchanged
       throughout the loop and so that the output can be computed from
       the *initial* input. We thus filter it.
    *)
    [%ldebug tpat_to_string ctx pat];
    let output_vars = try_destruct_tuple_or_ignored_tpat span pat in
    let output_vars =
      List.map
        (fun (p : tpat) ->
          match p.pat with
          | POpen (v, _) -> Some v
          | PIgnored -> None
          | _ -> [%craise] span "Not an open binder or an ignored pattern")
        output_vars
    in
    let input_vars =
      List.map
        (fun (p : tpat) ->
          match p.pat with
          | POpen (v, _) -> Some v
          | PIgnored -> None
          | _ -> [%internal_error] span)
        body.inputs
    in
    let input_var_ids =
      List.map (Option.map (fun (fv : fvar) -> fv.id)) input_vars
    in

    (* First, the inputs *)
    let non_constant_inputs =
      List.map
        (fun ((fv, el) : fvar option * texpr list) ->
          (* Check if all the expressions are actually exactly the
                     input expression *)
          match fv with
          | None -> false
          | Some fv ->
              not
                (List.for_all
                   (fun (e : texpr) ->
                     match e.e with
                     | FVar fid -> fid = fv.id
                     | _ -> false)
                   el))
        (List.combine input_vars rel.inputs)
    in
    let used_inputs =
      List.map
        (fun (fv : fvar option) ->
          match fv with
          | None -> false
          | Some fv -> FVarId.Set.mem fv.id rel.used_fvars)
        input_vars
    in
    let constant_inputs =
      FVarId.Set.of_list
        (List.filter_map
           (fun ((keep, fv) : _ * fvar option) ->
             if keep then None
             else
               match fv with
               | None -> None
               | Some fv -> Some fv.id)
           (List.combine non_constant_inputs input_vars))
    in
    (* Then, the outputs.
       Check if the output can be computed statically from the
       initial inputs. *)
    let output_known_statically (el : texpr list) : bool =
      (* The output is known statically only if it contains:
         - free variables (those were introduced *before* the loop)
         - locally bound vars (those can appear in expressions like [fun x => x])

         The non-locally bound vars are bound in the loop body: if the
         expression contains such variables we have to preserve it, because
         it means its value depends on what happens inside the loop.

         We check the presence of non-locally bound vars in a simple
         way: we simply open all the variables bound in the body,
         and check if there are remaining bound variables - those must
         be bound elsewhere.
       *)
      (* Check if there are bound vars *)
      let have_bvars =
        List.exists
          (fun x -> x)
          (List.map (fun e -> texpr_has_bvars (open_all_texpr ctx span e)) el)
      in
      if have_bvars then false
      else
        match el with
        | [] ->
            (* Could happen with infinite loops, for now we forbid them *)
            [%internal_error] span
        | e :: el ->
            if List.for_all (fun e' -> e = e') el then
              (* All the expressions are the same: now check
                         if all the free variables are filtered inputs *)
              let fvars = texpr_get_fvars e in
              FVarId.Set.subset fvars constant_inputs
            else false
    in
    let keep_outputs =
      let known_statically = List.map output_known_statically rel.outputs in
      List.map
        (fun (known, x) -> (not known) && Option.is_some x)
        (List.combine known_statically output_vars)
    in

    let keep_inputs =
      (* We preserve the inputs if:
         - they are modified throughout the loop and are used inside it
         - they are are used within the loop *and* we extract auxiliary
           functions for the loops (we want to preserve the order of the
           input). *)
      let constant_inputs = List.map (fun b -> not b) non_constant_inputs in
      let unit_or_ignored_inputs =
        List.map
          (fun (p : tpat) -> p.ty = mk_unit_ty || is_ignored_pat p)
          body.inputs
      in
      [%ldebug
        let bool_list_to_string =
          Print.list_to_string ~sep:"; " string_of_bool
        in
        "- inputs: "
        ^ Print.list_to_string ~sep:"; " (tpat_to_string ctx) body.inputs
        ^ "\n- constant_inputs: "
        ^ bool_list_to_string constant_inputs
        ^ "\n- used: "
        ^ bool_list_to_string used_inputs
        ^ "\n- unit_or_ignored: "
        ^ bool_list_to_string unit_or_ignored_inputs];
      let filter =
        Collections.List.map3
          (fun constant used unit_or_ignored ->
            (* Constant inputs: filter them if it is allowed or if
               the input is not used *)
            (constant && (filter_constant_inputs || not used))
            (* We filter all inputs which have unit type or are
               the ignored pattern *)
            || unit_or_ignored)
          constant_inputs used_inputs unit_or_ignored_inputs
      in
      (* Revert: we want to know which inputs to *keep* *)
      List.map (fun b -> not b) filter
    in

    [%ldebug
      "- keep_inputs: "
      ^ Print.list_to_string Print.bool_to_string keep_inputs
      ^ "\n- keep_outputs: "
      ^ Print.list_to_string Print.bool_to_string keep_outputs];

    (* We need to compute the new expressions for the outputs we filter,
       by substituting the free variables which appear in their expressions
       (which are inputs bound locally in the loop) with the initial inputs
       with which the loop is "called". We can then introduce the let-bindings. *)
    let to_initial_input =
      FVarId.Map.of_list
        (List.filter_map
           (fun (fv, v) ->
             match fv with
             | None -> None
             | Some fv -> Some (fv, v))
           (List.combine input_var_ids loop.inputs))
    in
    let update_initial_inputs (e : texpr) : texpr =
      let visitor =
        object
          inherit [_] map_expr

          method! visit_FVar _ fid =
            match FVarId.Map.find_opt fid to_initial_input with
            | None -> FVar fid
            | Some e -> e.e
        end
      in
      visitor#visit_texpr () e
    in
    let updt_outputs =
      List.filter_map
        (fun (keep, output_var, el) ->
          match el with
          | [] -> [%internal_error] span
          | e :: _ ->
              if keep || output_var = None then None
              else Some (update_initial_inputs e))
        (Collections.List.combine3 keep_outputs output_vars rel.outputs)
    in

    (* Update the loop body *)
    let continue_ty =
      let tys =
        List.filter_map
          (fun ((keep, input) : _ * texpr) ->
            if keep then Some input.ty else None)
          (List.combine keep_inputs loop.inputs)
      in
      mk_simpl_tuple_ty tys
    in
    let break_ty =
      let tys =
        List.filter_map
          (fun ((keep, x) : _ * fvar option) ->
            match (keep, x) with
            | true, Some x -> Some x.ty
            | _ -> None)
          (List.combine keep_outputs output_vars)
      in
      (* There may be only one output, which has type tuple: if it is
         the case we need to simplify it *)
      let tys =
        match tys with
        | [ ty ] -> try_destruct_tuple span ty
        | _ -> tys
      in
      mk_simpl_tuple_ty tys
    in

    [%ldebug
      "- continue_ty: "
      ^ ty_to_string ctx continue_ty
      ^ "\n- break_ty: " ^ ty_to_string ctx break_ty];

    (* Substitute the constant values in the body *)
    let body =
      [%sanity_check] span (List.length input_vars = List.length loop.inputs);
      let bindings = List.combine input_vars loop.inputs in
      let bindings =
        List.filter_map
          (fun ((keep, (fv, v)) : _ * (fvar option * _)) ->
            if keep then None
            else
              match fv with
              | None -> None
              | Some fv -> Some (fv.id, v))
          (List.combine keep_inputs bindings)
      in
      let subst = FVarId.Map.of_list bindings in
      substitute_in_loop_body subst body
    in

    (* Filter the arguments of the continue/breaks *)
    let body =
      update_continue_break keep_outputs keep_inputs continue_ty break_ty body
    in
    let filter keep xl =
      List.filter_map
        (fun (keep, x) -> if keep then Some x else None)
        (List.combine keep xl)
    in
    let compute_num keep n =
      List.length (List.filter (fun b -> b) (Collections.List.prefix n keep))
    in
    let loop =
      {
        loop with
        output_tys = filter keep_outputs loop.output_tys;
        num_output_values = compute_num keep_outputs loop.num_output_values;
        inputs = filter keep_inputs loop.inputs;
        num_input_conts = compute_num keep_inputs loop.num_input_conts;
        loop_body = body;
      }
    in
    [%ldebug
      "- output_tys: "
      ^ Print.list_to_string (ty_to_string ctx) loop.output_tys
      ^ "\n- num_output_values: "
      ^ string_of_int loop.num_output_values
      ^ "\n- inputs: "
      ^ Print.list_to_string (texpr_to_string ctx) loop.inputs
      ^ "\n- num_input_conts: "
      ^ string_of_int loop.num_input_conts];

    (* Introduce the loop outputs we filtered by adding let-bindings
               afterwards (they're not output by the loop anymore) *)
    let kept_output_vars, filt_output_vars =
      List.partition fst (List.combine keep_outputs output_vars)
    in
    let kept_output_vars = List.filter_map snd kept_output_vars in
    let filt_output_vars = List.filter_map snd filt_output_vars in
    let filt_output_vars = List.map (mk_tpat_from_fvar None) filt_output_vars in
    [%ldebug
      "- filt_output_vars:\n"
      ^ String.concat "\n" (List.map (tpat_to_string ctx) filt_output_vars)
      ^ "\n- updt_outputs:\n"
      ^ String.concat "\n" (List.map (texpr_to_string ctx) updt_outputs)];
    let next =
      mk_closed_lets span false
        (List.combine filt_output_vars updt_outputs)
        next
    in

    (* Inline the useless vars in the expression after the loop body *)
    let next =
      (inline_useless_var_assignments_visitor ~inline_named:true
         ~inline_const:true ~inline_pure:false ~inline_identity:true ctx def)
        #visit_texpr
        empty_inline_env next
    in

    (* *)
    let pat =
      mk_simpl_tuple_pat (List.map (mk_tpat_from_fvar None) kept_output_vars)
    in

    (* *)
    (pat, loop, next)
  in

  let rec update (e : texpr) : texpr =
    match e.e with
    | FVar _
    | BVar _
    | CVar _
    | Const _
    | Lambda _
    | App _
    | Qualif _
    | StructUpdate _
    | EError _ -> e
    | Loop _ ->
        (* A loop should always be bound by a let *)
        [%internal_error] span
    | Meta (m, e) -> mk_emeta m (update e)
    | Let (monadic, pat, bound, next) -> (
        let _, pat, next = open_binder ctx span pat next in

        (* Update the next expression first - there may be loops in there *)
        let next = update next in

        (* Filter the useless variables which appear in [pat] (some currently
           used variables may have been eliminated by simplifying the loops in
           next) *)
        let pat = filter_useless next pat in

        (* Check if the bound expression is a loop *)
        match bound.e with
        | Loop loop ->
            let _, body = open_loop_body ctx span loop.loop_body in

            (* First explore the loop body: we want to simplify the inner loops *)
            let body = { body with loop_body = update body.loop_body } in
            let loop = { loop with loop_body = body } in

            (* Update the loop itself *)
            let pat, loop, next = update_loop pat loop next in

            let pat, loop, next =
              if not filter_constant_inputs then
                (* Because we use [filter_constant_inputs = false], the first application of
                   [update_loop] filters all the outputs that need to be filtered, but may
                   leave some unused inputs (which became unused because they were used in
                   some outputs which got filtered). We thus have to call it again. *)
                update_loop pat loop next
              else (pat, loop, next)
            in

            let loop =
              { loop with loop_body = close_loop_body span loop.loop_body }
            in

            let loop : texpr =
              {
                e = Loop loop;
                ty = mk_result_ty (mk_simpl_tuple_ty loop.output_tys);
              }
            in

            (* Bind the loop *)
            mk_closed_let span monadic pat loop next
        | _ ->
            (* No need to update the bound expression *)
            mk_closed_let span monadic pat bound next)
    | Switch (scrut, switch) ->
        (* No need to update the scrutinee *)
        let switch =
          match switch with
          | If (e0, e1) -> If (update e0, update e1)
          | Match bl ->
              Match
                (List.map
                   (fun ({ pat; branch } : match_branch) ->
                     let _, pat, branch = open_binder ctx span pat branch in
                     let branch = update branch in
                     let pat, branch = close_binder span pat branch in
                     { pat; branch })
                   bl)
        in
        [%add_loc] mk_switch span scrut switch
  in
  let body =
    Option.map
      (fun body ->
        let _, body = open_fun_body ctx span body in
        let body = { body with body = update body.body } in
        close_fun_body span body)
      def.body
  in
  { def with body }

(** Reorder the outputs of loops, in particular to trigger simplifications with
    [loops_to_recursive].

    There are several issues linked to [loops_to_recursive]:
    {ul
     {- in order for [loops_to_recursive] to be triggered, it needs the backward
        functions to be used in the *output* in exactly the same order as they
        are received as input (the main reason is that it makes the code of
        [loops_to_recursive] slightly easier).
     }
     {- it can happen that some output *value* is actually a call to a loop
        backward function, while [loops_to_recursive] will only analyse the loop
        output backward functions, not the loop output values.

        For instance, we sometimes generate code like this:
        {[
          def loop (back : ...) (l : List a) :=
            match l with
            | Nil => ok (back ...) (* HERE *)
            | Cons ... => ...
        ]}
        where in [ok (back ...)], the expression [back ...] is tagged as an
        output value.

        This micro-pass changes the order of the output values and updates the
        split between values and backward functions so that [loops_to_recursive]
        can trigger. Of course we could do everything inside of
        [loops_to_recursive], but that would make the code quite complex.
     }
    }

    In case we do not reorder the outputs for [loops_to_recursive], this
    micro-pass will try to reorder the outputs to solve the following case:
    {[
      def foo ... :=
        let (x, y) <- loop (fun ... ->
         ok (x, y))
        ok (y, x)

         ~~>

      def foo ... :=
        loop (fun ... ->
         ok (y, x))
    ]} *)
let reorder_loop_outputs (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in

  (* Helper to update the breaks in a loop body. *)
  let update_and_close_loop_body (explore : texpr -> texpr)
      (output_indices : int list) (num_output_backs : int) (loop : loop) : texpr
      =
    let continue_ty =
      mk_simpl_tuple_ty (List.map (fun (e : texpr) -> e.ty) loop.inputs)
    in
    let rec update (e : texpr) : texpr =
      match e.e with
      | FVar _ | BVar _ | CVar _ | Const _ | Lambda _ | StructUpdate _ | Loop _
        ->
          (* Shouldn't happen *)
          [%internal_error] span
      | EError _ -> e
      | App _ | Qualif _ ->
          (* This might be a break or a continue *)
          begin
            match
              opt_destruct_loop_result_decompose_outputs ctx span
                ~intro_let:true e
            with
            | None -> e
            | Some ({ variant_id; args; _ }, rebind) ->
                if variant_id = loop_result_break_id then (
                  (* Reorder the outputs *)
                  [%sanity_check] span
                    (List.length args = List.length output_indices);
                  let args =
                    List.map
                      (fun i -> Collections.List.nth args i)
                      output_indices
                  in
                  let args = mk_simpl_tuple_texpr span args in
                  rebind (mk_break_texpr span continue_ty args))
                else
                  (* Nothing to do *)
                  e
          end
      | Let (monadic, pat, bound, next) ->
          (* No need to update the bound expression *)
          let _, pat, next = open_binder ctx span pat next in
          let next = update next in
          mk_closed_let span monadic pat bound next
      | Switch (scrut, switch) ->
          (* No need to update the scrutinee *)
          let switch =
            match switch with
            | If (e0, e1) -> If (update e0, update e1)
            | Match branches ->
                let branches =
                  List.map
                    (fun ({ pat; branch } : match_branch) ->
                      let _, pat, branch = open_binder ctx span pat branch in
                      let branch = update branch in
                      let pat, branch = close_binder span pat branch in
                      { pat; branch })
                    branches
                in
                Match branches
          in
          [%add_loc] mk_switch span scrut switch
      | Meta (m, e) -> mk_emeta m (update e)
    in

    let body = loop.loop_body in
    let body = { body with loop_body = update body.loop_body } in

    (* Recursively explore the loop body *)
    let body = { body with loop_body = explore body.loop_body } in

    (* Close the loop body *)
    let body = close_loop_body span body in

    (* Rebuild the loop *)
    let num_outputs = List.length loop.output_tys in
    let num_output_values = num_outputs - num_output_backs in
    let output_tys =
      List.map (fun i -> Collections.List.nth loop.output_tys i) output_indices
    in
    let loop =
      {
        loop with
        output_tys;
        num_output_values;
        inputs = loop.inputs;
        num_input_conts = loop.num_input_conts;
        loop_body = body;
      }
    in

    let loop : texpr =
      { e = Loop loop; ty = mk_result_ty (mk_simpl_tuple_ty loop.output_tys) }
    in
    [%ldebug "loop:\n" ^ texpr_to_string ctx loop];

    loop
  in

  (* Small helper: update a let-binding binding a loop, after we reordred the
     outputs *inside* the loop (i.e., the arguments given to the breaks) *)
  let update_let (monadic : bool) (pat : tpat) (loop : texpr) (next : texpr)
      (output_indices : int list) : texpr =
    (* Decompose the pattern, which should be a tuple *)
    let patl = try_destruct_tuple_or_ignored_tpat span pat in

    (* Reorder *)
    let patl = List.map (fun i -> Collections.List.nth patl i) output_indices in
    let pat = mk_simpl_tuple_pat patl in

    (* Create the let-binding *)
    mk_closed_let span monadic pat loop next
  in

  (* Small helper: attempt to compute a new order which would be useful for
     [loops_to_recursive] *)
  let compute_outputs_indices_to_reorder_backs (loop : loop) :
      (int list * int) option =
    (* Analyze the body *)
    let rel = compute_loop_input_output_rel span ctx loop in

    (* Go through all the outputs, check if some of them are actually
       calls to input backward functions *)
    (* Helper: is a continuation exactly a call to an input backward function? *)
    let input_conts_fvids_to_index =
      FVarId.Map.of_list
        (List.filter_map
           (fun x -> x)
           (List.mapi
              (fun i (p : tpat) ->
                match p.pat with
                | PIgnored -> None
                | POpen (fvar, _) -> Some (fvar.id, i)
                | _ -> [%internal_error] span)
              (Collections.List.prefix loop.num_input_conts
                 loop.loop_body.inputs)))
    in
    [%ldebug
      "- input_conts_fvids_to_index: "
      ^ FVarId.Map.to_string None string_of_int input_conts_fvids_to_index
      ^ "\n- num_input_conts: "
      ^ string_of_int loop.num_input_conts
      ^ "\n- num_output_values: "
      ^ string_of_int loop.num_output_values];

    let is_call_to_input (x : texpr) : int option =
      let _pats, body = raw_destruct_lambdas x in
      let _, body = raw_destruct_lets body in
      let f, _args = destruct_apps body in
      match f.e with
      | FVar fid -> FVarId.Map.find_opt fid input_conts_fvids_to_index
      | _ -> None
    in
    let { outputs; _ } : loop_rel = rel in
    [%ldebug "loop_rel:\n" ^ loop_rel_to_string ctx rel];
    let outputs_call_inputs =
      List.filter_map
        (fun (i, xl) ->
          match List.find_opt Option.is_some xl with
          | None -> None
          | Some x ->
              let x = Option.get x in
              if List.for_all (fun x' -> x' = Some x) xl then Some (i, x)
              else None)
        (List.mapi
           (fun i x -> (i, x))
           (List.map (List.map is_call_to_input) outputs))
    in
    [%ldebug
      "outputs_call_inputs:\n"
      ^ Print.list_to_string
          (fun (x, i) -> string_of_int x ^ " -> " ^ string_of_int i)
          outputs_call_inputs];

    (* We reorder only if every input backward function has a corresponding
       output. We first compute the map from input backward function (refered
       to by its index) to output index.

       TODO: it would be good to generalize, but it's unclear what we should do,
       so it should be driven by examples. *)
    let input_to_output =
      ref
        (Collections.IntMap.of_list
           (List.init loop.num_input_conts (fun i -> (i, []))))
    in
    List.iter
      (fun (output_index, input_index) ->
        input_to_output :=
          Collections.IntMap.add_to_list input_index output_index
            !input_to_output)
      outputs_call_inputs;
    let input_to_output = !input_to_output in

    (* Check that every input backward function maps to exactly one output *)
    let reorder =
      Collections.IntMap.for_all
        (fun _ x ->
          match x with
          | [ _ ] -> true
          | _ -> false)
        input_to_output
      && not (Collections.IntMap.is_empty input_to_output)
    in
    [%ldebug "reorder: " ^ string_of_bool reorder];

    if not reorder then None
    else
      (* First, simplify the map from input index to output index so that
         it maps to a single index (rather than a list of indices) *)
      let input_to_output =
        Collections.IntMap.map (fun xl -> List.hd xl) input_to_output
      in

      (* Then, compute the indices of the outputs to reorder - we need this
         to partition the outputs between those we put in front and the others *)
      let outputs_to_reorder =
        Collections.IntSet.of_list (Collections.IntMap.values input_to_output)
      in

      (* Finally, compute the list of the indices to use for the outputs.
         e.g., if we want the output to follow the order:
         output at index 2, output at index 0, then output at index 1,
         the list is [2; 0; 1] *)
      let num_outputs = List.length loop.output_tys in
      let output_indices =
        (* The prefix: the values which are not considered to be continuations *)
        List.filter_map
          (fun out_i ->
            (* We simply remove the outputs that will be moved to the end,
               because they are continuations that we want to reorder *)
            if Collections.IntSet.mem out_i outputs_to_reorder then None
            else Some out_i)
          (List.init num_outputs (fun i -> i))
        (* The suffix: the reordered continuations. *)
        @ Collections.IntMap.values input_to_output
      in
      [%sanity_check] span (List.length output_indices = num_outputs);

      Some (output_indices, Collections.IntMap.cardinal input_to_output)
  in

  (* Small helper: analyze the next expression to check if it is exactly
     [ok ...] or [break ...] called on the loop outputs, but in a different
     order.
   *)
  let compute_outputs_indices_if_followed_by_ok (loop : loop) (pat : tpat)
      (next : texpr) =
    (* Check if the next expression is [ok (...)] or [break (...)],
       and reorder the outputs accordingly. *)
    (* Deconstruct the pattern and check that it is a tuple of free variables *)
    [%ldebug "pat: " ^ tpat_to_string ctx pat];
    let patl = try_destruct_tuple_or_ignored_or_open_tpat span pat in
    let patl_fvars =
      List.map
        (fun (p : tpat) ->
          match p.pat with
          | POpen (fv, _) -> Some fv
          | _ -> None)
        patl
    in
    if not (List.for_all Option.is_some patl_fvars) then None
    else
      let patl_fvars = List.map Option.get patl_fvars in
      [%ldebug
        "patl_fvars: " ^ Print.list_to_string (fvar_to_string ctx) patl_fvars];

      (* Deconstruct the [next] expression *)
      let f, args = destruct_apps next in
      let is_ok_or_break =
        match f.e with
        | Qualif
            {
              id =
                AdtCons { adt_id = TBuiltin tid; variant_id = Some variant_id };
              _;
            } -> (
            match tid with
            | TResult when variant_id = result_ok_id -> true
            | TLoopResult when variant_id = loop_result_break_id -> true
            | _ -> false)
        | _ -> false
      in
      [%ldebug "is_ok_or_break: " ^ Print.bool_to_string is_ok_or_break];

      if (not is_ok_or_break) || List.length args <> 1 then None
      else
        (* Analyze the arguments to check if they are all variables,
           and if they are exactly the variables introduced by [patl]
           but in a different order. *)
        let args = try_destruct_tuple_texpr span (List.hd args) in
        let args_fvars =
          List.map
            (fun (a : texpr) ->
              match a.e with
              | FVar fid -> Some fid
              | _ -> None)
            args
        in
        [%ldebug
          "args_fvars: "
          ^ Print.list_to_string
              (Print.option_to_string FVarId.to_string)
              args_fvars];

        if not (List.for_all Option.is_some args_fvars) then None
        else
          let args_fvars = List.map Option.get args_fvars in
          [%ldebug
            "args_fvars: " ^ Print.list_to_string FVarId.to_string args_fvars];

          (* Check that the arguments are exactly the fvars bound by the let-binding
             but in a different order *)
          (* First, compute a map from pattern fvar id to index (which gives the position) *)
          let pat_fvar_to_index =
            FVarId.Map.of_list
              (List.mapi (fun i (fv : fvar) -> (fv.id, i)) patl_fvars)
          in
          [%ldebug
            "pat_fvar_to_index: "
            ^ FVarId.Map.to_string None string_of_int pat_fvar_to_index];

          (* Map every argument to the index of the fvar it uses, if it uses an fvar
             bound in the let *)
          let arg_to_index =
            List.mapi
              (fun arg_i fid ->
                match FVarId.Map.find_opt fid pat_fvar_to_index with
                | None -> None
                | Some pat_index -> Some (arg_i, pat_index))
              args_fvars
          in
          [%ldebug
            "arg_to_index: "
            ^ Print.list_to_string
                (Print.option_to_string
                   (Print.pair_to_string string_of_int string_of_int))
                arg_to_index];

          (* Check that we could map all the arguments to some input, and that
             the order is not respected *)
          if not (List.for_all Option.is_some arg_to_index) then None
          else
            let arg_to_index = List.map Option.get arg_to_index in
            if List.for_all (fun (i, i') -> i = i') arg_to_index then
              (* Order is the same: no need to reorder *)
              None
            else
              (* Order is not the same: we need to reorder *)
              let output_indices = List.map snd arg_to_index in
              (* Computing the number of output continuations is slightly annoying.
                 We do something approximate: we compute the length of the longest
                 suffix of the reordered outputs made of only continuations. *)
              let num_outputs = List.length loop.output_tys in
              let num_output_conts =
                match
                  List.find_index
                    (fun i -> i < loop.num_output_values)
                    (List.rev output_indices)
                with
                | Some i -> i
                | None -> num_outputs
              in
              Some (output_indices, num_output_conts)
  in

  let rec explore (e : texpr) : texpr =
    match e.e with
    | FVar _
    | BVar _
    | CVar _
    | Const _
    | Lambda _
    | App _
    | Qualif _
    | StructUpdate _
    | EError _ -> e
    | Loop _ ->
        (* A loop should always be bound by a let *)
        [%internal_error] span
    | Meta (m, e) -> mk_emeta m (explore e)
    | Let (monadic, pat, bound, next) -> (
        let _, pat, next = open_binder ctx span pat next in

        (* Check if the bound expression is a loop *)
        match bound.e with
        | Loop loop -> (
            let _, body = open_loop_body ctx span loop.loop_body in
            [%ldebug "body:\n" ^ loop_body_to_string ctx body];

            let loop = { loop with loop_body = body } in

            (* Check if we should reorder the output in an attempt to trigger the simplification
               implemented by [loops_to_recursive] *)
            match compute_outputs_indices_to_reorder_backs loop with
            | Some (output_indices, num_output_backs) ->
                (* Apply the update to the loop body - note that this *closes* the loop body *)
                let loop =
                  update_and_close_loop_body explore output_indices
                    num_output_backs loop
                in

                (* Apply the let-binding (we need to reorder the variables in the pattern) *)
                let next = explore next in
                let e = update_let monadic pat loop next output_indices in
                [%ldebug "let-expression:\n" ^ texpr_to_string ctx e];
                e
            | None -> (
                match
                  compute_outputs_indices_if_followed_by_ok loop pat next
                with
                | Some (output_indices, num_output_backs) ->
                    (* Apply the update to the loop body - note that this *closes* the loop body *)
                    let loop =
                      update_and_close_loop_body explore output_indices
                        num_output_backs loop
                    in

                    (* Apply the let-binding (we need to reorder the variables in the pattern) *)
                    let next = explore next in
                    let e = update_let monadic pat loop next output_indices in
                    [%ldebug "let-expression:\n" ^ texpr_to_string ctx e];
                    e
                | None ->
                    (* Do not reorder the output but recursively explore the loop body *)
                    let loop_body =
                      {
                        loop.loop_body with
                        loop_body = explore loop.loop_body.loop_body;
                      }
                    in
                    let loop =
                      { loop with loop_body = close_loop_body span loop_body }
                    in
                    let bound = { bound with e = Loop loop } in
                    let next = explore next in
                    mk_closed_let span monadic pat bound next))
        | _ ->
            (* No need to update the bound expression *)
            let next = explore next in
            mk_closed_let span monadic pat bound next)
    | Switch (scrut, switch) ->
        (* No need to update the scrutinee *)
        let switch =
          match switch with
          | If (e0, e1) -> If (explore e0, explore e1)
          | Match bl ->
              Match
                (List.map
                   (fun ({ pat; branch } : match_branch) ->
                     let _, pat, branch = open_binder ctx span pat branch in
                     let branch = explore branch in
                     let pat, branch = close_binder span pat branch in
                     { pat; branch })
                   bl)
        in
        [%add_loc] mk_switch span scrut switch
  in
  let body =
    Option.map
      (fun body ->
        let _, body = open_fun_body ctx span body in
        let body = { body with body = explore body.body } in
        close_fun_body span body)
      def.body
  in
  { def with body }

(** Attempts to transform loops to recursive functions which receive no backward
    functions as inputs and only *output* backward functions.

    We can do so if the output backward functions perform a terminal call to the
    input backward functions, and the input backward functions are the identiy.
    For instance:
    {[
      let list_nth_mut {T : Type} (ls : List T) (i : U32) : T × (T → List T) :=
        let (x, back) ← loop (fun back ls i =>
          match ls with
          | Cons x tl =>
            if i = 0 then break (x, fun y => back (Cons y tl))
            else
              let i1 ← i - 1
              let back' := fun l => back (Cons x l) (* Performs a terminal call to back *)
              continue back' tl i1
          | Nil => panic) (fun x -> x) ls i (* input back fun is the identity *)
       pure (x, back)

        ~>

      let list_nth_mut {T : Type} (ls : List T) (i : U32) : T × (T → List T) :=
        let (x, back) ← loop (fun ls i =>
          match ls with
          | Cons x tl =>
            if i = 0 then
              let back := fun y => Cons y tl (* Removed the call to the backward function *)
              break (x, back)
            else
              let i1 ← i - 1
              let x, back ← recLoopCall tl i1
              let back' := fun y =>
                let l := back y (* l is the original input of the continuation *)
                Cons x l
              break (x, back')
          | Nil => panic) ls i
       ok (x, back)
    ]}

    Note that we do not introduce recursive definitions for the loops *yet*: we
    first use the [RecLoopCall] function, and introduce the auxiliary
    definitions in [decompose_loops]. *)
let loops_to_recursive (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in

  (* Helper to update the continue/breaks in a loop body. *)
  let update_loop_body (input_conts_fids : FVarId.Set.t) (num_input_conts : int)
      (num_output_values : int) (output_conts_inputs : fvar list list)
      (break_outputs : fvar list) (continue_ty : ty) (break_ty : ty)
      (body : loop_body) : loop_body =
    let rec update (e : texpr) : texpr =
      match e.e with
      | FVar _ | BVar _ | CVar _ | Const _ | Lambda _ | StructUpdate _ | Loop _
        ->
          (* Shouldn't happen *)
          [%internal_error] span
      | EError _ -> e
      | App _ | Qualif _ ->
          (* This might be a break or a continue *)
          begin
            match
              opt_destruct_loop_result_decompose_outputs ctx span
                ~intro_let:true e
            with
            | None -> e
            | Some ({ variant_id; args = outputs; _ }, rebind) ->
                if variant_id = loop_result_break_id then
                  (* Update the backward functions.

                     We simply remove the call to the input backward function.
                  *)
                  let update_back (e : texpr) =
                    [%ldebug "- e:\n" ^ texpr_to_string ctx e];
                    (* It can happen that we directly call the backward function,
                       which is thus not a lambda. If this happens, we update it
                       so that it matches the more general case.

                       TODO: this will not work once we add support for
                       function pointers and closures.
                    *)
                    let e =
                      if is_fvar e then
                        let arg_ty, _ = destruct_arrow span e.ty in
                        let fv = mk_fresh_fvar ctx arg_ty in
                        let arg = mk_texpr_from_fvar fv in
                        let pat = mk_tpat_from_fvar None fv in
                        let app = [%add_loc] mk_app span e arg in
                        mk_closed_lambda span pat app
                      else e
                    in
                    let _, lam_pats, body = open_lambdas ctx span e in
                    let lets, body = open_lets ctx span body in
                    let _, args = destruct_apps body in
                    match args with
                    | [ arg ] ->
                        mk_closed_lambdas span lam_pats
                          (mk_closed_heterogeneous_lets span lets arg)
                    | _ -> [%internal_error] span
                  in
                  let values, backl =
                    Collections.List.split_at outputs num_output_values
                  in
                  let backl = List.map update_back backl in
                  let outputs = mk_simpl_tuple_texpr span (values @ backl) in
                  rebind (mk_break_texpr span continue_ty outputs)
                else if variant_id = loop_result_continue_id then (
                  (* Remove the continuations *)
                  let input_backl, input_values =
                    Collections.List.split_at outputs num_input_conts
                  in
                  let inputs = mk_simpl_tuple_texpr span input_values in
                  (* Replace the [continue] with a call to RecLoopCall *)
                  let call =
                    [%add_loc] mk_rec_loop_call_texpr span inputs break_ty
                  in
                  (* Bind the outputs *)
                  let output_values, output_backl =
                    Collections.List.split_at break_outputs num_output_values
                  in

                  [%ldebug
                    let el_to_string el =
                      String.concat "\n" (List.map (texpr_to_string ctx) el)
                    in
                    let fv_to_string el =
                      String.concat "\n" (List.map (fvar_to_string ctx) el)
                    in
                    "- input_values:\n" ^ el_to_string input_values
                    ^ "\n- input_backl:\n" ^ el_to_string input_backl
                    ^ "\n- output_values:\n" ^ fv_to_string output_values
                    ^ "\n- output_backl:\n" ^ fv_to_string output_backl];

                  (* Introduce the backward functions *)
                  [%sanity_check] span
                    (List.length input_backl = List.length output_backl);
                  let update_back (input : texpr) (back : fvar)
                      (back_inputs : fvar list) : texpr =
                    [%ldebug
                      "- input: " ^ texpr_to_string ctx input ^ "\n- back: "
                      ^ fvar_to_string ctx back ^ "\n- back_inputs: "
                      ^ Print.list_to_string (fvar_to_string ctx) back_inputs];
                    let _, lam_pats, body = open_lambdas ctx span input in
                    let let_pats, body = open_lets ctx span body in
                    let f, args = destruct_apps body in
                    match (f.e, lam_pats, args) with
                    | FVar _, [ pat ], [ arg ] ->
                        let back_inputs_el =
                          List.map mk_texpr_from_fvar back_inputs
                        in
                        let back = mk_texpr_from_fvar back in
                        let e =
                          mk_closed_heterogeneous_lets span let_pats arg
                        in
                        let e =
                          mk_closed_let span false pat
                            ([%add_loc] mk_apps span back back_inputs_el)
                            e
                        in
                        let back_inputs =
                          List.map (mk_tpat_from_fvar None) back_inputs
                        in
                        mk_closed_lambdas span back_inputs e
                    | _ -> [%internal_error] span
                  in

                  [%ldebug
                    let el_to_string el =
                      String.concat "\n" (List.map (texpr_to_string ctx) el)
                    in
                    let fv_to_string el =
                      String.concat "\n" (List.map (fvar_to_string ctx) el)
                    in
                    "- input_backl (length: "
                    ^ string_of_int (List.length input_backl)
                    ^ "):\n" ^ el_to_string input_backl
                    ^ "\n- output_backl (length: "
                    ^ string_of_int (List.length output_backl)
                    ^ "):\n" ^ fv_to_string output_backl
                    ^ "\n- output_conts_inputs (length: "
                    ^ string_of_int (List.length output_conts_inputs)
                    ^ "):\n"
                    ^ Print.list_to_string
                        (Print.list_to_string (fvar_to_string ctx))
                        output_conts_inputs];

                  let updated_backl =
                    Collections.List.map3 update_back input_backl output_backl
                      output_conts_inputs
                  in
                  let backl =
                    List.map
                      (fun (e : texpr) ->
                        let id = ctx.fresh_fvar_id () in
                        let fv : fvar =
                          { id; ty = e.ty; basename = Some "back" }
                        in
                        fv)
                      updated_backl
                  in
                  let outputs =
                    mk_simpl_tuple_texpr span
                      (List.map mk_texpr_from_fvar (output_values @ backl))
                  in
                  let output =
                    rebind (mk_break_texpr span continue_ty outputs)
                  in
                  let e =
                    mk_closed_lets span false
                      (List.combine
                         (List.map (mk_tpat_from_fvar None) backl)
                         updated_backl)
                      output
                  in
                  let e =
                    mk_closed_let span true
                      (mk_simpl_tuple_pat
                         (List.map (mk_tpat_from_fvar None) break_outputs))
                      call e
                  in
                  e)
                else (
                  [%sanity_check] span (variant_id = loop_result_fail_id);
                  let arg = mk_simpl_tuple_texpr span outputs in
                  mk_loop_result_fail_texpr span continue_ty break_ty arg)
          end
      | Let (monadic, pat, bound, next) ->
          (* No need to update the bound expression *)
          let _, pat, next = open_binder ctx span pat next in
          let next = update next in
          mk_closed_let span monadic pat bound next
      | Switch (scrut, switch) ->
          (* No need to update the scrutinee *)
          let switch =
            match switch with
            | If (e0, e1) -> If (update e0, update e1)
            | Match branches ->
                let branches =
                  List.map
                    (fun ({ pat; branch } : match_branch) ->
                      let _, pat, branch = open_binder ctx span pat branch in
                      let branch = update branch in
                      let pat, branch = close_binder span pat branch in
                      { pat; branch })
                    branches
                in
                Match branches
          in
          [%add_loc] mk_switch span scrut switch
      | Meta (m, e) -> mk_emeta m (update e)
    in

    let inputs = Collections.List.drop num_input_conts body.inputs in
    let body = { inputs; loop_body = update body.loop_body } in
    let body = close_loop_body span body in
    (* Check that all the input continuations disappeared from the loop body *)
    let fids = texpr_get_fvars body.loop_body in
    [%sanity_check] span
      (FVarId.Set.is_empty (FVarId.Set.inter fids input_conts_fids));
    (* *)
    body
  in

  let rec update (e : texpr) : texpr =
    match e.e with
    | FVar _
    | BVar _
    | CVar _
    | Const _
    | Lambda _
    | App _
    | Qualif _
    | StructUpdate _
    | EError _ -> e
    | Loop _ ->
        (* A loop should always be bound by a let *)
        [%internal_error] span
    | Meta (m, e) -> mk_emeta m (update e)
    | Let (monadic, pat, bound, next) -> (
        let _, pat, next = open_binder ctx span pat next in

        (* Check if the bound expression is a loop *)
        match bound.e with
        | Loop loop ->
            let _, body = open_loop_body ctx span loop.loop_body in
            [%ldebug "body:\n" ^ loop_body_to_string ctx body];

            (* Explore the loop body: we want to simplify the inner loops *)
            let body = { body with loop_body = update body.loop_body } in

            (* Analyze the body *)
            let rel =
              compute_loop_input_output_rel span ctx
                { loop with loop_body = body }
            in

            (* We transform the structure of the loop if:
               - there is at least an input continuation
               - all input continuations are the identity
               - all the output continuations, and the input continuations given
                 to the recursive calls, are exactly calls to an input continuation
            *)
            let input_conts =
              Collections.List.prefix loop.num_input_conts loop.inputs
            in
            (* Helper: is a continuation exactly the identity? *)
            let is_identity (x : texpr) : bool =
              let _, pats, body = open_lambdas ctx span x in
              match (pats, body.e) with
              | [ { pat = POpen (fv, _); _ } ], FVar fid -> fv.id = fid
              | _ -> false
            in
            let all_inputs_are_id = List.for_all is_identity input_conts in

            (* Helper: is a continuation exactly a call to an input backward function? *)
            let input_conts_fvids =
              tpats_get_fvars
                (Collections.List.prefix loop.num_input_conts body.inputs)
            in
            let input_conts_fvids_to_index =
              FVarId.Map.of_list
                (List.filter_map
                   (fun x -> x)
                   (List.mapi
                      (fun i (p : tpat) ->
                        match p.pat with
                        | PIgnored -> None
                        | POpen (fvar, _) -> Some (fvar.id, i)
                        | _ -> [%internal_error] span)
                      (Collections.List.prefix loop.num_input_conts body.inputs)))
            in
            [%ldebug
              "input_conts_fvids: "
              ^ FVarId.Set.to_string None input_conts_fvids
              ^ "\n- input_conts_fvids_to_index: "
              ^ FVarId.Map.to_string None string_of_int
                  input_conts_fvids_to_index
              ^ "\n- num_input_conts: "
              ^ string_of_int loop.num_input_conts
              ^ "\n- num_output_values: "
              ^ string_of_int loop.num_output_values];
            let is_call_to_input (i : int) (x : texpr) : bool =
              [%ldebug
                "- index: " ^ string_of_int i ^ "\n- x:\n"
                ^ texpr_to_string ctx x];
              let _pats, body = raw_destruct_lambdas x in
              let _, body = raw_destruct_lets body in
              let f, _args = destruct_apps body in
              (* TODO: we also need to check that the input backward functions
                 are not used elsewhere. We do this after the fact, through
                 a sanity check (we check that after we performed the transformation,
                 no use of the input backward functions remains), but it would be
                 better to do it before) *)
              match f.e with
              | FVar fid ->
                  FVarId.Set.mem fid input_conts_fvids
                  (* Also check that the order is correct - TODO: the first check
                     is subsumed by the second one *)
                  && FVarId.Map.find_opt fid input_conts_fvids_to_index = Some i
              | _ -> false
            in
            let { inputs; outputs; _ } : loop_rel = rel in
            [%ldebug "loop_rel:\n" ^ loop_rel_to_string ctx rel];
            let input_conts =
              Collections.List.prefix loop.num_input_conts inputs
            in
            let output_conts =
              Collections.List.drop loop.num_output_values outputs
            in
            [%ldebug
              "- input_conts:"
              ^ Print.list_to_string ~sep:"\n"
                  (Print.list_to_string (texpr_to_string ctx))
                  input_conts
              ^ "\n- output_conts:"
              ^ Print.list_to_string ~sep:"\n"
                  (Print.list_to_string (texpr_to_string ctx))
                  output_conts];
            let inputs_are_calls_to_inputs =
              List.mapi (fun i -> List.map (is_call_to_input i)) input_conts
            in
            let outputs_are_calls_to_inputs =
              List.mapi (fun i -> List.map (is_call_to_input i)) output_conts
            in

            [%ldebug
              "- all_inputs_are_id: "
              ^ string_of_bool all_inputs_are_id
              ^ "\n- inputs_are_calls_to_inputs: "
              ^ Print.list_to_string ~sep:"\n"
                  (Print.list_to_string string_of_bool)
                  inputs_are_calls_to_inputs
              ^ "\n- outputs_are_calls_to_inputs: "
              ^ Print.list_to_string ~sep:"\n"
                  (Print.list_to_string string_of_bool)
                  outputs_are_calls_to_inputs];

            let for_all = List.for_all (List.for_all (fun x -> x)) in
            if
              input_conts <> [] && all_inputs_are_id
              && for_all inputs_are_calls_to_inputs
              && for_all outputs_are_calls_to_inputs
              && List.length input_conts = List.length output_conts
            then (
              (* Transform the loop to introduce recursive calls and simplify
                 the backward functions *)
              let break_ty = mk_simpl_tuple_ty loop.output_tys in
              (* TODO: names for the outputs *)
              let break_outputs =
                List.mapi
                  (fun i ty ->
                    let id = ctx.fresh_fvar_id () in
                    let basename =
                      if i < loop.num_output_values then None else Some "back"
                    in
                    ({ id; basename; ty } : fvar))
                  loop.output_tys
              in
              let inputs =
                Collections.List.drop loop.num_input_conts loop.inputs
              in
              let continue_ty =
                mk_simpl_tuple_ty (List.map (fun (e : texpr) -> e.ty) inputs)
              in
              let output_conts_inputs =
                List.map
                  (fun el ->
                    match el with
                    | e :: _ ->
                        (* The function may have been simplified: if it is the case,
                           we need to reintroduce lambdas *)
                        if is_fvar e then
                          (* TODO: this will not work once we add support for
                             function pointers and closures. *)
                          let tys, _ = destruct_arrows e.ty in
                          List.map (mk_fresh_fvar ctx) tys
                        else
                          (* Open the lambdas *)
                          let _, pats, _ = open_lambdas ctx span e in
                          List.map
                            (fun x -> fst ([%add_loc] as_pat_open span x))
                            pats
                    | _ -> [%internal_error] span)
                  (Collections.List.drop loop.num_output_values rel.outputs)
              in

              [%ldebug
                "output_conts_inputs:\n"
                ^ String.concat ",\n"
                    (List.map
                       (Print.list_to_string (fvar_to_string ctx))
                       output_conts_inputs)];

              let body =
                update_loop_body input_conts_fvids loop.num_input_conts
                  loop.num_output_values output_conts_inputs break_outputs
                  continue_ty break_ty body
              in

              (* Check that the body doesn't contain uses of the input continuations anymore *)
              [%sanity_check] span
                (let fvars = texpr_get_fvars body.loop_body in
                 FVarId.Set.disjoint input_conts_fvids fvars);

              let loop =
                {
                  loop with
                  output_tys = loop.output_tys;
                  num_output_values = loop.num_output_values;
                  inputs =
                    Collections.List.drop loop.num_input_conts loop.inputs;
                  num_input_conts = 0;
                  loop_body = body;
                }
              in

              let loop : texpr =
                {
                  e = Loop loop;
                  ty = mk_result_ty (mk_simpl_tuple_ty loop.output_tys);
                }
              in

              [%ldebug "loop:\n" ^ texpr_to_string ctx loop];

              (* Bind the loop *)
              mk_closed_let span monadic pat loop next)
            else
              (* Do not apply any transformation *)
              let loop = { loop with loop_body = close_loop_body span body } in
              let bound = { bound with e = Loop loop } in
              mk_closed_let span monadic pat bound next
        | _ ->
            (* No need to update the bound expression *)
            let next = update next in
            mk_closed_let span monadic pat bound next)
    | Switch (scrut, switch) ->
        (* No need to update the scrutinee *)
        let switch =
          match switch with
          | If (e0, e1) -> If (update e0, update e1)
          | Match bl ->
              Match
                (List.map
                   (fun ({ pat; branch } : match_branch) ->
                     let _, pat, branch = open_binder ctx span pat branch in
                     let branch = update branch in
                     let pat, branch = close_binder span pat branch in
                     { pat; branch })
                   bl)
        in
        [%add_loc] mk_switch span scrut switch
  in
  let body =
    Option.map
      (fun body ->
        let _, body = open_fun_body ctx span body in
        let body = { body with body = update body.body } in
        close_fun_body span body)
      def.body
  in
  { def with body }

(** Introduce match expressions where a let-binding decomposes an enumeration
    with > 1 variants (see [decompose_let_match]).

    Such patterns can be introduced when calling backward functions. *)
let let_to_match (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in

  (* A pattern appearing in a let-binding needs to be updated if it deconstructs
     an enumeration with > 1 variants *)
  let pat_needs_update pat = tpat_decomposes_enum span ctx.type_decls pat in
  (* Quick check: does the expression contains a let-binding which needs to be updated? *)
  let needs_update (e : texpr) : bool =
    let expr_visitor =
      object
        inherit [_] iter_expr as super

        method! visit_Let env monadic pat bound next =
          if pat_needs_update pat then raise Utils.Found;
          super#visit_Let env monadic pat bound next
      end
    in
    try
      expr_visitor#visit_texpr () e;
      false
    with Utils.Found -> true
  in

  (* When introducing the match, we need to find default values in the "otherwise"
     branch. We do so by computing a map from type to expression found so far.
     We also store the size of the expression in order to use the smallest expressions
     as possible. *)
  let add_expr (env : (int * texpr) TyMap.t) (size : int) (e : texpr) :
      (int * texpr) TyMap.t =
    TyMap.update e.ty
      (fun x ->
        match x with
        | None -> Some (size, e)
        | Some (size', e') ->
            if size <= size' then Some (size, e) else Some (size', e'))
      env
  in

  (* Patterns can be converted to expressions (if they don't contain ignored patterns '_').
     We can use those as default expressions as well: this helper explores a pattern
     and registers all the expressions we find inside it. *)
  let rec add_pat_aux (env : (int * texpr) TyMap.t) (p : tpat) :
      (int * texpr) TyMap.t * int * texpr option =
    match p.pat with
    | PConstant lit -> (env, 1, Some { e = Const lit; ty = p.ty })
    | PBound _ -> [%internal_error] span
    | PIgnored -> (env, 1, None)
    | POpen (fv, _) -> (env, 1, Some { e = FVar fv.id; ty = fv.ty })
    | PAdt { variant_id; fields } ->
        let (env, size), fields =
          List.fold_left_map
            (fun (env, size) e ->
              let env, size', e = add_pat env e in
              ((env, size + size' + 1), e))
            (env, 0) fields
        in
        let e =
          if List.for_all Option.is_some fields then
            let fields = List.map Option.get fields in

            (* Retrieve the type id and the type args from the pat type (simpler this way *)
            let adt_id, generics = ty_as_adt span p.ty in

            (* Create the constructor *)
            let qualif_id = AdtCons { adt_id; variant_id } in
            let qualif = { id = qualif_id; generics } in
            let cons_e = Qualif qualif in
            let field_tys = List.map (fun (v : texpr) -> v.ty) fields in
            let cons_ty = mk_arrows field_tys p.ty in
            let cons = { e = cons_e; ty = cons_ty } in

            (* Apply the constructor *)
            Some ([%add_loc] mk_apps span cons fields)
          else None
        in

        (env, size, e)
  and add_pat (env : (int * texpr) TyMap.t) (p : tpat) :
      (int * texpr) TyMap.t * int * texpr option =
    let env, size, e = add_pat_aux env p in
    let env =
      match e with
      | None -> env
      | Some e -> add_expr env size e
    in
    (env, size, e)
  in

  (* See [add_pat] above *)
  let add_pat env p =
    let env, size, _ = add_pat env p in
    (env, size)
  in

  (* Update a let-binding by introducing a match, if necessary *)
  let update_let (env : (int * texpr) TyMap.t) (pat : tpat) (bound : texpr) :
      tpat * texpr =
    let refresh_var (var : fvar) =
      mk_fresh_fvar ctx ~basename:var.basename var.ty
    in
    let get_default_expr (var : fvar) =
      match TyMap.find_opt var.ty env with
      | Some (_, e) -> e
      | None -> [%internal_error] span
    in
    decompose_let_match span refresh_var get_default_expr ctx.type_decls pat
      bound
  in

  (* Recursively update an expression to decompose all the let-bindings *)
  let rec update_aux (env : (int * texpr) TyMap.t) (e : texpr) :
      (int * texpr) TyMap.t * int * texpr =
    match e.e with
    | FVar _ | BVar _ | CVar _ | Const _ | EError _ | Qualif _ -> (env, 1, e)
    | App (f, x) ->
        let env, nf, f = update env f in
        let env, nx, x = update env x in
        (env, nf + nx + 1, [%add_loc] mk_app span f x)
    | Lambda (pat, body) ->
        let _, pat, body = open_binder ctx span pat body in
        let env', size = add_pat env pat in
        let _, size', body = update env' body in
        (env, size + size' + 1, mk_closed_lambda span pat body)
    | Let (monadic, pat, bound, next) ->
        let _, pat, next = open_binder ctx span pat next in
        let pat, bound = update_let env pat bound in
        let env, s0, bound = update env bound in
        let env', s1 = add_pat env pat in
        let _, s2, next = update env' next in
        (env, s0 + s1 + s2 + 1, mk_closed_let span monadic pat bound next)
    | Switch (scrut, switch) ->
        let env, s0, scrut = update env scrut in
        let env, s1, switch =
          match switch with
          | If (e0, e1) ->
              let env, s1, e0 = update env e0 in
              let env, s2, e1 = update env e1 in
              (env, s1 + s2, If (e0, e1))
          | Match branches ->
              let sizes, branches =
                List.split
                  (List.map
                     (fun ({ pat; branch } : match_branch) ->
                       let _, pat, branch = open_binder ctx span pat branch in
                       let env, size = add_pat env pat in
                       let _, size', branch = update env branch in
                       let pat, branch = close_binder span pat branch in
                       (size + size', ({ pat; branch } : match_branch)))
                     branches)
              in
              let size = List.fold_left (fun n n' -> n + n') 0 sizes in
              (env, size, Match branches)
        in
        (env, s0 + s1 + 1, { e with e = Switch (scrut, switch) })
    | Loop loop ->
        let (env, size), inputs =
          List.fold_left_map
            (fun (env, size) e ->
              let env, size', e = update env e in
              ((env, size + size' + 1), e))
            (env, 0) loop.inputs
        in
        let size', loop_body =
          let ({ inputs; loop_body } : loop_body) = loop.loop_body in
          let _, inputs, loop_body = open_binders ctx span inputs loop_body in
          let env', size =
            List.fold_left
              (fun (env, size) input ->
                let env, size' = add_pat env input in
                (env, size + size'))
              (env, 0) inputs
          in
          let _, size', loop_body = update env' loop_body in
          let inputs, loop_body = close_binders span inputs loop_body in
          let loop_body : loop_body = { inputs; loop_body } in
          (size + size', loop_body)
        in
        let loop = { loop with inputs; loop_body } in
        (env, size + size' + 1, { e with e = Loop loop })
    | StructUpdate { struct_id; init; updates } ->
        let env, size, init =
          match init with
          | None -> (env, 0, None)
          | Some init ->
              let env, size, init = update env init in
              (env, size, Some init)
        in
        let (env, size), updates =
          List.fold_left_map
            (fun (env, size) (fid, e) ->
              let env, size', e = update env e in
              ((env, size + size' + 1), (fid, e)))
            (env, size) updates
        in
        (env, size, { e with e = StructUpdate { struct_id; init; updates } })
    | Meta (m, e') ->
        let env, size, e' = update env e' in
        (env, size + 1, { e with e = Meta (m, e') })
  and update env e =
    let env, size, e = update_aux env e in
    let env = add_expr env size e in
    (env, size, e)
  in

  let body =
    Option.map
      (fun (body : fun_body) ->
        (* Quick check: explore while updating only if necessary *)
        if needs_update body.body then
          let _, body = open_fun_body ctx span body in
          let env =
            List.fold_left
              (fun env input ->
                let env, _ = add_pat env input in
                env)
              TyMap.empty body.inputs
          in
          let _, _, e = update env body.body in
          let body = { body with body = e } in
          close_fun_body span body
        else body)
      def.body
  in
  { def with body }

(* TODO: reorder the branches of the matches/switche
   TODO: we might want to leverage more the assignment meta-data, for
   aggregates for instance. *)
let passes :
    ((unit -> bool) option * string * (ctx -> fun_decl -> fun_decl)) list =
  [
    (* Find informative names for the unnamed variables *)
    (None, "compute_pretty_names", compute_pretty_names);
    (* Remove the meta-information (it's only useful to compute the pretty names).

       Remark: some passes below use the fact that we removed the meta-data
       (otherwise we would have to "unmeta" expressions before matching) *)
    (None, "remove_meta_def", remove_meta);
    (* Convert the unit variables to [()] if they are used as right-values or
     * [_] if they are used as left values. *)
    (None, "unit_vars_to_unit", unit_vars_to_unit);
    (* Introduce [massert] - we do this early because it makes the AST nicer to
       read by removing indentation. *)
    (Some (fun _ -> !Config.intro_massert), "intro_massert", intro_massert);
    (* Simplify the let-bindings which bind the fields of ADTs
       which only have one variant (i.e., enumerations with one variant
       and structures). *)
    (None, "simplify_decompose_struct", simplify_decompose_struct);
    (* Introduce the special structure create/update expressions *)
    (None, "intro_struct_updates", intro_struct_updates);
    (* Simplify the lambdas *)
    (None, "simplify_lambdas", simplify_lambdas);
    (* Simplify the let-bindings *)
    (None, "simplify_let_bindings", simplify_let_bindings);
    (* Inline the useless variable reassignments *)
    ( None,
      "inline_useless_var_assignments",
      inline_useless_var_assignments ~inline_named:true ~inline_const:true
        ~inline_pure:true ~inline_identity:true ~inline_loop_back_calls:false );
    (* Simplify the lambdas by applying beta-reduction *)
    (None, "apply_beta_reduction", apply_beta_reduction);
    (* Eliminate the box functions - note that the "box" types were eliminated
       during the symbolic to pure phase: see the comments for [eliminate_box_functions] *)
    (None, "eliminate_box_functions", eliminate_box_functions);
    (* Remove the duplicated function calls *)
    (None, "simplify_duplicate_calls", simplify_duplicate_calls);
    (* Merge let bindings which bind an expression then decompose a tuple *)
    ( Some (fun _ -> !Config.merge_let_app_decompose_tuple),
      "merge_let_app_then_decompose_tuple",
      merge_let_app_then_decompose_tuple );
    (* Filter the useless variables, assignments, function calls, etc. *)
    (None, "filter_useless", filter_useless);
    (* Do the following kind of transformations (note that such expressions
       are frequently introduced when joining the contexts after a branching
       expression):

       {[
         let (b', x) := if b then (true, 1) else (false, 0) in
         ...

           ~~>

         let x := if b then 1 else 0 in
         let b' := b in // inlined afterwards by [inline_useless_var_assignments]
         ...
       ]}
    *)
    (None, "simplify_let_branching", simplify_let_branching);
    (* Simplify the lets immediately followed by a return.

       Ex.:
       {[
         x <-- f y;
         Return x

           ~~>

         f y
       ]}
    *)
    (None, "simplify_let_then_ok", simplify_let_then_ok ~ignore_loops:true);
    (* Simplify the lambdas again: this simplification might have been unlocked
       by [simplify_let_then_ok], and is useful for [filter_loop_useless_inputs_outputs] *)
    (None, "simplify_lambdas (pass 2)", simplify_lambdas);
    (* Decompose the loop outputs if they have the type tuple.

       We do so to make it simpler to analyze the relationship between inputs
       and outputs and that we need to do in [simplify_loop_output_conts],
       [filter_loop_useless_inputs_outputs], etc. Importantly, the passes below
       will not be correct (they might crash) if we don't do this here first.
    *)
    (None, "decompose_loop_outputs", decompose_loop_outputs);
    (* Simplify and filter the loop outputs.

       Note that calling [simplify_loop_output_conts] *before*
       [filter_loop_useless_inputs_outputs] leads to better code. In particular,
       [simplify_loop_output_conts] inlines some values inside the loop, which
       thus become necessary inputs and do not get eliminated by [simplify_loop_output_conts]
       in case we extract the loops to recursive functions (or simply introduce auxiliary
       functions for the loops). If those inputs get eliminated, we introduce binders back
       when actually introducing the auxiliary loop functions, but then the order of the
       inputs is not preserved anymore.
    *)
    (None, "simplify_loop_output_conts", simplify_loop_output_conts);
    (* [simplify_loop_output_conts] also introduces simplification opportunities
       for those 2 passes.
       TODO: it would be good to do both at once. *)
    (None, "apply_beta_reduction (pass 3)", apply_beta_reduction);
    ( None,
      "inline_useless_var_assignments (pass 3)",
      inline_useless_var_assignments ~inline_named:true ~inline_const:true
        ~inline_pure:true ~inline_identity:true ~inline_loop_back_calls:true );
    (* Filter the useless loop inputs and outputs.

       For now we do not filter the constant inputs: we will do this after
       (optionally) introducing auxiliary definitions for the loops: this allows
       us to make sure we preserve the order of the constant inputs. *)
    ( None,
      "filter_loop_useless_inputs_outputs",
      filter_loop_useless_inputs_outputs ~filter_constant_inputs:false );
    (* [filter_loop_useless_inputs_outputs] might have triggered simplification
       opportunities for [apply_beta_reduction] and [inline_useless_var_assignments].

       In particular, it often introduces expressions of the shape:
       {[
         let x = (fun y -> y) v in
         ...
       ]}
    *)
    (None, "apply_beta_reduction (pass 2)", apply_beta_reduction);
    ( None,
      "inline_useless_var_assignments (pass 2)",
      inline_useless_var_assignments ~inline_named:true ~inline_const:true
        ~inline_pure:true ~inline_identity:true ~inline_loop_back_calls:false );
    (* Reorder some of the loop outputs to permit [loops_to_recursive] to succeed *)
    (None, "reorder_loop_outputs", reorder_loop_outputs);
    (* Change the structure of the loops if we can simplify their backward
       functions. This is in preparation of [decompose_loops], which introduces
       auxiliary (and potentially recursive) functions. *)
    (None, "loops_to_recursive", loops_to_recursive);
    (* Introduce match expressions where let-bindings need to open enumerations *)
    (None, "let_to_match", let_to_match);
    (None, "flatten_struct_updates", flatten_struct_updates);
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
    (* Simplify the lambdas again *)
    (None, "simplify_lambdas (pass 2)", simplify_lambdas);
    (* Simplify the let-bindings - some simplifications may have been unlocked by
       the pass above (for instance, the lambda simplification) *)
    (None, "simplify_let_bindings (pass 2)", simplify_let_bindings);
    (* Inline the useless vars again *)
    ( None,
      "inline_useless_var_assignments (pass 4)",
      inline_useless_var_assignments ~inline_named:true ~inline_const:true
        ~inline_pure:false ~inline_identity:true ~inline_loop_back_calls:false
    );
    (* Filter the useless variables again *)
    (None, "filter_useless (pass 2)", filter_useless);
    (* Simplify the let-then return again (the lambda simplification may have
       unlocked more simplifications here) *)
    ( None,
      "simplify_let_then_ok (pass 2)",
      simplify_let_then_ok ~ignore_loops:false );
    (* Simplify the array/slice manipulations by introducing calls to [array_update]
       [slice_update] *)
    (None, "simplify_array_slice_update", simplify_array_slice_update);
    (* Simplify the let-then return again (the array simplification may have
       unlocked more simplifications here) *)
    ( None,
      "simplify_let_then_ok (pass 3)",
      simplify_let_then_ok ~ignore_loops:false );
    (* Decompose the monadic let-bindings - used by Coq *)
    ( Some (fun _ -> !Config.decompose_monadic_let_bindings),
      "decompose_monadic_let_bindings",
      decompose_monadic_let_bindings );
    (* Decompose nested let-patterns *)
    ( Some (fun _ -> !Config.decompose_nested_let_patterns),
      "decompose_nested_let_patterns",
      decompose_nested_let_patterns );
    (* Unfold the monadic let-bindings *)
    ( Some (fun _ -> !Config.unfold_monadic_let_bindings),
      "unfold_monadic_let_bindings",
      unfold_monadic_let_bindings );
    (* Introduce calls to [toResult] to lift pure function calls to monadic
       function calls *)
    ( Some (fun _ -> !Config.lift_pure_function_calls),
      "lift_pure_function_calls",
      lift_pure_function_calls );
  ]

(** Apply all the micro-passes to a function. *)
let apply_passes_to_def (ctx : ctx) (def : fun_decl) : fun_decl =
  List.fold_left
    (fun def (option, pass_name, pass) ->
      let apply =
        match option with
        | None -> true
        | Some option -> option ()
      in

      if apply then (
        [%ltrace "About to apply: '" ^ pass_name ^ "'"];
        let def' = pass ctx def in
        let updated = string_of_bool (def' <> def) in
        [%ltrace
          "After applying '" ^ pass_name ^ "'" ^ "(updated:" ^ updated
          ^ "):\n\n"
          ^ fun_decl_to_string ctx def'];
        def')
      else (
        [%ltrace "Ignoring " ^ pass_name ^ " due to the configuration\n"];
        def))
    def passes

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

(** Introduce type annotations.

    See [add_type_annotations].

    Note that we use the context only for printing. *)
let add_type_annotations_to_fun_decl (trans_ctx : trans_ctx)
    (trans_funs : pure_fun_translation FunDeclId.Map.t)
    (builtin_sigs : fun_sig Builtin.BuiltinFunIdMap.t)
    (type_decls : type_decl TypeDeclId.Map.t) (def : fun_decl) : fun_decl =
  let fmt = trans_ctx_to_pure_fmt_env trans_ctx in
  [%ldebug PrintPure.fun_decl_to_string fmt def];
  let span = def.item_meta.span in
  let _, fresh_fvar_id = FVarId.fresh_stateful_generator () in
  let fmt = trans_ctx_to_pure_fmt_env trans_ctx in
  let texpr_to_string (x : texpr) : string =
    PrintPure.texpr_to_string fmt false "" "  " x
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
  let mk_type_annot (e : texpr) : texpr =
    { e = Meta (TypeAnnot, e); ty = e.ty }
  in

  let rec visit (ty : ty) (e : texpr) : texpr =
    [%ldebug "visit:\n- ty: " ^ ty_to_string ty ^ "\n- e: " ^ texpr_to_string e];
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
        [%ldebug "exploring: " ^ texpr_to_string e];
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
              [%ldebug
                "- ty: " ^ ty_to_string ty ^ "\n- field_tys:\n"
                ^ String.concat "\n" (List.map ty_to_string field_tys)
                ^ "\n- supd.update:\n"
                ^ String.concat "\n"
                    (List.map
                       (fun (fid, f) ->
                         FieldId.to_string fid ^ " -> " ^ texpr_to_string f)
                       supd.updates)];
              (* Update the fields *)
              let updates =
                List.map
                  (fun ((fid, fe) : _ * texpr) ->
                    match FieldId.nth_opt field_tys fid with
                    | None -> [%internal_error] span
                    | Some field_ty -> (fid, visit field_ty fe))
                  supd.updates
              in
              { e with e = StructUpdate { supd with updates } }
          | _ ->
              (* The type of the structure is unknown: we add a type annotation.
                 From there, the type of the field updates is known *)
              let updates =
                List.map
                  (fun ((fid, fe) : _ * texpr) -> (fid, visit fe.ty fe))
                  supd.updates
              in
              let e = { e with e = StructUpdate { supd with updates } } in
              (* Add the type annotation, if the backend is Lean *)
              if Config.backend () = Lean then mk_type_annot e else e
        end
    | Meta (meta, e') ->
        let ty = if meta = TypeAnnot then e'.ty else ty in
        { e with e = Meta (meta, visit ty e') }
  and visit_App (ty : ty) (e : texpr) : texpr =
    [%ldebug
      "visit_App:\n- ty: " ^ ty_to_string ty ^ "\n- e: " ^ texpr_to_string e];
    (* Deconstruct the app *)
    let f, args = destruct_apps e in
    (* Compute the types of the arguments: it depends on the function *)
    let mk_holes () = List.map (fun _ -> hole) args in
    let mk_known () = List.map (fun (e : texpr) -> e.ty) args in
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
    (* evaluate to: (function type, arguments types, needs annotations) *)
    let compute_known_tys_from_fun_id (qualif : qualif) (fid : fun_id) :
        ty * ty list * bool =
      [%ldebug "fid: " ^ PrintPure.regular_fun_id_to_string fmt fid];
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
          | Loop _ | RecLoopCall _ -> (hole, mk_holes (), true)
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
    let e = [%add_loc] mk_apps span f args in
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
  map_open_all_fun_decl_body_expr fresh_fvar_id
    (fun (body : texpr) -> visit body.ty body)
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
  let add_annot (decl : fun_decl) =
    try
      add_type_annotations_to_fun_decl trans_ctx trans_funs_map builtin_sigs
        type_decls decl
    with Errors.CFailure error ->
      let name = name_to_string trans_ctx decl.item_meta.name in
      let name_pattern =
        try
          name_to_pattern_string (Some decl.item_meta.span) trans_ctx
            decl.item_meta.name
        with Errors.CFailure _ ->
          "(could not compute the name pattern due to a different error)"
      in
      [%save_error_opt_span] error.span
        ("Could not add type annotations to the fun declaration '" ^ name
       ^ " because of previous error\nName pattern: '" ^ name_pattern ^ "'");
      (* Keep the unchanged decl *)
      decl
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

  let mk_ctx () : ctx =
    let _, fresh_fvar_id = FVarId.fresh_stateful_generator () in
    { trans_ctx; type_decls; fun_decls; fresh_fvar_id }
  in

  (* Apply the micro-passes *)
  let apply (f : fun_decl) : pure_fun_translation =
    let ctx = mk_ctx () in

    (* Apply the micro-passes *)
    let f = apply_passes_to_def ctx f in

    (* Decompose the loops *)
    let f, loops = decompose_loops ctx f in

    (* Filter the constant inputs *)
    let simplify =
      filter_loop_useless_inputs_outputs ~filter_constant_inputs:true ctx
    in
    let f = simplify f in
    let loops = List.map simplify loops in

    (* Decomposing the loops and filtering the inputs might have introduced
       expressions of the shape:
       [let (x, y) = e in ok (x, y)]
       We need to resimplify those. *)
    let simplify = simplify_let_then_ok ~ignore_loops:false ctx in
    let f = simplify f in
    let loops = List.map simplify loops in

    [%ltrace
      let funs = f :: loops in
      "After decomposing loops:\n\n"
      ^ String.concat "\n\n" (List.map (fun_decl_to_string ctx) funs)];

    let trans : pure_fun_translation = { f; loops } in

    (* Introduce the fuel and the state, if necessary.

       We do this last, because some other passes need to manipulate the
       functions *wihout* fuel and state (otherwise it messes up the
       parameter manipulations). *)
    let trans = if !Config.use_fuel then add_fuel ctx trans else trans in

    trans
  in
  let transl =
    let num_decls = List.length transl in
    ProgressBar.with_parallel_reporter num_decls
      "Post-processed translated functions: " (fun report ->
        Parallel.parallel_map
          (fun x ->
            let x = apply x in
            report 1;
            x)
          transl)
  in

  (* Add the type annotations - we add those only now because we need
     to use the final types of the functions (in particular, we introduce
     loop functions and modify their types above).

     TODO: move
  *)
  let transl = add_type_annotations trans_ctx transl builtin_sigs type_decls in

  (* Update the "reducible" attribute *)
  compute_reducible (mk_ctx ()) transl
