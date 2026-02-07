open Pure
open PureUtils
open PureMicroPassesBase

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
