(** This module is used to extract the pure ASTs to various theorem provers.
    It defines utilities and helpers to make the work as easy as possible:
    we try to factorize as much as possible the different extractions to the
    backends we target.
 *)

open Errors
open Pure
open TranslateCore
module C = Contexts
module RegionVarId = T.RegionVarId

(** The local logger *)
let log = L.pure_to_extract_log

type extraction_ctx = {
  type_context : C.type_context;
  fun_context : C.fun_context;
}
(** Extraction context.

    Note that the extraction context contains information coming from the
    CFIM AST (not only the pure AST). This is useful for naming, for instance:
    we use the region information to generate the names of the backward
    functions, etc.
 *)

(** We use identifiers to look for name clashes *)
type id =
  | FunId of FunDefId.id * RegionGroupId.id option
  | TypeId of TypeDefId.id
  | VarId of VarId.id
  | UnknownId
      (** Used for stored various strings like keywords, definitions which
          should always be in context, etc. and which can't be linked to one
          of the above.
       *)
[@@deriving show, ord]

type region_group_info = {
  id : RegionGroupId.id;
      (** The id of the region group.
          Note that a simple way of generating unique names for backward
          functions is to use the region group ids.
       *)
  region_names : string option list;
      (** The names of the region variables included in this group.
          Note that names are not always available...
       *)
}

type name = Identifiers.name

type name_formatter = {
  bool_name : string;
  char_name : string;
  int_name : integer_type -> string;
  str_name : string;
  type_name : name -> string;  (** Provided a basename, compute a type name. *)
  fun_name : A.fun_id -> name -> int -> region_group_info option -> string;
      (** Inputs:
          - function id: this is especially useful to identify whether the
            function is an assumed function or a local function
          - function basename
          - number of region groups
          - region group information in case of a backward function
            (`None` if forward function)
       *)
  var_basename : name -> string;
      (** Generates a variable basename.

          Note that once the formatter generated a basename, we add an index
          if necessary to prevent name clashes.
       *)
}
(** A name formatter's role is to come up with name suggestions.
    For instance, provided some information about a function (its basename,
    information about the region group, etc.) it should come up with an
    appropriate name for the forward/backward function.
    
    It can of course apply many transformations, like changing to camel case/
    snake case, adding prefixes/suffixes, etc.
 *)

let compute_type_def_name (fmt : name_formatter) (def : type_def) : string =
  fmt.type_name def.name

(** A helper function: generates a function suffix from a region group
    information.
    TODO: move all those helpers.
*)
let default_fun_suffix (num_region_groups : int) (rg : region_group_info option)
    : string =
  (* There are several cases:
     - [rg] is `Some`: this is a forward function:
       - if there are no region groups (i.e., no backward functions) we don't
         add any suffix
       - if there are region gruops, we add "_fwd"
     - [rg] is `None`: this is a backward function:
       - this function has one region group: we add "_back"
       - this function has several backward function: we add "_back" and an
         additional suffix to identify the precise backward function
  *)
  match rg with
  | None -> if num_region_groups = 0 then "" else "_fwd"
  | Some rg ->
      assert (num_region_groups > 0);
      if num_region_groups = 1 then (* Exactly one backward function *)
        "_back"
      else if
        (* Several region groups/backward functions:
           - if all the regions in the group have names, we use those names
           - otherwise we use an index
        *)
        List.for_all Option.is_some rg.region_names
      then
        (* Concatenate the region names *)
        "_back" ^ String.concat "" (List.map Option.get rg.region_names)
      else (* Use the region index *)
        "_back" ^ RegionGroupId.to_string rg.id

(** Extract information from a function, and give this information to a
    [name_formatter] to generate a function's name.
    
    Note that we need region information coming from CFIM (when generating
    the name for a backward function, we try to use the names of the regions
    to 
 *)
let compute_fun_def_name (ctx : extraction_ctx) (fmt : name_formatter)
    (fun_id : A.fun_id) (rg_id : RegionGroupId.id option) : string =
  (* Lookup the function CFIM signature (we need the region information) *)
  let sg = CfimAstUtils.lookup_fun_sig fun_id ctx.fun_context.fun_defs in
  let basename = CfimAstUtils.lookup_fun_name fun_id ctx.fun_context.fun_defs in
  (* Compute the regions information *)
  let num_region_groups = List.length sg.regions_hierarchy in
  let rg_info =
    match rg_id with
    | None -> None
    | Some rg_id ->
        let rg = RegionGroupId.nth sg.regions_hierarchy rg_id in
        let regions =
          List.map (fun rid -> RegionVarId.nth sg.region_params rid) rg.regions
        in
        let region_names =
          List.map (fun (r : T.region_var) -> r.name) regions
        in
        Some { id = rg.id; region_names }
  in
  fmt.fun_name fun_id basename num_region_groups rg_info

(*
  let name_to_string (n : name) : string = show_name n

  module NameOrderedType = struct
    type t = name

    let compare = compare_name

    let to_string = name_to_string

    let pp_t = pp_name

    let show_t = show_name
  end

  module NameMap = Collections.MakeMapInj (NameOrderedType) (Id.NameOrderedType)
  (** Notice that we use the *injective* map to map identifiers to names.

      Of course, even if those names (which are string lists) don't collide,
      when converting them to strings we can still introduce collisions: we
      check that later.

      Note that we use injective maps for sanity: though we write the name
      generation with collision in mind, it is always good to have such checks.
  *)*)

(*let translate_fun_name (fdef : A.fun_def) (bid : T.RegionGroupId.id option) :
      Id.name =
    let sg = fdef.signature in
    (* General function to generate a suffix for a region group
     * (i.e., an abstraction)*)
    let rg_to_string (rg : T.region_var_group) : string =
      (* We are just a little bit smart:
         - if there is exactly one region id in the region group and this region
           has a name, we use this name
         - otherwise, we use the region number (note that region names shouldn't
           start with numbers)
      *)
      match rg.T.regions with
      | [ rid ] -> (
          let rvar = T.RegionVarId.nth sg.region_params rid in
          match rvar.name with
          | None -> T.RegionGroupId.to_string rg.T.id
          | Some name -> name)
      | _ -> T.RegionGroupId.to_string rg.T.id
    in
    (* There are several cases:
       - this is a forward function: we add "_fwd"
       - this is a backward function:
         - this function has one backward function: we add "_back"
         - this function has several backward function: we add "_back" and an
           additional suffix to identify the precise backward function
    *)
    let suffix =
      match bid with
      | None -> "_fwd"
      | Some bid -> (
          match sg.regions_hierarchy with
          | [] ->
              failwith "Unreachable"
              (* we can't get there if we ask for a back function *)
          | [ _ ] ->
              (* Exactly one backward function *)
              "_back"
          | _ ->
              (* Several backward functions *)
              let rg = T.RegionGroupId.nth sg.regions_hierarchy bid in
              "_back" ^ rg_to_string rg)
    in
    (* Final name *)
    let rec add_to_last (n : Id.name) : Id.name =
      match n with
      | [] -> failwith "Unreachable"
      | [ x ] -> [ x ^ suffix ]
      | x :: n -> x :: add_to_last n
    in
    add_to_last fdef.name

  (** Generates a name for a type (simply reuses the name in the definition) *)
  let translate_type_name (def : T.type_def) : Id.name = def.T.name
*)
