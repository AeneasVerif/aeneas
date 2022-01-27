(** This module is used to transform the pure ASTs to ASTs ready for extraction *)

open Errors
open Pure
open CfimAstUtils
module Id = Identifiers
module T = Types
module V = Values
module E = Expressions
module A = CfimAst
module M = Modules
module S = SymbolicAst
module TA = TypesAnalysis
module L = Logging
module PP = PrintPure

(** The local logger *)
let log = L.pure_to_extract_log

type name =
  | FunName of A.FunDefId.id * T.RegionVarId.id option
  | TypeName of T.TypeDefId.id
[@@deriving show, ord]

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
 *)

let translate_fun_name (fdef : A.fun_def) (bid : T.RegionGroupId.id option) :
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
