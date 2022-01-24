open Errors
module Id = Identifiers
module T = Types
module V = Values
module E = Expressions
module A = CfimAst
module M = Modules
module S = SymbolicAst
open Pure

type name =
  | FunName of A.FunDefId.id * V.BackwardFunctionId.id option
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

let fun_to_name (fdef : A.fun_def) (bid : V.BackwardFunctionId.id option) :
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
            (* Several backward functions - note that **we use the backward function id
             * as if it were a region group id** (there is a direct mapping between the
             * two - TODO: merge them) *)
            let rg = V.BackwardFunctionId.nth sg.regions_hierarchy bid in
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
let type_to_name (def : T.type_def) : Id.name = def.T.name

type type_context = { type_defs : type_def TypeDefId.Map.t }

type fun_context = unit
(** TODO *)

type synth_ctx = {
  names : NameMap.t;
  type_context : type_context;
  fun_context : fun_context;
  declarations : M.declaration_group list;
}

let rec translate_sty (ctx : synth_ctx) (ty : T.sty) : ty =
  let translate = translate_sty ctx in
  match ty with
  | T.Adt (type_id, regions, tys) ->
      assert (regions = []);
      let tys = List.map translate tys in
      Adt (type_id, tys)
  | TypeVar vid -> TypeVar vid
  | Bool -> Bool
  | Char -> Char
  | Never -> failwith "Unreachable"
  | Integer int_ty -> Integer int_ty
  | Str -> Str
  | Array ty -> Array (translate ty)
  | Slice ty -> Slice (translate ty)
  | Ref (_, rty, _) -> translate rty

let translate_field (ctx : synth_ctx) (f : T.field) : field =
  let field_name = f.field_name in
  let field_ty = translate_sty ctx f.field_ty in
  { field_name; field_ty }

let translate_fields (ctx : synth_ctx) (fl : T.field list) : field list =
  List.map (translate_field ctx) fl

let translate_variant (ctx : synth_ctx) (v : T.variant) : variant =
  let variant_name = v.variant_name in
  let fields = translate_fields ctx v.fields in
  { variant_name; fields }

let translate_variants (ctx : synth_ctx) (vl : T.variant list) : variant list =
  List.map (translate_variant ctx) vl

(** Translate a type def kind to IM *)
let translate_type_def_kind (ctx : synth_ctx) (kind : T.type_def_kind) :
    type_def_kind =
  match kind with
  | T.Struct fields -> Struct (translate_fields ctx fields)
  | T.Enum variants -> Enum (translate_variants ctx variants)

(** Translate a type definition from IM 

    TODO: this is not symbolic to pure but IM to pure. Still, I don't see the
    point of moving this definition for now.
 *)
let translate_type_def (ctx : synth_ctx) (def : T.type_def) :
    synth_ctx * type_def =
  (* Translate *)
  let def_id = def.T.def_id in
  let name = type_to_name def in
  let type_params = def.type_params in
  let kind = translate_type_def_kind ctx def.T.kind in
  let def = { def_id; name; type_params; kind } in
  (* Insert in the context *)
  (* type context *)
  let type_context = ctx.type_context in
  let type_defs = type_context.type_defs in
  let type_defs = TypeDefId.Map.add def_id def type_defs in
  let type_context = { type_defs } in
  (* names map *)
  let names = NameMap.add (TypeName def_id) name ctx.names in
  (* update the fields *)
  let ctx = { ctx with type_context; names } in
  (ctx, def)
