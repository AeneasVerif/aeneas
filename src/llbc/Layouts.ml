(** Queries about the memory layouts computed by Charon. *)

open Types
open Expressions
open LlbcAst

(** The alignments of the addresses that some calls to [as_ptr] and [as_mut_ptr]
    convert to raw pointers, when they are larger than the alignments of the
    element types. We compute them in the pre-passes (see
    [PrePasses.compute_view_alignment_hints]) because the places are not visible
    anymore when we evaluate the calls. *)
let view_alignment_hints : (Meta.span, int) Hashtbl.t = Hashtbl.create 16

let size_expr_constant (e : size_expr) : int option =
  match e with
  | SizeExprConstant { kind = CInteger (UnsignedInteger (_, v)); _ } ->
      Some (Z.to_int v)
  | _ -> None

(** The layout of a type declaration, provided all the targets agree on it *)
let type_decl_layout (decl : type_decl) : layout option =
  match decl.layout with
  | [] -> None
  | (_, layout) :: rest ->
      if List.for_all (fun (_, l) -> l = layout) rest then Some layout else None

let target_ptr_size (crate : crate) : int option =
  match crate.target_information with
  | (_, info) :: rest
    when List.for_all
           (fun (_, i) -> i.target_pointer_size = info.target_pointer_size)
           rest -> Some info.target_pointer_size
  | _ -> None

let decl_align (crate : crate) (id : TypeDeclId.id) : int option =
  match TypeDeclId.Map.find_opt id crate.type_decls with
  | None -> None
  | Some decl -> (
      match type_decl_layout decl with
      | Some { align = { chosen = Some e; _ }; _ } -> size_expr_constant e
      | _ -> None)

(** The alignment of a type, if it is known *)
let rec type_align (crate : crate) (ptr_size : int) (ty : ty) : int option =
  match ty with
  | TScalar (TInteger ity) -> (
      match ity with
      | Unsigned Usize | Signed Isize -> Some ptr_size
      | Unsigned U8 | Signed I8 -> Some 1
      | Unsigned U16 | Signed I16 -> Some 2
      | Unsigned U32 | Signed I32 -> Some 4
      | Unsigned U64 | Signed I64 -> Some 8
      | Unsigned U128 | Signed I128 -> Some 16)
  | TScalar TBool -> Some 1
  | TScalar TChar -> Some 4
  | TArray (ty, _, _) | TSlice (ty, _) -> type_align crate ptr_size ty
  | TAdt { id; builtin = None; generics } when generics.types = [] ->
      decl_align crate id
  | _ -> None

(** The offset of a field of a structure, if it is known *)
let field_offset (crate : crate) (id : TypeDeclId.id) (field_id : FieldId.id) :
    int option =
  match TypeDeclId.Map.find_opt id crate.type_decls with
  | None -> None
  | Some decl -> (
      match type_decl_layout decl with
      | Some { variant_layouts = [ Some { field_offsets; _ } ]; _ } -> (
          match FieldId.nth_opt field_offsets field_id with
          | Some { chosen = Some offset; _ } -> Some offset
          | _ -> None)
      | _ -> None)

let rec gcd (a : int) (b : int) : int = if b = 0 then a else gcd b (a mod b)

(** The alignment of the address of a place: the places are stored at addresses
    aligned for their types, but a place may also be more aligned than its type,
    for instance if it is a field of a [#[repr(align(n))]] structure. *)
let rec place_align (crate : crate) (ptr_size : int) (p : place) : int option =
  let ty_align = type_align crate ptr_size p.ty in
  let max_opt (a : int option) (b : int option) =
    match (a, b) with
    | Some a, Some b -> Some (max a b)
    | Some a, None | None, Some a -> Some a
    | None, None -> None
  in
  match p.kind with
  | PlaceLocal _ | PlaceGlobal _ -> ty_align
  | PlaceProjection (_, Deref) -> ty_align
  | PlaceProjection (parent, Field (None, field_id)) -> (
      match parent.ty with
      | TAdt { id; builtin = None; _ } -> (
          match
            (place_align crate ptr_size parent, field_offset crate id field_id)
          with
          | Some parent_align, Some offset ->
              max_opt (Some (gcd parent_align offset)) ty_align
          | _ -> ty_align)
      | _ -> ty_align)
  | PlaceProjection _ -> ty_align

(** The byte layout of a structure for which we generate a byte representation
    (see [ExtractTypes.extract_type_decl_byte_repr]) *)
type struct_layout = {
  size : int;
  align : int;
  fields : (FieldId.id * int) list;
      (** The fields, sorted by increasing offsets, with their offsets *)
}

let const_int (c : constant_expr) : int option =
  match c.kind with
  | CInteger (UnsignedInteger (_, v)) -> Some (Z.to_int v)
  | _ -> None

(** The size of a type which has a byte representation which does not depend on
    the target (we exclude [usize] and [isize], whose size depends on the
    platform in the Lean model). *)
let rec fixed_size (crate : crate) (ty : ty) : int option =
  match ty with
  | TScalar (TInteger ity) -> (
      match ity with
      | Unsigned U8 | Signed I8 -> Some 1
      | Unsigned U16 | Signed I16 -> Some 2
      | Unsigned U32 | Signed I32 -> Some 4
      | Unsigned U64 | Signed I64 -> Some 8
      | Unsigned U128 | Signed I128 -> Some 16
      | Unsigned Usize | Signed Isize -> None)
  | TArray (ty, n, _) -> (
      match (fixed_size crate ty, const_int n) with
      | Some size, Some n -> Some (size * n)
      | _ -> None)
  | TAdt { id; builtin = None; generics } when generics.types = [] -> (
      match struct_layout crate id with
      | Some layout -> Some layout.size
      | None -> None)
  | _ -> None

(** The byte layout of a structure, if all its fields have byte representations
    of fixed sizes and we know its layout *)
and struct_layout (crate : crate) (id : TypeDeclId.id) : struct_layout option =
  match TypeDeclId.Map.find_opt id crate.type_decls with
  | Some ({ kind = Struct fields; _ } as decl) when decl.generics.types = []
    -> (
      match type_decl_layout decl with
      | Some
          {
            size = { chosen = Some size; _ };
            align = { chosen = Some align; _ };
            variant_layouts = [ Some { field_offsets; _ } ];
            _;
          } -> (
          match (size_expr_constant size, size_expr_constant align) with
          | Some size, Some align -> (
              let fields =
                List.mapi
                  (fun i ((f : field), (o : offset_expr)) ->
                    (FieldId.of_int i, fixed_size crate f.field_ty, o.chosen))
                  (List.combine fields field_offsets)
              in
              if
                List.exists
                  (fun (_, s, o) -> Option.is_none s || Option.is_none o)
                  fields
              then None
              else
                let fields =
                  List.map
                    (fun (id, s, o) -> (id, Option.get s, Option.get o))
                    fields
                in
                let fields =
                  List.sort (fun (_, _, o0) (_, _, o1) -> compare o0 o1) fields
                in
                (* Check that the fields don't overlap and fit *)
                let rec check (cur : int) fields =
                  match fields with
                  | [] -> cur <= size
                  | (_, s, o) :: fields -> o >= cur && check (o + s) fields
                in
                match check 0 fields with
                | true when align > 0 && size mod align = 0 ->
                    Some
                      {
                        size;
                        align;
                        fields = List.map (fun (id, _, o) -> (id, o)) fields;
                      }
                | _ -> None)
          | _ -> None)
      | _ -> None)
  | _ -> None

(** The structures whose values are accessed through raw pointers: those are the
    structures for which we generate byte representations. *)
let byte_repr_structs (crate : crate) : TypeDeclId.Set.t =
  let found = ref TypeDeclId.Set.empty in
  let rec add_ty (ty : ty) : unit =
    match ty with
    | TArray (ty, _, _) | TSlice (ty, _) -> add_ty ty
    | TAdt { id; builtin = None; _ } ->
        if not (TypeDeclId.Set.mem id !found) then
          if Option.is_some (struct_layout crate id) then (
            found := TypeDeclId.Set.add id !found;
            match TypeDeclId.Map.find_opt id crate.type_decls with
            | Some { kind = Struct fields; _ } ->
                List.iter (fun (f : field) -> add_ty f.field_ty) fields
            | _ -> ())
    | _ -> ()
  in
  let visitor =
    object
      inherit [_] iter_statement as super

      method! visit_ty env ty =
        (match ty with
        | TRawPtr (ty, _) -> add_ty ty
        | _ -> ());
        super#visit_ty env ty
    end
  in
  FunDeclId.Map.iter
    (fun _ (d : fun_decl) ->
      List.iter (visitor#visit_ty ()) (d.signature.output :: d.signature.inputs);
      match d.body with
      | StructuredBody body ->
          List.iter
            (fun (l : local) -> visitor#visit_ty () l.local_ty)
            body.locals.locals;
          visitor#visit_block () body.body
      | _ -> ())
    crate.fun_decls;
  !found

let byte_repr_structs_memo : (crate * TypeDeclId.Set.t) option ref = ref None

let get_byte_repr_structs (crate : crate) : TypeDeclId.Set.t =
  match !byte_repr_structs_memo with
  | Some (c, s) when c == crate -> s
  | _ ->
      let s = byte_repr_structs crate in
      byte_repr_structs_memo := Some (crate, s);
      s

(** Does a type have a byte representation in the Lean model? *)
let rec has_byte_repr (crate : crate) (ty : ty) : bool =
  match ty with
  | TScalar (TInteger _) -> true
  | TVar (Free _) ->
      (* The functions which manipulate the values of a type parameter through
         raw pointers require a byte representation for it (see
         [get_byte_repr_type_params]) *)
      true
  | TArray (ty, _, _) -> has_byte_repr crate ty
  | TAdt { id; builtin = None; _ } ->
      TypeDeclId.Set.mem id (get_byte_repr_structs crate)
  | _ -> false

(** {1 Byte representations of type parameters}

    The generic functions which manipulate values of a type parameter [T]
    through raw pointers require a byte representation of [T]: we add an
    instance argument [[ByteRepr T]] to their signatures. *)

(** The indices of the type parameters of a type declaration which occur in
    pointee types of raw pointers in its fields *)
let rec decl_pointee_params (crate : crate) (visiting : TypeDeclId.Set.t)
    (memo : (TypeDeclId.id, TypeVarId.Set.t) Hashtbl.t) (id : TypeDeclId.id) :
    TypeVarId.Set.t =
  match Hashtbl.find_opt memo id with
  | Some s -> s
  | None ->
      if TypeDeclId.Set.mem id visiting then TypeVarId.Set.empty
      else
        let visiting = TypeDeclId.Set.add id visiting in
        let s =
          match TypeDeclId.Map.find_opt id crate.type_decls with
          | Some { kind = Struct fields; _ } ->
              List.fold_left
                (fun s (f : field) ->
                  TypeVarId.Set.union s
                    (pointee_vars crate visiting memo false f.field_ty))
                TypeVarId.Set.empty fields
          | Some { kind = Enum variants; _ } ->
              List.fold_left
                (fun s (v : variant) ->
                  List.fold_left
                    (fun s (f : field) ->
                      TypeVarId.Set.union s
                        (pointee_vars crate visiting memo false f.field_ty))
                    s v.fields)
                TypeVarId.Set.empty variants
          | _ -> TypeVarId.Set.empty
        in
        Hashtbl.replace memo id s;
        s

(** The type variables which occur in pointee types of raw pointers in a type
    ([under_ptr]: are we under a raw pointer?) *)
and pointee_vars (crate : crate) (visiting : TypeDeclId.Set.t)
    (memo : (TypeDeclId.id, TypeVarId.Set.t) Hashtbl.t) (under_ptr : bool)
    (ty : ty) : TypeVarId.Set.t =
  let explore = pointee_vars crate visiting memo in
  let union_map f l =
    List.fold_left
      (fun s x -> TypeVarId.Set.union s (f x))
      TypeVarId.Set.empty l
  in
  match ty with
  | TVar (Free v) ->
      if under_ptr then TypeVarId.Set.singleton v else TypeVarId.Set.empty
  | TRawPtr (ty, _) -> explore true ty
  | TRef (_, ty, _) | TArray (ty, _, _) | TSlice (ty, _) -> explore under_ptr ty
  | TAdt { id; builtin = None; generics } ->
      let params = decl_pointee_params crate visiting memo id in
      union_map
        (fun (i, ty) ->
          explore
            (under_ptr || TypeVarId.Set.mem (TypeVarId.of_int i) params)
            ty)
        (List.mapi (fun i ty -> (i, ty)) generics.types)
  | TAdt { generics; _ } -> union_map (explore under_ptr) generics.types
  | _ -> TypeVarId.Set.empty

(** Compute, for every function, the type parameters which require a byte
    representation *)
let compute_byte_repr_type_params (crate : crate) :
    TypeVarId.Set.t FunDeclId.Map.t =
  let memo = Hashtbl.create 16 in
  let pointee_vars = pointee_vars crate TypeDeclId.Set.empty memo in
  let needs = ref FunDeclId.Map.empty in
  let get (id : FunDeclId.id) =
    Option.value ~default:TypeVarId.Set.empty (FunDeclId.Map.find_opt id !needs)
  in
  let compute (d : fun_decl) : TypeVarId.Set.t =
    (* We leave the signatures of the opaque functions unchanged *)
    if
      not
        (match d.body with
        | StructuredBody _ -> true
        | _ -> false)
    then TypeVarId.Set.empty
    else
      let s = ref TypeVarId.Set.empty in
      let add ty = s := TypeVarId.Set.union !s (pointee_vars false ty) in
      List.iter add (d.signature.output :: d.signature.inputs);
      (match d.body with
      | StructuredBody body ->
          List.iter (fun (l : local) -> add l.local_ty) body.locals.locals;
          let visitor =
            object
              inherit [_] iter_statement as super

              method! visit_Call env call on_unwind =
                (match call.func with
                | FnOpRegular { kind = Fun g; generics } ->
                    let params = get g in
                    List.iteri
                      (fun i ty ->
                        if TypeVarId.Set.mem (TypeVarId.of_int i) params then
                          s := TypeVarId.Set.union !s (pointee_vars true ty))
                      generics.types
                | _ -> ());
                super#visit_Call env call on_unwind
            end
          in
          visitor#visit_block () body.body
      | _ -> ());
      !s
  in
  let changed = ref true in
  while !changed do
    changed := false;
    FunDeclId.Map.iter
      (fun id d ->
        let s = compute d in
        if not (TypeVarId.Set.equal s (get id)) then (
          changed := true;
          needs := FunDeclId.Map.add id s !needs))
      crate.fun_decls
  done;
  !needs

let byte_repr_type_params_memo :
    (crate * TypeVarId.Set.t FunDeclId.Map.t) option ref =
  ref None

let get_byte_repr_type_params (crate : crate) (id : FunDeclId.id) :
    TypeVarId.Set.t =
  let m =
    match !byte_repr_type_params_memo with
    | Some (c, m) when c == crate -> m
    | _ ->
        let m = compute_byte_repr_type_params crate in
        byte_repr_type_params_memo := Some (crate, m);
        m
  in
  Option.value ~default:TypeVarId.Set.empty (FunDeclId.Map.find_opt id m)
