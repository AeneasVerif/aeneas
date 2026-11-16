(** Detect the shared references to types with interior mutability.

    Aeneas translates a shared reference [&T] to the value of type [T] it points
    to. This is only sound if nothing can modify the memory behind the reference
    while it is alive, which is not the case if [T] contains an [UnsafeCell].
    For instance, [Cell::set(&self, ...)] and [AtomicU32::fetch_add(&self, ...)]
    modify the cell behind a shared reference. The pure signatures we generate
    for them can't return the new state of the cell (e.g.,
    [Cell.set : Cell T -> T -> Result Unit]), and [Cell.get c] is a function of
    [c] only: the generated model of a Rust program which writes then reads a
    cell can be used to prove false theorems (see
    https://github.com/AeneasVerif/aeneas/issues/1525).

    Until interior mutability is modeled (e.g., with a ghost state), we reject
    the code which uses such references. The user can ask for the unsound
    translation with [-allow-interior-mutability]. *)

open Types
open LlbcAst

(** Is this an opaque type of the standard library which has interior mutability
    (or which behaves like it, like the channels)?

    We don't see the fields of opaque types: we can only look at their names. We
    look at the beginning of the paths, and at the last identifier for
    [core::cell], because the module hierarchy of the standard library changes
    (e.g., [std::sync::poison::mutex::Mutex]). *)
let is_std_interior_mutable_name (name : name) : bool =
  let idents =
    List.map
      (fun (e : path_elem) ->
        match e with
        | PeIdent (s, _) -> Some s
        | _ -> None)
      name
  in
  match idents with
  | Some "core" :: Some "cell" :: _ :: _ -> (
      match List.rev idents with
      | Some
          ( "Cell"
          | "RefCell"
          | "UnsafeCell"
          | "SyncUnsafeCell"
          | "OnceCell"
          | "LazyCell" )
        :: _ -> true
      | _ -> false)
  | Some "core" :: Some "sync" :: Some "atomic" :: _ :: _ -> true
  | Some "std" :: Some "sync" :: _ :: _ -> true
  | _ -> false

type ctx = {
  type_decls : type_decl TypeDeclId.Map.t;
  im_cache : bool TypeDeclId.TreeMap.t ref;
      (** Memoizes {!is_interior_mutable} for the ADTs without generics *)
}

let is_non_generic (generics : generic_args) : bool =
  generics.types = []
  && generics.const_generics = []
  && generics.trait_refs = []

(** The maximum depth at which we explore the declarations of the ADTs. This
    protects us against types with polymorphic recursion. *)
let max_depth = 32

(** Does the type contain an [UnsafeCell], looking at the fields of the ADTs but
    not behind references and pointers?

    [stack] contains the ADT instantiations we are currently exploring: if we
    come across one of them again we consider that it has no interior
    mutability, which is correct for a recursive type (least fixed point). *)
let rec is_interior_mutable (ctx : ctx)
    (stack : (type_decl_id * generic_args) list) (ty : ty) : bool =
  match ty with
  | TAdt { builtin = Some (TTuple | TBox); generics; _ } ->
      List.exists (is_interior_mutable ctx stack) generics.types
  | TAdt { builtin = Some TStr; _ } -> false
  | TAdt { id; generics; builtin = None } ->
      is_adt_interior_mutable ctx stack id generics
  | TArray (ty, _, _) | TSlice (ty, _) | TPattern (ty, _) ->
      is_interior_mutable ctx stack ty
  | TRef _
  | TRawPtr _
  | TFnDef _
  | TFnPtr _
  | TDynTrait _
  | TVar _
  | TTraitType _
  | TPtrMetadata _
  | TScalar _
  | TNever
  | TError _ -> false

and is_adt_interior_mutable (ctx : ctx)
    (stack : (type_decl_id * generic_args) list) (id : type_decl_id)
    (generics : generic_args) : bool =
  let non_generic = is_non_generic generics in
  let cached =
    if non_generic then TypeDeclId.TreeMap.find_opt id !(ctx.im_cache) else None
  in
  match cached with
  | Some b -> b
  | None -> (
      match TypeDeclId.Map.find_opt id ctx.type_decls with
      | None -> false
      | Some decl ->
          let b =
            match (decl.item_meta.lang_item, decl.marker_traits) with
            | ( Some (RustcLangItemUnsafeCell | RustcLangItemCovariantUnsafeCell),
                _ ) -> true
            | _, Some marker_traits ->
                (* Computed by rustc: only available for the types without
                   generics *)
                not marker_traits.is_freeze
            | _, None -> (
                match decl.kind with
                | Struct _ | Enum _ | Union _ ->
                    if
                      List.length stack >= max_depth
                      || List.exists
                           (fun (id', generics') ->
                             id' = id && generics' = generics)
                           stack
                    then false
                    else
                      let stack = (id, generics) :: stack in
                      List.exists
                        (fun (_, tys) ->
                          List.exists (is_interior_mutable ctx stack) tys)
                        (Charon.Substitute
                         .type_decl_get_instantiated_variants_fields_types decl
                           generics)
                | Opaque -> is_std_interior_mutable_name decl.item_meta.name
                | Alias _ | TDeclError _ -> false)
          in
          (* A [true] result doesn't depend on the assumptions we make for the
             recursive types, so we can always memoize it. We can memoize a
             [false] result if we made no assumptions, i.e., if we are at the
             top. *)
          if non_generic && (b || stack = []) then
            ctx.im_cache := TypeDeclId.TreeMap.add id b !(ctx.im_cache);
          b)

(** A shared reference to a type with interior mutability. *)
type violation = {
  vspan : Meta.span;  (** Where we found the reference *)
  ref_ty : ty;  (** The type of the reference *)
}

(** Collect the shared references to types with interior mutability which appear
    in the body of the function (we look at the statements first, then at the
    locals) and in its signature. We do nothing for the functions without a
    body: the references are used (and thus detected) by their callers.

    Every operation on such a reference goes through a place or a local whose
    type is the type of the reference, so it is enough to look at the types
    which appear in the function. *)
let collect_violations (ctx : ctx) (f : fun_decl) : violation list =
  let violations = ref [] in
  let visitor =
    object
      inherit [_] iter_statement as super

      method! visit_statement _ (st : statement) =
        super#visit_statement st.span st

      method! visit_ty span ty =
        (match ty with
        | TRef (_, inner, RShared) ->
            if is_interior_mutable ctx [] inner then
              violations := { vspan = span; ref_ty = ty } :: !violations
        | _ -> ());
        super#visit_ty span ty
    end
  in
  (match f.body with
  | StructuredBody body ->
      visitor#visit_block body.body.span body.body;
      List.iter
        (fun (l : local) -> visitor#visit_ty l.span l.local_ty)
        body.locals.locals;
      let span = f.item_meta.span in
      List.iter (visitor#visit_ty span)
        (f.signature.output :: f.signature.inputs)
  | _ -> ());
  List.rev !violations

(** Check that the function doesn't use shared references to types with interior
    mutability. This is an error, unless the user passed the option
    [-allow-interior-mutability] (in which case this is a warning). *)
let check_fun_decl (decls_ctx : Contexts.decls_ctx) (f : fun_decl) : unit =
  let ctx =
    {
      type_decls = decls_ctx.type_ctx.type_decls;
      im_cache = ref TypeDeclId.TreeMap.empty;
    }
  in
  match collect_violations ctx f with
  | [] -> ()
  | v :: _ as violations ->
      let fmt_env = Print.Contexts.decls_ctx_to_fmt_env decls_ctx in
      let fmt_env =
        Print.fmt_env_replace_generics_and_preds fmt_env f.generics
      in
      let tys =
        List.sort_uniq compare
          (List.map (fun v -> Print.ty_to_string fmt_env v.ref_ty) violations)
      in
      let msg =
        "Aeneas does not support interior mutability. This code uses shared \
         references to types with interior mutability (e.g., `Cell`, \
         `RefCell`, atomics, `Mutex`): "
        ^ String.concat ", " (List.map (fun s -> "`" ^ s ^ "`") tys)
        ^ ".\n\
           Shared references are translated as immutable values, so the \
           effects of operations like `Cell::set(&self, ...)` or \
           `AtomicU32::fetch_add(&self, ...)` are lost, and the generated \
           model is unsound (see \
           https://github.com/AeneasVerif/aeneas/issues/1525)."
      in
      if !Config.allow_interior_mutability then [%warn] v.vspan msg
      else
        [%craise] v.vspan
          (msg
         ^ " Use `-allow-interior-mutability` to only get a warning and \
            generate the unsound model anyway.")
