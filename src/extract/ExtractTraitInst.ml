(** Computation of the [{Trait for Type}] notation strings used by the
    [trait_inst] Lean attribute.

    See [backends/lean/Aeneas/Tactic/Elab/TraitInst/Init.lean] for the Lean
    side: trait implementations registered with
    [@[trait_inst {Trait<Args> for SelfTy}]] can be referred to with the
    [{Trait<Args> for SelfTy}] notation instead of their (mangled) name.

    The pattern must mirror what the Lean attribute derives by reflection on the
    definition's type. In particular:
    - the type (and const generic) variables must be printed with the names of
      the binders of the definition: the Lean side turns them into pattern
      variables;
    - the trait arguments mirror the parameters of the Lean structure modeling
      the trait, minus the leading [Self] (so they include the lifted associated
      types, in order);
    - [Box] is erased, and [Slice]/[Array] use the dedicated syntax.

    The functions below return [None] when a type is not representable in the
    (deliberately restricted) notation grammar - e.g. arrow types, raw pointers,
    [dyn Trait] - in which case we simply do not register the implementation. *)

open Pure
open Config
open ExtractBase

let ( let* ) = Option.bind

let rec map_opt (f : 'a -> 'b option) (l : 'a list) : 'b list option =
  match l with
  | [] -> Some []
  | x :: l ->
      let* x = f x in
      let* l = map_opt f l in
      Some (x :: l)

(** Check that a name can be used inside the notation: it must be a dot
    separated sequence of simple identifiers (in particular, no identifiers
    which require escaping with «...»). *)
let name_is_simple (s : string) : bool =
  let segment_is_simple (s : string) : bool =
    s <> ""
    && (match s.[0] with
       | 'a' .. 'z' | 'A' .. 'Z' | '_' -> true
       | _ -> false)
    && String.for_all
         (fun c ->
           match c with
           | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' -> true
           | _ -> false)
         s
  in
  s <> "" && List.for_all segment_is_simple (String.split_on_char '.' s)

let rec ty_to_notation (ctx : extraction_ctx) (span : Meta.span) (ty : ty) :
    string option =
  match ty with
  | TAdt (TTuple, generics) -> (
      match generics.types with
      | [] ->
          (* The unit type is not representable in the notation grammar *)
          None
      | [ ty ] -> ty_to_notation ctx span ty
      | tys ->
          let* tys = map_opt (ty_to_notation ctx span) tys in
          Some ("(" ^ String.concat ", " tys ^ ")"))
  | TAdt (TBuiltin TSlice, generics) -> (
      match generics.types with
      | [ ty ] ->
          let* ty = ty_to_notation ctx span ty in
          Some ("Slice<" ^ ty ^ ">")
      | _ -> None)
  | TAdt (TBuiltin TArray, generics) -> (
      match (generics.types, generics.const_generics) with
      | [ ty ], [ cg ] ->
          let* ty = ty_to_notation ctx span ty in
          let* cg = cg_to_notation ctx span cg in
          Some ("Array<" ^ ty ^ ", " ^ cg ^ ">")
      | _ -> None)
  | TAdt (TBuiltin TStr, _) -> Some "Str"
  | TAdt
      (TBuiltin (TResult | TSum | TLoopResult | TError | TFuel | TRawPtr _), _)
    ->
      (* These should not appear in trait references *)
      None
  | TAdt ((TAdtId id as type_id), generics) ->
      (* The notation cannot express trait instance arguments *)
      if generics.trait_refs <> [] then None
      else
        (* Filter the type arguments, like [extract_ty] does for builtin
           types (e.g. we filter the allocator argument of [Vec]) *)
        let types =
          match TypeDeclId.Map.find_opt id ctx.types_filter_type_args_map with
          | None -> generics.types
          | Some filter ->
              List.filter_map
                (fun (b, ty) -> if b then Some ty else None)
                (List.combine filter generics.types)
        in
        let name = ctx_get_type (Some span) type_id ctx in
        if not (name_is_simple name) then None
        else
          let* tys = map_opt (ty_to_notation ctx span) types in
          let* cgs =
            map_opt (cg_to_notation ctx span) generics.const_generics
          in
          let args = tys @ cgs in
          if args = [] then Some name
          else Some (name ^ "<" ^ String.concat ", " args ^ ">")
  | TVar var ->
      let origin, id = origin_from_de_bruijn_var var in
      let name = ctx_get_type_var span origin id ctx in
      if name_is_simple name then Some name else None
  | TLiteral lty -> lit_ty_to_notation lty
  | TArrow _ | TTraitType _ | TNever | TError | TDynTrait _ -> None

and lit_ty_to_notation (lty : literal_type) : string option =
  match lty with
  | TBool -> Some (bool_name ())
  | TChar -> Some (char_name ())
  | TInt int_ty -> Some ("Std." ^ int_name (Signed int_ty))
  | TUInt int_ty -> Some ("Std." ^ int_name (Unsigned int_ty))
  | TFloat _ | TPureNat | TPureInt -> None

and cg_to_notation (ctx : extraction_ctx) (span : Meta.span)
    (cg : const_generic) : string option =
  match cg with
  | CgValue (VScalar sv) -> Some (Z.to_string (Scalars.get_val sv))
  | CgValue _ -> None
  | CgVar var ->
      let origin, id = origin_from_de_bruijn_var var in
      let name = ctx_get_const_generic_var span origin id ctx in
      if name_is_simple name then Some name else None
  | CgGlobal _ -> None

(** Maximum depth of the traversal of the parent clauses, both here and in the
    Lean elaborator's local context search. *)
let max_clause_depth = 4

(** Compute the notation for a trait declaration reference, e.g.
    [{core.clone.Clone for alloc.vec.Vec<T>}].

    The context must have the relevant generic parameters bound (e.g., for a
    trait implementation, the parameters of the implementation), so that the
    type variables get printed with the binder names appearing in the generated
    definition. *)
let trait_decl_ref_to_notation (ctx : extraction_ctx) (span : Meta.span)
    (tr : trait_decl_ref) : string option =
  let trait_name = ctx_get_trait_decl span tr.trait_decl_id ctx in
  if not (name_is_simple trait_name) then None
  else
    match tr.decl_generics.types with
    | self :: types ->
        let* self = ty_to_notation ctx span self in
        let* types = map_opt (ty_to_notation ctx span) types in
        let* cgs =
          map_opt (cg_to_notation ctx span) tr.decl_generics.const_generics
        in
        let args = types @ cgs in
        if args = [] then Some ("{" ^ trait_name ^ " for " ^ self ^ "}")
        else
          Some
            ("{" ^ trait_name ^ "<" ^ String.concat ", " args ^ "> for " ^ self
           ^ "}")
    | [] -> None

(** Compute the multiset of the notation strings of the trait clauses in scope
    (including their parent clauses, transitively), and store it in the context.

    This must mirror the local context search performed by the Lean elaborator:
    a clause reference is only printed with the notation when the notation
    string maps to exactly one reachable clause, and a trait implementation
    reference only when it maps to none (a matching clause in scope would shadow
    the registered implementation).

    Must be called (on the definition's generics) after the generic parameters
    have been added to the context, so that the type variables are printed with
    their binder names. *)
let ctx_add_trait_clause_notations (ctx : extraction_ctx) (span : Meta.span)
    (generics : generic_params) : extraction_ctx =
  if not (!trait_inst_notation && backend () = Lean) then ctx
  else
    let count = ref Collections.StringMap.empty in
    let add (s : string) =
      count :=
        Collections.StringMap.update s
          (function
            | Some n -> Some (n + 1)
            | None -> Some 1)
          !count
    in
    let rec visit (depth : int) (tr : trait_decl_ref) : unit =
      if depth >= max_clause_depth then ()
      else begin
        (match trait_decl_ref_to_notation ctx span tr with
        | Some s -> add s
        | None -> ());
        (* Recurse into the parent clauses *)
        match
          TraitDeclId.Map.find_opt tr.trait_decl_id ctx.trans_trait_decls
        with
        | None -> ()
        | Some decl ->
            let subst =
              PureUtils.make_subst_from_generics decl.generics tr.decl_generics
            in
            List.iter
              (fun (c : trait_param) ->
                let generics =
                  PureUtils.generic_args_substitute subst c.generics
                in
                visit (depth + 1)
                  { trait_decl_id = c.trait_id; decl_generics = generics })
              decl.parent_clauses
      end
    in
    List.iter
      (fun (c : trait_param) ->
        visit 0 { trait_decl_id = c.trait_id; decl_generics = c.generics })
      generics.trait_clauses;
    { ctx with trait_clause_notations = !count }

(** The number of trait clauses in scope whose notation is [s]. *)
let clause_notation_count (ctx : extraction_ctx) (s : string) : int =
  match Collections.StringMap.find_opt s ctx.trait_clause_notations with
  | Some n -> n
  | None -> 0

(** If the [trait_inst_notation] option is on and the given (instantiated) trait
    reference of a *trait implementation* can be printed with the notation,
    return the string to print (with the surrounding parentheses, which are
    required in particular at the start of a do-sequence).

    [is_local]: the implementation must have been translated (the builtin
    implementations of the standard library are not guaranteed to be
    registered).

    The notation must not be shadowed by a clause in scope with the same
    notation (the Lean elaborator searches the local context first). *)
let trait_impl_notation (ctx : extraction_ctx) (span : Meta.span)
    ~(is_local : bool) (tr : trait_decl_ref) : string option =
  if (not (!trait_inst_notation && backend () = Lean)) || not is_local then None
  else
    match trait_decl_ref_to_notation ctx span tr with
    | Some s when clause_notation_count ctx s = 0 -> Some ("(" ^ s ^ ")")
    | _ -> None

(** Same as {!trait_impl_notation} but for a reference to a trait *clause* in
    scope (a clause binder or a chain of parent clause projections): the
    notation must map to exactly one reachable clause. *)
let trait_clause_notation (ctx : extraction_ctx) (span : Meta.span)
    (tr : trait_decl_ref) : string option =
  if not (!trait_inst_notation && backend () = Lean) then None
  else
    match trait_decl_ref_to_notation ctx span tr with
    | Some s when clause_notation_count ctx s = 1 -> Some ("(" ^ s ^ ")")
    | _ -> None

(** For the [trait_inst_notation] option: if the given function is a method of a
    (local, registered) trait implementation, compute the
    [({Trait<Args> for Self}.method)] string to print instead of its name. The
    Lean elaborator resolves the notation to the implementation applied to its
    arguments, and the member access to the method *definition* applied to the
    same arguments - which is exactly the direct call we would print without the
    option.

    Also returns the generic arguments specific to the method (the arguments of
    the implementation are reconstructed by the elaborator so we must not print
    them), and the number of implementation type/const-generic parameters (so
    that the caller can filter the explicit-parameter information accordingly).

    [generics]: the arguments of the call (implementation + method arguments, in
    this order). *)
let impl_method_notation (ctx : extraction_ctx) (span : Meta.span)
    (fun_decl_id : FunDeclId.id) (generics : generic_args) :
    (string * generic_args * (int * int)) option =
  if not (!trait_inst_notation && backend () = Lean) then None
  else
    let* trans = ctx_lookup_fun_decl_info ctx fun_decl_id in
    match trans.f.src with
    | TraitImplItem (impl_ref, _, AssocIdMethod _, _) ->
        let impl_id = impl_ref.id in
        if ctx.current_trait_impl = Some impl_id then None
        else
          let* impl = TraitImplId.Map.find_opt impl_id ctx.trans_trait_impls in
          let n_ty = List.length impl.generics.types in
          let n_cg = List.length impl.generics.const_generics in
          let n_tr = List.length impl.generics.trait_clauses in
          if
            List.length generics.types < n_ty
            || List.length generics.const_generics < n_cg
            || List.length generics.trait_refs < n_tr
          then None
          else
            let take n l = List.filteri (fun i _ -> i < n) l in
            let drop n l = List.filteri (fun i _ -> i >= n) l in
            let impl_args : generic_args =
              {
                types = take n_ty generics.types;
                const_generics = take n_cg generics.const_generics;
                trait_refs = take n_tr generics.trait_refs;
              }
            in
            let subst =
              PureUtils.make_subst_from_generics impl.generics impl_args
            in
            let tr : trait_decl_ref =
              {
                trait_decl_id = impl.impl_trait.trait_decl_id;
                decl_generics =
                  PureUtils.generic_args_substitute subst
                    impl.impl_trait.decl_generics;
              }
            in
            let* notation = trait_impl_notation ctx span ~is_local:true tr in
            (* The extracted function name must be the implementation name
               followed by a single (dot-free) identifier, so that the Lean
               elaborator can find the method definition by name *)
            let fun_name =
              ctx_get_function span
                (FromLlbc (FunId (FRegular fun_decl_id), None))
                ctx
            in
            let impl_name = ctx_get_trait_impl span impl_id ctx in
            let prefix = impl_name ^ "." in
            if not (String.starts_with ~prefix fun_name) then None
            else
              let suffix =
                String.sub fun_name (String.length prefix)
                  (String.length fun_name - String.length prefix)
              in
              if String.contains suffix '.' then None
              else
                (* [notation] is of the shape ["({...})"]: insert the member
                   access before the closing parenthesis *)
                let inner =
                  String.sub notation 1 (String.length notation - 2)
                in
                let method_generics : generic_args =
                  {
                    types = drop n_ty generics.types;
                    const_generics = drop n_cg generics.const_generics;
                    trait_refs = drop n_tr generics.trait_refs;
                  }
                in
                Some
                  ( "(" ^ inner ^ "." ^ suffix ^ ")",
                    method_generics,
                    (n_ty, n_cg) )
    | _ -> None
