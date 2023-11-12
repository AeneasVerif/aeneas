(** This module contains various utilities for the assumed functions.

    Note that [Box::free] is peculiar: we don't really handle it as a function,
    because it is legal to free a box whose boxed value is [⊥] (it often
    happens that we move a value out of a box before freeing this box).
    Semantically speaking, we thus handle [Box::free] as a value drop and
    not as a function call, and thus never need its signature.
    
    TODO: implementing the concrete evaluation functions for the
    assumed functions is really annoying (see
    [InterpreterStatements.eval_non_local_function_call_concrete]),
    I think it should be possible, in most situations, to write bodies which
    model the behaviour of those unsafe functions. For instance, [Box::deref_mut]
    should simply be:
    {[
      fn deref_mut<'a, T>(x : &'a mut Box<T>) -> &'a mut T {
        &mut ( *x ) // box dereferencement is a primitive operation
      }
    ]}
    
    For vectors, we could "cheat" by using the index as a field index (vectors
    would be encoded as ADTs with a variable number of fields). Of course, it
    would require a bit of engineering, but it would probably be quite lightweight
    in the end.
    {[
      Vec::get_mut<'a,T>(v : &'a mut Vec<T>, i : usize) -> &'a mut T {
        &mut ( ( *x ).i )
      }
    ]}
 *)

open Names
open TypesUtils
module T = Types
module A = LlbcAst

module Sig = struct
  (** A few utilities *)

  let rvar_id_0 = T.RegionId.of_int 0
  let rvar_0 : T.region = T.RVar rvar_id_0
  let rg_id_0 = T.RegionGroupId.of_int 0
  let tvar_id_0 = T.TypeVarId.of_int 0
  let tvar_0 : T.ty = T.TypeVar tvar_id_0
  let cgvar_id_0 = T.ConstGenericVarId.of_int 0
  let cgvar_0 : T.const_generic = T.CGVar cgvar_id_0

  (** Region 'a of id 0 *)
  let region_param_0 : T.region_var = { T.index = rvar_id_0; name = Some "'a" }

  (** Region group: [{ parent={}; regions:{'a of id 0} }] *)
  let region_group_0 : T.region_group =
    { T.id = rg_id_0; regions = [ rvar_id_0 ]; parents = [] }

  (** Type parameter [T] of id 0 *)
  let type_param_0 : T.type_var = { T.index = tvar_id_0; name = "T" }

  let usize_ty : T.ty = T.TLiteral (TInteger Usize)

  (** Const generic parameter [const N : usize] of id 0 *)
  let cg_param_0 : T.const_generic_var =
    { T.index = cgvar_id_0; name = "N"; ty = TInteger Usize }

  let empty_const_generic_params : T.const_generic_var list = []

  let mk_generic_args regions types const_generics : T.generic_args =
    { regions; types; const_generics; trait_refs = [] }

  let mk_generic_params regions types const_generics : T.generic_params =
    { regions; types; const_generics; trait_clauses = [] }

  let mk_ref_ty (r : T.region) (ty : T.ty) (is_mut : bool) : T.ty =
    let ref_kind = if is_mut then T.Mut else T.Shared in
    mk_ref_ty r ty ref_kind

  let mk_array_ty (ty : T.ty) (cg : T.const_generic) : T.ty =
    TAdt (TAssumed TArray, mk_generic_args [] [ ty ] [ cg ])

  let mk_slice_ty (ty : T.ty) : T.ty =
    TAdt (TAssumed TSlice, mk_generic_args [] [ ty ] [])

  let mk_sig generics regions_hierarchy inputs output : A.fun_sig =
    let preds : T.predicates =
      { regions_outlive = []; types_outlive = []; trait_type_constraints = [] }
    in
    {
      is_unsafe = false;
      generics;
      preds;
      parent_params_info = None;
      regions_hierarchy;
      inputs;
      output;
    }

  (** [fn<T>(T) -> Box<T>] *)
  let box_new_sig : A.fun_sig =
    let generics = mk_generic_params [] [ type_param_0 ] [] (* <T> *) in
    let regions_hierarchy = [] in
    let inputs = [ tvar_0 (* T *) ] in
    let output = mk_box_ty tvar_0 (* Box<T> *) in
    mk_sig generics regions_hierarchy inputs output

  (** [fn<T>(Box<T>) -> ()] *)
  let box_free_sig : A.fun_sig =
    let generics = mk_generic_params [] [ type_param_0 ] [] (* <T> *) in
    let regions_hierarchy = [] in
    let inputs = [ mk_box_ty tvar_0 (* Box<T> *) ] in
    let output = mk_unit_ty (* () *) in
    mk_sig generics regions_hierarchy inputs output

  (** Array/slice functions *)

  (** Small helper.

      Return the type:
      {[
        fn<'a, T>(&'a input_ty, index_ty) -> &'a output_ty
      ]}

      Remarks:
      The [input_ty] and [output_ty] are parameterized by a type variable id.
      The [mut_borrow] boolean controls whether we use a shared or a mutable
      borrow.
   *)
  let mk_array_slice_borrow_sig (cgs : T.const_generic_var list)
      (input_ty : T.TypeVarId.id -> T.ty) (index_ty : T.ty option)
      (output_ty : T.TypeVarId.id -> T.ty) (is_mut : bool) : A.fun_sig =
    let generics =
      mk_generic_params [ region_param_0 ] [ type_param_0 ] cgs (* <'a, T> *)
    in
    let regions_hierarchy = [ region_group_0 ] (* <'a> *) in
    let inputs =
      [
        mk_ref_ty rvar_0
          (input_ty type_param_0.index)
          is_mut (* &'a (mut) input_ty<T> *);
      ]
    in
    let inputs =
      List.append inputs (match index_ty with None -> [] | Some ty -> [ ty ])
    in
    let output =
      mk_ref_ty rvar_0
        (output_ty type_param_0.index)
        is_mut (* &'a (mut) output_ty<T> *)
    in
    mk_sig generics regions_hierarchy inputs output

  let mk_array_slice_index_sig (is_array : bool) (is_mut : bool) : A.fun_sig =
    (* Array<T, N> *)
    let input_ty id =
      if is_array then mk_array_ty (T.TypeVar id) cgvar_0
      else mk_slice_ty (T.TypeVar id)
    in
    (* usize *)
    let index_ty = usize_ty in
    (* T *)
    let output_ty id = T.TypeVar id in
    let cgs = if is_array then [ cg_param_0 ] else [] in
    mk_array_slice_borrow_sig cgs input_ty (Some index_ty) output_ty is_mut

  let array_index_sig (is_mut : bool) = mk_array_slice_index_sig true is_mut
  let slice_index_sig (is_mut : bool) = mk_array_slice_index_sig false is_mut

  let array_to_slice_sig (is_mut : bool) : A.fun_sig =
    (* Array<T, N> *)
    let input_ty id = mk_array_ty (T.TypeVar id) cgvar_0 in
    (* Slice<T> *)
    let output_ty id = mk_slice_ty (T.TypeVar id) in
    let cgs = [ cg_param_0 ] in
    mk_array_slice_borrow_sig cgs input_ty None output_ty is_mut

  let array_repeat_sig =
    let generics =
      (* <T, N> *)
      mk_generic_params [] [ type_param_0 ] [ cg_param_0 ]
    in
    let regions_hierarchy = [] (* <> *) in
    let inputs = [ tvar_0 (* T *) ] in
    let output =
      (* [T; N] *)
      mk_array_ty tvar_0 cgvar_0
    in
    mk_sig generics regions_hierarchy inputs output

  (** Helper:
      [fn<T>(&'a [T]) -> usize]
   *)
  let slice_len_sig : A.fun_sig =
    let generics =
      mk_generic_params [ region_param_0 ] [ type_param_0 ] [] (* <'a, T> *)
    in
    let regions_hierarchy = [ region_group_0 ] (* <'a> *) in
    let inputs =
      [ mk_ref_ty rvar_0 (mk_slice_ty tvar_0) false (* &'a [T] *) ]
    in
    let output = mk_usize_ty (* usize *) in
    mk_sig generics regions_hierarchy inputs output
end

type raw_assumed_fun_info =
  A.assumed_fun_id * A.fun_sig * bool * name * bool list option

type assumed_fun_info = {
  fun_id : A.assumed_fun_id;
  fun_sig : A.fun_sig;
  can_fail : bool;
  name : name;
  keep_types : bool list option;
      (** We may want to filter some type arguments.

          For instance, all the `Vec` functions (and the `Vec` type itself) take
          an `Allocator` type as argument, that we ignore.
       *)
}

let mk_assumed_fun_info (raw : raw_assumed_fun_info) : assumed_fun_info =
  let fun_id, fun_sig, can_fail, name, keep_types = raw in
  { fun_id; fun_sig; can_fail; name; keep_types }

(** The list of assumed functions and all their information:
    - their signature
    - a boolean indicating whether the function can fail or not (if true: can fail)
    - their name

    Rk.: following what is written above, we don't include [Box::free].

    Remark about the vector functions: for [Vec::len] to be correct and return
    a [usize], we have to make sure that vectors are bounded by the max usize.
    As a consequence, [Vec::push] is monadic.
 *)
let raw_assumed_fun_infos : raw_assumed_fun_info list =
  [
    ( BoxNew,
      Sig.box_new_sig,
      false,
      to_name [ "alloc"; "boxed"; "Box"; "new" ],
      Some [ true; false ] );
    (* BoxFree shouldn't be used *)
    ( BoxFree,
      Sig.box_free_sig,
      false,
      to_name [ "alloc"; "boxed"; "Box"; "free" ],
      Some [ true; false ] );
    (* Array Index *)
    ( ArrayIndexShared,
      Sig.array_index_sig false,
      true,
      to_name [ "@ArrayIndexShared" ],
      None );
    ( ArrayIndexMut,
      Sig.array_index_sig true,
      true,
      to_name [ "@ArrayIndexMut" ],
      None );
    (* Array to slice*)
    ( ArrayToSliceShared,
      Sig.array_to_slice_sig false,
      true,
      to_name [ "@ArrayToSliceShared" ],
      None );
    ( ArrayToSliceMut,
      Sig.array_to_slice_sig true,
      true,
      to_name [ "@ArrayToSliceMut" ],
      None );
    (* Array Repeat *)
    (ArrayRepeat, Sig.array_repeat_sig, false, to_name [ "@ArrayRepeat" ], None);
    (* Slice Index *)
    ( SliceIndexShared,
      Sig.slice_index_sig false,
      true,
      to_name [ "@SliceIndexShared" ],
      None );
    ( SliceIndexMut,
      Sig.slice_index_sig true,
      true,
      to_name [ "@SliceIndexMut" ],
      None );
    (SliceLen, Sig.slice_len_sig, false, to_name [ "@SliceLen" ], None);
  ]

let assumed_fun_infos : assumed_fun_info list =
  List.map mk_assumed_fun_info raw_assumed_fun_infos

let get_assumed_fun_info (id : A.assumed_fun_id) : assumed_fun_info =
  match List.find_opt (fun x -> id = x.fun_id) assumed_fun_infos with
  | Some info -> info
  | None ->
      raise
        (Failure ("get_assumed_fun_info: not found: " ^ A.show_assumed_fun_id id))

let get_assumed_fun_sig (id : A.assumed_fun_id) : A.fun_sig =
  (get_assumed_fun_info id).fun_sig

let get_assumed_fun_name (id : A.assumed_fun_id) : fun_name =
  (get_assumed_fun_info id).name

let assumed_fun_can_fail (id : A.assumed_fun_id) : bool =
  (get_assumed_fun_info id).can_fail
