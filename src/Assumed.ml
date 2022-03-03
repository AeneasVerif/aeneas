(** This module contains various utilities for the assumed functions.

    Note that `Box::free` is peculiar: we don't really handle it as a function,
    because it is legal to free a box whose boxed value is `⊥` (it often
    happens that we move a value out of a box before freeing this box).
    Semantically speaking, we thus handle `Box::free` as a value drop and
    not as a function call, and thus never need its signature.
    
    TODO: implementing the concrete evaluation functions for the assumed
    functions is really annoying (see
    [InterpreterStatements.eval_non_local_function_call_concrete]).
    I think it should be possible, in most situations, to write bodies which
    model the behaviour of those unsafe functions. For instance, `Box::deref_mut`
    should simply be:
    ```
    fn deref_mut<'a, T>(x : &'a mut Box<T>) -> &'a mut T {
      &mut ( *x ) // box dereferencement is a primitive operation
    }
    ```
    
    For vectors, we could "cheat" by using the index as a field index (vectors
    would be encoded as ADTs with a variable number of fields). Of course, it
    would require a bit of engineering, but it would probably be quite lightweight
    in the end.
    ```
    Vec::get_mut<'a,T>(v : &'a mut Vec<T>, i : usize) -> &'a mut T {
      &mut ( ( *x ).i )
    }
    ```
 *)

open Names
open TypesUtils
module T = Types
module A = CfimAst

module Sig = struct
  (** A few utilities *)

  let rvar_id_0 = T.RegionVarId.of_int 0

  let rvar_0 : T.RegionVarId.id T.region = T.Var rvar_id_0

  let rg_id_0 = T.RegionGroupId.of_int 0

  let tvar_id_0 = T.TypeVarId.of_int 0

  let tvar_0 : T.sty = T.TypeVar tvar_id_0

  (** Region 'a of id 0 *)
  let region_param_0 : T.region_var = { T.index = rvar_id_0; name = Some "'a" }

  (** Region group: { parent={}; regions:{'a of id 0} } *)
  let region_group_0 : T.region_var_group =
    { T.id = rg_id_0; regions = [ rvar_id_0 ]; parents = [] }

  (** Type parameter `T` of id 0 *)
  let type_param_0 : T.type_var = { T.index = tvar_id_0; name = "T" }

  let mk_ref_ty (r : T.RegionVarId.id T.region) (ty : T.sty) (is_mut : bool) :
      T.sty =
    let ref_kind = if is_mut then T.Mut else T.Shared in
    mk_ref_ty r ty ref_kind

  (** `fn<T>(&'a mut T, T) -> T` *)
  let mem_replace_sig : A.fun_sig =
    (* The signature fields *)
    let region_params = [ region_param_0 ] (* <'a> *) in
    let regions_hierarchy = [ region_group_0 ] (* [{<'a>}] *) in
    let type_params = [ type_param_0 ] (* <T> *) in
    let inputs =
      [ mk_ref_ty rvar_0 tvar_0 true (* &'a mut T *); tvar_0 (* T *) ]
    in
    let output = tvar_0 (* T *) in
    {
      region_params;
      num_early_bound_regions = 0;
      regions_hierarchy;
      type_params;
      inputs;
      output;
    }

  (** `fn<T>(T) -> Box<T>` *)
  let box_new_sig : A.fun_sig =
    {
      region_params = [];
      num_early_bound_regions = 0;
      regions_hierarchy = [];
      type_params = [ type_param_0 ] (* <T> *);
      inputs = [ tvar_0 (* T *) ];
      output = mk_box_ty tvar_0 (* Box<T> *);
    }

  (** Helper for `Box::deref_shared` and `Box::deref_mut`.
      Returns:
      `fn<'a, T>(&'a (mut) Box<T>) -> &'a (mut) T`
  *)
  let box_deref_gen_sig (is_mut : bool) : A.fun_sig =
    (* The signature fields *)
    let region_params = [ region_param_0 ] in
    let regions_hierarchy = [ region_group_0 ] (* <'a> *) in
    {
      region_params;
      num_early_bound_regions = 0;
      regions_hierarchy;
      type_params = [ type_param_0 ] (* <T> *);
      inputs =
        [ mk_ref_ty rvar_0 (mk_box_ty tvar_0) is_mut (* &'a (mut) Box<T> *) ];
      output = mk_ref_ty rvar_0 tvar_0 is_mut (* &'a (mut) T *);
    }

  (** `fn<'a, T>(&'a Box<T>) -> &'a T` *)
  let box_deref_shared_sig = box_deref_gen_sig false

  (** `fn<'a, T>(&'a mut Box<T>) -> &'a mut T` *)
  let box_deref_mut_sig = box_deref_gen_sig true

  (** `fn<T>() -> Vec<T>` *)
  let vec_new_sig : A.fun_sig =
    let region_params = [] in
    let regions_hierarchy = [] in
    let type_params = [ type_param_0 ] (* <T> *) in
    let inputs = [] in
    let output = mk_vec_ty tvar_0 (* Vec<T> *) in
    {
      region_params;
      num_early_bound_regions = 0;
      regions_hierarchy;
      type_params;
      inputs;
      output;
    }

  (** `fn<T>(&'a mut Vec<T>, T)` *)
  let vec_push_sig : A.fun_sig =
    (* The signature fields *)
    let region_params = [ region_param_0 ] in
    let regions_hierarchy = [ region_group_0 ] (* <'a> *) in
    let type_params = [ type_param_0 ] (* <T> *) in
    let inputs =
      [
        mk_ref_ty rvar_0 (mk_vec_ty tvar_0) true (* &'a mut Vec<T> *);
        tvar_0 (* T *);
      ]
    in
    let output = mk_unit_ty (* () *) in
    {
      region_params;
      num_early_bound_regions = 0;
      regions_hierarchy;
      type_params;
      inputs;
      output;
    }

  (** `fn<T>(&'a mut Vec<T>, usize, T)` *)
  let vec_insert_sig : A.fun_sig =
    (* The signature fields *)
    let region_params = [ region_param_0 ] in
    let regions_hierarchy = [ region_group_0 ] (* <'a> *) in
    let type_params = [ type_param_0 ] (* <T> *) in
    let inputs =
      [
        mk_ref_ty rvar_0 (mk_vec_ty tvar_0) true (* &'a mut Vec<T> *);
        mk_usize_ty (* usize *);
        tvar_0 (* T *);
      ]
    in
    let output = mk_unit_ty (* () *) in
    {
      region_params;
      num_early_bound_regions = 0;
      regions_hierarchy;
      type_params;
      inputs;
      output;
    }

  (** `fn<T>(&'a Vec<T>) -> usize` *)
  let vec_len_sig : A.fun_sig =
    (* The signature fields *)
    let region_params = [ region_param_0 ] in
    let regions_hierarchy = [ region_group_0 ] (* <'a> *) in
    let type_params = [ type_param_0 ] (* <T> *) in
    let inputs =
      [ mk_ref_ty rvar_0 (mk_vec_ty tvar_0) false (* &'a Vec<T> *) ]
    in
    let output = mk_usize_ty (* usize *) in
    {
      region_params;
      num_early_bound_regions = 0;
      regions_hierarchy;
      type_params;
      inputs;
      output;
    }

  (** Helper:
      `fn<T>(&'a (mut) Vec<T>, usize) -> &'a (mut) T`
   *)
  let vec_index_gen_sig (is_mut : bool) : A.fun_sig =
    (* The signature fields *)
    let region_params = [ region_param_0 ] in
    let regions_hierarchy = [ region_group_0 ] (* <'a> *) in
    let type_params = [ type_param_0 ] (* <T> *) in
    let inputs =
      [
        mk_ref_ty rvar_0 (mk_vec_ty tvar_0) is_mut (* &'a (mut) Vec<T> *);
        mk_usize_ty;
        (* usize *)
      ]
    in
    let output = mk_ref_ty rvar_0 tvar_0 is_mut (* &'a (mut) T *) in
    {
      region_params;
      num_early_bound_regions = 0;
      regions_hierarchy;
      type_params;
      inputs;
      output;
    }

  (** `fn<T>(&'a Vec<T>, usize) -> &'a T` *)
  let vec_index_shared_sig : A.fun_sig = vec_index_gen_sig false

  (** `fn<T>(&'a mut Vec<T>, usize) -> &'a mut T` *)
  let vec_index_mut_sig : A.fun_sig = vec_index_gen_sig true
end

type assumed_info = A.assumed_fun_id * A.fun_sig * bool * name

(** The list of assumed functions and all their information:
    - their signature
    - a boolean indicating whether they are monadic or not (i.e., if they
      can fail or not)
    - their name

    Rk.: following what is written above, we don't include `Box::free`.
    
    Remark about the vector functions: for `Vec::len` to be correct and return
    a `usize`, we have to make sure that vectors are bounded by the max usize.
    Followingly, `Vec::push` is monadic.
 *)
let assumed_infos : assumed_info list =
  let deref_pre = [ "core"; "ops"; "deref" ] in
  let vec_pre = [ "alloc"; "vec"; "Vec" ] in
  let index_pre = [ "core"; "ops"; "index" ] in
  [
    (A.Replace, Sig.mem_replace_sig, false, to_name [ "core"; "mem"; "replace" ]);
    (BoxNew, Sig.box_new_sig, false, to_name [ "alloc"; "boxed"; "Box"; "new" ]);
    ( BoxDeref,
      Sig.box_deref_shared_sig,
      false,
      to_name (deref_pre @ [ "Deref"; "deref" ]) );
    ( BoxDerefMut,
      Sig.box_deref_mut_sig,
      false,
      to_name (deref_pre @ [ "DerefMut"; "deref_mut" ]) );
    (VecNew, Sig.vec_new_sig, false, to_name (vec_pre @ [ "new" ]));
    (VecPush, Sig.vec_push_sig, true, to_name (vec_pre @ [ "push" ]));
    (VecInsert, Sig.vec_insert_sig, true, to_name (vec_pre @ [ "insert" ]));
    (VecLen, Sig.vec_len_sig, false, to_name (vec_pre @ [ "len" ]));
    ( VecIndex,
      Sig.vec_index_shared_sig,
      true,
      to_name (index_pre @ [ "Index"; "index" ]) );
    ( VecIndexMut,
      Sig.vec_index_mut_sig,
      true,
      to_name (index_pre @ [ "IndexMut"; "index_mut" ]) );
  ]

let get_assumed_info (id : A.assumed_fun_id) : assumed_info =
  List.find (fun (id', _, _, _) -> id = id') assumed_infos

let get_assumed_sig (id : A.assumed_fun_id) : A.fun_sig =
  let _, sg, _, _ = get_assumed_info id in
  sg

let get_assumed_name (id : A.assumed_fun_id) : fun_name =
  let _, _, _, name = get_assumed_info id in
  name

let assumed_is_monadic (id : A.assumed_fun_id) : bool =
  let _, _, b, _ = get_assumed_info id in
  b
