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

module T = Types
module A = CfimAst
open TypesUtils

(** `T -> Box<T>` *)
let box_new_sig : A.fun_sig =
  let tvar_id_0 = T.TypeVarId.of_int 0 in
  let tvar_0 = T.TypeVar tvar_id_0 in
  {
    region_params = [];
    num_early_bound_regions = 0;
    regions_hierarchy = [];
    type_params = [ { index = tvar_id_0; name = "T" } ];
    inputs = [ tvar_0 (* T *) ];
    output = mk_box_ty tvar_0 (* Box<T> *);
  }

(** Helper for `Box::deref_shared` and `Box::deref_mut`.
    Returns:
    `&'a (mut) Box<T> -> &'a (mut) T`
 *)
let box_deref_sig (is_mut : bool) : A.fun_sig =
  let rvar_id_0 = T.RegionVarId.of_int 0 in
  let rvar_0 = T.Var rvar_id_0 in
  let rg_id_0 = T.RegionGroupId.of_int 0 in
  let tvar_id_0 = T.TypeVarId.of_int 0 in
  let tvar_0 = T.TypeVar tvar_id_0 in
  let ref_kind = if is_mut then T.Mut else T.Shared in
  (* The signature fields *)
  let region_params = [ { T.index = rvar_id_0; name = Some "'a" } ] in
  let regions_hierarchy =
    [ { T.id = rg_id_0; regions = [ rvar_id_0 ]; parents = [] } ]
    (* <'a> *)
  in
  {
    region_params;
    num_early_bound_regions = 0;
    regions_hierarchy;
    type_params = [ { index = tvar_id_0; name = "T" } ] (* <T> *);
    inputs =
      [ mk_ref_ty rvar_0 (mk_box_ty tvar_0) ref_kind (* &'a (mut) Box<T> *) ];
    output = mk_ref_ty rvar_0 tvar_0 ref_kind (* &'a (mut) T *);
  }

(** `&'a Box<T> -> &'a T` *)
let box_deref_shared_sig = box_deref_sig false

(** `&'a mut Box<T> -> &'a mut T` *)
let box_deref_mut_sig = box_deref_sig true

(** The list of assumed functions, and their signatures.

    Rk.: following what is written above, we don't include `Box::free`.
 *)
let assumed_sigs : (A.assumed_fun_id * A.fun_sig) list =
  [
    (BoxNew, box_new_sig);
    (BoxDeref, box_deref_shared_sig);
    (BoxDerefMut, box_deref_mut_sig);
  ]

let assumed_names : (A.assumed_fun_id * Identifiers.name) list =
  [
    (BoxNew, [ "alloc"; "boxed"; "Box"; "new" ]);
    (BoxDeref, [ "core"; "ops"; "deref"; "Deref"; "deref" ]);
    (BoxDerefMut, [ "core"; "ops"; "deref"; "DerefMut"; "deref_mut" ]);
  ]
