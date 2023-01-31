open HolKernel boolLib bossLib Parse
open boolTheory arithmeticTheory integerTheory intLib listTheory stringTheory

open primitivesArithTheory primitivesBaseTacLib ilistTheory primitivesTheory
open primitivesLib

val _ = new_theory "testHashmap"

(*
 * Examples of proofs
 *)

Datatype:
  list_t =
    ListCons 't list_t
  | ListNil
End

val nth_mut_fwd_def = Define ‘
  nth_mut_fwd (ls : 't list_t) (i : u32) : 't result =
  case ls of
  | ListCons x tl =>
    if u32_to_int i = (0:int)
    then Return x
    else
      do
      i0 <- u32_sub i (int_to_u32 1);
      nth_mut_fwd tl i0
      od
  | ListNil => 
    Fail Failure
’
                                            
(*** Examples of proofs on [nth] *)
val list_t_v_def = Define ‘
  list_t_v ListNil = [] /\
  list_t_v (ListCons x tl) = x :: list_t_v tl
’

Theorem nth_mut_fwd_spec:
  !(ls : 't list_t) (i : u32).
    u32_to_int i < len (list_t_v ls) ==>
    case nth_mut_fwd ls i of
    | Return x => x = index (u32_to_int i) (list_t_v ls)
    | Fail _ => F
    | Loop => F
Proof
  Induct_on ‘ls’ >> rw [list_t_v_def, len_def] >~ [‘ListNil’]
  >-(massage >> int_tac) >>
  pure_once_rewrite_tac [nth_mut_fwd_def] >> rw [] >>
  fs [index_eq] >>
  progress >> progress
QED

val _ = new_constant ("insert", “: u32 -> 't -> (u32 # 't) list_t -> (u32 # 't) list_t result”)
val insert_def = new_axiom ("insert_def", “
 insert (key : u32) (value : 't) (ls : (u32 # 't) list_t) : (u32 # 't) list_t result =
  case ls of
  | ListCons (ckey, cvalue) tl =>
    if ckey = key
    then Return (ListCons (ckey, value) tl)
    else
      do
      tl0 <- insert key value tl;
      Return (ListCons (ckey, cvalue) tl0)
      od
  | ListNil => Return (ListCons (key, value) ListNil)
 ”)

(* Property that keys are pairwise distinct *)
val distinct_keys_def = Define ‘
  distinct_keys (ls : (u32 # 't) list) =
    !i j.
      0 < i ⇒ i < len ls ==>
      0 < j ⇒ j < len ls ==>
      FST (index i ls) = FST (index j ls) ⇒
      i = j
’

val lookup_raw_def = Define ‘
  lookup_raw key [] = NONE /\
  lookup_raw key ((k, v) :: ls) =
    if k = key then SOME v else lookup_raw key ls
’

val lookup_def = Define ‘
  lookup key ls = lookup_raw key (list_t_v ls)
’

Theorem insert_lem:
  !ls key value.
    (* The keys are pairwise distinct *)
    distinct_keys (list_t_v ls) ==>
    case insert key value ls of
    | Return ls1 =>
      (* We updated the binding *)
      lookup key ls1 = SOME value /\
      (* The other bindings are left unchanged *)
      (!k. k <> key ==> lookup k ls = lookup k ls1)
      (* TODO: invariant *)
    | Fail _ => F
    | Loop => F
Proof
  Induct_on ‘ls’ >> rw [list_t_v_def] >~ [‘ListNil’] >>
  pure_once_rewrite_tac [insert_def] >> rw []
  >- (rw [lookup_def, lookup_raw_def, list_t_v_def])
  >- (rw [lookup_def, lookup_raw_def, list_t_v_def]) >>
  case_tac >> rw []
  >- (rw [lookup_def, lookup_raw_def, list_t_v_def])
  >- (rw [lookup_def, lookup_raw_def, list_t_v_def]) >>
  progress
  >- (
    (* Disctinct keys *)
    fs [distinct_keys_def] >>
    rpt strip_tac >>
    first_x_assum (qspecl_assume [‘i + 1’, ‘j + 1’]) >> fs [] >>
    pop_assum irule >>
    fs [index_eq, add_sub_same_eq, len_def] >>
    int_tac) >>
  fs [lookup_def, lookup_raw_def, list_t_v_def]
QED

val _ = export_theory ()
