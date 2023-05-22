(* Examples which use divDefLib.DefineDiv *)

open HolKernel
open divDefLib

val _ = new_theory "divDefLibTest"

(* nth *)

Datatype:
  list_t =
    ListCons 't list_t
  | ListNil
End

(* A version of [nth] which doesn't use machine integers *)
val [nth0_def] = DefineDiv ‘
  nth0 (ls : 't list_t) (i : int) : 't result =
    case ls of
    | ListCons x tl =>
      if i = (0:int)
      then (Return x)
      else
        do
        nth0 tl (i - 1)
        od
    | ListNil => Fail Failure
’
val _ = primitivesLib.assert_return “nth0 (ListCons 0 ListNil) 0”

val [nth_def] = DefineDiv ‘
  nth (ls : 't list_t) (i : u32) : 't result =
    case ls of
    | ListCons x tl =>
      if u32_to_int i = (0:int)
      then (Return x)
      else
        do
        i0 <- u32_sub i (int_to_u32 1);
        nth tl i0
        od
    | ListNil => Fail Failure
’
val _ = primitivesLib.assert_return “nth (ListCons 0 ListNil) (int_to_u32 0)”

(* even, odd *)

val [even_def, odd_def] = DefineDiv ‘
  (even (i : int) : bool result = if i = 0 then Return T else odd (i - 1)) /\
  (odd (i : int) : bool result = if i = 0 then Return F else even (i - 1))
’

(* btree *)

Datatype:
  btree =
    BLeaf 'a
  | BNode btree btree
End

val [btree_height_def] = DefineDiv ‘
  btree_height (tree : 'a btree) : int result =
    case tree of
    | BLeaf _ => Return 1
    | BNode l r =>
      do
      hl <- btree_height l;
      hr <- btree_height r;
      Return (hl + hr)
      od
’

(* tree 2 *)

Datatype:
  tree =
    TLeaf 'a
  | TNode node ;
  
  node = 
    Node (tree list)
End

val [tree_height_def, tree_nodes_height_def] = DefineDiv ‘
  (tree_height (tree : 'a tree) : int result =
    case tree of
      TLeaf _ => Return 1
    | TNode n =>
      case n of Node ls => tree_nodes_height ls) ∧

  (tree_nodes_height (ls : ('a tree) list) : int result =
    case ls of
      [] => Return 0
    | t :: tl =>
      do
        h1 <- tree_height t;
        h2 <- tree_nodes_height tl;
        Return (h1 + h2)
      od)
’

val _ = export_theory ()
