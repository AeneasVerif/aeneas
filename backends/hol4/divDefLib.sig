(* This library implements an automated method, DefineDiv, which generates
   definitions by means of the fixed-point operator ‘fix’ introduced in
   ‘divDefScript’.

   For examples of how to use the fixed-point operator step by step on
   hand-written examples, see divDefExampleTheory.

   The current file is organized so as to follow the steps detailed in
   divDefExampleTheory.

   For examples of how to use DefiveDiv, see divDefLibExampleScript.

   Limitations: our encoding has limitations with regards to higher-order functions. More
   precisely, the following definition wouldn't be accepted, because we don't know how
   “MAP” would use ‘explore_tree’, meaning we can't prove the validity property required
   by the fixed point upon defining ‘explore_tree’ and ‘explore_node’:

   {[
     Datatype:
       tree =
         Leaf int
       | Node (tree list)
     End

     explore_tree (t : tree) : tree =
       case t of
         Leaf i => Leaf i
       | Node ns => Node (explore_node ns)

     explore_node (ns : tree list) : tree list =
       MAP explore_tree ns (* This is not supported *)
   ]}

   *However*, our encoding does allow defining a function ‘f’ *then* giving it
   as argument to a higher-order function such as ‘MAP’.

   Remark: "Partial recursive functions in higher-order logic", Alexander Krauss,
   introduces an interesting approach by means of an inductive. It could be
   interesting to try and compare. One advantage of the current approach, though,
   is that it is compatible with an "execution" through [EVAL]. But if we manage
   to make [EVAL] use arbitrary rewriting theorems, then it doesn't make a
   difference.
 *)

signature divDefLib =
sig
  include Abbrev

  val DefineDiv : term quotation -> thm list
end
