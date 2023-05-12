(* This library implements an automated method, DefineDiv, which generates
   definitions by means of the fixed-point operator ‘fix’ introduced in
   ‘divDefScript’.

   For examples of how to use the fixed-point operator step by step on
   hand-written examples, see divDefExampleTheory.

   The current file is organized so as to follow the steps detailed in
   divDefExampleTheory.

   For examples of how to use DefiveDiv, see divDefLibExampleScript.
 *)

signature divDefLib =
sig
  include Abbrev

  val DefineDiv : term quotation -> thm list
end
