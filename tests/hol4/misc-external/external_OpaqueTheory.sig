signature external_OpaqueTheory =
sig
  type thm = Thm.thm
  
  val external_Opaque_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [external_Types] Parent theory of "external_Opaque"
   
   
*)
end
