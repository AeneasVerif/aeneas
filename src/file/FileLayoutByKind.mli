(** The split by kind ([-split-files]): the definitions are split between
    [Types], [Funs], the templates the user fills in for the opaque declarations
    ([TypesExternal], [FunsExternal]), and the templates for the decreases
    clauses. *)

include FileLayout.S
