(** The legacy split ([-split-files-legacy]): the definitions are split by kind,
    between [Types], [Funs], the templates the user fills in for the opaque
    declarations ([TypesExternal], [FunsExternal]), and the templates for the
    decreases clauses. This is the only split for the backends other than Lean.
*)

include FileLayout.S
