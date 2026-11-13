(** The manifests of the external crates (option [-extern-crate]): the crates
    translated beforehand by Aeneas, whose items the writer names after their
    Lean definitions instead of emitting them (see {!ExtractExternal}).

    The entries are indexed by their exact Rust name (the [rust_name] of the
    manifest): with the same version of Charon, the items of a crate reach the
    crates which depend on it under the same names. *)

(** Load the manifest at [path] of the external crate [crate], written by
    [-emit-json], and register its entries.

    Raises [Failure] if the manifest is missing or invalid, if it is the
    manifest of another crate, if it was written from the output of another
    version of Charon than [charon_version] or with another Lean module mode, or
    if one of its items is already registered (by this manifest or another). *)
val load : charon_version:string -> string -> string -> unit

(** [true] if no entry is registered (no [-extern-crate]). *)
val is_empty : unit -> bool

(** The entry of the item with the given Rust name, if any. Loop functions are
    not registered: they are only used by the function they belong to. *)

val find_function : string -> Manifest.function_entry option
val find_type : string -> Manifest.type_entry option
val find_global : string -> Manifest.global_entry option
val find_trait_decl : string -> Manifest.trait_decl_entry option
val find_trait_impl : string -> Manifest.trait_impl_entry option

(** The Lean modules defining the registered entries, which the generated files
    import. *)
val imported_modules : unit -> string list
