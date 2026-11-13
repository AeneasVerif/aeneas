(** The external items: the items of the crates translated beforehand by Aeneas
    and given with [-extern-crate] (see {!ExternManifest}).

    They are handled by the writer only: an item is external if its exact Rust
    name is listed in a loaded manifest. The writer then names it after its Lean
    definition (with the names of its fields, variants, trait items...) and does
    not emit it. The translation of the crate is unchanged. *)

open Pure
open ExtractBase

(** Look up a name ([None] without loading the name when there is no external
    crate) *)
let find (find : string -> 'a option) (ctx : extraction_ctx) (name : Types.name)
    : 'a option =
  if ExternManifest.is_empty () then None else find (name_to_string ctx name)

(** {1 For the emission: is an item external?} *)

let is_fun ctx name =
  Option.is_some (find ExternManifest.find_function ctx name)

let is_type ctx name = Option.is_some (find ExternManifest.find_type ctx name)

let is_global ctx name =
  Option.is_some (find ExternManifest.find_global ctx name)

let is_trait_decl ctx name =
  Option.is_some (find ExternManifest.find_trait_decl ctx name)

let is_trait_impl ctx name =
  Option.is_some (find ExternManifest.find_trait_impl ctx name)

(** {1 For the naming: the entry of an external item}

    An item which also has a model in the Aeneas library ([builtin_info]) is
    defined twice, which is an error. *)

let entry (find_entry : string -> 'a option) (ctx : extraction_ctx)
    (item_meta : Types.item_meta) ~(has_model : bool) : 'a option =
  let found = find find_entry ctx item_meta.name in
  if Option.is_some found && has_model then
    [%craise] item_meta.span
      (name_to_string ctx item_meta.name
      ^ " is defined twice: by a model of the Aeneas library and by the \
         manifest of an external crate (option -extern-crate)");
  found

let type_entry ctx (def : type_decl) =
  entry ExternManifest.find_type ctx def.item_meta
    ~has_model:(Option.is_some def.builtin_info)

let fun_entry ctx (def : fun_decl) =
  entry ExternManifest.find_function ctx def.item_meta
    ~has_model:(Option.is_some def.builtin_info)

let global_entry ctx (def : global_decl) =
  entry ExternManifest.find_global ctx def.item_meta
    ~has_model:(Option.is_some def.builtin_info)

let trait_decl_entry ctx (def : trait_decl) =
  entry ExternManifest.find_trait_decl ctx def.item_meta
    ~has_model:(Option.is_some def.builtin_info)

let trait_impl_entry ctx (def : trait_impl) =
  entry ExternManifest.find_trait_impl ctx def.item_meta
    ~has_model:(Option.is_some def.builtin_info)

(** The Lean name recorded for the item [rust] in [pairs] (fields, variants,
    trait items...) of the entry of [owner]. *)
let find_pair (span : Meta.span) (ctx : extraction_ctx) (owner : Types.name)
    (kind : string) (pairs : Manifest.name_pair list) (rust : string) : string =
  match List.find_opt (fun (p : Manifest.name_pair) -> p.rust = rust) pairs with
  | Some p -> p.lean
  | None ->
      [%craise] span
        ("The manifest of the external crate defining "
       ^ name_to_string ctx owner ^ " has no " ^ kind ^ " '" ^ rust ^ "'")
