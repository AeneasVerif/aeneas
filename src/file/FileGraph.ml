(** Given a translated LLBC crate, this module groups the declarations into
    source-file buckets, builds the dependency graph between the buckets, and
    computes its strongly-connected components. *)

open LlbcAst
open LlbcAstUtils
open Types
open Meta

(** Where a declaration/reference lands in the projected file graph.

    If the external item is a builtin already modeled by Aeneas then it will not
    get written to a separate external Lean file, so even if the external
    buckets are non-empty, it may be that no external file is actually
    generated. *)
type bucket =
  | BFile of string
      (** A local source file, keyed on its path below the crate's source root
          (e.g. ["foo.rs"], ["geometry/mod.rs"]) — see
          {!FileMapping.relative_source_path}. The path charon actually reported
          is kept separately in {!t.bucket_source}, for diagnostics. *)
  | BExternalTypes  (** Referenced external type declarations. *)
  | BExternalFuns  (** Referenced external functions/globals/traits. *)
[@@deriving show, ord]

module BucketOrd : Collections.OrderedType with type t = bucket = struct
  type t = bucket

  let compare = compare_bucket
  let to_string = show_bucket
  let pp_t = pp_bucket
  let show_t = show_bucket
end

module BucketSet = Collections.MakeSet (BucketOrd)
module BucketMap = Collections.MakeMap (BucketOrd)

(** The bucket an item belongs to, or [None] if we can't find its metadata.

    Local items goes into [BFile], and external items go into [BExternalTypes]
    or [BExternalFuns] depending on their kind. *)
let bucket_of_item (crate : crate) ~(root : string list)
    ~(on_source : bucket -> string -> unit) (id : item_id) : bucket option =
  match crate_get_item_meta crate id with
  | None -> None
  | Some meta ->
      if not meta.is_local then
        Some
          (match id with
          | IdType _ -> BExternalTypes
          | _ -> BExternalFuns)
      else
        let file = meta.span.data.file in
        let path = Meta.path_of_file_name file.name in
        (* the key is the file's path relative to the source root (for example
        [foo.rs] for [crates/crate1/src/foo.rs]). A file outside the root keeps
        the path charon reported (for example for macro invocations, and
        [include!]). *)
        let key =
          match FileMapping.relative_source_path ~root path with
          | Some key -> key
          | None -> String.concat "/" (FileMapping.path_components path)
        in
        let b = BFile key in
        on_source b path;
        Some b
