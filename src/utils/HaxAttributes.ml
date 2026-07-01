(** Parsing of hax's [_hax::json(...)] item attributes.

    Hax encodes [#[hax_lib::requires(...)]] / [#[hax_lib::ensures(|r| ...)]]
    annotations (and several internal markers) as [_hax::json] attributes
    carrying a JSON payload. This module decodes those payloads; the consumers
    ({!HaxProducer.produce} and the late-skip pre-pass) decide what to do with
    them. *)

let log = Logging.translate_log

(** Role carried by an [AssociatedItem] payload. Hax defines more roles
    ([Decreases], [SmtPat], …); we collapse the ones we don't handle into
    [Other_role]. *)
type hax_role = Requires | Ensures | Other_role

(** A parsed [_hax::json(...)] payload. Hax emits several payload shapes (`Uid`,
    `AssociatedItem`, `ItemStatus`, `NeverErased`, `Language`, …); we act on the
    three we care about and lump the rest into [Other_payload]. *)
type hax_payload =
  | Uid of string  (** [{"Uid":{"uid":"<hex32>"}}] — tags a decoration fn *)
  | Associated_item of { role : hax_role; uid : string }
      (** [{"AssociatedItem":{"role":"Requires"|"Ensures","item":{"uid":"<hex32>"}}}]
          — links a real fn to a decoration fn by uid. *)
  | Late_skip
      (** [{"ItemStatus":{"Included":{"late_skip":true}}}] — hax-internal helper
          (the [const _: () = { … }] wrapper around a decoration, the
          [fn future] helper inside an [ensures] block, …). These items are not
          meant to appear in the extracted output. *)
  | Other_payload

(** Two-step parse of the [args] string charon stores for a [_hax::json] attr.

    Charon records [args] as the verbatim pretty-print of the token stream
    inside the [(...)], which for hax-emitted attributes is a Rust string
    literal containing the JSON: e.g. [args] = ["{\"Uid\":{\"uid\":\"...\"}}"].
    The outer Rust string-literal escapes happen to also be valid JSON string
    escapes, so we parse twice with [Yojson.Safe.from_string]: first to unwrap
    the string literal, then to parse the inner JSON. *)
let parse_args (args : string) : Yojson.Safe.t option =
  try
    match Yojson.Safe.from_string args with
    | `String inner -> Some (Yojson.Safe.from_string inner)
    | _ -> None
  with _ -> None

let role_of_string : string -> hax_role = function
  | "Requires" -> Requires
  | "Ensures" -> Ensures
  | _ -> Other_role

let parse_payload (j : Yojson.Safe.t) : hax_payload =
  match j with
  | `Assoc [ ("Uid", `Assoc [ ("uid", `String uid) ]) ] -> Uid uid
  | `Assoc [ ("AssociatedItem", `Assoc fields) ] -> (
      let role = ref None and uid = ref None in
      List.iter
        (fun (k, v) ->
          match (k, v) with
          | "role", `String r -> role := Some (role_of_string r)
          | "item", `Assoc [ ("uid", `String u) ] -> uid := Some u
          | _ -> ())
        fields;
      match (!role, !uid) with
      | Some role, Some uid -> Associated_item { role; uid }
      | _ -> Other_payload)
  | `Assoc
      [
        ( "ItemStatus",
          `Assoc [ ("Included", `Assoc [ ("late_skip", `Bool true) ]) ] );
      ] -> Late_skip
  | _ -> Other_payload

(** Parse one [Meta.attribute]; [None] for anything that isn't a recognized
    [_hax::json] payload. *)
let parse_attr : Charon.Meta.attribute -> hax_payload option = function
  | AttrUnknown { path = "_hax::json"; args = Some s } -> (
      match parse_args s with
      | Some j -> Some (parse_payload j)
      | None ->
          (* A [_hax::json] attribute whose args we couldn't decode as the
             expected two-step JSON *)
          [%ltrace Printf.sprintf "failed to parse _hax::json payload: %s" s];
          None)
  | _ -> None
