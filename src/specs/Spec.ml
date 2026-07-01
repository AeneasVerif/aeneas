open Identifiers
open Meta
module SpecId = IdGen ()
module ProofId = IdGen ()

(** The shape of a spec entry *)
type spec_kind = HaxSpec of HaxSpecs.spec [@@deriving show]

(** A spec entry: a statement of correctness *)
type spec = { id : SpecId.id; kind : spec_kind; span : span option }
[@@deriving show]

(** The shape of a proof-obligation entry *)
type proof_kind = HaxProof of HaxSpecs.obligation [@@deriving show]

(** A proof obligation: a theorem to discharge *)
type proof_obligation = {
  id : ProofId.id;
  kind : proof_kind;
  span : span option;
}
[@@deriving show]

(** The extra Lean modules the configured spec source needs to elaborate *)
let required_imports () : string list =
  match !Config.opt_spec_config with
  | Some (Config.Hax, _) -> HaxSpecs.required_imports ()
  | None -> []
