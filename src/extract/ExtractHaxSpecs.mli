(** Lean printer for {!HaxSpecs.spec} and {!HaxSpecs.obligation} entries. *)

module F = Format

(** Emits one [HaxSpecs.spec] entry. The [span option] is used for errors *)
val emit_spec :
  ExtractBase.extraction_ctx ->
  F.formatter ->
  HaxSpecs.spec ->
  Meta.span option ->
  unit

(** Emits one [HaxSpecs.obligation] entry. The [span option] is used for errors
*)
val emit_obligation :
  ExtractBase.extraction_ctx ->
  F.formatter ->
  HaxSpecs.obligation ->
  Meta.span option ->
  unit
