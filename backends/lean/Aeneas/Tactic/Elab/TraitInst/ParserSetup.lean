import Lean

namespace Aeneas.TraitInst

/-! Register a parser that parses a single `>` character, even when `>>` follows.
    This avoids the standard issue where `Vec<_>>` is tokenized as `>>` instead
    of `>` followed by `>`.

    This parser is only referenced by the `traitInstType` and `traitInstId` syntax
    rules — it is never invoked during normal Lean term/command parsing. -/

open Lean Parser in
@[run_parser_attribute_hooks]
def closingAngle := rawCh '>' (trailingWs := true)

end Aeneas.TraitInst
