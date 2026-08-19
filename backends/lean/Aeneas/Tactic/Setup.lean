module
public import Aeneas.Std.Slice
public import Aeneas.Data.Vector
public section

namespace Aeneas

open Lean Elab Command Term Meta

/-- When `true` (default), using the deprecated `#setup_aeneas_simps` command emits a warning. -/
meta register_option Deprecated.setupAeneasSimps : Bool := {
  defValue := true
  descr := "Emit warnings when using the deprecated `#setup_aeneas_simps` command"
}

private meta def emitSetupAeneasSimpsWarning : CommandElabM Unit := do
  if Deprecated.setupAeneasSimps.get (← getOptions) then
    logWarning m!"`#setup_aeneas_simps` has been deprecated. \
      Set `set_option Aeneas.Deprecated.setupAeneasSimps false` to silence this warning."

elab "#setup_aeneas_simps" : command => do
  -- Emit a warning
  emitSetupAeneasSimpsWarning
  --
  let stx ←
    `(command|
      attribute [-simp]
        /- We want to use `getElem!` as much as possible so we deactivate
          lemmas which turn `getElem!` into `getD`, and activate lemmas
          which turn `getElem` into `getElem!`.
        -/
        _root_.List.getElem!_eq_getElem?_getD
        _root_.Array.set!_eq_setIfInBounds
        _root_.getElem!_pos
        /- This one is annoying when writing, for instance, cryptographic specifications:
           it tends to reduce terms we don't want to reduce, leading to blowups -/
        _root_.List.reduceReplicate
        /- We often existentially quantify booleans in the specifications -/
        _root_.Bool.exists_bool)
  elabCommand stx.raw
  let stx ←
    `(command|
      attribute [-simp_lists] _root_.getElem!_pos)
  elabCommand stx.raw
  /- When activating lemmas, we only activate them locally so as not to pollute
     other contexts. -/
  let stx ←
    `(command|
      /- Activating the lemmas to convert `get` to `getElem!` and `set` to `set!` -/
      attribute [local simp, local simp_lists_hyps_simps, local simp_lists]
          _root_.List.Inhabited_getElem_eq_getElem!
          _root_.Array.Inhabited_getElem_eq_getElem!
          _root_.Aeneas.Std.Slice.Inhabited_getElem_eq_getElem!
          _root_.Vector.Inhabited_getElem_eq_getElem!
          _root_.Array.set_eq_set!
          _root_.Vector.set_eq_set!)
  elabCommand stx.raw

end Aeneas
