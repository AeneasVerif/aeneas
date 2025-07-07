import Aeneas.Vector

namespace Aeneas

open Lean Elab Command Term Meta

-- TODO: generalize to use extensible sets

elab "#setup_aeneas_simps" : command => do
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
  /- When activating lemmas, we only activate them locally so as not to pollute
     other contexts. -/
  let stx ←
    `(command|
      /- Activating the lemmas to convert `get` to `getElem!` and `set` to `set!` -/
      attribute [local simp]
          _root_.List.Inhabited_getElem_eq_getElem!
          _root_.Array.Inhabited_getElem_eq_getElem!
          _root_.Vector.Inhabited_getElem_eq_getElem!
          _root_.Array.set_eq_set!
          _root_.Vector.set_eq_set!)
  elabCommand stx.raw

end Aeneas
