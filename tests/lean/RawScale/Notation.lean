module

public import Aeneas.Std.Heap.Effects
public import Aeneas.Std.WP

/-! Paper-facing notation for framed heap contracts. Open `Aeneas.Std.HeapWP`
    to enable it. The pre/postconditions remain separation assertions; ordinary
    `c ⦃ result => proposition ⦄` retains its existing pure-WP meaning. -/

public section

namespace Aeneas.Std.HeapWP

scoped infixr:35 " ∗ " => SepLogic.sep

scoped syntax:54 "⦃ " term " ⦄ " term:55 " ⦃ " term+ " => " term " ⦄" : term
scoped syntax:54 "⦃ " term " ⦄ " term:55 " ⦃ " term " ⦄" : term

macro_rules
  | `(⦃ $pre ⦄ $program ⦃ $x => $post ⦄) => do
    let post ← Aeneas.mk_function_syntax post 0 [x]
    `(Aeneas.Std.HeapWP.Triple $pre $program $post)

macro_rules
  | `(⦃ $pre ⦄ $program ⦃ $x $xs:term* => $post ⦄) => do
    let post ← Aeneas.mk_function_syntax post 0 (x :: xs.toList)
    `(Aeneas.Std.HeapWP.Triple $pre $program $post)

macro_rules
  | `(⦃ $pre ⦄ $program ⦃ $post ⦄) =>
    `(Aeneas.Std.HeapWP.Triple $pre $program $post)

end Aeneas.Std.HeapWP
