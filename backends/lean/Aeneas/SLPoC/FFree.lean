import Aeneas.Std.Primitives

namespace Aeneas.SLPoC

inductive FFree (E : Type → Type 1) (α : Type) : Type 1 where
  | ok (value : α)
  | fail (error : Std.Error)
  | div
  | event {β : Type} (e : E β) (next : β → FFree E α)

namespace FFree

def bind {E : Type → Type 1} {α β : Type} (m : FFree E α)
    (next : α → FFree E β) : FFree E β :=
  match m with
  | .ok value => next value
  | .fail error => .fail error
  | .div => .div
  | .event e k =>
    .event e fun result => bind (k result) next

instance (E : Type → Type 1) : Monad (FFree E) where
  pure := .ok
  bind := bind

def trigger {E : Type → Type 1} {α : Type} (e : E α) : FFree E α :=
  .event e .ok

end FFree

end Aeneas.SLPoC
