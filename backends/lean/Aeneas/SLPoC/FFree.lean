namespace Aeneas.SLPoC

inductive FFree (E : Type → Type 1) (α : Type) : Type 1 where
  | ok (value : α)
  | event {β : Type} (e : E β) (next : β → FFree E α)

namespace FFree

def bind {E : Type → Type 1} {α β : Type} (m : FFree E α)
    (next : α → FFree E β) : FFree E β :=
  match m with
  | .ok value => next value
  | .event e k =>
    .event e fun result => bind (k result) next

instance (E : Type → Type 1) : Monad (FFree E) where
  pure := .ok
  bind := bind

instance (E : Type → Type 1) : LawfulMonad (FFree E) :=
  LawfulMonad.mk' (FFree E)
    (id_map := by
      intro α m
      induction m
      · rfl
      · rename_i β event next ih
        simp only [Functor.map, bind]
        apply congrArg (FFree.event event)
        funext value
        exact ih value)
    (pure_bind := by intros; rfl)
    (bind_assoc := by
      intro α β γ m next₁ next₂
      induction m
      · rfl
      · rename_i δ event next ih
        apply congrArg (FFree.event event)
        funext value
        exact ih value)

def trigger {E : Type → Type 1} {α : Type} (e : E α) : FFree E α :=
  .event e .ok

end FFree

end Aeneas.SLPoC
