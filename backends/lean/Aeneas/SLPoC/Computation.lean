import Aeneas.SLPoC.FFree
import Aeneas.SLPoC.Heap

namespace Aeneas.SLPoC

inductive StEvents : Type → Type 1 where
  | Alloc {α : Type} (value : α) : StEvents (ref α)
  | Read {α : Type} (r : ref α) : StEvents α
  | Update {α : Type} (r : ref α) (value : α) : StEvents Unit
  | Free {α : Type} (r : ref α) : StEvents Unit

abbrev St := FFree StEvents

instance St.instLawfulMonad : LawfulMonad St :=
  inferInstanceAs (LawfulMonad (FFree StEvents))

namespace State

def alloc {α : Type} (value : α) : St (ref α) :=
  FFree.trigger (.Alloc value)

def read {α : Type} (r : ref α) : St α :=
  FFree.trigger (.Read r)

def update {α : Type} (r : ref α) (value : α) : St Unit :=
  FFree.trigger (.Update r value)

def free {α : Type} (r : ref α) : St Unit :=
  FFree.trigger (.Free r)
end State

inductive Evaluates : St α → Heap → α → Heap → Prop where
  | ok (value : α) (h : Heap) :
      Evaluates (.ok value) h value h
  | alloc {β : Type} {value : β} {next : ref β → St α}
      {h₀ h₁ h₂ : Heap} {r : ref β} {result : α}
      (hFresh : fresh h₀ r value h₁)
      (hNext : Evaluates (next r) h₁ result h₂) :
      Evaluates (.event (.Alloc value) next) h₀ result h₂
  | read {β : Type} {r : ref β} {next : β → St α}
      {h₀ h₁ : Heap} {result : α}
      (hContains : contains h₀ r)
      (hNext : Evaluates (next (read r h₀ hContains)) h₀ result h₁) :
      Evaluates (.event (.Read r) next) h₀ result h₁
  | update {β : Type} {r : ref β} {value : β} {next : Unit → St α}
      {h₀ h₁ : Heap} {result : α}
      (hContains : contains h₀ r)
      (hNext :
        Evaluates (next ()) (update r value h₀ hContains) result h₁) :
      Evaluates (.event (.Update r value) next) h₀ result h₁
  | free {β : Type} {r : ref β} {next : Unit → St α}
      {h₀ h₁ : Heap} {result : α}
      (hContains : contains h₀ r)
      (hNext : Evaluates (next ()) (free r h₀ hContains) result h₁) :
      Evaluates (.event (.Free r) next) h₀ result h₁

end Aeneas.SLPoC
