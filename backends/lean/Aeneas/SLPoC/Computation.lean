import Aeneas.SLPoC.FFree
import Aeneas.SLPoC.Heap

namespace Aeneas.SLPoC

inductive StEvents : Type → Type 1 where
  | Alloc {α : Type} (value : α) : StEvents (Ref α)
  | Read {α : Type} (r : Ref α) : StEvents α
  | Update {α : Type} (r : Ref α) (value : α) : StEvents Unit
  | Free {α : Type} (r : Ref α) : StEvents Unit

abbrev St := FFree StEvents

instance St.instLawfulMonad : LawfulMonad St :=
  inferInstanceAs (LawfulMonad (FFree StEvents))

def alloc {α : Type} (value : α) : St (Ref α) :=
  FFree.trigger (.Alloc value)

def read {α : Type} (r : Ref α) : St α :=
  FFree.trigger (.Read r)

def update {α : Type} (r : Ref α) (value : α) : St Unit :=
  FFree.trigger (.Update r value)

def free {α : Type} (r : Ref α) : St Unit :=
  FFree.trigger (.Free r)

inductive Evaluates : St α → Heap → α → Heap → Prop where
  | ok (value : α) (h : Heap) :
      Evaluates (.ok value) h value h
  | alloc {β : Type} {value : β} {next : Ref β → St α}
      {h₀ h₁ h₂ : Heap} {r : Ref β} {result : α}
      (hFresh : fresh h₀ r value h₁)
      (hNext : Evaluates (next r) h₁ result h₂) :
      Evaluates (.event (.Alloc value) next) h₀ result h₂
  | read {β : Type} {r : Ref β} {next : β → St α}
      {h₀ h₁ : Heap} {result : α}
      (hContains : contains h₀ r)
      (hNext : Evaluates (next (Heap.read r h₀ hContains)) h₀ result h₁) :
      Evaluates (.event (.Read r) next) h₀ result h₁
  | update {β : Type} {r : Ref β} {value : β} {next : Unit → St α}
      {h₀ h₁ : Heap} {result : α}
      (hContains : contains h₀ r)
      (hNext :
        Evaluates (next ()) (Heap.update r value h₀ hContains) result h₁) :
      Evaluates (.event (.Update r value) next) h₀ result h₁
  | free {β : Type} {r : Ref β} {next : Unit → St α}
      {h₀ h₁ : Heap} {result : α}
      (hContains : contains h₀ r)
      (hNext : Evaluates (next ()) (Heap.free r h₀ hContains) result h₁) :
      Evaluates (.event (.Free r) next) h₀ result h₁

end Aeneas.SLPoC
