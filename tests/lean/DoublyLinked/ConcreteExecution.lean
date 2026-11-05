module

public import DoublyLinked.ConcreteLayout
public import DoublyLinked.SafeProperties
public import Aeneas.Std.Heap.Execution
meta import DoublyLinked.ConcreteLayout
import all DoublyLinked.Raw
import all DoublyLinked.FunsExternal
import all Aeneas.Std.Alloc.Boxed
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Heap

@[expose] public section

open Aeneas Aeneas.Std HeapWP

namespace doubly_linked.concrete

deriving instance DecidableEq for Node

def root : Ptr := ⟨0, 256#usize⟩
def allocated : Heap :=
  ((Heap.newBlock repr [bytes (ext.blankNode 0#u32)] true root.address none Heap.empty).getD
    (root, Heap.empty)).2
def initialized : Heap :=
  (Heap.write repr root (Node.mk root root 0#u32)
    (bytes (Node.mk root root 0#u32)) rfl allocated).getD Heap.empty

private theorem selected {α : Type} (run : Option α) (fallback : α)
    (success : run.isSome = true) : run = some (run.getD fallback) := by
  cases run
  · contradiction
  · rfl

/-- Canonical stored null links are accepted during the first allocation.
    This does not authorize dereferencing address zero. -/
theorem blank_allocates :
    Heap.newBlock repr [bytes (ext.blankNode 0#u32)] true root.address none Heap.empty =
      some (root, allocated) := by
  have first : (Heap.newBlock repr [bytes (ext.blankNode 0#u32)] true
      root.address none Heap.empty).map Prod.fst = some root := by native_decide
  generalize h : Heap.newBlock repr [bytes (ext.blankNode 0#u32)] true
    root.address none Heap.empty = run at *
  cases run
  · simp at first
  · rename_i pair
    have same := Option.some.inj first
    simp only [allocated, h, Option.getD_some]
    exact congrArg some (Prod.ext same rfl)

/-- The actual safe constructor, not a second implementation of its effects. -/
theorem new_runs :
    Runs (LinkedList.new repr) Heap.empty ⟨root, 0#usize⟩ initialized := by
  unfold LinkedList.new ext.allocate_node alloc.boxed.Box.into_raw
  apply Runs.bind (value := root) (s₁ := allocated)
  · apply Runs.allocatingModify
    exact ⟨[bytes (ext.blankNode 0#u32)], root.address, none,
      ⟨rfl, True.intro⟩, blank_allocates⟩
  unfold init ext.write_node
  apply Runs.bind (value := ()) (s₁ := initialized)
  · apply Runs.checkedModify
    exact ⟨bytes (Node.mk root root 0#u32), rfl,
      selected _ Heap.empty (by native_decide)⟩
  exact Runs.pure _ _

theorem null_not_readable :
    Heap.read repr (ext.blankNode 0#u32).prev allocated = none := by native_decide

theorem initialized_links :
    Heap.read repr root initialized = some (Node.mk root root 0#u32) := by native_decide

/-- Instantiate the complete owning-list constructor contract, including its
    abstraction and arbitrary frame, with the concrete padded descriptor. -/
theorem new_spec (s : Heap) (F : SepLogic.Fragment) (hi : s.Inv)
    (hm : SepLogic.Fragment.Matches s F) :
    Spec (LinkedList.new repr) (fun self stop => ListState repr self [] F stop) s :=
  LinkedList.new.spec repr layout (by decide) s F hi hm

end doubly_linked.concrete
