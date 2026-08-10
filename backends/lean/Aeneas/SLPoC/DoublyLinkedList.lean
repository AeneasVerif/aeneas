import Aeneas.SLPoC.ST

/-!
# Doubly-linked list: executable definitions

A port of the Verus doubly-linked-list example
(`https://github.com/verus-lang/verus/blob/main/examples/doubly_linked.rs`)
to the separation-logic proof of concept.

The Rust code is imperative and manipulates `&mut self`; the port turns every
method into a function that consumes `self` and returns the updated value, which
is the shape a functional translation of the Rust code takes.

This file contains the computational part only.  The ghost state, the
representation predicate, the specifications and their proofs live in
`Aeneas.SLPoC.DoublyLinkedListSpec`.
-/

namespace Aeneas.SLPoC

/-- Pointers are allocation identifiers, so they are trivially inhabited.  This
instance is what makes the `unwrap`s of the Rust code expressible. -/
instance instInhabitedRef {α : Type} : Inhabited (Ref α) :=
  ⟨(0 : Nat)⟩

/-- Single node in the list. -/
structure Node (V : Type) where
  prev : Option (Ref (Node V))
  next : Option (Ref (Node V))
  payload : V

/-- Doubly-linked list.  Contains a head pointer and a tail pointer; the ghost
state of the Verus version lives in the specifications instead. -/
structure DoublyLinkedList (V : Type) where
  head : Option (Ref (Node V))
  tail : Option (Ref (Node V))

namespace DoublyLinkedList

variable {V : Type}

/-! ## Interface of executable functions -/

/-- Construct a new, empty, doubly-linked list. -/
def new : St (DoublyLinkedList V) :=
  pure { head := none, tail := none }

/-- Insert one node, assuming the linked list is empty. -/
def pushEmptyCase (s : DoublyLinkedList V) (v : V) : St (DoublyLinkedList V) := do
  -- Allocate a node to contain the payload
  let ptr ← alloc { prev := none, next := none, payload := v }
  -- Update head and tail pointers
  pure { s with tail := some ptr, head := some ptr }

/-- Insert a value at the end of the list. -/
def pushBack (s : DoublyLinkedList V) (v : V) : St (DoublyLinkedList V) := do
  match s.tail with
  | none =>
    -- Special case: list is empty
    pushEmptyCase s v
  | some oldTailPtr =>
    -- Allocate a new node to go on the end.  Its `prev` field points to the old
    -- tail pointer.
    let newTailPtr ← alloc { prev := some oldTailPtr, next := none, payload := v }
    -- Update the `next` pointer of the previous tail node
    let oldTailNode ← read oldTailPtr
    update oldTailPtr { oldTailNode with next := some newTailPtr }
    -- Update `self.tail`
    pure { s with tail := some newTailPtr }

/-- Take a value from the end of the list.  Requires the list to be non-empty. -/
def popBack (s : DoublyLinkedList V) : St (DoublyLinkedList V × V) := do
  -- Deallocate the last node in the list and get the payload.
  let lastPtr := s.tail.get!
  let lastNode ← read lastPtr
  free lastPtr
  let v := lastNode.payload
  match lastNode.prev with
  | none =>
    -- If this was the *only* node in the list, we set both `head` and `tail` to
    -- `none`.
    pure ({ s with tail := none, head := none }, v)
  | some penultimatePtr =>
    -- Otherwise the `tail` pointer becomes the previously second-to-last
    -- pointer, whose `next` field must be cleared.
    let penultimateNode ← read penultimatePtr
    update penultimatePtr { penultimateNode with next := none }
    pure ({ s with tail := some penultimatePtr }, v)

/-- Insert a value at the front of the list. -/
def pushFront (s : DoublyLinkedList V) (v : V) : St (DoublyLinkedList V) := do
  match s.head with
  | none =>
    -- Special case: list is empty
    pushEmptyCase s v
  | some oldHeadPtr =>
    -- Allocate a new node to go at the front.  Its `next` field points to the
    -- old head pointer.
    let newHeadPtr ← alloc { prev := none, next := some oldHeadPtr, payload := v }
    -- Update the `prev` pointer of the previous head node
    let oldHeadNode ← read oldHeadPtr
    update oldHeadPtr { oldHeadNode with prev := some newHeadPtr }
    -- Update `self.head`
    pure { s with head := some newHeadPtr }

/-- Take a value from the front of the list.  Requires the list to be
non-empty. -/
def popFront (s : DoublyLinkedList V) : St (DoublyLinkedList V × V) := do
  -- Deallocate the first node in the list and get the payload.
  let firstPtr := s.head.get!
  let firstNode ← read firstPtr
  free firstPtr
  let v := firstNode.payload
  match firstNode.next with
  | none =>
    -- If this was the *only* node in the list, we set both `head` and `tail` to
    -- `none`.
    pure ({ s with tail := none, head := none }, v)
  | some secondPtr =>
    -- Otherwise the `head` pointer becomes the previously second pointer, whose
    -- `prev` field must be cleared.
    let secondNode ← read secondPtr
    update secondPtr { secondNode with prev := none }
    pure ({ s with head := some secondPtr }, v)

/-- The `while j < i` loop of `get`, walking the list from index `j` to
index `i`. -/
def getLoop (i : Nat) (j : Nat) (ptr : Ref (Node V)) : St (Ref (Node V)) :=
  if j < i then do
    -- Get the next node from the `next` field
    let node ← read ptr
    let nextPtr := node.next.get!
    getLoop i (j + 1) nextPtr
  else
    pure ptr
termination_by i - j
decreasing_by omega

/-- Get the `i`th value of the list. -/
def get (s : DoublyLinkedList V) (i : Nat) : St V := do
  -- Iterate the nodes from 0 to i, starting at the head node
  let ptr ← getLoop i 0 s.head.get!
  -- Get this node's payload and return it
  let node ← read ptr
  pure node.payload

end DoublyLinkedList

/-- Iterator over a doubly-linked list.  `index` is ghost state in the Verus
version. -/
structure Iterator (V : Type) where
  l : DoublyLinkedList V
  cur : Option (Ref (Node V))
  index : Nat

namespace Iterator

variable {V : Type}

/-- Create an iterator positioned at the front of `l`. -/
def new (l : DoublyLinkedList V) : St (Iterator V) :=
  pure { l := l, cur := l.head, index := 0 }

/-- The value the iterator currently points at. -/
def value (it : Iterator V) : St V := do
  let cur := it.cur.get!
  let node ← read cur
  pure node.payload

/-- Advance the iterator; returns whether it still points at a value. -/
def moveNext (it : Iterator V) : St (Iterator V × Bool) := do
  let cur := it.cur.get!
  let node ← read cur
  match node.next with
  | none => pure ({ it with cur := none, index := it.index + 1 }, false)
  | some nextPtr =>
    pure ({ it with cur := some nextPtr, index := it.index + 1 }, true)

end Iterator

end Aeneas.SLPoC
