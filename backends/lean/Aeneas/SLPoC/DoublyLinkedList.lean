import Aeneas.SLPoC.ST

/-!
# Doubly-linked list: executable definitions

A port of the Verus doubly-linked-list example
(`https://github.com/verus-lang/verus/blob/main/examples/doubly_linked.rs`).
Every `&mut self` method becomes a function that consumes `self` and returns the
updated value, which is the shape a functional translation of the Rust code
takes.

The ghost state, the specifications and their proofs live in
`Aeneas.SLPoC.DoublyLinkedListSpec`.
-/

namespace Aeneas.SLPoC

/-- Single node in the list. -/
structure Node (V : Type) where
  prev : Option (Ptr (Node V))
  next : Option (Ptr (Node V))
  payload : V

/-- Doubly-linked list.  Contains a head pointer and a tail pointer; the ghost
state of the Verus version lives in the specifications instead. -/
structure DoublyLinkedList (V : Type) where
  head : Option (Ptr (Node V))
  tail : Option (Ptr (Node V))

namespace DoublyLinkedList

variable {V : Type}

/-! ## Interface of executable functions -/

/-- Construct a new, empty, doubly-linked list. -/
def new : St (DoublyLinkedList V) :=
  pure { head := none, tail := none }

/-- Insert one node, assuming the linked list is empty. -/
def pushEmptyCase (s : DoublyLinkedList V) (v : V) : St (DoublyLinkedList V) := do
  let ptr ← alloc { prev := none, next := none, payload := v }
  pure { s with tail := some ptr, head := some ptr }

/-- Insert a value at the end of the list. -/
def pushBack (s : DoublyLinkedList V) (v : V) : St (DoublyLinkedList V) := do
  match s.tail with
  | none =>
    pushEmptyCase s v
  | some oldTailPtr =>
    let newTailPtr ← alloc { prev := some oldTailPtr, next := none, payload := v }
    let oldTailNode ← read oldTailPtr
    update oldTailPtr { oldTailNode with next := some newTailPtr }
    pure { s with tail := some newTailPtr }

/-- Take a value from the end of the list.  Requires the list to be non-empty. -/
def popBack (s : DoublyLinkedList V) : St (DoublyLinkedList V × V) := do
  let lastPtr := s.tail.get!
  let lastNode ← read lastPtr
  free lastPtr
  let v := lastNode.payload
  match lastNode.prev with
  -- No `prev`: this was the only node, so the list becomes empty.
  | none =>
    pure ({ s with tail := none, head := none }, v)
  | some penultimatePtr =>
    let penultimateNode ← read penultimatePtr
    update penultimatePtr { penultimateNode with next := none }
    pure ({ s with tail := some penultimatePtr }, v)

/-- Insert a value at the front of the list. -/
def pushFront (s : DoublyLinkedList V) (v : V) : St (DoublyLinkedList V) := do
  match s.head with
  | none =>
    pushEmptyCase s v
  | some oldHeadPtr =>
    let newHeadPtr ← alloc { prev := none, next := some oldHeadPtr, payload := v }
    let oldHeadNode ← read oldHeadPtr
    update oldHeadPtr { oldHeadNode with prev := some newHeadPtr }
    pure { s with head := some newHeadPtr }

/-- Take a value from the front of the list.  Requires the list to be
non-empty. -/
def popFront (s : DoublyLinkedList V) : St (DoublyLinkedList V × V) := do
  let firstPtr := s.head.get!
  let firstNode ← read firstPtr
  free firstPtr
  let v := firstNode.payload
  match firstNode.next with
  -- No `next`: this was the only node, so the list becomes empty.
  | none =>
    pure ({ s with tail := none, head := none }, v)
  | some secondPtr =>
    let secondNode ← read secondPtr
    update secondPtr { secondNode with prev := none }
    pure ({ s with head := some secondPtr }, v)

/-- The `while j < i` loop of `get`, walking the list from index `j` to
index `i`. -/
def getLoop (i : Nat) (j : Nat) (ptr : Ptr (Node V)) : St (Ptr (Node V)) :=
  if j < i then do
    let node ← read ptr
    let nextPtr := node.next.get!
    getLoop i (j + 1) nextPtr
  else
    pure ptr
termination_by i - j
decreasing_by omega

/-- Get the `i`th value of the list. -/
def get (s : DoublyLinkedList V) (i : Nat) : St V := do
  let ptr ← getLoop i 0 s.head.get!
  let node ← read ptr
  pure node.payload

end DoublyLinkedList

/-- Iterator over a doubly-linked list.  `index` is ghost state in the Verus
version. -/
structure Iterator (V : Type) where
  l : DoublyLinkedList V
  cur : Option (Ptr (Node V))
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
