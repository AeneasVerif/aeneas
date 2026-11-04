/- Safe owning API factored from the Aeneas extraction of doubly_linked/safe.rs.
Manual adaptation: thread the same explicit node Repr through heap effects,
clear's recursive helper, and Drop. See ../EXTRACTION.md. -/
module
public import Aeneas
public import DoublyLinked.Types
public import DoublyLinked.Raw
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.internalConstructors false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048

namespace doubly_linked

/-- [doubly_linked::{doubly_linked::LinkedList}::new]:
    Source: 'tests/src/doubly_linked/safe.rs', lines 9:4-13:5
    Visibility: public -/
def LinkedList.new (repr : Aeneas.Std.Repr Node) : Result LinkedList := do
  let root ← ext.allocate_node repr 0#u32
  init repr root 0#u32
  ok { root, len := 0#usize }

/-- [doubly_linked::{doubly_linked::LinkedList}::len]:
    Source: 'tests/src/doubly_linked/safe.rs', lines 15:4-17:5
    Visibility: public -/
def LinkedList.impl.len (self : LinkedList) : Result Std.Usize := do
  ok self.len

/-- [doubly_linked::{doubly_linked::LinkedList}::is_empty]:
    Source: 'tests/src/doubly_linked/safe.rs', lines 19:4-21:5
    Visibility: public -/
def LinkedList.is_empty (self : LinkedList) : Result Bool := do
  ok (self.len = 0#usize)

/-- [doubly_linked::{doubly_linked::LinkedList}::front]:
    Source: 'tests/src/doubly_linked/safe.rs', lines 23:4-32:5
    Visibility: public -/
def LinkedList.front (repr : Aeneas.Std.Repr Node) (self : LinkedList) : Result (Option Std.U32) := do
  let b ← LinkedList.is_empty self
  if b
  then ok none
  else
    let sentinel ← ext.read_node repr self.root
    let n ← ext.read_node repr sentinel.next
    ok (some n.value)

/-- [doubly_linked::{doubly_linked::LinkedList}::back]:
    Source: 'tests/src/doubly_linked/safe.rs', lines 34:4-43:5
    Visibility: public -/
def LinkedList.back (repr : Aeneas.Std.Repr Node) (self : LinkedList) : Result (Option Std.U32) := do
  let b ← LinkedList.is_empty self
  if b
  then ok none
  else
    let sentinel ← ext.read_node repr self.root
    let n ← ext.read_node repr sentinel.prev
    ok (some n.value)

/-- [doubly_linked::{doubly_linked::LinkedList}::push_front]:
    Source: 'tests/src/doubly_linked/safe.rs', lines 45:4-53:5
    Visibility: public -/
def LinkedList.push_front
  (repr : Aeneas.Std.Repr Node) (self : LinkedList) (value : Std.U32) : Result LinkedList := do
  let o ← lift (Usize.checked_add self.len 1#usize)
  let len ← core.option.Option.expect o (toStr "list length overflow")
  let node ← ext.allocate_node repr value
  init repr node value
  insert_after repr self.root node
  ok { self with len }

/-- [doubly_linked::{doubly_linked::LinkedList}::pop_front]:
    Source: 'tests/src/doubly_linked/safe.rs', lines 55:4-66:5
    Visibility: public -/
def LinkedList.pop_front
  (repr : Aeneas.Std.Repr Node) (self : LinkedList) : Result ((Option Std.U32) × LinkedList) := do
  let b ← LinkedList.is_empty self
  if b
  then ok (none, self)
  else
    let node ← remove_after repr self.root
    let n ← ext.take_node repr node
    let i ← self.len - 1#usize
    ok (some n.value, { self with len := i })

/-- [doubly_linked::{doubly_linked::LinkedList}::clear]: loop 0:
    Source: 'tests/src/doubly_linked/safe.rs', lines 69:8-71:9
    Visibility: public -/
@[rust_loop]
def LinkedList.clear_loop (repr : Aeneas.Std.Repr Node) (self : LinkedList) : Result LinkedList := do
  let b ← LinkedList.is_empty self
  if b
  then ok self
  else let (_, self1) ← LinkedList.pop_front repr self
       LinkedList.clear_loop repr self1
partial_fixpoint

/-- [doubly_linked::{doubly_linked::LinkedList}::clear]:
    Source: 'tests/src/doubly_linked/safe.rs', lines 68:4-72:5
    Visibility: public -/
@[reducible]
def LinkedList.clear (repr : Aeneas.Std.Repr Node) (self : LinkedList) : Result LinkedList := do
  LinkedList.clear_loop repr self

/-- [doubly_linked::{impl core::ops::drop::Drop for doubly_linked::LinkedList}::drop]:
    Source: 'tests/src/doubly_linked/safe.rs', lines 76:4-79:5
    Visibility: public -/
def LinkedList.Insts.CoreOpsDropDrop.drop
  (repr : Aeneas.Std.Repr Node) (self : LinkedList) : Result LinkedList := do
  let self1 ← LinkedList.clear repr self
  let _ ← ext.take_node repr self1.root
  ok self1

/-- Trait implementation: [doubly_linked::{impl core::ops::drop::Drop for doubly_linked::LinkedList}]
    Source: 'tests/src/doubly_linked/safe.rs', lines 75:0-80:1 -/
@[reducible]
def LinkedList.Insts.CoreOpsDropDrop (repr : Aeneas.Std.Repr Node) : core.ops.drop.Drop LinkedList := {
  drop := LinkedList.Insts.CoreOpsDropDrop.drop repr
}

end doubly_linked
