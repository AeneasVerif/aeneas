/- Raw API factored from the Aeneas extraction of doubly_linked/raw.rs.
Manual adaptation: thread an explicit node Repr through heap-effect callers.
Control flow and pointer reads/writes are unchanged. See ../EXTRACTION.md. -/
module
public import Aeneas
public import DoublyLinked.Types
public import DoublyLinked.FunsExternal
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

/-- [doubly_linked::{impl core::clone::Clone for doubly_linked::Node}::clone]:
    Source: 'tests/src/doubly_linked/raw.rs', lines 2:9-2:14
    Visibility: public -/
def Node.Insts.CoreCloneClone.clone (self : Node) : Result Node := do
  ok self

/-- Trait implementation: [doubly_linked::{impl core::clone::Clone for doubly_linked::Node}]
    Source: 'tests/src/doubly_linked/raw.rs', lines 2:9-2:14 -/
@[reducible]
def Node.Insts.CoreCloneClone : core.clone.Clone Node := {
  clone := Node.Insts.CoreCloneClone.clone
}

/-- Trait implementation: [doubly_linked::{impl core::marker::Copy for doubly_linked::Node}]
    Source: 'tests/src/doubly_linked/raw.rs', lines 2:16-2:20 -/
@[reducible]
def Node.Insts.CoreMarkerCopy : core.marker.Copy Node := {
  cloneInst := Node.Insts.CoreCloneClone
}

/-- [doubly_linked::init]:
    Source: 'tests/src/doubly_linked/raw.rs', lines 43:0-52:1
    Visibility: public -/
def init (repr : Aeneas.Std.Repr Node) (node : MutRawPtr Node) (value : Std.U32) : Result Unit := do
  ext.write_node repr node (Node.mk node node value)

/-- [doubly_linked::set_next]:
    Source: 'tests/src/doubly_linked/raw.rs', lines 54:0-57:1 -/
def set_next
  (repr : Aeneas.Std.Repr Node) (node : MutRawPtr Node) (next : MutRawPtr Node) : Result Unit := do
  let old ← ext.read_node repr node
  ext.write_node repr node (Node.mk old.prev next old.value)

/-- [doubly_linked::set_prev]:
    Source: 'tests/src/doubly_linked/raw.rs', lines 59:0-62:1 -/
def set_prev
  (repr : Aeneas.Std.Repr Node) (node : MutRawPtr Node) (prev : MutRawPtr Node) : Result Unit := do
  let old ← ext.read_node repr node
  ext.write_node repr node (Node.mk prev old.next old.value)

/-- [doubly_linked::insert_after]:
    Source: 'tests/src/doubly_linked/raw.rs', lines 70:0-83:1
    Visibility: public -/
def insert_after
  (repr : Aeneas.Std.Repr Node) (left : MutRawPtr Node) (node : MutRawPtr Node) : Result Unit := do
  let before ← ext.read_node repr left
  let inserted ← ext.read_node repr node
  ext.write_node repr node (Node.mk left before.next inserted.value)
  set_next repr left node
  set_prev repr before.next node

/-- [doubly_linked::remove]:
    Source: 'tests/src/doubly_linked/raw.rs', lines 91:0-96:1
    Visibility: public -/
def remove (repr : Aeneas.Std.Repr Node) (node : MutRawPtr Node) : Result Unit := do
  let old ← ext.read_node repr node
  set_next repr old.prev old.next
  set_prev repr old.next old.prev
  init repr node old.value

/-- [doubly_linked::remove_after]:
    Source: 'tests/src/doubly_linked/raw.rs', lines 103:0-108:1
    Visibility: public -/
def remove_after (repr : Aeneas.Std.Repr Node) (root : MutRawPtr Node) : Result (MutRawPtr Node) := do
  let sentinel ← ext.read_node repr root
  remove repr sentinel.next
  ok sentinel.next

end doubly_linked
