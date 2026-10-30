module

public import DoublyLinked.Raw
import all Aeneas.Std.Heap.Separation

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic

namespace doubly_linked

abbrev Ptr := MutRawPtr Node

def nodeAt (repr : Aeneas.Std.Repr Node) (p prev next : Ptr) (value : U32) : Assertion :=
  pointsTo repr p (.mk prev next value)

@[simp] theorem Node.mk_eta (node : Node) : Node.mk node.prev node.next node.value = node := by
  cases node
  rfl

@[step] theorem Node.Insts.CoreCloneClone.clone.spec (node : Node) :
    Node.Insts.CoreCloneClone.clone node ⦃ (result : Node) => result = node ⦄ := by
  simp [Node.Insts.CoreCloneClone.clone]

theorem frameLeft {P R : Assertion} {c : Result α} {Q : α → Assertion}
    (ht : HeapWP.Triple P c Q) :
    HeapWP.Triple (sep R P) c (fun x => sep R (Q x)) :=
  HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ h hp => (sep_comm _ _ h).mp hp) (HeapWP.frame ht)

theorem framePure {P R : Assertion} {c : Result α} {A : α → Prop} {Q : α → Assertion}
    (ht : HeapWP.Triple P c (fun x h => A x ∧ Q x h)) :
    HeapWP.Triple (sep P R) c (fun x h => A x ∧ sep (Q x) R h) :=
  HeapWP.Triple.conseq (fun _ hp => hp)
    (fun _ h hp => (sep_and_left _ _ _ h).mp hp) (HeapWP.frame ht)

theorem frameLeftPure {P R : Assertion} {c : Result α} {A : α → Prop} {Q : α → Assertion}
    (ht : HeapWP.Triple P c (fun x h => A x ∧ Q x h)) :
    HeapWP.Triple (sep R P) c (fun x h => A x ∧ sep R (Q x) h) :=
  HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ h hp => ⟨hp.1, (sep_comm _ _ h).mp hp.2⟩) (framePure ht)

variable (repr : Aeneas.Std.Repr Node) (hsize : 0 < repr.size)
include hsize

theorem ext.read_node.spec (p : Ptr) (old : Node) :
    HeapWP.Triple (pointsTo repr p old) (ext.read_node repr p)
      (fun result h => result = old ∧ pointsTo repr p old 0 h) := by
  exact HeapWP.read.spec repr p old 0 hsize

theorem ext.write_node.spec (p : Ptr) (old value : Node) :
    HeapWP.Triple (pointsTo repr p old) (ext.write_node repr p value)
      (fun _ => pointsTo repr p value) := by
  exact HeapWP.write.spec repr p old value hsize

theorem init.spec (node : Ptr) (old : Node) (value : U32) :
    HeapWP.Triple (pointsTo repr node old) (init repr node value)
      (fun _ => nodeAt repr node node node value) := by
  /- One whole-node write establishes both self-links and the supplied payload. -/
  exact ext.write_node.spec repr hsize node old _

theorem set_next.spec (node next : Ptr) (old : Node) :
    HeapWP.Triple (pointsTo repr node old) (set_next repr node next)
      (fun _ => nodeAt repr node old.prev next old.value) := by
  /- Read the current whole node, retain its predecessor and payload, then write. -/
  unfold set_next
  apply HeapWP.Triple.bind (ext.read_node.spec repr hsize node old)
  intro observed
  apply HeapWP.Triple.pure_pre
  intro he
  subst observed
  exact ext.write_node.spec repr hsize node old _

theorem set_prev.spec (node prev : Ptr) (old : Node) :
    HeapWP.Triple (pointsTo repr node old) (set_prev repr node prev)
      (fun _ => nodeAt repr node prev old.next old.value) := by
  /- Symmetric to set_next; crucially this reads after any previous link update. -/
  unfold set_prev
  apply HeapWP.Triple.bind (ext.read_node.spec repr hsize node old)
  intro observed
  apply HeapWP.Triple.pure_pre
  intro he
  subst observed
  exact ext.write_node.spec repr hsize node old _

theorem insert_after.distinct_spec (left node right previous following : Ptr)
    (lv nv rv : U32) :
    HeapWP.Triple
      (sep (nodeAt repr left previous right lv)
        (sep (nodeAt repr node node node nv) (nodeAt repr right left following rv)))
      (insert_after repr left node)
      (fun _ => sep (nodeAt repr left previous node lv)
        (sep (nodeAt repr node left right nv) (nodeAt repr right node following rv))) := by
  /- Read left and the detached node; write the inserted links. Frame the other
  two nodes around each write, then update left.next and right.prev. -/
  unfold insert_after
  apply HeapWP.Triple.bind (framePure (ext.read_node.spec repr hsize left (.mk previous right lv)))
  intro before
  apply HeapWP.Triple.pure_pre
  intro he
  subst before
  apply HeapWP.Triple.bind
    (frameLeftPure (framePure (ext.read_node.spec repr hsize node (.mk node node nv))))
  intro inserted
  apply HeapWP.Triple.pure_pre
  intro he
  subst inserted
  apply HeapWP.Triple.bind
    (frameLeft (HeapWP.frame (ext.write_node.spec repr hsize node (.mk node node nv) _)))
  intro _
  apply HeapWP.Triple.bind (HeapWP.frame (set_next.spec repr hsize left node (.mk previous right lv)))
  intro _
  exact frameLeft (frameLeft (set_prev.spec repr hsize right node (.mk left following rv)))

theorem insert_after.empty_spec (root node : Ptr) (sv nv : U32) :
    HeapWP.Triple
      (sep (nodeAt repr root root root sv) (nodeAt repr node node node nv))
      (insert_after repr root node)
      (fun _ => sep (nodeAt repr root node node sv) (nodeAt repr node root root nv)) := by
  /- The successor aliases root. set_prev must reread the updated root rather
  than overwrite its new next pointer with the original snapshot. -/
  unfold insert_after
  apply HeapWP.Triple.bind (framePure (ext.read_node.spec repr hsize root (.mk root root sv)))
  intro before
  apply HeapWP.Triple.pure_pre
  intro he
  subst before
  apply HeapWP.Triple.bind (frameLeftPure (ext.read_node.spec repr hsize node (.mk node node nv)))
  intro inserted
  apply HeapWP.Triple.pure_pre
  intro he
  subst inserted
  apply HeapWP.Triple.bind
    (frameLeft (ext.write_node.spec repr hsize node (.mk node node nv) _))
  intro _
  apply HeapWP.Triple.bind (HeapWP.frame (set_next.spec repr hsize root node (.mk root root sv)))
  intro _
  exact HeapWP.frame (set_prev.spec repr hsize root node (.mk root node sv))

theorem remove.distinct_spec (node previous following outerPrev outerNext : Ptr)
    (nv pv fv : U32) :
    HeapWP.Triple
      (sep (nodeAt repr node previous following nv)
        (sep (nodeAt repr previous outerPrev node pv) (nodeAt repr following node outerNext fv)))
      (remove repr node)
      (fun _ => sep (nodeAt repr node node node nv)
        (sep (nodeAt repr previous outerPrev following pv)
          (nodeAt repr following previous outerNext fv))) := by
  /- Follow the stored links, reconnect the two neighbours using framed setters,
  then initialize the removed node's self-links with its original payload. -/
  unfold remove
  apply HeapWP.Triple.bind (framePure (ext.read_node.spec repr hsize node (.mk previous following nv)))
  intro old
  apply HeapWP.Triple.pure_pre
  intro he
  subst old
  apply HeapWP.Triple.bind
    (frameLeft (HeapWP.frame (set_next.spec repr hsize previous following (.mk outerPrev node pv))))
  intro _
  apply HeapWP.Triple.bind
    (frameLeft (frameLeft (set_prev.spec repr hsize following previous (.mk node outerNext fv))))
  intro _
  exact HeapWP.frame (init.spec repr hsize node (.mk previous following nv) nv)

theorem remove.last_spec (node root : Ptr) (nv sv : U32) :
    HeapWP.Triple
      (sep (nodeAt repr node root root nv) (nodeAt repr root node node sv))
      (remove repr node)
      (fun _ => sep (nodeAt repr node node node nv) (nodeAt repr root root root sv)) := by
  /- Both neighbours are root: sequential setter specs preserve both updates.
  The removed node stays allocated and readable with the same payload. -/
  unfold remove
  apply HeapWP.Triple.bind (framePure (ext.read_node.spec repr hsize node (.mk root root nv)))
  intro old
  apply HeapWP.Triple.pure_pre
  intro he
  subst old
  apply HeapWP.Triple.bind (frameLeft (set_next.spec repr hsize root root (.mk node node sv)))
  intro _
  apply HeapWP.Triple.bind (frameLeft (set_prev.spec repr hsize root root (.mk node root sv)))
  intro _
  exact HeapWP.frame (init.spec repr hsize node (.mk root root nv) nv)

theorem remove.detached_spec (node : Ptr) (value : U32) :
    HeapWP.Triple (nodeAt repr node node node value) (remove repr node)
      (fun _ => nodeAt repr node node node value) := by
  /- All three pointers alias; each setter and init preserves the same node. -/
  unfold remove
  apply HeapWP.Triple.bind (ext.read_node.spec repr hsize node (.mk node node value))
  intro old
  apply HeapWP.Triple.pure_pre
  intro he
  subst old
  apply HeapWP.Triple.bind (set_next.spec repr hsize node node (.mk node node value))
  intro _
  apply HeapWP.Triple.bind (set_prev.spec repr hsize node node (.mk node node value))
  intro _
  exact init.spec repr hsize node (.mk node node value) value

/-- info: 'doubly_linked.insert_after.distinct_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms insert_after.distinct_spec

/-- info: 'doubly_linked.insert_after.empty_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms insert_after.empty_spec

/-- info: 'doubly_linked.remove.distinct_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms remove.distinct_spec

/-- info: 'doubly_linked.remove.last_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms remove.last_spec

/-- info: 'doubly_linked.remove.detached_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms remove.detached_spec

end doubly_linked
