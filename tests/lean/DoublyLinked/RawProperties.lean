module

public import DoublyLinked.Raw
import all DoublyLinked.Raw
public import Aeneas.Std.Heap.EffectSpecs
import all Aeneas.Std.Heap.Separation

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic

namespace doubly_linked

variable {roots : List Nat}

abbrev Ptr := MutRawPtr Node

/-- Calibration of the two stored pointer fields, independently of their
physical offsets or the padding chosen by a concrete Rust layout. -/
structure NodeLayout (repr : Aeneas.Std.Repr Node) : Prop where
  carries : ∀ node q, repr.Carries node q →
    q.provenance = node.prev.provenance ∨ q.provenance = node.next.provenance
  links : ∀ node bytes, repr.encode node bytes →
    (∃ i : Fin repr.size, ∃ lane, bytes[i.val] = .pointer (node.prev.cast Unit) lane) ∧
    (∃ i : Fin repr.size, ∃ lane, bytes[i.val] = .pointer (node.next.cast Unit) lane)

def nodeAt (repr : Aeneas.Std.Repr Node)
    (p prev next : Ptr) (value : U32) : Assertion :=
  pointsTo repr p p.address (.mk prev next value)

def Knows (P : Assertion) (q : Ptr) : Prop :=
  ∀ h, P h → HasProvenance h q.provenance

theorem Knows.left {P R : Assertion} {q : Ptr} (known : Knows P q) : Knows (sep P R) q := by
  rintro h ⟨a, b, _, rfl, hp, _⟩
  exact (known a hp).mono (fun _ hr => .inl hr)

theorem Knows.right {P R : Assertion} {q : Ptr} (known : Knows R q) : Knows (sep P R) q := by
  rintro h ⟨a, b, _, rfl, _, hr⟩
  exact (known b hr).mono (fun _ member => .inr member)

theorem nodeAt_knows (repr : Aeneas.Std.Repr Node) (layout : NodeLayout repr)
     (p prev next : Ptr) (value : U32) (hsize : 0 < repr.size) :
    Knows (nodeAt repr p prev next value) p ∧
      Knows (nodeAt repr p prev next value) prev ∧
      Knows (nodeAt repr p prev next value) next := by
  have known (h : Fragment) (hp : nodeAt repr p prev next value h) :
      HasProvenance h p.provenance ∧ HasProvenance h prev.provenance ∧
        HasProvenance h next.provenance := by
    obtain ⟨data, encoded, _, _, cells⟩ := hp
    have member (i : Fin repr.size) :
        h (.cell p.provenance (p.offsetFrom p.address + i.val) p.address
          (.shared 0 data[i.val])) := by
      rw [cells]
      exact ⟨i.val, by simp, by simp⟩
    obtain ⟨⟨i, lane, previous⟩, ⟨j, otherLane, following⟩⟩ :=
      layout.links (.mk prev next value) data encoded
    refine ⟨.inl ⟨_, member ⟨0, hsize⟩, rfl⟩, ?_, ?_⟩
    · exact .inr ⟨p.provenance, _, p.address, 0, prev.cast Unit, lane,
        previous ▸ member i, rfl⟩
    · exact .inr ⟨p.provenance, _, p.address, 0, next.cast Unit, otherLane,
        following ▸ member j, rfl⟩
  exact ⟨fun h hp => (known h hp).1, fun h hp => (known h hp).2.1,
    fun h hp => (known h hp).2.2⟩

@[simp] theorem Node.mk_eta (node : Node) : Node.mk node.prev node.next node.value = node := by
  cases node
  rfl

@[step] theorem Node.Insts.CoreCloneClone.clone.spec (node : Node) :
    Node.Insts.CoreCloneClone.clone node ⦃ (result : Node) => result = node ⦄ := by
  simp [Node.Insts.CoreCloneClone.clone]

theorem framePure {P R : Assertion} {c : Result α} {A : α → Prop} {Q : α → Assertion}
    (ht : HeapWP.RootTriple roots P c (fun x h => A x ∧ Q x h)) :
    HeapWP.RootTriple roots (sep P R) c (fun x h => A x ∧ sep (Q x) R h) :=
  HeapWP.RootTriple.conseq (fun _ hp => hp)
    (fun _ h hp => (sep_and_left _ _ _ h).mp hp) (HeapWP.RootTriple.frame ht)

theorem frameLeftPure {P R : Assertion} {c : Result α} {A : α → Prop} {Q : α → Assertion}
    (ht : HeapWP.RootTriple roots P c (fun x h => A x ∧ Q x h)) :
    HeapWP.RootTriple roots (sep R P) c (fun x h => A x ∧ sep R (Q x) h) :=
  HeapWP.RootTriple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ h hp => ⟨hp.1, (sep_comm _ _ h).mp hp.2⟩) (framePure ht)

theorem frameLeft {P R : Assertion} {c : Result α} {Q : α → Assertion}
    (ht : HeapWP.RootTriple roots P c Q) :
    HeapWP.RootTriple roots (sep R P) c (fun x => sep R (Q x)) :=
  HeapWP.RootTriple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ h hp => (sep_comm _ _ h).mp hp) (HeapWP.RootTriple.frame ht)

theorem sep_middle (P Q R : Assertion) (h : Fragment) :
    sep P (sep Q R) h ↔ sep Q (sep P R) h := by
  rw [← sep_assoc P Q R h, ← sep_assoc Q P R h]
  exact ⟨sep_mono (fun h hp => (sep_comm P Q h).mp hp) (fun _ hp => hp),
    sep_mono (fun h hp => (sep_comm Q P h).mp hp) (fun _ hp => hp)⟩

theorem focusMiddle {P Q Q' R : Assertion} {c : Result α}
    (ht : HeapWP.RootTriple roots (sep Q (sep P R)) c (fun _ => sep Q' (sep P R))) :
    HeapWP.RootTriple roots (sep P (sep Q R)) c (fun _ => sep P (sep Q' R)) :=
  HeapWP.RootTriple.conseq (fun h hp => (sep_middle _ _ _ h).mp hp)
    (fun _ h hp => (sep_middle _ _ _ h).mp hp) ht

theorem focusLast {P Q R R' : Assertion} {c : Result α}
    (ht : HeapWP.RootTriple roots (sep R (sep P Q)) c (fun _ => sep R' (sep P Q))) :
    HeapWP.RootTriple roots (sep P (sep Q R)) c (fun _ => sep P (sep Q R')) :=
  HeapWP.RootTriple.conseq
    (fun h hp => (sep_comm _ _ h).mp ((sep_assoc _ _ _ h).mpr hp))
    (fun _ h hp => (sep_assoc _ _ _ h).mp ((sep_comm _ _ h).mp hp)) ht

variable (repr : Aeneas.Std.Repr Node) (layout : NodeLayout repr)
    (hsize : 0 < repr.size)
include hsize

theorem ext.read_node.spec (p : Ptr) (old : Node) :
    HeapWP.RootTriple roots (pointsTo repr p p.address old) (ext.read_node repr p)
      (fun result h => result = old ∧ pointsTo repr p p.address old 0 h) :=
  HeapWP.RootTriple.read repr p p.address old 0 hsize

include layout

theorem ext.write_node.spec (p : Ptr) (old value : Node) (R : Assertion)
    (previous : Knows (sep (pointsTo repr p p.address old) R) value.prev)
    (following : Knows (sep (pointsTo repr p p.address old) R) value.next) :
    HeapWP.RootTriple roots (sep (pointsTo repr p p.address old) R) (ext.write_node repr p value)
      (fun _ => sep (pointsTo repr p p.address value) R) := by
  apply HeapWP.RootTriple.write_local repr p p.address old value R ?_ hsize
  intro h hp q carried
  rcases layout.carries value q carried with same | same
  · exact same.symm ▸ previous h hp
  · exact same.symm ▸ following h hp

theorem init.spec (node : Ptr) (old : Node) (value : U32) (R : Assertion) :
    HeapWP.RootTriple roots (sep (pointsTo repr node node.address old) R) (init repr node value)
      (fun _ => sep (nodeAt repr node node node value) R) := by
  have known := (nodeAt_knows repr layout node old.prev old.next old.value hsize).1.left
    (R := R)
  simpa only [nodeAt, Node.mk_eta, init] using
    ext.write_node.spec (roots := roots) repr layout hsize node old (.mk node node value) R known known

theorem set_next.spec (node next : Ptr) (old : Node) (R : Assertion)
    (newLink : Knows (sep (pointsTo repr node node.address old) R) next) :
    HeapWP.RootTriple roots (sep (pointsTo repr node node.address old) R) (set_next repr node next)
      (fun _ => sep (nodeAt repr node old.prev next old.value) R) := by
  unfold set_next
  apply HeapWP.RootTriple.bind (framePure (ext.read_node.spec repr hsize node old))
  intro observed
  apply HeapWP.RootTriple.pure_pre
  intro equal
  subst observed
  apply ext.write_node.spec (roots := roots) repr layout hsize node old (.mk old.prev next old.value) R ?_ newLink
  simpa only [nodeAt, Node.mk_eta, Node.prev._simpLemma_] using
    (nodeAt_knows repr layout node old.prev old.next old.value hsize).2.1.left (R := R)

theorem set_prev.spec (node prev : Ptr) (old : Node) (R : Assertion)
    (newLink : Knows (sep (pointsTo repr node node.address old) R) prev) :
    HeapWP.RootTriple roots (sep (pointsTo repr node node.address old) R) (set_prev repr node prev)
      (fun _ => sep (nodeAt repr node prev old.next old.value) R) := by
  unfold set_prev
  apply HeapWP.RootTriple.bind (framePure (ext.read_node.spec repr hsize node old))
  intro observed
  apply HeapWP.RootTriple.pure_pre
  intro equal
  subst observed
  apply ext.write_node.spec (roots := roots) repr layout hsize node old (.mk prev old.next old.value) R newLink ?_
  simpa only [nodeAt, Node.mk_eta, Node.next._simpLemma_] using
    (nodeAt_knows repr layout node old.prev old.next old.value hsize).2.2.left (R := R)

theorem insert_after.distinct_spec (left node right previous following : Ptr) (lv nv rv : U32) :
    HeapWP.RootTriple roots
      (sep (nodeAt repr left previous right lv)
        (sep (nodeAt repr node node node nv) (nodeAt repr right left following rv)))
      (insert_after repr left node)
      (fun _ => sep (nodeAt repr left previous node lv)
        (sep (nodeAt repr node left right nv) (nodeAt repr right node following rv))) := by
  unfold insert_after
  apply HeapWP.RootTriple.bind (framePure (ext.read_node.spec repr hsize left (.mk previous right lv)))
  intro before
  apply HeapWP.RootTriple.pure_pre
  intro equal
  subst before
  apply HeapWP.RootTriple.bind
    (frameLeftPure (framePure (ext.read_node.spec repr hsize node (.mk node node nv))))
  intro inserted
  apply HeapWP.RootTriple.pure_pre
  intro equal
  subst inserted
  apply HeapWP.RootTriple.bind (focusMiddle
    (ext.write_node.spec (roots := roots) repr layout hsize node (.mk node node nv) (.mk left right nv) _
      (nodeAt_knows repr layout left previous right lv hsize |>.1.left.right)
      (nodeAt_knows repr layout right left following rv hsize |>.1.right.right)))
  intro _
  apply HeapWP.RootTriple.bind
    (set_next.spec (roots := roots) repr layout hsize left node (.mk previous right lv) _
      (nodeAt_knows repr layout node left right nv hsize |>.1.left.right))
  intro _
  exact focusLast (set_prev.spec (roots := roots) repr layout hsize right node (.mk left following rv) _
    (nodeAt_knows repr layout node left right nv hsize |>.1.right.right))

theorem insert_after.empty_spec (root node : Ptr) (sv nv : U32) :
    HeapWP.RootTriple roots
      (sep (nodeAt repr root root root sv) (nodeAt repr node node node nv))
      (insert_after repr root node)
      (fun _ => sep (nodeAt repr root node node sv) (nodeAt repr node root root nv)) := by
  unfold insert_after
  apply HeapWP.RootTriple.bind (framePure (ext.read_node.spec repr hsize root (.mk root root sv)))
  intro before
  apply HeapWP.RootTriple.pure_pre
  intro equal
  subst before
  apply HeapWP.RootTriple.bind (frameLeftPure (ext.read_node.spec repr hsize node (.mk node node nv)))
  intro inserted
  apply HeapWP.RootTriple.pure_pre
  intro equal
  subst inserted
  have write := ext.write_node.spec (roots := roots) repr layout hsize node (.mk node node nv) (.mk root root nv)
    (nodeAt repr root root root sv)
    (nodeAt_knows repr layout root root root sv hsize |>.1.right)
    (nodeAt_knows repr layout root root root sv hsize |>.1.right)
  apply HeapWP.RootTriple.bind (HeapWP.RootTriple.conseq
    (fun h hp => (sep_comm _ _ h).mp hp) (fun _ h hp => (sep_comm _ _ h).mp hp) write)
  intro _
  apply HeapWP.RootTriple.bind
    (set_next.spec (roots := roots) repr layout hsize root node (.mk root root sv) _
      (nodeAt_knows repr layout node root root nv hsize |>.1.right))
  intro _
  exact set_prev.spec (roots := roots) repr layout hsize root node (.mk root node sv) _
    (nodeAt_knows repr layout node root root nv hsize |>.1.right)

theorem remove.distinct_spec (node previous following outerPrev outerNext : Ptr) (nv pv fv : U32) :
    HeapWP.RootTriple roots
      (sep (nodeAt repr node previous following nv)
        (sep (nodeAt repr previous outerPrev node pv) (nodeAt repr following node outerNext fv)))
      (remove repr node)
      (fun _ => sep (nodeAt repr node node node nv)
        (sep (nodeAt repr previous outerPrev following pv)
          (nodeAt repr following previous outerNext fv))) := by
  unfold remove
  apply HeapWP.RootTriple.bind (framePure (ext.read_node.spec repr hsize node (.mk previous following nv)))
  intro old
  apply HeapWP.RootTriple.pure_pre
  intro equal
  subst old
  apply HeapWP.RootTriple.bind (focusMiddle
    (set_next.spec (roots := roots) repr layout hsize previous following (.mk outerPrev node pv) _
      (nodeAt_knows repr layout following node outerNext fv hsize |>.1.right.right)))
  intro _
  apply HeapWP.RootTriple.bind (focusLast
    (set_prev.spec (roots := roots) repr layout hsize following previous (.mk node outerNext fv) _
      (nodeAt_knows repr layout previous outerPrev following pv hsize |>.1.right.right)))
  intro _
  exact init.spec (roots := roots) repr layout hsize node (.mk previous following nv) nv _

theorem remove.last_spec (node root : Ptr) (nv sv : U32) :
    HeapWP.RootTriple roots
      (sep (nodeAt repr node root root nv) (nodeAt repr root node node sv))
      (remove repr node)
      (fun _ => sep (nodeAt repr node node node nv) (nodeAt repr root root root sv)) := by
  unfold remove
  apply HeapWP.RootTriple.bind (framePure (ext.read_node.spec repr hsize node (.mk root root nv)))
  intro old
  apply HeapWP.RootTriple.pure_pre
  intro equal
  subst old
  have next := set_next.spec (roots := roots) repr layout hsize root root (.mk node node sv)
    (nodeAt repr node root root nv)
    (nodeAt_knows repr layout root node node sv hsize |>.1.left)
  apply HeapWP.RootTriple.bind (HeapWP.RootTriple.conseq
    (fun h hp => (sep_comm _ _ h).mp hp) (fun _ h hp => (sep_comm _ _ h).mp hp) next)
  intro _
  have prev := set_prev.spec (roots := roots) repr layout hsize root root (.mk node root sv)
    (nodeAt repr node root root nv)
    (nodeAt_knows repr layout root node root sv hsize |>.1.left)
  apply HeapWP.RootTriple.bind (HeapWP.RootTriple.conseq
    (fun h hp => (sep_comm _ _ h).mp hp) (fun _ h hp => (sep_comm _ _ h).mp hp) prev)
  intro _
  exact init.spec (roots := roots) repr layout hsize node (.mk root root nv) nv _

theorem remove.detached_spec (node : Ptr) (value : U32) :
    HeapWP.RootTriple roots (nodeAt repr node node node value) (remove repr node)
      (fun _ => nodeAt repr node node node value) := by
  apply HeapWP.RootTriple.conseq (fun h hp => (sep_empty_right _ h).mpr hp)
    (fun _ h hp => (sep_empty_right _ h).mp hp)
  unfold remove
  apply HeapWP.RootTriple.bind (framePure (ext.read_node.spec repr hsize node (.mk node node value)))
  intro old
  apply HeapWP.RootTriple.pure_pre
  intro equal
  subst old
  have known := nodeAt_knows repr layout node node node value hsize |>.1.left (R := empty)
  apply HeapWP.RootTriple.bind (set_next.spec (roots := roots) repr layout hsize node node (.mk node node value) empty known)
  intro _
  apply HeapWP.RootTriple.bind (set_prev.spec (roots := roots) repr layout hsize node node (.mk node node value) empty known)
  intro _
  exact init.spec (roots := roots) repr layout hsize node (.mk node node value) value empty

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
