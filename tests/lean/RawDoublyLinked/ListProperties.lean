module

public import RawDoublyLinked.Properties
import all Aeneas.Std.Heap.Separation

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic

namespace raw_doubly_linked

abbrev Entries := List (Ptr × U32)

def firstPtr (fallback : Ptr) : Entries → Ptr
  | [] => fallback
  | (p, _) :: _ => p

def lastPtr (fallback : Ptr) : Entries → Ptr
  | [] => fallback
  | [(p, _)] => p
  | _ :: next :: rest => lastPtr fallback (next :: rest)

/-- Every payload and both links, with exclusive ownership of each node. -/
def chain (repr : Aeneas.Std.Repr Node) (previous root : Ptr) : Entries → Assertion
  | [] => emp
  | (node, value) :: rest =>
    sep (nodeAt repr node previous (firstPtr root rest) value) (chain repr node root rest)

/-- The sentinel closes both ends of a finite sequence of payload-bearing nodes. -/
def ring (repr : Aeneas.Std.Repr Node) (root : Ptr) (sentinelValue : U32) (entries : Entries) : Assertion :=
  sep (nodeAt repr root (lastPtr root entries) (firstPtr root entries) sentinelValue)
    (chain repr root root entries)

theorem sepAssoc (P Q R : Assertion) : sep (sep P Q) R = sep P (sep Q R) := by
  funext h
  apply propext
  constructor
  · rintro ⟨_, c, hd, rfl, ⟨a, b, hab, rfl, hp, hq⟩, hr⟩
    obtain ⟨hac, hbc⟩ := Fragment.disjoint_union_left.mp hd
    exact ⟨a, b ∪ c, Fragment.disjoint_union_right.mpr ⟨hab, hac⟩,
      Fragment.union_assoc _ _ _, hp, b, c, hbc, rfl, hq, hr⟩
  · rintro ⟨a, _, hd, rfl, hp, ⟨b, c, hbc, rfl, hq, hr⟩⟩
    obtain ⟨hab, hac⟩ := Fragment.disjoint_union_right.mp hd
    exact ⟨a ∪ b, c, Fragment.disjoint_union_left.mpr ⟨hac, hbc⟩,
      (Fragment.union_assoc _ _ _).symm, ⟨a, b, hab, rfl, hp, hq⟩, hr⟩

theorem sepSwap (P Q R : Assertion) (h : Fragment) :
    sep P (sep Q R) h ↔ sep Q (sep P R) h := by
  rw [← sepAssoc P Q R, ← sepAssoc Q P R]
  exact ⟨sep_mono (fun h hp => (sep_comm P Q h).mp hp) (fun _ hp => hp),
    sep_mono (fun h hp => (sep_comm Q P h).mp hp) (fun _ hp => hp)⟩

theorem sepEmpRight (P : Assertion) : sep P emp = P := by
  funext h
  exact propext ((sep_comm P emp h).trans (sep_emp_left P h))

variable (repr : Aeneas.Std.Repr Node) (hsize : 0 < repr.size)
include hsize

/-- Insertion at the sentinel implements list cons, preserving all old payloads. -/
theorem insert_after.spec (root node : Ptr) (sv value : U32) (entries : Entries) :
    HeapWP.Triple
      (sep (nodeAt repr node node node value) (ring repr root sv entries))
      (insert_after repr root node)
      (fun _ => ring repr root sv ((node, value) :: entries)) := by
  /- Split entries into empty/nonempty. Use empty_spec when the two neighbours
  alias the sentinel; otherwise expose the first chain node, apply distinct_spec,
  and frame the unchanged tail. Reassociate separation to rebuild the new ring. -/
  cases entries
  · apply HeapWP.Triple.conseq ?_ ?_ (insert_after.empty_spec repr hsize root node sv value)
    · intro h hp
      simpa only [ring, chain, lastPtr, firstPtr, sepEmpRight] using (sep_comm _ _ h).mp hp
    · intro _ h hp
      simpa only [ring, chain, lastPtr, firstPtr, sepEmpRight] using hp
  · rename_i entry rest
    rcases entry with ⟨first, fv⟩
    apply HeapWP.Triple.conseq ?_ ?_
      (HeapWP.frame (R := chain repr first root rest)
        (insert_after.distinct_spec repr hsize root node first
          (lastPtr root ((first, fv) :: rest)) (firstPtr root rest) sv value fv))
    · intro h hp
      change sep (nodeAt repr node node node value)
        (sep (nodeAt repr root (lastPtr root ((first, fv) :: rest)) first sv)
          (sep (nodeAt repr first root (firstPtr root rest) fv) (chain repr first root rest))) h at hp
      simpa only [sepAssoc] using (sepSwap _ _ _ h).mp hp
    · intro _ h hp
      simpa only [ring, chain, lastPtr, firstPtr, sepAssoc] using hp

theorem remove_front.spec (root node : Ptr) (sv value : U32) (rest : Entries) :
    HeapWP.Triple (ring repr root sv ((node, value) :: rest)) (remove repr node)
      (fun _ => sep (nodeAt repr node node node value) (ring repr root sv rest)) := by
  /- Expose the first node and its neighbours, frame the untouched suffix, and
  rebuild the shortened ring. Empty rest is the aliased-neighbour case. -/
  cases rest
  · apply HeapWP.Triple.conseq ?_ ?_ (remove.last_spec repr hsize node root value sv)
    · intro h hp
      have hp' : sep (nodeAt repr root node node sv) (nodeAt repr node root root value) h := by
        simpa only [ring, chain, lastPtr, firstPtr, sepEmpRight] using hp
      exact (sep_comm _ _ h).mp hp'
    · intro _ h hp
      simpa only [ring, chain, lastPtr, firstPtr, sepEmpRight] using hp
  · rename_i entry tail
    rcases entry with ⟨next, nv⟩
    apply HeapWP.Triple.conseq ?_ ?_
      (HeapWP.frame (R := chain repr next root tail)
        (remove.distinct_spec repr hsize node root next
          (lastPtr root ((next, nv) :: tail)) (firstPtr root tail) value sv nv))
    · intro h hp
      change sep (nodeAt repr root (lastPtr root ((next, nv) :: tail)) node sv)
        (sep (nodeAt repr node root next value)
          (sep (nodeAt repr next node (firstPtr root tail) nv) (chain repr next root tail))) h at hp
      simpa only [sepAssoc] using (sepSwap _ _ _ h).mp hp
    · intro _ h hp
      simpa only [ring, chain, lastPtr, firstPtr, sepAssoc] using hp

/-- Removing the first element implements list tail and returns that exact node. -/
theorem remove_after.spec (root node : Ptr) (sv value : U32) (rest : Entries) :
    HeapWP.Triple (ring repr root sv ((node, value) :: rest))
      (remove_after repr root)
      (fun result h => result = node ∧
        sep (nodeAt repr node node node value) (ring repr root sv rest) h) := by
  /- Read the sentinel and use its stored next pointer. For rest empty apply
  remove.last_spec; otherwise expose the successor and apply remove.distinct_spec,
  framing the remaining tail. Restore the exact detached node and residual ring. -/
  unfold remove_after
  apply HeapWP.Triple.bind
    (framePure (ext.read_node.spec repr hsize root
      (.mk (lastPtr root ((node, value) :: rest)) node sv)))
  intro sentinel
  apply HeapWP.Triple.pure_pre
  intro he
  subst sentinel
  apply HeapWP.Triple.bind (remove_front.spec repr hsize root node sv value rest)
  intro _
  exact HeapWP.Triple.pure _ node

/-- info: 'raw_doubly_linked.insert_after.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms insert_after.spec

/-- info: 'raw_doubly_linked.remove_after.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms remove_after.spec

end raw_doubly_linked
