module

public import DoublyLinked.Ownership
import all Aeneas.Std.Heap.Resources
import all Aeneas.Std.Scalar.CheckedOps.Add
import all Aeneas.Std.Core.CoreOption

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic

namespace doubly_linked

theorem checked_increment (x : Usize)
    (hb : x.val + 1 < 2 ^ UScalarTy.numBits .Usize) :
    ∃ y, Usize.checked_add x 1#usize = some y ∧ y.val = x.val + 1 := by
  have h := Usize.checked_add_bv_spec x 1#usize
  cases he : Usize.checked_add x 1#usize
  · simp only [he] at h
    scalar_tac
  · rename_i y
    simp only [he] at h
    exact ⟨y, rfl, by simpa using h.2.1⟩

theorem expect_some (value : Usize) (msg : Str) :
    core.option.Option.expect (some value) msg = Result.ok value := rfl

theorem lift_ok (value : α) : lift value = Result.ok value := rfl

variable (repr : Aeneas.Std.Repr Node) (layout : NodeLayout repr) (hsize : 0 < repr.size)
include layout hsize

/-- Construction creates an empty owned list, preserving the external frame. -/
theorem LinkedList.new.spec (s : Heap) (F : Fragment) (hi : s.Inv)
    (hm : Fragment.Matches s F)
    (feasible : ∃ p s', State.newBlock repr [ext.blankNode 0#u32] true s p s') :
    HeapWP.Spec (LinkedList.new repr) (fun self s' => ListState repr self [] F s') s := by
  /- intoRaw.spec allocates a blank sentinel with its cleanup token.
  Frame that token around init.spec, then use listState_intro. -/
  unfold LinkedList.new
  apply HeapWP.Spec.bind (HeapWP.intoRaw_return.spec repr (ext.blankNode 0#u32) s F hi hm feasible)
  rintro root s' ⟨authority, _, h, hd, hm', hi', hp⟩
  have hinit := HeapWP.RootTriple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ hp => hp)
    (init.spec (roots := [root.provenance]) repr layout hsize root (ext.blankNode 0#u32) 0#u32
      (alloc repr root root.address 1 true))
  apply HeapWP.Spec.bind (hinit h F s' hp hd hm' hi' (by simpa using authority))
  rintro _ s'' ⟨authority', h', hd', hm'', hi'', hp'⟩
  have ho : owned repr ⟨root, 0#usize⟩ [] h' := by
    refine ⟨rfl, ?_⟩
    simpa only [ring, firstPtr, lastPtr, chain, cleanup, sepEmpRight] using hp'
  exact HeapWP.Spec.pure _ _ _ |>.mpr
    (listState_intro repr hsize s'' ⟨root, 0#usize⟩ [] h' F hd' hm'' hi'' ho authority')

/-- Push implements plain-list cons, subject to placement feasibility and the length bound. -/
theorem LinkedList.push_front.spec (self : LinkedList) (values : List U32) (value : U32)
    (F : Fragment) (s : Heap) (hs : ListState repr self values F s)
    (feasible : ∃ p s', State.newBlock repr [ext.blankNode value] true s p s')
    (hlen : values.length + 1 < 2 ^ UScalarTy.numBits .Usize) :
    HeapWP.Spec (LinkedList.push_front repr self value)
      (fun self' s' => ListState repr self' (value :: values) F s') s := by
  /- The length bound makes checked_add/expect succeed. Allocate using
  intoRaw.spec with the existing list and F as frame. insert_owned restores
  the invariant for cons; listState_intro gives the concrete toList equality. -/
  obtain ⟨h, hd, hm, hi, ⟨entries, rfl, hp, authority⟩, _⟩ := hs
  have hb : self.len.val + 1 < 2 ^ UScalarTy.numBits .Usize := by
    simpa only [hp.1, List.length_map] using hlen
  obtain ⟨len, hadd, hv⟩ := checked_increment self.len hb
  have hlen' : len.val = entries.length + 1 := by rw [hv, hp.1]
  unfold LinkedList.push_front
  rw [hadd]
  simp only [lift_ok, bind_ok, expect_some]
  apply HeapWP.Spec.bind
    (HeapWP.intoRaw_preserving.spec repr (ext.blankNode value) s (h ∪ F) hi hm feasible)
  rintro p s' ⟨preserve, fresh, _, a, had, ham, hai, hap⟩
  have authority' : ∀ root ∈ p.provenance :: rootIds self entries, RootReturn s' root := by
    intro root member
    rcases List.mem_cons.mp member with same | member
    · exact same ▸ fresh
    · obtain ⟨blk, old, active⟩ := owned_active repr self entries hp
        ((Fragment.matches_union _ _ _).mp hm).1 member
      exact preserve root blk old active (authority root member)
  obtain ⟨hah, haF⟩ := Fragment.disjoint_union_right.mp had
  have hd' : (a ∪ h).Disjoint F := Fragment.disjoint_union_left.mpr ⟨haF, hd⟩
  have hm' : Fragment.Matches s' ((a ∪ h) ∪ F) := by
    simpa only [Fragment.union_assoc] using ham
  have hpre : sep (sep (alloc repr p p.address 1 true) (pointsTo repr p p.address (ext.blankNode value)))
      (fun h => sep (ring repr self.root 0#u32 entries)
        (sep (alloc repr self.root self.root.address 1 true) (cleanup repr entries)) h) (a ∪ h) :=
    ⟨a, h, hah, rfl, hap, hp.2⟩
  apply HeapWP.Spec.mono
    (insert_owned repr layout hsize self entries p value len hlen'
      (a ∪ h) F s' hpre hd' hm' hai authority')
  rintro self' s'' ⟨authority'', h', hd'', hm'', hi'', root', hp'⟩
  apply listState_intro repr hsize s'' self' ((p, value) :: entries) h' F hd'' hm'' hi'' hp'
  intro root member
  apply authority'' root
  simp only [rootIds, root', List.map_cons, List.mem_cons] at member ⊢
  tauto

/-- Pop implements plain-list head/tail, including the empty case, and frees the removed node. -/
theorem LinkedList.pop_front.spec (self : LinkedList) (values : List U32)
    (F : Fragment) (s : Heap) (hs : ListState repr self values F s) :
    HeapWP.Spec (LinkedList.pop_front repr self)
      (fun (result, self') s' =>
        result = values.head? ∧ ListState repr self' values.tail F s') s := by
  /- Unpack the hidden entries, apply pop_front_owned, map tail/head, and
  reconstruct ListState with listState_intro and its deterministic equality. -/
  obtain ⟨h, hd, hm, hi, ⟨entries, rfl, hp, authority⟩, _⟩ := hs
  apply HeapWP.Spec.mono (LinkedList.pop_front_owned repr layout hsize self entries
    (fun _ member => rootIds_member self member) h F s hp hd hm hi authority)
  rintro ⟨result, self'⟩ s' ⟨authority', h', hd', hm', hi', hr, root', hp'⟩
  refine ⟨hr, ?_⟩
  simpa using listState_intro repr hsize s' self' entries.tail h' F hd' hm' hi' hp'
    (fun root member => authority' root (rootIds_tail root' member))

omit layout in
theorem LinkedList.front.spec (self : LinkedList) (values : List U32)
    (F : Fragment) (s : Heap) (hs : ListState repr self values F s) :
    HeapWP.Spec (LinkedList.front repr self)
      (fun result s' => result = values.head? ∧ ListState repr self values F s') s := by
  /- Apply front_owned and reconstruct the unchanged ListState. -/
  obtain ⟨h, hd, hm, hi, ⟨entries, rfl, hp, authority⟩, _⟩ := hs
  apply HeapWP.Spec.mono (LinkedList.front_owned repr hsize self entries h F s hp hd hm hi authority)
  rintro result s' ⟨authority', h', hd', hm', hi', hr, hp'⟩
  exact ⟨hr, listState_intro repr hsize s' self entries h' F hd' hm' hi' hp' authority'⟩

omit layout in
theorem LinkedList.back.spec (self : LinkedList) (values : List U32)
    (F : Fragment) (s : Heap) (hs : ListState repr self values F s) :
    HeapWP.Spec (LinkedList.back repr self)
      (fun result s' => result = values.getLast? ∧ ListState repr self values F s') s := by
  /- Apply back_owned and reconstruct the unchanged ListState. -/
  obtain ⟨h, hd, hm, hi, ⟨entries, rfl, hp, authority⟩, _⟩ := hs
  apply HeapWP.Spec.mono (LinkedList.back_owned repr hsize self entries h F s hp hd hm hi authority)
  rintro result s' ⟨authority', h', hd', hm', hi', hr, hp'⟩
  exact ⟨hr, listState_intro repr hsize s' self entries h' F hd' hm' hi' hp' authority'⟩

omit layout hsize in
theorem LinkedList.len.spec (self : LinkedList) (values : List U32)
    (F : Fragment) (s : Heap) (hs : ListState repr self values F s) :
    HeapWP.Spec (LinkedList.impl.len self)
      (fun result s' => result.val = values.length ∧ ListState repr self values F s') s := by
  /- The stored length agrees with hidden entries.length; map preserves length. -/
  have hlen : self.len.val = values.length := by
    obtain ⟨_, _, _, _, ⟨entries, rfl, hp, _⟩, _⟩ := hs
    simpa only [List.length_map] using hp.1
  exact HeapWP.Spec.pure _ _ _ |>.mpr ⟨hlen, hs⟩

omit layout hsize in
theorem LinkedList.is_empty.spec (self : LinkedList) (values : List U32)
    (F : Fragment) (s : Heap) (hs : ListState repr self values F s) :
    HeapWP.Spec (LinkedList.is_empty self)
      (fun result s' => result = values.isEmpty ∧ ListState repr self values F s') s := by
  /- Exact length makes the stored zero test equivalent to plain-list emptiness. -/
  have hlen : self.len.val = values.length := by
    obtain ⟨_, _, _, _, ⟨entries, rfl, hp, _⟩, _⟩ := hs
    simpa only [List.length_map] using hp.1
  apply HeapWP.Spec.pure _ _ _ |>.mpr
  refine ⟨?_, hs⟩
  cases values
  · have hz : self.len = 0#usize := by scalar_tac
    simp [hz]
  · have hz : self.len ≠ 0#usize := by intro he; simp [he] at hlen
    simp [hz]

/-- Clearing retains the empty sentinel and releases all payload nodes. -/
theorem LinkedList.clear.spec (self : LinkedList) (values : List U32)
    (F : Fragment) (s : Heap) (hs : ListState repr self values F s) :
    HeapWP.Spec (LinkedList.clear repr self)
      (fun self' s' => ListState repr self' [] F s') s := by
  /- Apply clear_owned and reconstruct ListState for the empty sequence. -/
  obtain ⟨h, hd, hm, hi, ⟨entries, _, hp, authority⟩, _⟩ := hs
  apply HeapWP.Spec.mono (LinkedList.clear_owned repr layout hsize self entries
    (fun _ member => rootIds_member self member) h F s hp hd hm hi authority)
  rintro self' s' ⟨authority', h', hd', hm', hi', root', hp'⟩
  apply listState_intro repr hsize s' self' [] h' F hd' hm' hi' hp'
  intro root member
  apply authority' root
  apply List.mem_cons.mpr
  left
  simpa only [rootIds, root', List.map_nil, List.mem_cons, List.not_mem_nil, or_false] using member

/-- Destruction consumes the list's entire ownership, preserving unrelated resources. -/
theorem LinkedList.drop.spec (self : LinkedList) (values : List U32)
    (F : Fragment) (s : Heap) (hs : ListState repr self values F s) :
    HeapWP.Spec (LinkedList.Insts.CoreOpsDropDrop.drop repr self)
      (fun _ s' => Fragment.Matches s' F ∧ s'.Inv) s := by
  /- Apply drop_owned; its empty footprint makes the remaining matched
  fragment exactly F. The heap invariant is retained by the framed triple. -/
  obtain ⟨h, hd, hm, hi, ⟨entries, _, hp, authority⟩, _⟩ := hs
  apply HeapWP.Spec.mono (LinkedList.drop_owned repr layout hsize self entries
    (fun _ member => rootIds_member self member) (by simp [rootIds])
    h F s hp hd hm hi authority)
  rintro _ s' ⟨_, h', _, hm', hi', he⟩
  change h' = ∅ at he
  rw [he, Fragment.empty_union] at hm'
  exact ⟨hm', hi'⟩

/-- info: 'doubly_linked.LinkedList.new.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LinkedList.new.spec

/-- info: 'doubly_linked.LinkedList.push_front.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LinkedList.push_front.spec

/-- info: 'doubly_linked.LinkedList.pop_front.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LinkedList.pop_front.spec

/-- info: 'doubly_linked.LinkedList.front.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LinkedList.front.spec

/-- info: 'doubly_linked.LinkedList.back.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LinkedList.back.spec

/-- info: 'doubly_linked.LinkedList.len.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LinkedList.len.spec

/-- info: 'doubly_linked.LinkedList.is_empty.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LinkedList.is_empty.spec

/-- info: 'doubly_linked.LinkedList.clear.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LinkedList.clear.spec

/-- info: 'doubly_linked.LinkedList.drop.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LinkedList.drop.spec

/-- info: 'doubly_linked.owned_toList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms owned_toList

end doubly_linked
