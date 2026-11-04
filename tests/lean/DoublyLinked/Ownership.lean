module

public import DoublyLinked.ListProperties
public import DoublyLinked.Safe
import all Aeneas.Std.Heap.Resources
import all Aeneas.Std.Scalar.CheckedOps.Add
import all Aeneas.Std.Core.CoreOption

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic

namespace doubly_linked

variable {roots : List Nat}

theorem pure_triple (R : Assertion) {c : Result α} {P : α → Prop} (hc : WP.spec c P) :
    HeapWP.RootTriple roots R c (fun value h => P value ∧ R h) := by
  intro h F s hr hd hm hi authority
  apply HeapWP.Spec.mono (HeapWP.Spec.of_spec hc s)
  rintro value _ ⟨hp, rfl⟩
  exact ⟨authority, h, hd, hm, hi, hp, hr⟩

/-- Cleanup authority for every payload node, independently of its current links. -/
def cleanup (repr : Aeneas.Std.Repr Node) : Entries → Assertion
  | [] => empty
  | (p, _) :: rest => sep (alloc repr p p.address 1 true) (cleanup repr rest)

/-- The private length is exact, and the list owns its sentinel and every node. -/
def owned (repr : Aeneas.Std.Repr Node) (self : LinkedList) (entries : Entries) : Assertion :=
  fun h => self.len.val = entries.length ∧
    sep (ring repr self.root 0#u32 entries)
      (sep (alloc repr self.root self.root.address 1 true) (cleanup repr entries)) h

/-- Public abstraction hides node addresses, but specifies the entire payload sequence. -/
def listOwns (repr : Aeneas.Std.Repr Node) (self : LinkedList) (values : List U32) : Assertion :=
  fun h => ∃ entries, entries.map Prod.snd = values ∧ owned repr self entries h

def rootIds (self : LinkedList) (entries : Entries) : List Nat :=
  self.root.provenance :: entries.map (fun entry => entry.1.provenance)

theorem rootIds_member (self : LinkedList) {entries : Entries} {entry : Ptr × U32}
    (member : entry ∈ entries) : entry.1.provenance ∈ rootIds self entries :=
  List.mem_cons.mpr (.inr (List.mem_map.mpr ⟨entry, member, rfl⟩))

theorem rootIds_tail {self self' : LinkedList} {entries : Entries}
    (same : self'.root = self.root) {root : Nat} (member : root ∈ rootIds self' entries.tail) :
    root ∈ rootIds self entries := by
  cases entries
  · simpa only [rootIds, same, List.tail_nil] using member
  · simp only [rootIds, same, List.tail_cons, List.map_cons, List.mem_cons] at member ⊢
    tauto

/-- A deterministic observation of heap contents; invalid/unreadable states return none. -/
def readValues (repr : Aeneas.Std.Repr Node) (s : Heap) (p : Ptr) : Nat → Option (List U32)
  | 0 => some []
  | n + 1 => do
    let node ← Heap.read repr p s
    let rest ← readValues repr s node.next n
    some (node.value :: rest)

def LinkedList.toList (repr : Aeneas.Std.Repr Node) (s : Heap) (self : LinkedList) :
    Option (List U32) := do
  let sentinel ← Heap.read repr self.root s
  readValues repr s sentinel.next self.len.val

/-- The complete public-state assertion, including an arbitrary unchanged external frame. -/
def ListState (repr : Aeneas.Std.Repr Node) (self : LinkedList) (values : List U32)
    (F : Fragment) (s : Heap) : Prop :=
  ∃ h, h.Disjoint F ∧ Fragment.Matches s (h ∪ F) ∧ s.Inv ∧
    (∃ entries, entries.map Prod.snd = values ∧ owned repr self entries h ∧
      ∀ root ∈ rootIds self entries, RootReturn s root) ∧
    self.toList repr s = some values

theorem cleanup_active (repr : Aeneas.Std.Repr Node) (entries : Entries)
    {h : Fragment} {s : Heap} (hp : cleanup repr entries h) (hm : Fragment.Matches s h)
    {root : Nat} (member : root ∈ entries.map (fun entry => entry.1.provenance)) :
    ∃ blk, s.allocations root = some blk ∧ blk.active = true := by
  induction entries generalizing h
  · simp at member
  · rename_i entry rest ih
    rcases entry with ⟨p, value⟩
    obtain ⟨a, b, _, rfl, ha, hb⟩ := hp
    obtain ⟨hma, hmb⟩ := (Fragment.matches_union _ _ _).mp hm
    rcases List.mem_cons.mp member with same | member
    · subst root
      exact alloc_active ha hma
    · exact ih hb hmb member

theorem owned_active (repr : Aeneas.Std.Repr Node) (self : LinkedList) (entries : Entries)
    {h : Fragment} {s : Heap} (hp : owned repr self entries h) (hm : Fragment.Matches s h)
    {root : Nat} (member : root ∈ rootIds self entries) :
    ∃ blk, s.allocations root = some blk ∧ blk.active = true := by
  obtain ⟨_, a, b, _, rfl, _, c, d, _, rfl, hc, hd⟩ := hp
  have hm' := ((Fragment.matches_union _ _ _).mp hm).2
  obtain ⟨hmc, hmd⟩ := (Fragment.matches_union _ _ _).mp hm'
  rcases List.mem_cons.mp member with same | member
  · subst root
    exact alloc_active hc hmc
  · exact cleanup_active repr entries hd hmd member

theorem sepRotate (P Q R : Assertion) : sep P (sep Q R) = sep Q (sep P R) := by
  funext h
  exact propext (sepSwap P Q R h)

theorem sepMiddle (A B C D : Assertion) :
    sep (sep A B) (sep C D) = sep (sep B C) (sep A D) := by
  rw [sepAssoc A B (sep C D), sepRotate A B (sep C D),
    sepRotate A C D, ← sepAssoc B C (sep A D)]

theorem sepEmpLeft (P : Assertion) : sep empty P = P := by
  funext h
  exact propext (sep_empty_left P h)

theorem sepDetach (N R A B C : Assertion) :
    sep (sep N R) (sep A (sep B C)) = sep (sep B N) (sep R (sep A C)) := by
  rw [sepAssoc N R (sep A (sep B C)), sepRotate A B C,
    sepRotate R B (sep A C), sepRotate N B (sep R (sep A C)),
    ← sepAssoc B N (sep R (sep A C))]

variable (repr : Aeneas.Std.Repr Node) (layout : NodeLayout repr) (hsize : 0 < repr.size)
include hsize

theorem readValues_chain (s : Heap) (previous root : Ptr) (entries : Entries)
    (h : Fragment) (hp : chain repr previous root entries h) (hm : Fragment.Matches s h) :
    readValues repr s (firstPtr root entries) entries.length = some (entries.map Prod.snd) := by
  induction entries generalizing previous h
  · rfl
  · rename_i entry rest ih
    rcases entry with ⟨p, value⟩
    obtain ⟨a, b, _, rfl, ha, hb⟩ := hp
    obtain ⟨hma, hmb⟩ := (Fragment.matches_union _ _ _).mp hm
    have hr := read_of_pointsTo hsize ha hma
    change (do
      let node ← Heap.read repr p s
      let tail ← readValues repr s node.next rest.length
      some (node.value :: tail)) = some (value :: rest.map Prod.snd)
    rw [hr]
    change (readValues repr s (firstPtr root rest) rest.length).bind
      (fun tail => some (value :: tail)) = _
    rw [ih _ _ hb hmb]
    rfl

theorem owned_toList (s : Heap) (self : LinkedList) (entries : Entries) (h : Fragment)
    (hp : owned repr self entries h) (hm : Fragment.Matches s h) :
    self.toList repr s = some (entries.map Prod.snd) := by
  obtain ⟨hlen, a, b, _, rfl, ha, _⟩ := hp
  obtain ⟨r, c, _, rfl, hr, hc⟩ := ha
  have hma := ((Fragment.matches_union _ _ _).mp hm).1
  obtain ⟨hmr, hmc⟩ := (Fragment.matches_union _ _ _).mp hma
  have hread := read_of_pointsTo hsize hr hmr
  unfold LinkedList.toList
  rw [hread]
  change readValues repr s (firstPtr self.root entries) self.len.val = _
  rw [hlen]
  exact readValues_chain repr hsize s self.root self.root entries c hc hmc

omit hsize in
theorem ListState.toList {s : Heap} {self : LinkedList} {values : List U32} {F : Fragment}
    (hs : ListState repr self values F s) : self.toList repr s = some values := by
  exact hs.choose_spec.2.2.2.2

theorem listState_intro (s : Heap) (self : LinkedList) (entries : Entries) (h F : Fragment)
    (hd : h.Disjoint F) (hm : Fragment.Matches s (h ∪ F)) (hi : s.Inv)
    (hp : owned repr self entries h)
    (authority : ∀ root ∈ rootIds self entries, RootReturn s root) :
    ListState repr self (entries.map Prod.snd) F s :=
  ⟨h, hd, hm, hi, ⟨entries, rfl, hp, authority⟩,
    owned_toList repr hsize s self entries h hp ((Fragment.matches_union _ _ _).mp hm).1⟩

theorem ext.take_node.spec (p : Ptr) (node : Node) (member : p.provenance ∈ roots) :
    HeapWP.RootTriple roots (sep (alloc repr p p.address 1 true) (pointsTo repr p p.address node))
      (ext.take_node repr p) (fun result h => result = node ∧ empty h) :=
  HeapWP.RootTriple.fromRaw repr p p.address node hsize member

include layout

/-- Internal insertion after allocation. All existing cleanup rights are framed. -/
theorem insert_owned (self : LinkedList) (entries : Entries) (p : Ptr) (value : U32)
    (len : Usize) (hlen : len.val = entries.length + 1) :
    HeapWP.RootTriple roots
      (sep (sep (alloc repr p p.address 1 true) (pointsTo repr p p.address (ext.blankNode value)))
        (fun h => sep (ring repr self.root 0#u32 entries)
          (sep (alloc repr self.root self.root.address 1 true) (cleanup repr entries)) h))
      (do init repr p value
          insert_after repr self.root p
          pure { self with len })
      (fun result h => result.root = self.root ∧ owned repr result ((p, value) :: entries) h) := by
  /- Frame the cleanup token while init establishes detached self-links.
  Frame all cleanup tokens around insert_after.spec, then regroup the new
  node's token with the old cleanup chain and use hlen for the exact length. -/
  have hinsert := insert_after.spec (roots := roots) repr layout hsize self.root p 0#u32 value entries
  apply HeapWP.RootTriple.bind
    (HeapWP.RootTriple.frame
      (HeapWP.RootTriple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
        (fun _ h hp => (sep_comm _ _ h).mp hp)
        (init.spec (roots := roots) repr layout hsize p (ext.blankNode value) value _)))
  intro _
  apply HeapWP.RootTriple.bind
    (HeapWP.RootTriple.conseq (fun h hp => by
        change sep (sep (alloc repr p p.address 1 true) (nodeAt repr p p p value))
          (sep (ring repr self.root 0#u32 entries)
            (sep (alloc repr self.root self.root.address 1 true) (cleanup repr entries))) h at hp
        rw [sepMiddle] at hp
        exact hp)
      (fun _ _ hp => hp)
      (HeapWP.RootTriple.frame (R := sep (alloc repr p p.address 1 true)
        (sep (alloc repr self.root self.root.address 1 true) (cleanup repr entries)))
        hinsert))
  intro _ h F s hp hd hm hi authority
  apply HeapWP.Spec.pure _ _ _ |>.mpr
  refine ⟨authority, h, hd, hm, hi, rfl, ?_, ?_⟩
  · simpa using hlen
  · simpa only [cleanup, sepRotate (alloc repr p p.address 1 true) (alloc repr self.root self.root.address 1 true)] using hp

omit layout in
theorem read_first (root p : Ptr) (value : U32) (rest : Entries) :
    HeapWP.RootTriple roots (ring repr root 0#u32 ((p, value) :: rest))
      (do let sentinel ← ext.read_node repr root
          let n ← ext.read_node repr sentinel.next
          pure (some n.value))
      (fun result h => result = some value ∧ ring repr root 0#u32 ((p, value) :: rest) h) := by
  apply HeapWP.RootTriple.bind
    (framePure (ext.read_node.spec repr hsize root
      (.mk (lastPtr root ((p, value) :: rest)) p 0#u32)))
  intro sentinel
  apply HeapWP.RootTriple.pure_pre
  intro he
  subst sentinel
  apply HeapWP.RootTriple.bind
    (frameLeftPure (framePure (ext.read_node.spec repr hsize p (.mk root (firstPtr root rest) value))))
  intro n
  apply HeapWP.RootTriple.pure_pre
  intro he
  subst n
  exact HeapWP.RootTriple.pure _ (some value)

omit layout in
theorem read_last_chain (previous root p : Ptr) (value : U32) (rest : Entries) :
    HeapWP.RootTriple roots (chain repr previous root ((p, value) :: rest))
      (ext.read_node repr (lastPtr root ((p, value) :: rest)))
      (fun n h => some n.value = (((p, value) :: rest).map Prod.snd).getLast? ∧
        chain repr previous root ((p, value) :: rest) h) := by
  induction rest generalizing previous p value
  · apply HeapWP.RootTriple.conseq ?_ ?_ (ext.read_node.spec repr hsize p (.mk previous root value))
    · intro h hp
      simpa only [chain, firstPtr, sepEmpRight, nodeAt] using hp
    · rintro n h ⟨rfl, hp⟩
      exact ⟨rfl, by simpa only [chain, firstPtr, sepEmpRight, nodeAt] using hp⟩
  · rename_i entry rest ih
    rcases entry with ⟨next, nv⟩
    apply HeapWP.RootTriple.conseq (fun _ hp => hp) ?_ (frameLeftPure (ih p next nv))
    intro n h hp
    exact ⟨by simpa using hp.1, hp.2⟩

omit layout in
theorem read_last (root p : Ptr) (value : U32) (rest : Entries) :
    HeapWP.RootTriple roots (ring repr root 0#u32 ((p, value) :: rest))
      (do let sentinel ← ext.read_node repr root
          let n ← ext.read_node repr sentinel.prev
          pure (some n.value))
      (fun result h => result = (((p, value) :: rest).map Prod.snd).getLast? ∧
        ring repr root 0#u32 ((p, value) :: rest) h) := by
  apply HeapWP.RootTriple.bind
    (framePure (ext.read_node.spec repr hsize root
      (.mk (lastPtr root ((p, value) :: rest)) p 0#u32)))
  intro sentinel
  apply HeapWP.RootTriple.pure_pre
  intro he
  subst sentinel
  apply HeapWP.RootTriple.bind (frameLeftPure (read_last_chain repr hsize root root p value rest))
  intro n
  apply HeapWP.RootTriple.pure_pre
  intro he
  apply HeapWP.RootTriple.conseq (fun _ hp => hp) ?_ (HeapWP.RootTriple.pure _ (some n.value))
  rintro result h ⟨rfl, hp⟩
  exact ⟨he, hp⟩

omit layout in
theorem LinkedList.front_owned (self : LinkedList) (entries : Entries) :
    HeapWP.RootTriple roots (owned repr self entries) (LinkedList.front repr self)
      (fun result h => result = (entries.map Prod.snd).head? ∧ owned repr self entries h) := by
  /- Split entries. The exact length selects the empty branch. Otherwise read
  the sentinel and first node with framed read contracts, retaining ownership. -/
  apply HeapWP.RootTriple.pure_pre
  intro hlen
  unfold LinkedList.front LinkedList.is_empty
  simp only [bind_ok]
  cases entries
  · have hz : self.len = 0#usize := by scalar_tac
    simp [hz]
    apply HeapWP.RootTriple.conseq (fun _ hp => hp) ?_ (HeapWP.RootTriple.pure _ none)
    rintro result h ⟨rfl, hp⟩
    exact ⟨rfl, hlen, hp⟩
  · rename_i entry rest
    rcases entry with ⟨p, value⟩
    have hz : self.len ≠ 0#usize := by intro he; simp [he] at hlen
    simp [hz]
    apply HeapWP.RootTriple.conseq (fun _ hp => hp) ?_ (framePure (read_first repr hsize self.root p value rest))
    intro result h hp
    exact ⟨hp.1, hlen, hp.2⟩

omit layout in
theorem LinkedList.back_owned (self : LinkedList) (entries : Entries) :
    HeapWP.RootTriple roots (owned repr self entries) (LinkedList.back repr self)
      (fun result h => result = (entries.map Prod.snd).getLast? ∧ owned repr self entries h) := by
  /- The empty case is pure. For a nonempty chain, recursively expose/read
  its last node, frame every earlier node, and use the sentinel's prev link. -/
  apply HeapWP.RootTriple.pure_pre
  intro hlen
  unfold LinkedList.back LinkedList.is_empty
  simp only [bind_ok]
  cases entries
  · have hz : self.len = 0#usize := by scalar_tac
    simp [hz]
    apply HeapWP.RootTriple.conseq (fun _ hp => hp) ?_ (HeapWP.RootTriple.pure _ none)
    rintro result h ⟨rfl, hp⟩
    exact ⟨rfl, hlen, hp⟩
  · rename_i entry rest
    rcases entry with ⟨p, value⟩
    have hz : self.len ≠ 0#usize := by intro he; simp [he] at hlen
    simp [hz]
    apply HeapWP.RootTriple.conseq (fun _ hp => hp) ?_ (framePure (read_last repr hsize self.root p value rest))
    intro result h hp
    exact ⟨hp.1, hlen, hp.2⟩

theorem LinkedList.pop_front_owned (self : LinkedList) (entries : Entries)
    (members : ∀ entry ∈ entries, entry.1.provenance ∈ roots) :
    HeapWP.RootTriple roots (owned repr self entries) (LinkedList.pop_front repr self)
      (fun (result, self') h => result = (entries.map Prod.snd).head? ∧
        self'.root = self.root ∧ owned repr self' entries.tail h) := by
  /- For nonempty entries apply remove_after.spec, framing cleanup authority.
  Pair the detached node's bytes with its cleanup token and apply take_node.spec.
  The positive input length permits subtraction; regroup the residual ring. -/
  apply HeapWP.RootTriple.pure_pre
  intro hlen
  unfold LinkedList.pop_front LinkedList.is_empty
  simp only [bind_ok]
  cases entries
  · have hz : self.len = 0#usize := by scalar_tac
    simp [hz]
    intro h F s hp hd hm hi authority
    exact HeapWP.Spec.pure _ _ _ |>.mpr ⟨authority, h, hd, hm, hi, rfl, rfl, hlen, hp⟩
  · rename_i entry rest
    rcases entry with ⟨p, value⟩
    have hz : self.len ≠ 0#usize := by intro he; simp [he] at hlen
    simp [hz]
    apply HeapWP.RootTriple.bind (framePure (remove_after.spec (roots := roots) repr layout hsize self.root p 0#u32 value rest))
    intro node
    apply HeapWP.RootTriple.pure_pre
    intro he
    subst node
    have htake := ext.take_node.spec (roots := roots) repr hsize p (.mk p p value)
      (members (p, value) (by simp))
    have hframed := framePure (R := sep (ring repr self.root 0#u32 rest)
      (sep (alloc repr self.root self.root.address 1 true) (cleanup repr rest))) htake
    apply HeapWP.RootTriple.bind
      (HeapWP.RootTriple.conseq (fun h hp => by
          change sep (sep (nodeAt repr p p p value) (ring repr self.root 0#u32 rest))
            (sep (alloc repr self.root self.root.address 1 true) (sep (alloc repr p p.address 1 true) (cleanup repr rest))) h at hp
          rw [sepDetach] at hp
          exact hp)
        (Q := fun n h => n = Node.mk p p value ∧
          sep (ring repr self.root 0#u32 rest)
            (sep (alloc repr self.root self.root.address 1 true) (cleanup repr rest)) h)
        (fun _ _ hp => ⟨hp.1, by simpa only [sepEmpLeft] using hp.2⟩) hframed)
    intro n
    apply HeapWP.RootTriple.pure_pre
    intro he
    subst n
    have hpos : (1#usize).val ≤ self.len.val := by simp only [List.length_cons] at hlen; agrind
    apply HeapWP.RootTriple.bind (pure_triple _ (Usize.sub_spec hpos))
    intro len
    apply HeapWP.RootTriple.pure_pre
    intro hsub h F s hp hd hm hi authority
    apply HeapWP.Spec.pure _ _ _ |>.mpr
    refine ⟨authority, h, hd, hm, hi, rfl, rfl, ?_, hp⟩
    simp only [List.length_cons] at hlen
    agrind

theorem LinkedList.clear_loop_owned (self : LinkedList) (entries : Entries)
    (members : ∀ entry ∈ entries, entry.1.provenance ∈ roots) :
    HeapWP.RootTriple roots (owned repr self entries) (LinkedList.clear_loop repr self)
      (fun result h => result.root = self.root ∧ owned repr result [] h) := by
  /- Induct on entries. The empty branch is pure. Otherwise pop_front_owned
  supplies ownership of entries.tail, and the induction hypothesis finishes.
  Thus this is total correctness, with entries.length as a decreasing measure. -/
  induction entries generalizing self
  · intro h F s hp hd hm hi authority
    have hz : self.len = 0#usize := by have := hp.1; scalar_tac
    unfold LinkedList.clear_loop LinkedList.is_empty
    simp only [hz, bind_ok]
    exact HeapWP.Spec.pure _ _ _ |>.mpr ⟨authority, h, hd, hm, hi, rfl, hp⟩
  · rename_i entry rest ih
    intro h F s hp hd hm hi authority
    have hz : self.len ≠ 0#usize := by
      intro he
      have hlen := hp.1
      simp [he] at hlen
    unfold LinkedList.clear_loop LinkedList.is_empty
    simp only [hz, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
    apply HeapWP.Spec.bind (LinkedList.pop_front_owned repr layout hsize self (entry :: rest)
      members h F s hp hd hm hi authority)
    rintro ⟨value, self'⟩ s' ⟨authority', h', hd', hm', hi', _, root', hp'⟩
    apply HeapWP.Spec.mono (ih self' (fun entry he => members entry (by simp [he]))
      h' F s' hp' hd' hm' hi' authority')
    rintro result s'' ⟨authority'', h'', hd'', hm'', hi'', root'', hp''⟩
    exact ⟨authority'', h'', hd'', hm'', hi'', root''.trans root', hp''⟩

theorem LinkedList.clear_owned (self : LinkedList) (entries : Entries)
    (members : ∀ entry ∈ entries, entry.1.provenance ∈ roots) :
    HeapWP.RootTriple roots (owned repr self entries) (LinkedList.clear repr self)
      (fun result h => result.root = self.root ∧ owned repr result [] h) := by
  /- The extracted wrapper calls clear_loop_owned with the same invariant. -/
  exact LinkedList.clear_loop_owned repr layout hsize self entries members

theorem LinkedList.drop_owned (self : LinkedList) (entries : Entries)
    (members : ∀ entry ∈ entries, entry.1.provenance ∈ roots)
    (sentinel : self.root.provenance ∈ roots) :
    HeapWP.RootTriple roots (owned repr self entries) (LinkedList.Insts.CoreOpsDropDrop.drop repr self)
      (fun _ => empty) := by
  /- clear_owned leaves only the sentinel and its cleanup authority.
  take_node.spec consumes both, so no list resources remain. -/
  unfold LinkedList.Insts.CoreOpsDropDrop.drop
  apply HeapWP.RootTriple.bind (LinkedList.clear_owned repr layout hsize self entries members)
  intro self'
  apply HeapWP.RootTriple.pure_pre
  intro root'
  apply HeapWP.RootTriple.pure_pre
  intro _
  apply HeapWP.RootTriple.bind
    (HeapWP.RootTriple.conseq (fun h hp => by
        have hp' : sep (pointsTo repr self'.root self'.root.address (.mk self'.root self'.root 0#u32))
            (alloc repr self'.root self'.root.address 1 true) h := by
          simpa only [ring, chain, firstPtr, lastPtr, cleanup, sepEmpRight, nodeAt] using hp
        exact (sep_comm _ _ h).mp hp')
      (fun _ _ hp => hp.2)
      (ext.take_node.spec repr hsize self'.root (.mk self'.root self'.root 0#u32)
        (root'.symm ▸ sentinel)))
  intro _
  exact HeapWP.RootTriple.conseq (fun _ hp => hp) (fun _ _ hp => hp.2)
    (HeapWP.RootTriple.pure empty self')

end doubly_linked
