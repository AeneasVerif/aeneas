import Aeneas.SLPoC.Step

/-!
# Asterinas intrusive frame-list kernel

This file ports the extractable sequential kernel exercised by
`LinkedList::push_front`, `LinkedList::pop_front`, and the latter's call to
`CursorMut::take_current` in Asterinas/vostd
`ostd/src/mm/frame/linked_list.rs`.  A frame exists independently of a list and
already has a metadata slot.  `pushFront` writes intrusive `prev`/`next` links
into that slot and transfers its exclusive points-to resource to the list;
`popFront` removes exactly that slot, clears both links and the membership
marker, and returns the same frame.  Neither operation allocates or frees heap
storage.

The source's `MetaRegionOwners`, raw frame-to-metadata address conversion,
representation permissions, reference count, drop obligation, atomics, and
lazy global list-ID allocator are deliberately collapsed into typed metadata
slots and ordinary separation-logic ownership.  A nonzero `listId` is supplied
when constructing this sequential kernel, standing for the ID minted by that
framework.  The slot's `inList` field models the source region owner's
`in_list_perm`; exclusive `↦` ownership models the unique raw-frame and
type-specific representation permissions.  Thus the abstraction omits global
region arithmetic and concurrency, but not the intrusive links or the linear
ownership transfer.  The cursor helper implements the source's general
constant-time rewiring code; the proved view is the exact front-cursor
split used by public `pop_front`.
-/

namespace Aeneas.SLPoC

open scoped SepLogic

namespace AsterinasIntrusiveFrameList

/-! # Executable definitions -/

/-- One metadata slot embedded in the independently existing frame metadata
region.  `payload` is the source `Link<M>.meta`. -/
structure FrameSlot (M : Type) where
  frameId : Nat
  payload : M
  prev : Option (Ptr (FrameSlot M))
  next : Option (Ptr (FrameSlot M))
  inList : Option Nat

/-- A unique frame handle.  The metadata slot is pre-existing; list operations
never allocate it. -/
structure Frame (M : Type) where
  id : Nat
  slot : Ptr (FrameSlot M)

/-- Executable fields of the source `LinkedList`. -/
structure LinkedList (M : Type) where
  front : Option (Ptr (FrameSlot M))
  back : Option (Ptr (FrameSlot M))
  size : Nat
  listId : Nat

/-- Executable fields of `CursorMut`.  The source borrow of the list is
represented by carrying the list value linearly through the state monad. -/
structure Cursor (M : Type) where
  list : LinkedList M
  current : Option (Ptr (FrameSlot M))

/-- Construct an empty sequential list with an ID supplied by the abstracted
metadata-region/list-ID framework. -/
def new (listId : Nat) : St (LinkedList M) :=
  pure { front := none, back := none, size := 0, listId }

/-- Construct the cursor used by both public front operations. -/
def cursorFront (s : LinkedList M) : St (Cursor M) :=
  pure { list := s, current := s.front }

/-- Public `push_front`: initialize the detached frame's existing intrusive
slot, repair the old front's back-link, and publish the slot as the new front.
There is intentionally no `alloc`. -/
def pushFront (s : LinkedList M) (frame : Frame M) : St (LinkedList M) := do
  let frameSlot ← read frame.slot
  update frame.slot
    { frameSlot with prev := none, next := s.front, inList := some s.listId }
  match s.front with
  | none =>
      pure
        { s with
          front := some frame.slot
          back := some frame.slot
          size := s.size + 1 }
  | some oldFront =>
      let oldFrontSlot ← read oldFront
      update oldFront { oldFrontSlot with prev := some frame.slot }
      pure { s with front := some frame.slot, size := s.size + 1 }

/-- Constant-time cursor removal, matching the source rewiring order.  On
success the cursor advances to `next`; the removed slot is detached and the
same frame handle is reconstructed from its slot. -/
def takeCurrent (cursor : Cursor M) : St (Cursor M × Option (Frame M)) := do
  match cursor.current with
  | none => pure (cursor, none)
  | some current =>
      let currentSlot ← read current
      let next := currentSlot.next
      let list ←
        match currentSlot.prev with
        | none => pure { cursor.list with front := next }
        | some prev =>
            let prevSlot ← read prev
            update prev { prevSlot with next := next }
            pure cursor.list
      let list ←
        match next with
        | none => pure { list with back := currentSlot.prev }
        | some nextPtr =>
            let nextSlot ← read nextPtr
            update nextPtr { nextSlot with prev := currentSlot.prev }
            pure list
      update current
        { currentSlot with prev := none, next := none, inList := none }
      let list := { list with size := list.size - 1 }
      pure
        ({ list, current := next },
          some { id := currentSlot.frameId, slot := current })

/-- Public `pop_front`: make the source front cursor and delegate removal to
`takeCurrent`. -/
def popFront (s : LinkedList M) : St (LinkedList M × Option (Frame M)) := do
  let (cursor, frame) ←
    takeCurrent { list := s, current := s.front }
  pure (cursor.list, frame)

/-! # Ghost state, specifications and proofs -/

/-- A pure entry remembers the independent frame identity and its metadata
payload.  Entry order is front-to-back. -/
abbrev Entry (M : Type) := Frame M × M

/-- Pure frame sequence represented by a ghost entry sequence. -/
def frameSequence (entries : List (Entry M)) : List (Frame M) :=
  entries.map Prod.fst

@[simp] theorem frameSequence_cons (frame : Frame M) (payload : M)
    (rest : List (Entry M)) :
    frameSequence ((frame, payload) :: rest) =
      frame :: frameSequence rest := rfl

/-- First intrusive slot in a pure sequence. -/
def firstSlot : List (Entry M) → Option (Ptr (FrameSlot M))
  | [] => none
  | (frame, _) :: _ => some frame.slot

/-- Last intrusive slot in a pure sequence. -/
def lastSlot : List (Entry M) → Option (Ptr (FrameSlot M))
  | [] => none
  | (frame, _) :: [] => some frame.slot
  | _ :: (frame, payload) :: rest =>
      lastSlot ((frame, payload) :: rest)

/-- Exact value stored in an owned intrusive metadata slot. -/
def linkedValue (listId : Nat) (frame : Frame M) (payload : M)
    (prev next : Option (Ptr (FrameSlot M))) : FrameSlot M :=
  { frameId := frame.id
    payload
    prev
    next
    inList := some listId }

/-- Exact detached-frame value.  This is the ownership returned by removal and
consumed by insertion. -/
def detachedValue (frame : Frame M) (payload : M) : FrameSlot M :=
  { frameId := frame.id
    payload
    prev := none
    next := none
    inList := none }

/-- Recursive ownership of an intrusive suffix.  The explicit predecessor
parameter makes every stored back-link part of the representation. -/
def ownedFrom (listId : Nat) :
    Option (Ptr (FrameSlot M)) → List (Entry M) → SLProp
  | _, [] => emp
  | prev, (frame, payload) :: rest =>
      iprop(
        frame.slot ↦
          linkedValue listId frame payload prev (firstSlot rest) ∗
        ownedFrom listId (some frame.slot) rest)

/-- Exclusive ownership of a frame outside every list. -/
def detachedFrame (frame : Frame M) (payload : M) : SLProp :=
  frame.slot ↦ detachedValue frame payload

/-- Full recursive list representation tied to the pure frame sequence.
Repeated slot pointers cannot satisfy this assertion because `↦` is exclusive;
that is the typed counterpart of the source's unique-frame/representation
permissions. -/
def listRep (s : LinkedList M) (entries : List (Entry M)) : SLProp :=
  iprop(
    ⌜s.listId ≠ 0 ∧
      s.front = firstSlot entries ∧
      s.back = lastSlot entries ∧
      s.size = entries.length⌝ ∗
    ownedFrom s.listId none entries)

/-- A cursor owns the list it mutably borrows and identifies its front. -/
def frontCursorRep (cursor : Cursor M) (entries : List (Entry M)) : SLProp :=
  iprop(⌜cursor.current = cursor.list.front⌝ ∗ listRep cursor.list entries)

attribute [step_post_simps]
  linkedValue detachedValue firstSlot lastSlot ownedFrom listRep frontCursorRep

@[simp] theorem firstSlot_nil :
    firstSlot ([] : List (Entry M)) = none := rfl

@[simp] theorem firstSlot_cons (frame : Frame M) (payload : M)
    (rest : List (Entry M)) :
    firstSlot ((frame, payload) :: rest) = some frame.slot := rfl

@[simp] theorem lastSlot_nil :
    lastSlot ([] : List (Entry M)) = none := rfl

@[simp] theorem lastSlot_singleton (frame : Frame M) (payload : M) :
    lastSlot [(frame, payload)] = some frame.slot := rfl

@[simp] theorem lastSlot_cons_cons (frame₁ frame₂ : Frame M)
    (payload₁ payload₂ : M) (rest : List (Entry M)) :
    lastSlot ((frame₁, payload₁) :: (frame₂, payload₂) :: rest) =
      lastSlot ((frame₂, payload₂) :: rest) := rfl

@[simp] theorem ownedFrom_nil (listId : Nat)
    (prev : Option (Ptr (FrameSlot M))) :
    ownedFrom listId prev [] = emp := rfl

@[simp] theorem ownedFrom_cons (listId : Nat)
    (prev : Option (Ptr (FrameSlot M))) (frame : Frame M) (payload : M)
    (rest : List (Entry M)) :
    ownedFrom listId prev ((frame, payload) :: rest) =
      iprop(
        frame.slot ↦
          linkedValue listId frame payload prev (firstSlot rest) ∗
        ownedFrom listId (some frame.slot) rest) := rfl

/-- Exact cursor split used by `pop_front`: the current cell is separated from
the recursively owned suffix, whose predecessor is exactly the current slot. -/
theorem frontCursorRep_cons_split (cursor : Cursor M)
    (frame : Frame M) (payload : M) (rest : List (Entry M)) :
    frontCursorRep cursor ((frame, payload) :: rest) ⊢
      iprop(
        ⌜cursor.current = some frame.slot ∧
          cursor.list.listId ≠ 0 ∧
          cursor.list.front = some frame.slot ∧
          cursor.list.back = lastSlot ((frame, payload) :: rest) ∧
          cursor.list.size = rest.length + 1⌝ ∗
        frame.slot ↦
          linkedValue cursor.list.listId frame payload none (firstSlot rest) ∗
        ownedFrom cursor.list.listId (some frame.slot) rest) := by
  unfold frontCursorRep listRep
  simp only [firstSlot_cons, ownedFrom_cons, List.length_cons]
  apply himpl_hpure_l
  intro hcursor
  apply himpl_hpure_l
  intro hlist
  sl_frame

/-- Recombine the exact cursor split into the recursive list representation. -/
theorem frontCursorRep_cons_recombine (cursor : Cursor M)
    (frame : Frame M) (payload : M) (rest : List (Entry M)) :
    iprop(
      ⌜cursor.current = some frame.slot ∧
        cursor.list.listId ≠ 0 ∧
        cursor.list.front = some frame.slot ∧
        cursor.list.back = lastSlot ((frame, payload) :: rest) ∧
        cursor.list.size = rest.length + 1⌝ ∗
      frame.slot ↦
        linkedValue cursor.list.listId frame payload none (firstSlot rest) ∗
      ownedFrom cursor.list.listId (some frame.slot) rest) ⊢
    frontCursorRep cursor ((frame, payload) :: rest) := by
  unfold frontCursorRep listRep
  simp only [firstSlot_cons, ownedFrom_cons, List.length_cons]
  apply himpl_hpure_l
  intro h
  sl_frame

/-- The empty cursor/list view exposes both null ends and size. -/
theorem frontCursorRep_nil_split (cursor : Cursor M) :
    frontCursorRep cursor [] ⊢
      iprop(
        ⌜cursor.current = none ∧
          cursor.list.listId ≠ 0 ∧
          cursor.list.front = none ∧
          cursor.list.back = none ∧
          cursor.list.size = 0⌝) := by
  unfold frontCursorRep listRep
  simp only [firstSlot_nil, lastSlot_nil, ownedFrom_nil, List.length_nil]
  apply himpl_hpure_l
  intro hcursor
  apply himpl_hpure_l
  intro hlist
  sl_frame

/-- Creating the explicit front cursor is ownership-neutral. -/
@[step]
theorem cursorFront.spec (s : LinkedList M) (entries : List (Entry M)) :
    ⦃ listRep s entries ⦄ cursorFront s
    ⦃⇓ cursor => frontCursorRep cursor entries⦄ := by
  unfold cursorFront
  refine triple_conseq
    (P := listRep s entries)
    (Q := fun cursor => frontCursorRep cursor entries)
    (triple_frame
      (pure.spec ({ list := s, current := s.front } : Cursor M))
      (listRep s entries)) ?_ ?_
  · rw [hstar_hempty_l_eq]
    exact himpl_refl _
  · intro cursor
    apply himpl_hpure_l
    intro hcursor
    subst cursor
    unfold frontCursorRep
    sl_frame

/-- `new` owns no frame cells and represents the empty pure sequence. -/
@[step]
theorem new.spec (listId : Nat) (hnonzero : listId ≠ 0) :
    ⦃ emp ⦄ (new listId : St (LinkedList M))
      ⦃⇓ s => listRep s []⦄ := by
  unfold new
  sl_step*

/-- Exact ownership-transfer and sequence specification for public
`push_front`: the supplied independent frame becomes precisely the new head.
The executable definition contains no allocation; the affine triple alone
does not establish an exact operational heap delta. -/
@[step]
theorem pushFront.spec (s : LinkedList M) (entries : List (Entry M))
    (frame : Frame M) (payload : M) :
    ⦃ listRep s entries ∗ detachedFrame frame payload ⦄
      pushFront s frame
    ⦃⇓ s' => listRep s' ((frame, payload) :: entries)⦄ := by
  unfold pushFront detachedFrame
  cases entries with
  | nil =>
      simp only [listRep, firstSlot_nil, lastSlot_nil, ownedFrom_nil,
        List.length_nil]
      sl_pull hlist
      simp only [hlist.2.1]
      simp only [detachedValue]
      sl_step* 2
      sl_pure
      simp_all [linkedValue]
      sl_frame
  | cons head rest =>
      rcases head with ⟨oldFrame, oldPayload⟩
      simp only [listRep, firstSlot_cons, ownedFrom_cons, List.length_cons]
      rw [hstar_assoc_eq]
      sl_pull hlist
      simp only [hlist.2.1]
      simp only [linkedValue, detachedValue]
      sl_step* 4
      sl_pure
      simp_all
      sl_frame

/-- Empty cursor removal reports `none` and preserves the exact empty
ownership. -/
@[step]
theorem takeCurrent.empty.spec (cursor : Cursor M) :
    ⦃ frontCursorRep cursor [] ⦄ takeCurrent cursor
    ⦃⇓ (cursor', result) =>
      ⌜cursor' = cursor ∧ result = none⌝ ∗ frontCursorRep cursor' []⦄ := by
  unfold takeCurrent frontCursorRep listRep
  simp only [firstSlot_nil, lastSlot_nil, ownedFrom_nil, List.length_nil]
  sl_pull hcursor hlist
  simp only [hcursor, hlist.2.1]
  sl_pure
  simp_all
  sl_frame

/-- Exact split/recombine theorem for cursor removal.  It consumes the current
head cell plus its suffix view, clears and returns that same frame, advances
the cursor to the old suffix, and re-establishes the recursive representation
for precisely `rest`. -/
@[step]
theorem takeCurrent.cons.spec (cursor : Cursor M) (frame : Frame M)
    (payload : M) (rest : List (Entry M)) :
    ⦃ frontCursorRep cursor ((frame, payload) :: rest) ⦄
      takeCurrent cursor
    ⦃⇓ (cursor', result) =>
      ⌜result = some frame⌝ ∗
      detachedFrame frame payload ∗
      frontCursorRep cursor' rest⦄ := by
  unfold takeCurrent detachedFrame frontCursorRep listRep
  simp only [firstSlot_cons, ownedFrom_cons, List.length_cons]
  sl_pull hcursor hlist
  simp only [hcursor, hlist.2.1]
  simp only [linkedValue, detachedValue]
  cases rest with
  | nil =>
      simp only [firstSlot_nil, ownedFrom_nil]
      sl_step* 4
      sl_pure
      simp_all
      sl_frame
  | cons next rest' =>
      rcases next with ⟨nextFrame, nextPayload⟩
      simp only [firstSlot_cons, ownedFrom_cons]
      sl_step* 6
      sl_pure
      simp [linkedValue]
      simp only [lastSlot_cons_cons] at hlist
      sl_frame

/-- Public empty pop reports empty and preserves the list exactly. -/
@[step]
theorem popFront.empty.spec (s : LinkedList M) :
    ⦃ listRep s [] ⦄ popFront s
    ⦃⇓ (s', result) =>
      ⌜s' = s ∧ result = none⌝ ∗ listRep s' []⦄ := by
  unfold popFront
  let initial : Cursor M := { list := s, current := s.front }
  have htake :
      ⦃ listRep s [] ⦄ takeCurrent initial
      ⦃⇓ (cursor, result) =>
        ⌜cursor = initial ∧ result = none⌝ ∗
        frontCursorRep cursor []⦄ := by
    apply triple_conseq (takeCurrent.empty.spec initial)
    · unfold initial frontCursorRep
      sl_frame
    · intro result
      exact himpl_refl _
  refine triple_bind htake ?_
  rintro ⟨cursor, result⟩
  sl_pure
  unfold initial frontCursorRep
  sl_frame

/-- Public nonempty pop returns/removes exactly the pure head and transfers its
detached unique ownership back to the caller. -/
@[step]
theorem popFront.cons.spec (s : LinkedList M) (frame : Frame M)
    (payload : M) (rest : List (Entry M)) :
    ⦃ listRep s ((frame, payload) :: rest) ⦄ popFront s
    ⦃⇓ (s', result) =>
      ⌜result = some frame⌝ ∗
      detachedFrame frame payload ∗
      listRep s' rest⦄ := by
  unfold popFront
  let initial : Cursor M := { list := s, current := s.front }
  have htake :
      ⦃ listRep s ((frame, payload) :: rest) ⦄ takeCurrent initial
      ⦃⇓ (cursor, result) =>
        ⌜result = some frame⌝ ∗
        detachedFrame frame payload ∗
        frontCursorRep cursor rest⦄ := by
    apply triple_conseq (takeCurrent.cons.spec initial frame payload rest)
    · unfold initial frontCursorRep
      sl_frame
    · intro result
      exact himpl_refl _
  refine triple_bind htake ?_
  rintro ⟨cursor, result⟩
  sl_pure
  unfold frontCursorRep
  simp_all
  sl_frame

end AsterinasIntrusiveFrameList

end Aeneas.SLPoC
