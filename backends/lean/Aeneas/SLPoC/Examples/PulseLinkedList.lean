import Aeneas.SLPoC.Step

/-!
# Pulse sequential linked lists

A Lean SLPoC port of the sequential first-order fragment of
[`Pulse.Lib.LinkedList`](https://github.com/FStarLang/FStar/blob/master/pulse/lib/pulse/lib/Pulse.Lib.LinkedList.fst)
and its interface.  The port covers the owning linked-list predicate and the
basic operations `isEmpty`, `head`, `pop`, `length`, `create`, `cons`,
`append`, `isLastCell`, `appendAtLastCell`, `detachNext`, `split`, `insert`,
`delete`, and `reverse`.  Pulse's wand-based cursor, iterator, length-loop, and
iterative-append fragments are intentionally outside this first-order scope.
-/

namespace Aeneas.SLPoC

open scoped SepLogic

namespace PulseLinkedList

/-! # Executable definitions -/

/-- A Pulse linked-list cell. -/
structure Node (α : Type) where
  head : α
  tail : Option (Ptr (Node α))

/-- Pulse's nullable `node_ptr`. -/
abbrev Link (α : Type) := Option (Ptr (Node α))

/-- Test whether a linked list is empty. -/
def isEmpty (x : Link α) : St Bool :=
  pure x.isNone

/-- Read the first element.  The proof argument is the erased counterpart of
Pulse's non-empty-list precondition. -/
def head (x : Link α) (hne : x ≠ none) : St α :=
  match x with
  | none => False.elim (hne rfl)
  | some p => do
      let node ← read p
      pure node.head

/-- Remove and free the first cell, returning the remaining list and value. -/
def pop (x : Link α) (hne : x ≠ none) : St (Link α × α) :=
  match x with
  | none => False.elim (hne rfl)
  | some p => do
      let node ← read p
      free p
      pure (node.tail, node.head)

/-- Recursive length, with Pulse's erased logical list made explicit to justify
structural recursion. -/
def length : List α → Link α → St Nat
  | [], _ => pure 0
  | _ :: _, none => pure 0
  | _ :: xs, some p => do
      let node ← read p
      let n ← length xs node.tail
      pure (n + 1)

/-- Construct the empty linked list. -/
def create (α : Type) : St (Link α) :=
  pure none

/-- Allocate and prepend one cell. -/
def cons (v : α) (x : Link α) : St (Link α) := do
  let p ← alloc { head := v, tail := x }
  pure (some p)

/-- Append `y` in place to the non-empty list `x`.  The first argument is
Pulse's erased logical list and supplies the recursion measure. -/
def append : List α → Link α → Link α → St Unit
  | [], _, _ => pure ()
  | _ :: _, none, _ => pure ()
  | _ :: xs, some p, y => do
      let node ← read p
      match xs with
      | [] => update p { node with tail := y }
      | _ :: _ => append xs node.tail y

/-- Test whether a non-empty list consists of exactly one cell. -/
def isLastCell (x : Link α) (hne : x ≠ none) : St Bool :=
  match x with
  | none => False.elim (hne rfl)
  | some p => do
      let node ← read p
      isEmpty node.tail

/-- Attach `y` directly after the only cell of `x`. -/
def appendAtLastCell (x y : Link α) (hne : x ≠ none) : St Unit :=
  match x with
  | none => False.elim (hne rfl)
  | some p => do
      let node ← read p
      update p { node with tail := y }

/-- Detach the tail following the first cell. -/
def detachNext (x : Link α) (hne : x ≠ none) : St (Link α) :=
  match x with
  | none => False.elim (hne rfl)
  | some p => do
      let node ← read p
      update p { node with tail := none }
      pure node.tail

/-- Split after the first `n` cells.  Pulse uses a `UInt32`; `Nat` is the
unbounded first-order counterpart used by this model. -/
def split : Nat → Link α → St (Link α)
  | 0, x => pure x
  | _ + 1, none => pure none
  | 1, some p => do
      let node ← read p
      update p { node with tail := none }
      pure node.tail
  | n + 2, some p => do
      let node ← read p
      split (n + 1) node.tail

/-- Insert `item` after the first `n` cells. -/
def insert (xs : List α) (x : Link α) (item : α) (n : Nat) : St Unit := do
  let tail ← split n x
  let inserted ← cons item tail
  append (xs.take n) x inserted

/-- The upstream Pulse implementation of `delete` currently has the same body
as `insert`; this definition deliberately preserves that actual behavior. -/
def delete (xs : List α) (x : Link α) (item : α) (n : Nat) : St Unit :=
  insert xs x item n

/-- Tail-recursive in-place reversal with an accumulator. -/
def reverseAppend : List α → Link α → Link α → St (Link α)
  | [], _, acc => pure acc
  | _ :: _, none, acc => pure acc
  | _ :: xs, some p, acc => do
      let node ← read p
      update p { node with tail := acc }
      reverseAppend xs node.tail (some p)

/-- Reverse a linked list in place. -/
def reverse (xs : List α) (x : Link α) : St (Link α) :=
  reverseAppend xs x none

/-! # Ghost state, specifications and proofs -/

/-- Exact ownership of a linked list with pure view `xs`. -/
def isList : Link α → List α → SLProp
  | none, [] => emp
  | some p, x :: xs =>
      hexists fun next =>
        iprop(p ↦ { head := x, tail := next } ∗ isList next xs)
  | _, _ => ⌜False⌝

@[simp] theorem isList_none_nil : isList (none : Link α) [] = emp := rfl

@[simp] theorem isList_none_cons (x : α) (xs : List α) :
    isList (none : Link α) (x :: xs) = ⌜False⌝ := rfl

@[simp] theorem isList_some_nil (p : Ptr (Node α)) :
    isList (some p) [] = ⌜False⌝ := rfl

/-- Unfold one owned cell. -/
theorem isList_unfold (p : Ptr (Node α)) (x : α) (xs : List α) :
    isList (some p) (x :: xs) ⊢
      hexists fun next =>
        iprop(p ↦ { head := x, tail := next } ∗ isList next xs) := by
  sl_frame

/-- Fold one owned cell. -/
theorem isList_fold (p : Ptr (Node α)) (x : α) (next : Link α)
    (xs : List α) :
    p ↦ { head := x, tail := next } ∗ isList next xs ⊢
      isList (some p) (x :: xs) := by
  change _ ⊢ hexists fun next' =>
    iprop(p ↦ { head := x, tail := next' } ∗ isList next' xs)
  exact himpl_hexists_r next (himpl_refl _)

/-- A list is empty exactly when its link is null. -/
@[step]
theorem isEmpty.spec (x : Link α) (xs : List α) :
    ⦃ isList x xs ⦄ isEmpty x
      ⦃⇓ b => ⌜b = decide (xs = [])⌝ ∗ isList x xs⦄ := by
  unfold isEmpty
  cases xs with
  | nil =>
      cases x
      · sl_step*
      · sl_pull
        contradiction
  | cons v vs =>
      cases x with
      | none =>
          sl_pull
          contradiction
      | some p =>
          simp only [Option.isNone_some, List.cons_ne_nil, decide_false]
          sl_step*

/-- `head` preserves ownership and returns the exact first value. -/
@[step]
theorem head.spec (x : Link α) (v : α) (xs : List α) (hne : x ≠ none) :
    ⦃ isList x (v :: xs) ⦄ head x hne
      ⦃⇓ result => ⌜result = v⌝ ∗ isList x (v :: xs)⦄ := by
  cases x with
  | none => contradiction
  | some p =>
      simp only [head]
      sl_pull next
      sl_step*

/-- `pop` frees the first cell and returns its exact tail and value. -/
@[step]
theorem pop.spec (x : Link α) (v : α) (xs : List α) (hne : x ≠ none) :
    ⦃ isList x (v :: xs) ⦄ pop x hne
      ⦃⇓ (tail, result) => ⌜result = v⌝ ∗ isList tail xs⦄ := by
  cases x with
  | none => contradiction
  | some p =>
      simp only [pop, isList]
      sl_pull next
      sl_step
      sl_step
      sl_pure
      sl_frame

/-- Recursive `length` preserves every cell and computes the pure-list length. -/
@[step]
theorem length.spec (x : Link α) (xs : List α) :
    ⦃ isList x xs ⦄ length xs x
      ⦃⇓ n => ⌜n = xs.length⌝ ∗ isList x xs⦄ := by
  induction xs generalizing x with
  | nil =>
      cases x
      · simp only [length, List.length_nil]
        sl_step*
      · sl_pull
        contradiction
  | cons v xs ih =>
      cases x with
      | none =>
          sl_pull
          contradiction
      | some p =>
          simp only [length, List.length_cons]
          sl_pull next
          sl_step
          sl_step with ih next
          sl_step*

/-- `create` returns the uniquely represented empty list. -/
@[step]
theorem create.spec :
    ⦃ emp ⦄ create α ⦃⇓ x => isList x []⦄ := by
  unfold create
  sl_pure
  change emp ⊢ emp
  sl_frame

/-- `cons` allocates one cell and prepends its value to the exact view. -/
@[step]
theorem cons.spec (v : α) (x : Link α) (xs : List α) :
    ⦃ isList x xs ⦄ cons v x
      ⦃⇓ y => isList y (v :: xs)⦄ := by
  unfold cons
  sl_step
  sl_pure
  exact isList_fold _ v x xs

/-- `append` preserves the head link `x` and mutates its last cell so that its
exact view becomes `xs ++ ys`. -/
@[step]
theorem append.spec (x y : Link α) (xs ys : List α) (hne : xs ≠ []) :
    ⦃ isList x xs ∗ isList y ys ⦄ append xs x y
      ⦃⇓ isList x (xs ++ ys)⦄ := by
  induction xs generalizing x y ys with
  | nil => contradiction
  | cons v xs ih =>
      cases x with
      | none =>
          sl_pull
          contradiction
      | some p =>
          simp only [isList]
          sl_pull next
          cases xs with
          | nil =>
              simp only [append, List.singleton_append]
              sl_step*
          | cons w ws =>
              simp only [append, List.cons_append]
              sl_step
              sl_step with ih (x := next) (y := y) (ys := ys) (by simp)

/-- `isLastCell` preserves ownership and exactly characterizes a singleton. -/
@[step]
theorem isLastCell.spec (x : Link α) (v : α) (xs : List α)
    (hne : x ≠ none) :
    ⦃ isList x (v :: xs) ⦄ isLastCell x hne
      ⦃⇓ b => ⌜b = decide (xs = [])⌝ ∗ isList x (v :: xs)⦄ := by
  cases x with
  | none => contradiction
  | some p =>
      simp only [isLastCell]
      sl_pull next
      sl_step
      sl_step with isEmpty.spec next xs

/-- `appendAtLastCell` implements Pulse's singleton-specialized append helper. -/
@[step]
theorem appendAtLastCell.spec (x y : Link α) (v : α) (ys : List α)
    (hne : x ≠ none) :
    ⦃ isList x [v] ∗ isList y ys ⦄ appendAtLastCell x y hne
      ⦃⇓ isList x (v :: ys)⦄ := by
  cases x with
  | none => contradiction
  | some p =>
      simp only [appendAtLastCell, isList]
      sl_pull next
      sl_step*

/-- `detachNext` turns the first cell into a singleton and returns the exact
detached tail. -/
@[step]
theorem detachNext.spec (x : Link α) (v : α) (xs : List α) (hne : x ≠ none) :
    ⦃ isList x (v :: xs) ⦄ detachNext x hne
      ⦃⇓ tail => isList x [v] ∗ isList tail xs⦄ := by
  cases x with
  | none => contradiction
  | some p =>
      simp only [detachNext, isList]
      sl_pull next
      sl_step
      sl_step
      sl_pure
      refine himpl_hexists_r none ?_
      simp only [isList]
      sl_frame

/-- `split n` leaves the first `n` values under the original head link and
returns ownership of the exact suffix. -/
@[step]
theorem split.spec (n : Nat) (x : Link α) (xs : List α)
    (hpos : 0 < n) (hle : n ≤ xs.length) :
    ⦃ isList x xs ⦄ split n x
      ⦃⇓ tail => isList x (xs.take n) ∗ isList tail (xs.drop n)⦄ := by
  induction n generalizing x xs with
  | zero => omega
  | succ n ih =>
      rcases xs with _ | ⟨v, xs⟩
      · simp at hle
      · cases x with
        | none =>
            sl_pull
            contradiction
        | some p =>
            sl_pull next
            cases n with
            | zero =>
                simp only [split, List.take, List.drop]
                sl_step
                sl_step
                sl_pure
                apply hstar_mono
                · refine himpl_hexists_r (none : Link α) ?_
                  simp only [isList]
                  sl_frame
                · sl_frame
            | succ n =>
                simp only [split, List.take, List.drop]
                sl_step
                sl_step with ih (x := next) (xs := xs) (by omega) (by simpa using hle)

/-- `insert` splits the exact view and inserts `item` at index `n`. -/
@[step]
theorem insert.spec (n : Nat) (x : Link α) (xs : List α) (item : α)
    (hpos : 0 < n) (hlt : n < xs.length) :
    ⦃ isList x xs ⦄ insert xs x item n
      ⦃⇓ isList x (xs.take n ++ item :: xs.drop n)⦄ := by
  have htake : xs.take n ≠ [] := by
    cases n with
    | zero => omega
    | succ n =>
        cases xs <;> simp_all
  unfold insert
  sl_step with split.spec n x xs hpos (Nat.le_of_lt hlt)
  sl_step with cons.spec item tail (xs.drop n)
  sl_step with append.spec x inserted (xs.take n) (item :: xs.drop n) htake

/-- Pulse's current `delete` body is insertion; its exact specification records
that behavior rather than claiming removal. -/
@[step]
theorem delete.spec (n : Nat) (x : Link α) (xs : List α) (item : α)
    (hpos : 0 < n) (hlt : n < xs.length) :
    ⦃ isList x xs ⦄ delete xs x item n
      ⦃⇓ isList x (xs.take n ++ item :: xs.drop n)⦄ := by
  unfold delete
  sl_step with insert.spec n x xs item hpos hlt

/-- Accumulator form of reversal: the result has view `xs.reverse ++ ys`. -/
@[step]
theorem reverseAppend.spec (x acc : Link α) (xs ys : List α) :
    ⦃ isList x xs ∗ isList acc ys ⦄ reverseAppend xs x acc
      ⦃⇓ result => isList result (xs.reverse ++ ys)⦄ := by
  induction xs generalizing x acc ys with
  | nil =>
      cases x
      · simp only [isList, reverseAppend, List.reverse_nil, List.nil_append]
        sl_pure
        sl_frame
      · sl_pull
        contradiction
  | cons v xs ih =>
      cases x with
      | none =>
          sl_pull
          contradiction
      | some p =>
          simp only [isList, reverseAppend, List.reverse_cons, List.append_assoc,
            List.singleton_append]
          sl_pull next
          sl_step
          sl_step
          sl_step with ih (x := next) (acc := some p) (ys := v :: ys)

/-- `reverse` consumes the original orientation and returns exact ownership in
reverse pure-list order. -/
@[step]
theorem reverse.spec (x : Link α) (xs : List α) :
    ⦃ isList x xs ⦄ reverse xs x
      ⦃⇓ result => isList result xs.reverse⦄ := by
  unfold reverse
  sl_step with reverseAppend.spec x none xs []

end PulseLinkedList

end Aeneas.SLPoC
