import Aeneas.SLPoC.Step

/-!
# `InPlaceOrDisjointBuffer`, specified against `EqOrDisj`

[SymCRust](https://github.com/microsoft/VCR) implements SymCrypt's C contract,
which lets a caller pass the same buffer as source and as destination.  Rust's
`&`/`&mut` cannot express that, so `SymCRust/src/common.rs` carries a raw pair:

```rust
pub struct InPlaceOrDisjointBuffer<'a, T> {
    src: *const T,
    dst: *mut T,
    len: usize,
    _phantom: PhantomData<&'a mut [T]>,
}
```

whose `unsafe fn from_raw_parts` demands that *"`src` and `dst` must be either
equal or completely disjoint"*.  `EqOrDisj (List T)` is exactly that ghost
state, and this file specifies the whole interface against it:

the ten entries of its interface — `new_in_place`, `new_disjoint`,
`new_disjoint_from_slices`, `unsafe from_raw_parts`, `len`, `unsafe
loadu_si128_src`, `unsafe loadu_si128_dst`, `unsafe storeu_si128`, `src` and
`dst`.  Every entry is specified by a Hoare triple, so the specifications
compose with `sl_step`, and the pure entries — the constructors, `len`, `src`
and `dst` — are calls returning in `St` like the rest.  Every declaration that
has a Rust counterpart carries its Rust name;
the rest (`owns`, `ownsCells`, `readCells`, `writeCells`, `borrow_intro`, …) is
the model underneath and is named in Lean style.

`aes_xmm.rs`'s `BufferM128` trait renames the three `_si128` entries to
`m128_loadu_src`, `m128_loadu_dst` and `m128_storeu`; it adds nothing.

The whole content of the pattern is `EqOrDisj.write`: giving the write view new
contents leaves the read view alone in the `.disjoint` case and *replaces* it in
the `.equal` case.  The Aeneas development of this very code,
`SymCRust/lean/Symcrust/Properties/Aes/Axioms/BufferModel.lean`, instead
axiomatizes two independent ghost views `srcView`/`dstView` and asserts that a
store preserves `srcView` unconditionally — true only in the disjoint mode.

Separation replaces the disjointness side conditions: the `.disjoint` case owns
two separated views, so no hypothesis has to say that they do not overlap, and
the partial overlap the `unsafe` contract rules out is not expressible.

The `_si128` entries move 128 bits at a time.  That width is orthogonal to the
aliasing question, so it is taken here as one cell per lane: the last section
instantiates the buffer at `Std.U128` cells and lane offsets.
-/

namespace Aeneas.SLPoC

open scoped SepLogic

namespace Examples

/-! ## The ghost state -/

/-- Two views of memory that are either the same or separated: the ghost state
of a `src`/`dst` pair. -/
inductive EqOrDisj (α : Type) where
  | equal (value : α)
  | disjoint (leftValue rightValue : α)

/-- What the read view holds. -/
def EqOrDisj.read {α : Type} (relation : EqOrDisj α) : α :=
  match relation with
  | .equal value => value
  | .disjoint leftValue _ => leftValue

/-- What the write view holds. -/
def EqOrDisj.written {α : Type} (relation : EqOrDisj α) : α :=
  match relation with
  | .equal value => value
  | .disjoint _ rightValue => rightValue

/-- Give the write view the contents `value`. -/
def EqOrDisj.write {α : Type} (relation : EqOrDisj α)
    (value : α) : EqOrDisj α :=
  match relation with
  | .equal _ => .equal value
  | .disjoint leftValue _ => .disjoint leftValue value

@[simp] theorem EqOrDisj.written_write {α : Type} (relation : EqOrDisj α)
    (value : α) : (relation.write value).written = value := by
  cases relation <;> rfl

/-- Writing is visible to the reader exactly when the two views are the same:
this single pair of equations is the whole pattern. -/
@[simp] theorem EqOrDisj.read_write_equal {α : Type} (old value : α) :
    ((EqOrDisj.equal old).write value).read = value := rfl

@[simp] theorem EqOrDisj.read_write_disjoint {α : Type}
    (leftValue rightValue value : α) :
    ((EqOrDisj.disjoint leftValue rightValue).write value).read =
      leftValue := rfl

/-! ## One view, cell by cell -/

/-- Ownership of one view: the `i`-th cell of `cells` holds the `i`-th value of
`values`.  Same model as `PulseArray.ownsCells`. -/
def ownsCells {α : Type} : List (Ptr α) → List α → SLProp
  | [], [] => emp
  | p :: ps, value :: values => iprop(p ↦ value ∗ ownsCells ps values)
  | _, _ => ⌜False⌝

@[simp] theorem ownsCells_nil {α : Type} :
    ownsCells ([] : List (Ptr α)) ([] : List α) = emp := rfl

@[simp] theorem ownsCells_cons {α : Type} (p : Ptr α) (ps : List (Ptr α))
    (value : α) (values : List α) :
    ownsCells (p :: ps) (value :: values) =
      iprop(p ↦ value ∗ ownsCells ps values) := rfl

/-- Ownership forces the two lists to have the same length. -/
theorem ownsCells.length_eq {α : Type} {cells : List (Ptr α)}
    {values : List α} {h : Heap} (hOwns : ownsCells cells values h) :
    cells.length = values.length := by
  induction cells generalizing values h with
  | nil =>
      cases values with
      | nil => rfl
      | cons value values => exact hOwns.1.elim
  | cons p cells ih =>
      cases values with
      | nil => exact hOwns.1.elim
      | cons value values =>
          obtain ⟨h₁, h₂, _, _, _, hTail⟩ := hOwns
          simp only [List.length_cons, ih hTail]

/-- Read the `i`-th cell of a view. -/
def readCells {α : Type} : List (Ptr α) → Nat → St (Option α)
  | [], _ => pure none
  | p :: _, 0 => do
      let value ← read p
      pure (some value)
  | _ :: ps, i + 1 => readCells ps i

/-- Write the `i`-th cell of a view; an out-of-range offset does nothing. -/
def writeCells {α : Type} : List (Ptr α) → Nat → α → St Unit
  | [], _, _ => pure ()
  | p :: _, 0, value => update p value
  | _ :: ps, i + 1, value => writeCells ps i value

@[step]
theorem readCells.spec {α : Type} (cells : List (Ptr α))
    (values : List α) (i : Nat) :
    ⦃ ownsCells cells values ⦄ readCells cells i
      ⦃⇓ result => ⌜result = values[i]?⌝ ∗ ownsCells cells values⦄ := by
  induction cells generalizing values i with
  | nil =>
      cases values with
      | nil =>
          simp only [readCells, List.getElem?_nil]
          sl_step*
      | cons value values =>
          sl_pull
          contradiction
  | cons p cells ih =>
      cases values with
      | nil =>
          sl_pull
          contradiction
      | cons value values =>
          cases i with
          | zero =>
              simp only [readCells, List.getElem?_cons_zero]
              sl_step*
          | succ i =>
              simp only [readCells, List.getElem?_cons_succ]
              sl_step with ih values i

@[step]
theorem writeCells.spec {α : Type} (cells : List (Ptr α))
    (values : List α) (i : Nat) (value : α) :
    ⦃ ownsCells cells values ⦄ writeCells cells i value
      ⦃⇓ ownsCells cells (values.set i value)⦄ := by
  induction cells generalizing values i with
  | nil =>
      cases values with
      | nil =>
          simp only [writeCells, List.set_nil]
          sl_step*
      | cons value values =>
          sl_pull
          contradiction
  | cons p cells ih =>
      cases values with
      | nil =>
          sl_pull
          contradiction
      | cons old values =>
          cases i with
          | zero =>
              simp only [writeCells, List.set_cons_zero]
              sl_step*
          | succ i =>
              simp only [writeCells, List.set_cons_succ]
              sl_step with ih values i

/-! ## The buffer -/

/-- The two views of an `InPlaceOrDisjointBuffer`, cell by cell.  The `len`
field of the Rust struct is the common length of the two, and its `PhantomData`
is the lifetime the borrow checker tracks; neither has a counterpart here. -/
structure InPlaceOrDisjointBuffer (α : Type) where
  srcCells : List (Ptr α)
  dstCells : List (Ptr α)

/-- Ownership of a buffer.  The aliased case owns *one* view and records that
the two are the same cells; the separated case owns two views of equal length —
`new_disjoint_from_slices` asserts that equality, and the Aeneas model states it
as the axiom `Buffer.length_eq`. -/
def owns {α : Type} (buffer : InPlaceOrDisjointBuffer α)
    (relation : EqOrDisj (List α)) : SLProp :=
  match relation with
  | .equal values =>
      iprop(⌜buffer.srcCells = buffer.dstCells⌝ ∗
        ownsCells buffer.dstCells values)
  | .disjoint srcValues dstValues =>
      iprop(⌜srcValues.length = dstValues.length⌝ ∗
        ownsCells buffer.srcCells srcValues ∗
        ownsCells buffer.dstCells dstValues)

/-! ### Construction

The four constructors build the same pair of views; what distinguishes them is
which ghost case they establish, and at what cost to the caller.  Three of them
are registered with `step`; `from_raw_parts` has one specification per legal
case of its `unsafe` contract, so it is the one entry whose case the caller
picks. -/

/-- `new_in_place(buffer: &'a mut [T])`: one slice, used as both views. -/
def InPlaceOrDisjointBuffer.new_in_place {α : Type}
    (cells : List (Ptr α)) : St (InPlaceOrDisjointBuffer α) :=
  pure ⟨cells, cells⟩

/-- `new_disjoint::<N>(src: &'a [T; N], dst: &'a mut [T; N])`: two arrays whose
common length is a type-level constant. -/
def InPlaceOrDisjointBuffer.new_disjoint {α : Type}
    (src dst : List (Ptr α)) : St (InPlaceOrDisjointBuffer α) :=
  pure ⟨src, dst⟩

/-- `new_disjoint_from_slices(src: &'a [T], dst: &'a mut [T])`: two slices, with
a run-time `assert_eq!` on their lengths. -/
def InPlaceOrDisjointBuffer.new_disjoint_from_slices {α : Type}
    (src dst : List (Ptr α)) : St (InPlaceOrDisjointBuffer α) :=
  pure ⟨src, dst⟩

/-- `unsafe from_raw_parts(src, dst, len)`: the C boundary, and the only
constructor that can produce either case. -/
def InPlaceOrDisjointBuffer.from_raw_parts {α : Type}
    (src dst : List (Ptr α)) : St (InPlaceOrDisjointBuffer α) :=
  pure ⟨src, dst⟩

/-- A `&mut [T]` is a whole view, so `new_in_place` yields the aliased case. -/
@[step]
theorem InPlaceOrDisjointBuffer.new_in_place.spec {α : Type}
    (cells : List (Ptr α)) (values : List α) :
    ⦃ ownsCells cells values ⦄ InPlaceOrDisjointBuffer.new_in_place cells
      ⦃⇓ buffer => owns buffer (.equal values)⦄ := by
  simp only [InPlaceOrDisjointBuffer.new_in_place, owns]
  sl_pure
  exact hpure_hstar_intro _ rfl

/-- `&[T; N]` and `&mut [T; N]` cannot alias and have the same length, so the
caller owes only the two views. -/
@[step]
theorem InPlaceOrDisjointBuffer.new_disjoint.spec {α : Type} (n : Nat)
    (src dst : List (Ptr α)) (srcValues dstValues : List α)
    (hSrc : srcValues.length = n) (hDst : dstValues.length = n) :
    ⦃ ownsCells src srcValues ∗ ownsCells dst dstValues ⦄
      InPlaceOrDisjointBuffer.new_disjoint src dst
    ⦃⇓ buffer => owns buffer (.disjoint srcValues dstValues)⦄ := by
  simp only [InPlaceOrDisjointBuffer.new_disjoint, owns]
  sl_pure
  exact hpure_hstar_intro _ (hSrc.trans hDst.symm)

/-- Same, with the length equality the Rust code asserts at run time. -/
@[step]
theorem InPlaceOrDisjointBuffer.new_disjoint_from_slices.spec {α : Type}
    (src dst : List (Ptr α)) (srcValues dstValues : List α)
    (hLength : srcValues.length = dstValues.length) :
    ⦃ ownsCells src srcValues ∗ ownsCells dst dstValues ⦄
      InPlaceOrDisjointBuffer.new_disjoint_from_slices src dst
    ⦃⇓ buffer => owns buffer (.disjoint srcValues dstValues)⦄ := by
  simp only [InPlaceOrDisjointBuffer.new_disjoint_from_slices, owns]
  sl_pure
  exact hpure_hstar_intro _ hLength

/-- `from_raw_parts` with two pointers to the same memory.  The caller owns one
view and gets the aliased case. -/
theorem InPlaceOrDisjointBuffer.from_raw_parts.equal_spec {α : Type}
    (cells : List (Ptr α)) (values : List α) :
    ⦃ ownsCells cells values ⦄
      InPlaceOrDisjointBuffer.from_raw_parts cells cells
    ⦃⇓ buffer => owns buffer (.equal values)⦄ := by
  simp only [InPlaceOrDisjointBuffer.from_raw_parts, owns]
  sl_pure
  exact hpure_hstar_intro _ rfl

/-- `from_raw_parts` with two pointers to separated memory.  Owning the two
views separately *is* the disjointness half of the `unsafe` contract; the
partial overlap it also rules out cannot be stated in the first place. -/
theorem InPlaceOrDisjointBuffer.from_raw_parts.disjoint_spec {α : Type}
    (src dst : List (Ptr α)) (srcValues dstValues : List α)
    (hLength : srcValues.length = dstValues.length) :
    ⦃ ownsCells src srcValues ∗ ownsCells dst dstValues ⦄
      InPlaceOrDisjointBuffer.from_raw_parts src dst
    ⦃⇓ buffer => owns buffer (.disjoint srcValues dstValues)⦄ := by
  simp only [InPlaceOrDisjointBuffer.from_raw_parts, owns]
  sl_pure
  exact hpure_hstar_intro _ hLength

/-! ### Length -/

/-- `len(&self) -> usize`. -/
def InPlaceOrDisjointBuffer.len {α : Type}
    (buffer : InPlaceOrDisjointBuffer α) : St Nat :=
  pure buffer.srcCells.length

/-- `len` is the common length of the two views.  The second conjunct is the
Aeneas axiom `Buffer.length_eq`; here it is a theorem. -/
@[step]
theorem InPlaceOrDisjointBuffer.len.spec {α : Type}
    (buffer : InPlaceOrDisjointBuffer α) (relation : EqOrDisj (List α)) :
    ⦃ owns buffer relation ⦄ buffer.len
      ⦃⇓ n =>
        ⌜n = relation.read.length ∧
          relation.read.length = relation.written.length⌝ ∗
        owns buffer relation⦄ := by
  simp only [InPlaceOrDisjointBuffer.len]
  sl_pure
  intro h hBuffer
  refine hpure_hstar_intro _ ?_ h hBuffer
  cases relation with
  | equal values =>
      simp only [owns] at hBuffer
      obtain ⟨h₁, h₂, _, _, ⟨hSame, _⟩, hOwns⟩ := hBuffer
      simp only [EqOrDisj.read, EqOrDisj.written, hSame, and_true]
      exact ownsCells.length_eq hOwns
  | disjoint srcValues dstValues =>
      simp only [owns] at hBuffer
      obtain ⟨h₁, h₂, _, _, ⟨hLength, _⟩, hViews⟩ := hBuffer
      obtain ⟨h₃, h₄, _, _, hSrc, _⟩ := hViews
      exact ⟨ownsCells.length_eq hSrc, hLength⟩

/-! ### The `_si128` accessors

The three `unsafe` entries the stitched AES-GCM kernel runs on.  Their offsets
are cell offsets, and the value moved is one cell. -/

/-- `loadu_si128_src(&self, offset)`. -/
def InPlaceOrDisjointBuffer.loadu_si128_src {α : Type}
    (buffer : InPlaceOrDisjointBuffer α) (i : Nat) : St (Option α) :=
  readCells buffer.srcCells i

/-- `loadu_si128_dst(&self, offset)`: reading *back* the write view, which
AES-GCM needs in order to feed GHASH with the ciphertext it has just stored. -/
def InPlaceOrDisjointBuffer.loadu_si128_dst {α : Type}
    (buffer : InPlaceOrDisjointBuffer α) (i : Nat) : St (Option α) :=
  readCells buffer.dstCells i

/-- `storeu_si128(&mut self, offset, value)`. -/
def InPlaceOrDisjointBuffer.storeu_si128 {α : Type}
    (buffer : InPlaceOrDisjointBuffer α) (i : Nat) (value : α) : St Unit :=
  writeCells buffer.dstCells i value

@[step]
theorem InPlaceOrDisjointBuffer.loadu_si128_src.spec {α : Type}
    (buffer : InPlaceOrDisjointBuffer α) (relation : EqOrDisj (List α))
    (i : Nat) :
    ⦃ owns buffer relation ⦄ buffer.loadu_si128_src i
      ⦃⇓ result =>
        ⌜result = relation.read[i]?⌝ ∗ owns buffer relation⦄ := by
  cases relation with
  | equal values =>
      simp only [owns, InPlaceOrDisjointBuffer.loadu_si128_src, EqOrDisj.read]
      sl_pull hSame
      rw [hSame]
      sl_step*
  | disjoint srcValues dstValues =>
      simp only [owns, InPlaceOrDisjointBuffer.loadu_si128_src, EqOrDisj.read]
      sl_step*

@[step]
theorem InPlaceOrDisjointBuffer.loadu_si128_dst.spec {α : Type}
    (buffer : InPlaceOrDisjointBuffer α) (relation : EqOrDisj (List α))
    (i : Nat) :
    ⦃ owns buffer relation ⦄ buffer.loadu_si128_dst i
      ⦃⇓ result =>
        ⌜result = relation.written[i]?⌝ ∗ owns buffer relation⦄ := by
  cases relation <;>
    simp only [owns, InPlaceOrDisjointBuffer.loadu_si128_dst,
      EqOrDisj.written] <;>
    sl_step*

/-- The store law.  Nothing else is needed to know what the read view holds
afterwards: `EqOrDisj.write` keeps a single list in the aliased case, so the two
views cannot drift apart. -/
@[step]
theorem InPlaceOrDisjointBuffer.storeu_si128.spec {α : Type}
    (buffer : InPlaceOrDisjointBuffer α) (relation : EqOrDisj (List α))
    (i : Nat) (value : α) :
    ⦃ owns buffer relation ⦄ buffer.storeu_si128 i value
      ⦃⇓ owns buffer
          (relation.write (relation.written.set i value))⦄ := by
  cases relation <;>
    simp only [owns, InPlaceOrDisjointBuffer.storeu_si128, EqOrDisj.write,
      EqOrDisj.written, List.length_set] <;>
    sl_step*

/-! ### The whole-view borrows

```rust
pub fn src(&self) -> &[T] { … }
pub fn dst(&mut self) -> &mut [T] { … }
```

The stitched kernel hands those slices to GHASH — `&buffer.dst()[o .. o + 8 *
AES_BLOCK_SIZE]` in the encryption kernel, `buffer.src()` in the decryption
one.
They are *borrows*: `src` lends the read view and takes it back unchanged, `dst`
lends the write view and takes it back holding whatever the borrower left in it,
which in the aliased case is also what the read view holds afterwards.  This
logic has no fractional permissions, so a borrow is full ownership plus a wand
giving it back; the wand plays the role of the back-function Aeneas gives
`dst`. -/

/-- Lend `lent`, keep `frame`, and take the loan back to restore `restored`. -/
theorem borrow_intro {lent frame loan restored : SLProp}
    (hBack : loan ∗ frame ⊢ restored) :
    lent ∗ frame ⊢ lent ∗ (loan -∗ restored) :=
  hstar_mono (himpl_refl lent) (hwand_intro hBack)

/-- The same, for a loan given back holding different contents `x`. -/
theorem borrow_intro_forall {ι : Sort _} {lent frame : SLProp}
    {loan restored : ι → SLProp}
    (hBack : ∀ x, loan x ∗ frame ⊢ restored x) :
    lent ∗ frame ⊢ lent ∗ (∀ˢ x, loan x -∗ restored x) :=
  hstar_mono (himpl_refl lent)
    (hforall_intro fun x => hwand_intro (hBack x))

/-- `src(&self) -> &[T]`. -/
def InPlaceOrDisjointBuffer.src {α : Type}
    (buffer : InPlaceOrDisjointBuffer α) : St (List (Ptr α)) :=
  pure buffer.srcCells

/-- `dst(&mut self) -> &mut [T]`. -/
def InPlaceOrDisjointBuffer.dst {α : Type}
    (buffer : InPlaceOrDisjointBuffer α) : St (List (Ptr α)) :=
  pure buffer.dstCells

/-- `src` lends the read view, which the borrower gives back unchanged. -/
@[step]
theorem InPlaceOrDisjointBuffer.src.spec {α : Type}
    (buffer : InPlaceOrDisjointBuffer α) (relation : EqOrDisj (List α)) :
    ⦃ owns buffer relation ⦄ buffer.src
      ⦃⇓ cells =>
        ⌜cells = buffer.srcCells⌝ ∗
        ownsCells cells relation.read ∗
          (ownsCells cells relation.read -∗ owns buffer relation)⦄ := by
  simp only [InPlaceOrDisjointBuffer.src]
  sl_pure
  refine himpl_trans ?_ (hpure_hstar_intro _ rfl)
  cases relation with
  | equal values =>
      simp only [owns, EqOrDisj.read]
      apply himpl_hpure_l
      intro hSame
      rw [hSame]
      refine himpl_trans (himpl_of_eq (hstar_hempty_r_eq _).symm)
        (borrow_intro ?_)
      exact himpl_trans (himpl_of_eq (hstar_hempty_r_eq _))
        (hpure_hstar_intro _ rfl)
  | disjoint srcValues dstValues =>
      simp only [owns, EqOrDisj.read]
      apply himpl_hpure_l
      intro hLength
      exact borrow_intro (hpure_hstar_intro _ hLength)

/-- `dst` lends the write view.  Giving it back holding `values` moves the ghost
state by `EqOrDisj.write`, so the aliased case records that the read view has
changed as well.  A `&mut [T]` cannot be resized, whence the length premise. -/
@[step]
theorem InPlaceOrDisjointBuffer.dst.spec {α : Type}
    (buffer : InPlaceOrDisjointBuffer α) (relation : EqOrDisj (List α)) :
    ⦃ owns buffer relation ⦄ buffer.dst
      ⦃⇓ cells =>
        ⌜cells = buffer.dstCells⌝ ∗
        ownsCells cells relation.written ∗
          (∀ˢ values,
            ⌜values.length = relation.written.length⌝ ∗
                ownsCells cells values -∗
              owns buffer (relation.write values))⦄ := by
  simp only [InPlaceOrDisjointBuffer.dst]
  sl_pure
  refine himpl_trans ?_ (hpure_hstar_intro _ rfl)
  cases relation with
  | equal values =>
      simp only [owns, EqOrDisj.written, EqOrDisj.write]
      apply himpl_hpure_l
      intro hSame
      refine himpl_trans (himpl_of_eq (hstar_hempty_r_eq _).symm)
        (borrow_intro_forall fun newValues => ?_)
      refine himpl_trans (himpl_of_eq (hstar_hempty_r_eq _)) ?_
      apply himpl_hpure_l
      intro _
      exact hpure_hstar_intro _ hSame
  | disjoint srcValues dstValues =>
      simp only [owns, EqOrDisj.written, EqOrDisj.write]
      apply himpl_hpure_l
      intro hLength
      refine himpl_trans (himpl_of_eq (hstar_comm_eq _ _))
        (borrow_intro_forall fun newValues => ?_)
      refine himpl_trans (himpl_of_eq (hstar_assoc_eq _ _ _)) ?_
      apply himpl_hpure_l
      intro hNew
      exact himpl_trans (himpl_of_eq (hstar_comm_eq _ _))
        (hpure_hstar_intro _ (hLength.trans hNew.symm))

/-- `ghash_append(&buffer.src()[..])`: take the read view out and read it. -/
def load_through_src {α : Type} (buffer : InPlaceOrDisjointBuffer α)
    (i : Nat) : St (Option α) := do
  let cells ← buffer.src
  readCells cells i

/-- `buffer.dst()[i] = value`: take the write view out and write through it. -/
def store_through_dst {α : Type} (buffer : InPlaceOrDisjointBuffer α)
    (i : Nat) (value : α) : St Unit := do
  let cells ← buffer.dst
  writeCells cells i value

/-- Reading through the borrowed read view agrees with `loadu_si128_src`: the
loan comes back and the buffer is intact. -/
theorem InPlaceOrDisjointBuffer.src.roundTrip {α : Type}
    (buffer : InPlaceOrDisjointBuffer α) (relation : EqOrDisj (List α))
    (i : Nat) :
    ⦃ owns buffer relation ⦄ load_through_src buffer i
      ⦃⇓ result =>
        ⌜result = relation.read[i]?⌝ ∗ owns buffer relation⦄ := by
  simp only [load_through_src]
  sl_step
  refine triple_conseq_frame
    (H₂ := iprop(ownsCells buffer.srcCells relation.read -∗
      owns buffer relation))
    (readCells.spec buffer.srcCells relation.read i) (himpl_refl _) ?_
  intro result
  exact himpl_trans (himpl_of_eq (hstar_assoc_eq _ _ _))
    (hstar_mono (himpl_refl _) (hwand_cancel _ _))

/-- Writing through the borrowed write view agrees with `storeu_si128`.  The two
specifications are proved independently — `storeu_si128.spec` by case analysis,
this one by cancelling the wand of `dst.spec` — so their agreement is a check
that the borrow is not vacuous. -/
theorem InPlaceOrDisjointBuffer.dst.roundTrip {α : Type}
    (buffer : InPlaceOrDisjointBuffer α) (relation : EqOrDisj (List α))
    (i : Nat) (value : α) :
    ⦃ owns buffer relation ⦄ store_through_dst buffer i value
      ⦃⇓ owns buffer
          (relation.write (relation.written.set i value))⦄ := by
  simp only [store_through_dst]
  sl_step
  refine triple_conseq_frame
    (H₂ := iprop(∀ˢ values,
      ⌜values.length = relation.written.length⌝ ∗
          ownsCells buffer.dstCells values -∗
        owns buffer (relation.write values)))
    (writeCells.spec buffer.dstCells relation.written i value)
    (himpl_refl _) ?_
  intro _
  have hLength :
      (relation.written.set i value).length = relation.written.length := by
    simp
  refine himpl_trans (hstar_mono
    (hpure_hstar_intro
      (ownsCells buffer.dstCells (relation.written.set i value)) hLength)
    (hforall_specialize (relation.written.set i value))) ?_
  exact hwand_cancel _ _

/-! ## What the pattern is about

A store followed by a read of the *source*: the interface is used identically in
both cases, and the ghost state alone says what comes back. -/

/-- Store, then read the read view back at the same offset. -/
def storeThenLoadSrc {α : Type} (buffer : InPlaceOrDisjointBuffer α) (i : Nat)
    (value : α) : St (Option α) := do
  buffer.storeu_si128 i value
  buffer.loadu_si128_src i

/-- Store, then read the write view back at the same offset, as the stitched
kernel does before absorbing a block into GHASH. -/
def storeThenLoadDst {α : Type} (buffer : InPlaceOrDisjointBuffer α) (i : Nat)
    (value : α) : St (Option α) := do
  buffer.storeu_si128 i value
  buffer.loadu_si128_dst i

theorem storeThenLoadSrc.spec {α : Type} (buffer : InPlaceOrDisjointBuffer α)
    (relation : EqOrDisj (List α)) (i : Nat) (value : α) :
    ⦃ owns buffer relation ⦄ storeThenLoadSrc buffer i value
      ⦃⇓ result =>
        ⌜result =
          (relation.write (relation.written.set i value)).read[i]?⌝ ∗
        owns buffer
          (relation.write (relation.written.set i value))⦄ := by
  simp only [storeThenLoadSrc]
  sl_step*

/-- The read-back returns the stored value in both cases. -/
theorem storeThenLoadDst.spec {α : Type} (buffer : InPlaceOrDisjointBuffer α)
    (relation : EqOrDisj (List α)) (i : Nat) (value : α) :
    ⦃ owns buffer relation ⦄ storeThenLoadDst buffer i value
      ⦃⇓ result =>
        ⌜result = (relation.written.set i value)[i]?⌝ ∗
        owns buffer
          (relation.write (relation.written.set i value))⦄ := by
  simp only [storeThenLoadDst]
  sl_step*

/-- Aliased: the store *is* visible through the read view — the plaintext the
buffer came in with is gone.  A model that gives a buffer two independent views
and lets every store preserve the read one cannot state this. -/
example {α : Type} (buffer : InPlaceOrDisjointBuffer α) (values : List α)
    (i : Nat) (value : α) :
    ⦃ owns buffer (.equal values) ⦄ storeThenLoadSrc buffer i value
      ⦃⇓ result =>
        ⌜result = (values.set i value)[i]?⌝ ∗
        owns buffer (.equal (values.set i value))⦄ :=
  storeThenLoadSrc.spec buffer (.equal values) i value

/-- Separated: the read view still holds the value it came in with. -/
example {α : Type} (buffer : InPlaceOrDisjointBuffer α)
    (srcValues dstValues : List α) (i : Nat) (value : α) :
    ⦃ owns buffer (.disjoint srcValues dstValues) ⦄
      storeThenLoadSrc buffer i value
    ⦃⇓ result =>
        ⌜result = srcValues[i]?⌝ ∗
        owns buffer (.disjoint srcValues (dstValues.set i value))⦄ :=
  storeThenLoadSrc.spec buffer (.disjoint srcValues dstValues) i value

/-! ## The 128-bit instance

`loadu_si128_src`, `loadu_si128_dst` and `storeu_si128` move a `__m128i`, i.e.
128 bits, at a byte offset into an `InPlaceOrDisjointBuffer<u8>`.  Nothing above
depends on the width, so it is enough to take one cell per 128-bit lane: the
cells hold `Std.U128`, and offsets count lanes. -/

/-- `m128_loadu_src` of `aes_xmm.rs`'s `BufferM128`. -/
def InPlaceOrDisjointBuffer.m128_loadu_src
    (buffer : InPlaceOrDisjointBuffer Std.U128) (i : Nat) :
    St (Option Std.U128) :=
  buffer.loadu_si128_src i

/-- `m128_loadu_dst`. -/
def InPlaceOrDisjointBuffer.m128_loadu_dst
    (buffer : InPlaceOrDisjointBuffer Std.U128) (i : Nat) :
    St (Option Std.U128) :=
  buffer.loadu_si128_dst i

/-- `m128_storeu`. -/
def InPlaceOrDisjointBuffer.m128_storeu
    (buffer : InPlaceOrDisjointBuffer Std.U128) (i : Nat)
    (value : Std.U128) : St Unit :=
  buffer.storeu_si128 i value

@[step]
theorem InPlaceOrDisjointBuffer.m128_loadu_src.spec
    (buffer : InPlaceOrDisjointBuffer Std.U128)
    (relation : EqOrDisj (List Std.U128)) (i : Nat) :
    ⦃ owns buffer relation ⦄ InPlaceOrDisjointBuffer.m128_loadu_src buffer i
      ⦃⇓ result =>
        ⌜result = relation.read[i]?⌝ ∗ owns buffer relation⦄ := by
  simp only [InPlaceOrDisjointBuffer.m128_loadu_src]
  sl_step*

@[step]
theorem InPlaceOrDisjointBuffer.m128_loadu_dst.spec
    (buffer : InPlaceOrDisjointBuffer Std.U128)
    (relation : EqOrDisj (List Std.U128)) (i : Nat) :
    ⦃ owns buffer relation ⦄ InPlaceOrDisjointBuffer.m128_loadu_dst buffer i
      ⦃⇓ result =>
        ⌜result = relation.written[i]?⌝ ∗ owns buffer relation⦄ := by
  simp only [InPlaceOrDisjointBuffer.m128_loadu_dst]
  sl_step*

@[step]
theorem InPlaceOrDisjointBuffer.m128_storeu.spec
    (buffer : InPlaceOrDisjointBuffer Std.U128)
    (relation : EqOrDisj (List Std.U128)) (i : Nat) (value : Std.U128) :
    ⦃ owns buffer relation ⦄ InPlaceOrDisjointBuffer.m128_storeu buffer i value
      ⦃⇓ owns buffer
          (relation.write (relation.written.set i value))⦄ := by
  simp only [InPlaceOrDisjointBuffer.m128_storeu]
  sl_step*

/-- The lane at a stored offset reads back as the stored lane, through the write
view, in both cases — the read-back the stitched kernel relies on. -/
example (buffer : InPlaceOrDisjointBuffer Std.U128)
    (relation : EqOrDisj (List Std.U128))
    (i : Nat) (value : Std.U128)
    (hBound : i < relation.written.length) :
    ⦃ owns buffer relation ⦄ storeThenLoadDst buffer i value
      ⦃⇓ result =>
        ⌜result = some value⌝ ∗
        owns buffer
          (relation.write (relation.written.set i value))⦄ := by
  refine triple_conseq (storeThenLoadDst.spec buffer relation i value)
    (himpl_refl _) ?_
  intro result
  apply himpl_hpure_l
  intro hResult
  refine hpure_hstar_intro _ ?_
  rw [hResult]
  simp [hBound]

end Examples

end Aeneas.SLPoC
