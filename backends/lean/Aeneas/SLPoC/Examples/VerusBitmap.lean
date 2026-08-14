import Aeneas.SLPoC.Examples.PulseArrayTests

/-!
# Verus bitmap

This module is a Lean SLPoC port of
[`verus-lang/verus/examples/bitmap.rs`](https://github.com/verus-lang/verus/blob/main/examples/bitmap.rs).
It corresponds to the source `u64_view`, `BitMap::from`, `BitMap::get_bit`,
`BitMap::set_bit`, and `BitMap::or`, together with the three word-level
bit-vector proof functions.

The Rust `Vec<u64>` is represented by the stable cell-wise
`Aeneas.SLPoC.PulseArray.Array` model.  A `Word` contains a natural-number bit
mask proved smaller than `2^64`; executable word operations use `Nat.testBit`,
shifts, OR, XOR, and reduction modulo `2^64`.  Thus the executable bitmap is
not replaced by a Boolean array.  As in the source, public bit operations
require an index below `64 * numberOfWords`, and bitmap OR requires equal word
counts.  The source's `u32`/`usize` cast concern is absent because Lean indices
are unbounded naturals.

Rust permits the two shared references passed to `BitMap::or` to alias.  The
actual `bitmapOr bitmap bitmap` execution is proved below with one ownership
resource: it reads each shared cell twice sequentially and preserves it.  The
separate `bitmapOrSelf` definition is only an optional one-read optimization;
its result is logically equal, but it is not used to justify source aliasing.
-/

namespace Aeneas.SLPoC

open scoped SepLogic

namespace VerusBitmap

/-! # Executable definitions -/

/-- The fixed width of the source `u64` buckets. -/
def wordWidth : Nat := 64

/-- One more than the largest source `u64` value. -/
def wordModulus : Nat := 2 ^ wordWidth

/-- A machine-word-style natural-number mask, normalized to 64 bits. -/
structure Word where
  val : Nat
  isLt : val < wordModulus

/-- Normalize an arbitrary natural-number mask to one source `u64`. -/
def mkWord (value : Nat) : Word :=
  ⟨value % wordModulus, Nat.mod_lt _ (by simp [wordModulus])⟩

/-- The all-zero word. -/
def zeroWord : Word := mkWord 0

/-- Source `get_bit64_macro!`: inspect one bit of a word. -/
def getWordBit (word : Word) (index : Nat) : Bool :=
  word.val.testBit index

/-- A one-bit natural-number mask. -/
def bitMask (index : Nat) : Nat :=
  1 <<< index

/-- Source `set_bit64_macro!`.

Setting uses OR.  Clearing XORs the selected mask only when that bit is
currently set.  The final reduction models the fixed-width `u64` result. -/
def setWordBit (word : Word) (index : Nat) (bit : Bool) : Word :=
  mkWord <|
    if bit then
      word.val ||| bitMask index
    else if getWordBit word index then
      word.val ^^^ bitMask index
    else
      word.val

/-- Source word-level bitwise OR. -/
def orWord (left right : Word) : Word :=
  mkWord (left.val ||| right.val)

/-- The source bitmap, backed by PulseArray's separately owned word cells. -/
structure Bitmap where
  bits : PulseArray.Array Word

/-- Source `BitMap::from`: wrap an existing word array without changing it. -/
def fromArray (bits : PulseArray.Array Word) : Bitmap :=
  ⟨bits⟩

/-- Number of represented bits. -/
def bitLengthFromWordCount (wordCount : Nat) : Nat :=
  wordCount * wordWidth

/-- Bucket containing a global bit index. -/
def bucketIndex (index : Nat) : Nat :=
  index / wordWidth

/-- Position within the selected bucket. -/
def bitIndex (index : Nat) : Nat :=
  index % wordWidth

/-- Source `BitMap::get_bit`.

The default branch makes the executable total; the specification proves it is
unreachable under the source bound. -/
def getBit (bitmap : Bitmap) (index : Nat) : St Bool := do
  let bucket ← PulseArray.readAt bitmap.bits (bucketIndex index)
  pure (getWordBit (bucket.getD zeroWord) (bitIndex index))

/-- Pure word-list update performed by `setBit`. -/
def setWords (words : List Word) (index : Nat) (bit : Bool) : List Word :=
  let bucket := bucketIndex index
  let oldWord := words[bucket]?.getD zeroWord
  words.set bucket (setWordBit oldWord (bitIndex index) bit)

/-- Source `BitMap::set_bit`.

As for `getBit`, the operation is total, while its exact specification assumes
the source bound and proves that the write succeeds. -/
def setBit (bitmap : Bitmap) (index : Nat) (bit : Bool) : St Unit := do
  let bucket ← PulseArray.readAt bitmap.bits (bucketIndex index)
  let newWord := setWordBit (bucket.getD zeroWord) (bitIndex index) bit
  let _ ← PulseArray.writeAt bitmap.bits (bucketIndex index) newWord
  pure ()

/-- Pure bucket-wise OR, matching the result vector built by the source loop. -/
def orWords (left right : List Word) : List Word :=
  (left.zip right).map fun pair => orWord pair.1 pair.2

/-- Allocate result cells while preserving both input arrays.

The unequal-shape branches make the executable total.  The public OR
specification assumes equal word counts, as does the Verus source. -/
def orCells : List (Ptr Word) → List (Ptr Word) → St (List (Ptr Word))
  | left :: lefts, right :: rights => do
      let leftWord ← read left
      let rightWord ← read right
      let result ← alloc (orWord leftWord rightWord)
      let results ← orCells lefts rights
      pure (result :: results)
  | _, _ => pure []

/-- Source `BitMap::or`: allocate a fresh bitmap containing bucket-wise OR. -/
def bitmapOr (left right : Bitmap) : St Bitmap := do
  let cells ← orCells left.bits.cells right.bits.cells
  pure ⟨⟨cells⟩⟩

/-- Pure exact-self OR words. -/
def orSelfWords (words : List Word) : List Word :=
  words.map fun word => orWord word word

/-- Exact-self specialization of the source OR loop.

Each input cell is read once, remains owned, and contributes a fresh result
cell containing `orWord word word`. -/
def orSelfCells : List (Ptr Word) → St (List (Ptr Word))
  | [] => pure []
  | cell :: cells => do
      let word ← read cell
      let result ← alloc (orWord word word)
      let results ← orSelfCells cells
      pure (result :: results)

/-- Optional one-read optimization of exact-self OR.

The actual aliased source execution remains `bitmapOr bitmap bitmap` and has a
separate specification below. -/
def bitmapOrSelf (bitmap : Bitmap) : St Bitmap := do
  let cells ← orSelfCells bitmap.bits.cells
  pure ⟨⟨cells⟩⟩

/-! # Ghost state, specifications and proofs -/

/-- The finite Boolean-sequence view of a word list.

`bitLength words` is its length; outside that length this total observation
function returns `false`. -/
def bitView (words : List Word) (index : Nat) : Bool :=
  match words[bucketIndex index]? with
  | some word => getWordBit word (bitIndex index)
  | none => false

/-- Length of the Boolean-sequence view. -/
def bitLength (words : List Word) : Nat :=
  bitLengthFromWordCount words.length

/-- Exact ownership of every word cell in a bitmap. -/
def rep (bitmap : Bitmap) (words : List Word) : SLProp :=
  PulseArray.owns bitmap.bits words

@[simp] theorem wordWidth_pos : 0 < wordWidth := by
  decide

@[simp] theorem bitMask_eq (index : Nat) :
    bitMask index = 2 ^ index := by
  simp [bitMask, Nat.shiftLeft_eq]

/-- Normalization does not change an in-range bit. -/
theorem getWordBit_mkWord (value index : Nat) (hindex : index < wordWidth) :
    getWordBit (mkWord value) index = value.testBit index := by
  simp [getWordBit, mkWord, wordModulus, Nat.testBit_mod_two_pow, hindex]

/-- Word-level refinement of the Verus `set_bit64_proof`, selected location. -/
theorem getWordBit_setWordBit_same (word : Word) (index : Nat) (bit : Bool)
    (hindex : index < wordWidth) :
    getWordBit (setWordBit word index bit) index = bit := by
  unfold setWordBit
  rw [getWordBit_mkWord _ _ hindex]
  cases bit with
  | false =>
      cases hset : word.val.testBit index with
      | false => simp [getWordBit, hset]
      | true =>
          simp [getWordBit, hset, bitMask_eq, Nat.testBit_xor]
  | true =>
      simp [bitMask_eq, Nat.testBit_or]

/-- Word-level refinement of `set_bit64_proof`, every other location. -/
theorem getWordBit_setWordBit_other (word : Word) (index other : Nat) (bit : Bool)
    (hother : other < wordWidth) (hne : other ≠ index) :
    getWordBit (setWordBit word index bit) other = getWordBit word other := by
  unfold setWordBit
  rw [getWordBit_mkWord _ _ hother]
  cases bit with
  | false =>
      cases hset : word.val.testBit index with
      | false => simp [getWordBit, hset]
      | true =>
          simp [getWordBit, hset, bitMask_eq, Nat.testBit_xor,
            hne.symm]
  | true =>
      simp [getWordBit, bitMask_eq, Nat.testBit_or, hne.symm]

/-- Word-level refinement of the Verus `bit_or_64_proof`. -/
theorem getWordBit_orWord (left right : Word) (index : Nat)
    (hindex : index < wordWidth) :
    getWordBit (orWord left right) index =
      (getWordBit left index || getWordBit right index) := by
  unfold orWord
  rw [getWordBit_mkWord _ _ hindex]
  exact Nat.testBit_or _ _ _

/-- The logical bit view has exactly 64 bits per owned word. -/
@[simp] theorem bitLength_eq (words : List Word) :
    bitLength words = words.length * 64 := by
  rfl

/-- A source-level bit bound selects an existing word cell. -/
theorem bucketIndex_lt_length (words : List Word) (index : Nat)
    (hindex : index < bitLength words) :
    bucketIndex index < words.length := by
  unfold bucketIndex bitLength bitLengthFromWordCount wordWidth at *
  omega

/-- Every selected in-bounds bucket position is a valid `u64` bit index. -/
theorem bitIndex_lt_width (index : Nat) :
    bitIndex index < wordWidth := by
  unfold bitIndex
  exact Nat.mod_lt _ wordWidth_pos

/-- Refinement from the Boolean-sequence view to its selected concrete word. -/
theorem bitView_eq_getElem (words : List Word) (index : Nat)
    (hindex : index < bitLength words) :
    bitView words index =
      getWordBit
        (words[bucketIndex index]'(bucketIndex_lt_length words index hindex))
        (bitIndex index) := by
  have hbucket := bucketIndex_lt_length words index hindex
  simp [bitView, List.getElem?_eq_getElem hbucket]

/-- `setWords` preserves the exact number of represented bits. -/
@[simp] theorem bitLength_setWords (words : List Word) (index : Nat) (bit : Bool) :
    bitLength (setWords words index bit) = bitLength words := by
  simp [bitLength, bitLengthFromWordCount, setWords]

/-- Source-level set property at the selected bit. -/
theorem bitView_setWords_same (words : List Word) (index : Nat) (bit : Bool)
    (hindex : index < bitLength words) :
    bitView (setWords words index bit) index = bit := by
  have hbucket := bucketIndex_lt_length words index hindex
  have hbit := bitIndex_lt_width index
  simp [bitView, setWords, hbucket, getWordBit_setWordBit_same, hbit]

/-- Source-level set property away from the selected bit. -/
theorem bitView_setWords_other (words : List Word) (index other : Nat) (bit : Bool)
    (hindex : index < bitLength words) (hother : other < bitLength words)
    (hne : other ≠ index) :
    bitView (setWords words index bit) other = bitView words other := by
  have hbucket := bucketIndex_lt_length words index hindex
  have hotherBucket := bucketIndex_lt_length words other hother
  have hotherBit := bitIndex_lt_width other
  by_cases hbuckets : bucketIndex index = bucketIndex other
  · have hbits : bitIndex other ≠ bitIndex index := by
      intro heq
      apply hne
      have hbuckets' : index / wordWidth = other / wordWidth := by
        simpa [bucketIndex] using hbuckets
      have heq' : other % wordWidth = index % wordWidth := by
        simpa [bitIndex] using heq
      calc
        other = wordWidth * (other / wordWidth) + other % wordWidth := by
          symm
          exact Nat.div_add_mod other wordWidth
        _ = wordWidth * (index / wordWidth) + index % wordWidth := by
          rw [← hbuckets', heq']
        _ = index := Nat.div_add_mod index wordWidth
    simp [bitView, setWords, hotherBucket,
      hbuckets, getWordBit_setWordBit_other, hotherBit, hbits]
  · simp [bitView, setWords, hotherBucket, hbuckets]

/-- Complete source `Seq::update` characterization of bitmap set. -/
theorem bitView_setWords (words : List Word) (index : Nat) (bit : Bool)
    (hindex : index < bitLength words) (other : Nat)
    (hother : other < bitLength words) :
    bitView (setWords words index bit) other =
      if other = index then bit else bitView words other := by
  split
  · rename_i heq
    subst other
    exact bitView_setWords_same words index bit hindex
  · rename_i hne
    exact bitView_setWords_other words index other bit hindex hother hne

/-- Equal-size bucket-wise OR preserves the exact source bitmap length. -/
theorem length_orWords (left right : List Word)
    (hlength : left.length = right.length) :
    (orWords left right).length = left.length := by
  simp [orWords, hlength]

/-- Concrete lookup refinement for bucket-wise OR. -/
theorem getElem_orWords (left right : List Word) (index : Nat)
    (hlength : left.length = right.length) (hindex : index < left.length) :
    ((orWords left right)[index]'(by
        rw [length_orWords left right hlength]
        exact hindex)) =
      orWord (left[index]'hindex) (right[index]'(by omega)) := by
  simp [orWords, List.getElem_map, List.getElem_zip]

/-- Source-level pointwise-disjunction property of bitmap OR. -/
theorem bitView_orWords (left right : List Word)
    (hlength : left.length = right.length) (index : Nat)
    (hindex : index < bitLength left) :
    bitView (orWords left right) index =
      (bitView left index || bitView right index) := by
  have hleftBucket := bucketIndex_lt_length left index hindex
  have hrightLength : bitLength right = bitLength left := by
    simp [bitLength, bitLengthFromWordCount, hlength]
  have hrightBucket :=
    bucketIndex_lt_length right index (hrightLength ▸ hindex)
  have hresultLength := length_orWords left right hlength
  have hresultBucket : bucketIndex index < (orWords left right).length := by
    simpa [hresultLength] using hleftBucket
  rw [bitView_eq_getElem _ _ (by simpa [bitLength, bitLengthFromWordCount,
    hresultLength] using hindex)]
  rw [bitView_eq_getElem left index hindex]
  rw [bitView_eq_getElem right index (hrightLength ▸ hindex)]
  rw [getElem_orWords left right (bucketIndex index) hlength hleftBucket]
  exact getWordBit_orWord _ _ _ (bitIndex_lt_width index)

/-- Exact logical relation between the single-traversal self execution and
the original two-argument execution applied to the same bitmap. -/
theorem orSelfWords_eq_orWords_self (words : List Word) :
    orSelfWords words = orWords words words := by
  induction words with
  | nil => rfl
  | cons word words ih =>
      change orWord word word :: orSelfWords words =
        orWord word word :: orWords words words
      rw [ih]

/-- Exact-self OR preserves the source bitmap length. -/
@[simp] theorem length_orSelfWords (words : List Word) :
    (orSelfWords words).length = words.length := by
  simp [orSelfWords]

/-- Exact-self OR has the same pointwise Boolean view as
`bitmapOr bitmap bitmap`. -/
theorem bitView_orSelfWords (words : List Word) (index : Nat)
    (hindex : index < bitLength words) :
    bitView (orSelfWords words) index =
      (bitView words index || bitView words index) := by
  rw [orSelfWords_eq_orWords_self]
  exact bitView_orWords words words rfl index hindex

/-! ## Exact separation-logic specifications -/

/-- `from` preserves the exact PulseArray representation and ownership. -/
@[simp] theorem rep_fromArray (bits : PulseArray.Array Word) (words : List Word) :
    rep (fromArray bits) words = PulseArray.owns bits words := rfl

/-- Exact source `get_bit` specification: return the modeled bit and preserve
every word cell unchanged. -/
@[step]
theorem getBit.spec (bitmap : Bitmap) (words : List Word) (index : Nat)
    (hindex : index < bitLength words) :
    ⦃ rep bitmap words ⦄ getBit bitmap index
      ⦃⇓ bit => ⌜bit = bitView words index⌝ ∗ rep bitmap words⦄ := by
  unfold getBit
  sl_step with PulseArray.readAt.spec bitmap.bits words (bucketIndex index)
  
  have hin := bucketIndex_lt_length words index hindex
  simp only [List.getElem?_eq_getElem hin, Option.getD_some]
  rw [bitView_eq_getElem words index hindex]
  sl_step*

/-- Exact source `set_bit` specification.  Ownership is preserved at every
cell, with precisely the selected word replaced by the concrete mask update;
the pure conjunct states the complete Boolean-sequence update property. -/
@[step]
theorem setBit.spec (bitmap : Bitmap) (words : List Word) (index : Nat)
    (bit : Bool) (hindex : index < bitLength words) :
    ⦃ rep bitmap words ⦄ setBit bitmap index bit
      ⦃⇓ _ =>
        ⌜bitLength (setWords words index bit) = bitLength words ∧
          ∀ other, other < bitLength words →
            bitView (setWords words index bit) other =
              if other = index then bit else bitView words other⌝ ∗
        rep bitmap (setWords words index bit)⦄ := by
  unfold setBit
  sl_step with PulseArray.readAt.spec bitmap.bits words (bucketIndex index)
  
  have hin := bucketIndex_lt_length words index hindex
  sl_step
  have hPure :
      bitLength (setWords words index bit) = bitLength words ∧
        ∀ other, other < bitLength words →
          bitView (setWords words index bit) other =
            if other = index then bit else bitView words other := by
    constructor
    · exact bitLength_setWords words index bit
    · intro other hother
      exact bitView_setWords words index bit hindex other hother
  have hsetWords :
      words.set (bucketIndex index)
          (setWordBit (words[bucketIndex index]?.getD zeroWord)
            (bitIndex index) bit) =
        setWords words index bit := by
    rfl
  rw [hsetWords]
  sl_step*

/-- Recursive disjoint OR specification.  Both input cell lists remain owned
and unchanged, while every returned pointer is freshly allocated and owns the
corresponding bucket-wise OR word. -/
@[step]
theorem orCells.disjoint_spec (leftCells rightCells : List (Ptr Word))
    (leftWords rightWords : List Word)
    (hlength : leftWords.length = rightWords.length) :
    ⦃ PulseArray.ownsCells leftCells leftWords ∗
       PulseArray.ownsCells rightCells rightWords ⦄
      orCells leftCells rightCells
    ⦃⇓ resultCells =>
      PulseArray.ownsCells leftCells leftWords ∗
      PulseArray.ownsCells rightCells rightWords ∗
      PulseArray.ownsCells resultCells (orWords leftWords rightWords)⦄ := by
  induction leftCells generalizing leftWords rightCells rightWords with
  | nil =>
      cases leftWords with
      | cons word words =>
          sl_pull
          contradiction
      | nil =>
          cases rightWords with
          | cons word words =>
              simp at hlength
          | nil =>
              cases rightCells with
              | nil =>
                  simp only [orCells]
                  sl_pure
                  simp only [orWords, List.zip, PulseArray.ownsCells_nil]
                  sl_frame
              | cons right rights =>
                  simp only [PulseArray.ownsCells]
                  rw [hstar_comm_eq _ (⌜False⌝)]
                  apply triple_hpure
                  intro hfalse
                  contradiction
  | cons left leftCells ih =>
      cases leftWords with
      | nil =>
          sl_pull
          contradiction
      | cons leftWord leftWords =>
          cases rightCells with
          | nil =>
              cases rightWords with
              | nil =>
                  simp at hlength
              | cons rightWord rightWords =>
                  simp only [PulseArray.ownsCells]
                  rw [hstar_comm_eq _ (⌜False⌝)]
                  apply triple_hpure
                  intro hfalse
                  contradiction
          | cons right rightCells =>
              cases rightWords with
              | nil =>
                  simp only [PulseArray.ownsCells]
                  rw [hstar_comm_eq _ (⌜False⌝)]
                  apply triple_hpure
                  intro hfalse
                  contradiction
              | cons rightWord rightWords =>
                  simp only [PulseArray.ownsCells_cons, orCells, orWords,
                    List.zip_cons_cons, List.map_cons]
                  have htail : leftWords.length = rightWords.length := by
                    simpa using hlength
                  sl_step* 3
                  sl_step with ih rightCells leftWords rightWords htail
                  sl_pure
                  simp only [PulseArray.ownsCells_cons]
                  sl_frame

/-- Actual exact-self execution of `orCells cells cells` under one ownership
resource.  Each step reads the same pointer twice sequentially, retains its
ownership, allocates a fresh result cell, and recurses on the shared tail.

This theorem deliberately is not a `[step]` rule, avoiding ambiguity with the
disjoint rule for the same executable function. -/
theorem orCells.self_spec (cells : List (Ptr Word)) (words : List Word) :
    ⦃ PulseArray.ownsCells cells words ⦄
      orCells cells cells
    ⦃⇓ resultCells =>
      PulseArray.ownsCells cells words ∗
      PulseArray.ownsCells resultCells (orWords words words)⦄ := by
  induction cells generalizing words with
  | nil =>
      cases words with
      | nil =>
          simp only [orCells, orWords, List.zip, PulseArray.ownsCells_nil]
          sl_pure
          sl_frame
      | cons word words =>
          sl_pull
          contradiction
  | cons cell cells ih =>
      cases words with
      | nil =>
          sl_pull
          contradiction
      | cons word words =>
          simp only [PulseArray.ownsCells_cons, orCells, orWords,
            List.zip_cons_cons, List.map_cons]
          sl_step* 3
          sl_step with ih words
          sl_pure
          simp only [PulseArray.ownsCells_cons]
          sl_frame

/-- Recursive specification for the optional optimized self-OR helper.  One ownership resource suffices:
the input list remains owned and each returned pointer is freshly allocated
with the corresponding `orWord word word`. -/
@[step]
theorem orSelfCells.spec (cells : List (Ptr Word)) (words : List Word) :
    ⦃ PulseArray.ownsCells cells words ⦄
      orSelfCells cells
    ⦃⇓ resultCells =>
      PulseArray.ownsCells cells words ∗
      PulseArray.ownsCells resultCells (orSelfWords words)⦄ := by
  induction cells generalizing words with
  | nil =>
      cases words with
      | nil =>
          simp only [orSelfCells, orSelfWords, List.map_nil,
            PulseArray.ownsCells_nil]
          sl_pure
          sl_frame
      | cons word words =>
          sl_pull
          contradiction
  | cons cell cells ih =>
      cases words with
      | nil =>
          sl_pull
          contradiction
      | cons word words =>
          simp only [PulseArray.ownsCells_cons, orSelfCells, orSelfWords,
            List.map_cons]
          sl_step* 2
          sl_step with ih words
          sl_pure
          simp only [PulseArray.ownsCells_cons]
          sl_frame

/-- Complete specification for the optional optimized self-OR helper.  It uses
one ownership resource, preserves the input, and returns the same logical words
as the actual aliased source execution. -/
@[step]
theorem bitmapOrSelf.spec (bitmap : Bitmap) (words : List Word) :
    ⦃ rep bitmap words ⦄
      bitmapOrSelf bitmap
    ⦃⇓ result =>
      ⌜orSelfWords words = orWords words words ∧
        bitLength (orSelfWords words) = bitLength words ∧
        ∀ index, index < bitLength words →
          bitView (orSelfWords words) index =
            (bitView words index || bitView words index)⌝ ∗
      rep bitmap words ∗ rep result (orSelfWords words)⦄ := by
  unfold bitmapOrSelf rep
  sl_step with orSelfCells.spec bitmap.bits.cells words
  have hpure :
      orSelfWords words = orWords words words ∧
        bitLength (orSelfWords words) = bitLength words ∧
        ∀ index, index < bitLength words →
          bitView (orSelfWords words) index =
            (bitView words index || bitView words index) := by
    refine ⟨orSelfWords_eq_orWords_self words, ?_, ?_⟩
    · simp [bitLength, bitLengthFromWordCount]
    · intro index hindex
      exact bitView_orSelfWords words index hindex
  sl_pure
  sl_frame

/-- Complete exact specification of the legal source call
`bitmapOr bitmap bitmap`.  The executable is the original two-read OR:
one ownership resource is threaded through both sequential reads of every
shared cell, the input is preserved exactly, and the fresh result has the
source length and pointwise-disjunction view.

This theorem is intentionally not a `[step]` rule, so it cannot conflict with
the disjoint rule for `bitmapOr`. -/
theorem bitmapOr.self_spec (bitmap : Bitmap) (words : List Word) :
    ⦃ rep bitmap words ⦄
      bitmapOr bitmap bitmap
    ⦃⇓ result =>
      ⌜bitLength (orWords words words) = bitLength words ∧
        ∀ index, index < bitLength words →
          bitView (orWords words words) index =
            (bitView words index || bitView words index)⌝ ∗
      rep bitmap words ∗ rep result (orWords words words)⦄ := by
  unfold bitmapOr rep
  sl_step with orCells.self_spec bitmap.bits.cells words
  have hpure :
      bitLength (orWords words words) = bitLength words ∧
        ∀ index, index < bitLength words →
          bitView (orWords words words) index =
            (bitView words index || bitView words index) := by
    constructor
    · simp [bitLength, bitLengthFromWordCount, length_orWords]
    · intro index hindex
      exact bitView_orWords words words rfl index hindex
  sl_pure
  sl_frame

/-- Complete exact source `or` specification for the disjoint case.  Its two
input ownership resources require separate heap footprints; it preserves both
inputs, owns all fresh result cells, preserves the bitmap length, and proves
pointwise Boolean disjunction.  Exact self-aliasing is covered instead by
`bitmapOr.self_spec`, without duplicating ownership. -/
@[step]
theorem bitmapOr.disjoint_spec (left right : Bitmap)
    (leftWords rightWords : List Word)
    (hlength : leftWords.length = rightWords.length) :
    ⦃ rep left leftWords ∗ rep right rightWords ⦄
      bitmapOr left right
    ⦃⇓ result =>
      ⌜bitLength (orWords leftWords rightWords) = bitLength leftWords ∧
        ∀ index, index < bitLength leftWords →
          bitView (orWords leftWords rightWords) index =
            (bitView leftWords index || bitView rightWords index)⌝ ∗
      rep left leftWords ∗ rep right rightWords ∗
      rep result (orWords leftWords rightWords)⦄ := by
  unfold bitmapOr rep
  sl_step with orCells.disjoint_spec left.bits.cells right.bits.cells
    leftWords rightWords hlength
  have hpure :
      bitLength (orWords leftWords rightWords) = bitLength leftWords ∧
        ∀ index, index < bitLength leftWords →
          bitView (orWords leftWords rightWords) index =
            (bitView leftWords index || bitView rightWords index) := by
    constructor
    · simp [bitLength, bitLengthFromWordCount, length_orWords _ _ hlength]
    · intro index hindex
      exact bitView_orWords leftWords rightWords hlength index hindex
  sl_pure
  sl_frame

end VerusBitmap

end Aeneas.SLPoC
