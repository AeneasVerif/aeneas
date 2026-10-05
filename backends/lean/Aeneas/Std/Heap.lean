module

public import Mathlib.Data.Finmap
public import Aeneas.Data.Byte

public section

namespace Aeneas

/-- A partial commutative monoid (PCM), represented by a total union operation
whose meaningful inputs are selected by `Compatible`. -/
class PartialCommMonoid (α : Type u) [EmptyCollection α] [Union α] where
  Compatible : α → α → Prop
  compatible_comm {a b : α} : Compatible a b → Compatible b a
  compatible_empty_left (a : α) : Compatible ∅ a
  compatible_assoc (a b c : α) :
    Compatible a b ∧ Compatible (a ∪ b) c ↔
      Compatible b c ∧ Compatible a (b ∪ c)
  union_assoc {a b c : α} :
    Compatible a b → Compatible (a ∪ b) c →
      a ∪ b ∪ c = a ∪ (b ∪ c)
  empty_union (a : α) : ∅ ∪ a = a
  union_empty (a : α) : a ∪ ∅ = a
  union_comm_of_compatible {a b : α} :
    Compatible a b → a ∪ b = b ∪ a

end Aeneas

namespace Aeneas.Std

/-!
# The heap

The heap is byte-addressed.  An **address** is an allocation identifier
together with a byte offset into that allocation, and a heap is a finite map
from addresses to the bytes they hold:

```text
Loc  = AllocId × Nat
Heap = Loc ⇀ Byte            (finitely supported)
```

A value lives in the heap through its `ByteRepr`: a fixed-size encoding as a
list of bytes.  Reading at a type decodes the bytes found at an address, so
reinterpreting memory at another type is only a matter of decoding the same
bytes differently: casting a pointer does not touch the heap.

Two heaps compose when the addresses they use are disjoint, so `∪` is a plain
disjoint union.  Ownership is *byte-granular*, which is what lets one
allocation be owned a part at a time, and a value of any size be viewed as the
bytes it is made of.

[`RawPtr`](RawPtr.lean) builds the Rust pointer view on this heap.
-/

/- An allocation identifier is fresh and behaves like a monotonic
   counter, not a concrete address in machine memory. -/
abbrev AllocId := Nat

/-- An address: the allocation, and the byte of it this address names. -/
abbrev Loc := AllocId × Nat

/-- The address `i` bytes past `a`, in the same allocation. -/
@[expose]
def Loc.add (a : Loc) (i : Nat) : Loc := (a.1, a.2 + i)

@[simp] theorem Loc.fst_add (a : Loc) (i : Nat) : (a.add i).1 = a.1 := rfl

@[simp] theorem Loc.snd_add (a : Loc) (i : Nat) : (a.add i).2 = a.2 + i := rfl

@[simp] theorem Loc.add_zero (a : Loc) : a.add 0 = a := rfl

theorem Loc.add_add (a : Loc) (i j : Nat) : (a.add i).add j = a.add (i + j) := by
  simp [Loc.add, Nat.add_assoc]

/-- A fixed-size encoding of the values of `α` as bytes: what lets a value of `α`
live in the heap.  Decoding accepts exactly the encodings, so the bytes found
at an address determine the value they hold.  A value of `α` may only be read
or written at an offset that is a multiple of `align`, which divides `size` as
in Rust. -/
class ByteRepr (α : Type) where
  size : Nat
  align : Nat
  align_dvd_size : align ∣ size
  encode : α → List Byte
  decode : List Byte → Option α
  length_encode (x : α) : (encode x).length = size
  decode_encode (x : α) : decode (encode x) = some x
  encode_of_decode {bytes : List Byte} {x : α} :
    decode bytes = some x → encode x = bytes

/-! ## References -/

/-- A reference to a value in the heap: a bare address, the type being a
phantom index that constrains specifications only. -/
@[expose]
def Ref (_ : Type) := Loc

namespace Ref

instance instInhabited {α : Type} : Inhabited (Ref α) := ⟨((0 : AllocId), 0)⟩

instance instDecidableEq {α : Type} : DecidableEq (Ref α) :=
  inferInstanceAs (DecidableEq Loc)

@[expose]
def addr {α : Type} (r : Ref α) : Loc := r

end Ref

abbrev HeapImpl := Finmap fun _ : Loc => Byte

/-- A finite collection of bytes. -/
structure Heap where
  private mk ::
  private impl : HeapImpl

namespace Heap

private def lookup (h : Heap) (address : Loc) : Option Byte :=
  h.impl.lookup address

private def erase (h : Heap) (address : Loc) : Heap :=
  ⟨h.impl.erase address⟩

private def keys (h : Heap) :=
  h.impl.keys

private theorem ext_impl {h₁ h₂ : Heap}
    (hEq : h₁.impl = h₂.impl) : h₁ = h₂ := by
  cases h₁
  cases h₂
  cases hEq
  rfl

private theorem ext_lookup {h₁ h₂ : Heap}
    (hEq : ∀ address, h₁.lookup address = h₂.lookup address) : h₁ = h₂ :=
  ext_impl (Finmap.ext_lookup hEq)

def empty : Heap := ⟨∅⟩

instance instEmptyCollection : EmptyCollection Heap := ⟨empty⟩

def union (h₁ h₂ : Heap) : Heap := ⟨h₁.impl ∪ h₂.impl⟩

instance instUnion : Union Heap := ⟨Heap.union⟩

def mem (address : Loc) (h : Heap) : Prop :=
  address ∈ h.impl

instance instMembership : Membership Loc Heap :=
  ⟨fun h address => Heap.mem address h⟩

/-- The number of bytes the heap owns. -/
def size (h : Heap) : Nat :=
  h.impl.keys.card

def compatible (h₁ h₂ : Heap) : Prop :=
  Finmap.Disjoint h₁.impl h₂.impl

private theorem mem_union {address : Loc} {h₁ h₂ : Heap} :
    address ∈ h₁ ∪ h₂ ↔ address ∈ h₁ ∨ address ∈ h₂ :=
  Finmap.mem_union

private theorem lookup_union_left {address : Loc}
    {h₁ h₂ : Heap} (hMem : address ∈ h₁) :
    (h₁ ∪ h₂).lookup address = h₁.lookup address :=
  Finmap.lookup_union_left hMem

private theorem lookup_union_right {address : Loc}
    {h₁ h₂ : Heap} (hMem : address ∉ h₁) :
    (h₁ ∪ h₂).lookup address = h₂.lookup address :=
  Finmap.lookup_union_right hMem

private theorem lookup_eq_none {address : Loc} {h : Heap} :
    h.lookup address = none ↔ address ∉ h :=
  Finmap.lookup_eq_none

private theorem mem_of_lookup_eq_some {address : Loc} {h : Heap} {b : Byte}
    (hLookup : h.lookup address = some b) : address ∈ h :=
  Finmap.mem_of_lookup_eq_some hLookup

private theorem mem_erase {address erasedAddress : Loc} {h : Heap} :
    address ∈ h.erase erasedAddress ↔
      address ≠ erasedAddress ∧ address ∈ h :=
  Finmap.mem_erase

private theorem lookup_erase_ne {address erasedAddress : Loc} {h : Heap}
    (hNe : address ≠ erasedAddress) :
    (h.erase erasedAddress).lookup address = h.lookup address :=
  Finmap.lookup_erase_ne hNe

/-- Union is associative, compatible or not: it is left-biased. -/
theorem union_assoc (h₁ h₂ h₃ : Heap) :
    (h₁ ∪ h₂) ∪ h₃ = h₁ ∪ (h₂ ∪ h₃) := by
  apply Heap.ext_impl
  exact Finmap.union_assoc

@[simp]
theorem empty_union (h : Heap) : empty ∪ h = h := by
  apply Heap.ext_impl
  exact Finmap.empty_union

@[simp]
theorem union_empty (h : Heap) : h ∪ empty = h := by
  apply Heap.ext_impl
  exact Finmap.union_empty

/-- Heaps form a PCM under disjoint union. -/
instance instPartialCommMonoid : PartialCommMonoid Heap where
  Compatible := Heap.compatible
  compatible_comm hCompatible := by
    exact Finmap.Disjoint.symm _ _ hCompatible
  compatible_empty_left h := by
    exact Finmap.disjoint_empty h.impl
  compatible_assoc a b c := by
    change
      Finmap.Disjoint a.impl b.impl ∧
          Finmap.Disjoint (a.impl ∪ b.impl) c.impl ↔
        Finmap.Disjoint b.impl c.impl ∧
          Finmap.Disjoint a.impl (b.impl ∪ c.impl)
    rw [Finmap.disjoint_union_left, Finmap.disjoint_union_right]
    constructor
    · rintro ⟨hab, hac, hbc⟩
      exact ⟨hbc, hab, hac⟩
    · rintro ⟨hbc, hab, hac⟩
      exact ⟨hab, hac, hbc⟩
  union_assoc _ _ := by
    apply Heap.ext_impl
    exact Finmap.union_assoc
  empty_union _ := by
    apply Heap.ext_impl
    exact Finmap.empty_union
  union_empty _ := by
    apply Heap.ext_impl
    exact Finmap.union_empty
  union_comm_of_compatible hCompatible := by
    apply Heap.ext_impl
    exact Finmap.union_comm_of_disjoint hCompatible

theorem union_right_cancel {h₁ h₂ frame : Heap}
    (hCompatible₁ : PartialCommMonoid.Compatible h₁ frame)
    (hCompatible₂ : PartialCommMonoid.Compatible h₂ frame)
    (hEq : h₁ ∪ frame = h₂ ∪ frame) : h₁ = h₂ := by
  apply Heap.ext_impl
  exact (Finmap.union_cancel hCompatible₁ hCompatible₂).mp (congrArg Heap.impl hEq)

theorem mem_of_sub_left {address : Loc} {h₁ h₂ : Heap} (hMem : address ∈ h₁) :
    address ∈ h₁ ∪ h₂ :=
  mem_union.mpr (Or.inl hMem)

/-! ## Runs of bytes

The heap of a value is the run of bytes encoding it, and the heap of a run is
the union of the heaps of its bytes. -/

/-- The heap of the single byte at `address`. -/
def singleton (address : Loc) (b : Byte) : Heap :=
  ⟨Finmap.singleton address b⟩

theorem mem_singleton {address : Loc} {b : Byte} {other : Loc} :
    other ∈ singleton address b ↔ other = address :=
  Finmap.mem_singleton _ _ _

private theorem lookup_singleton (address : Loc) (b : Byte) :
    (singleton address b).lookup address = some b :=
  Finmap.lookup_singleton_eq

/-- The heap of the bytes `bs`, starting at `address`. -/
def bytes (address : Loc) : List Byte → Heap
  | [] => empty
  | b :: rest => singleton address b ∪ bytes (address.add 1) rest

@[simp] theorem bytes_nil (address : Loc) : bytes address [] = empty := by
  unfold bytes; rfl

theorem bytes_cons (address : Loc) (b : Byte) (rest : List Byte) :
    bytes address (b :: rest) = singleton address b ∪ bytes (address.add 1) rest := by
  rw [bytes]

theorem mem_bytes {address : Loc} {bs : List Byte} {other : Loc} :
    other ∈ bytes address bs ↔ ∃ i, i < bs.length ∧ other = address.add i := by
  induction bs generalizing address with
  | nil =>
      simp only [bytes_nil, List.length_nil, Nat.not_lt_zero, false_and,
        exists_false, iff_false]
      intro hMem
      exact (Finmap.notMem_empty (a := other)) hMem
  | cons b rest ih =>
      rw [bytes_cons, Heap.mem_union, mem_singleton, ih]
      constructor
      · rintro (rfl | ⟨i, hi, rfl⟩)
        · exact ⟨0, by simp, rfl⟩
        · exact ⟨i + 1, by simpa using hi, by rw [Loc.add_add, Nat.add_comm]⟩
      · rintro ⟨i, hi, rfl⟩
        cases i with
        | zero => exact Or.inl rfl
        | succ j =>
            exact Or.inr ⟨j, by simpa using hi, by rw [Loc.add_add, Nat.add_comm]⟩

/-- Which addresses a run owns depends on its length only. -/
theorem mem_bytes_of_length_eq {address other : Loc} {bs bs' : List Byte}
    (hLength : bs'.length = bs.length) :
    other ∈ bytes address bs' ↔ other ∈ bytes address bs := by
  rw [mem_bytes, mem_bytes, hLength]

private theorem lookup_bytes_add {address : Loc} {bs : List Byte} {i : Nat}
    (hi : i < bs.length) :
    (bytes address bs).lookup (address.add i) = some bs[i] := by
  induction bs generalizing address i with
  | nil => simp at hi
  | cons b rest ih =>
      rw [bytes_cons]
      cases i with
      | zero =>
          rw [Loc.add_zero, lookup_union_left (mem_singleton.mpr rfl),
            lookup_singleton]
          rfl
      | succ j =>
          have hNotMem : address.add (j + 1) ∉ singleton address b := by
            rw [mem_singleton]
            intro hEq
            have := congrArg Prod.snd hEq
            simp at this
          rw [lookup_union_right hNotMem,
            show address.add (j + 1) = (address.add 1).add j by
              rw [Loc.add_add, Nat.add_comm]]
          exact ih (by simpa using hi)

/-- Splitting a run into two adjacent ones splits its heap. -/
theorem bytes_append (address : Loc) (xs ys : List Byte) :
    bytes address (xs ++ ys) = bytes address xs ∪ bytes (address.add xs.length) ys := by
  induction xs generalizing address with
  | nil => simp
  | cons b rest ih =>
      rw [List.cons_append, bytes_cons, bytes_cons, ih, List.length_cons,
        Loc.add_add, Nat.add_comm 1, Heap.union_assoc]

/-- The two halves of a split run own disjoint bytes. -/
theorem compatible_bytes_append (address : Loc) (xs ys : List Byte) :
    PartialCommMonoid.Compatible (bytes address xs)
      (bytes (address.add xs.length) ys) := by
  intro other hLeft hRight
  obtain ⟨i, hi, hL⟩ := mem_bytes.mp hLeft
  obtain ⟨j, -, hR⟩ := mem_bytes.mp hRight
  rw [Loc.add_add] at hR
  have hOffset := (congrArg Prod.snd hL).symm.trans (congrArg Prod.snd hR)
  simp at hOffset
  omega

/-- A frame disjoint from a run is disjoint from every run of the same length
at the same address. -/
theorem compatible_bytes_of_length_eq {address : Loc} {bs bs' : List Byte}
    {frame : Heap} (hLength : bs'.length = bs.length)
    (hCompatible : PartialCommMonoid.Compatible (bytes address bs) frame) :
    PartialCommMonoid.Compatible (bytes address bs') frame := by
  intro other hMem hFrame
  exact hCompatible other
    ((mem_bytes_of_length_eq (address := address) hLength).mp hMem) hFrame

/-- Runs in different allocations are disjoint. -/
theorem compatible_bytes_of_fst_ne {address address' : Loc} {bs bs' : List Byte}
    (hNe : address.1 ≠ address'.1) :
    PartialCommMonoid.Compatible (bytes address bs) (bytes address' bs') := by
  intro other hLeft hRight
  obtain ⟨_, -, hL⟩ := mem_bytes.mp hLeft
  obtain ⟨_, -, hR⟩ := mem_bytes.mp hRight
  have hL' := congrArg Prod.fst hL
  have hR' := congrArg Prod.fst hR
  simp only [Loc.fst_add] at hL' hR'
  exact hNe (hL'.symm.trans hR')

/-! ## Sub-heaps

The assertions of `Aeneas.SepLogic` are *affine*: they own the cells they
describe and say nothing about the rest of the heap.  Semantically that means
they are closed under the extension order below, the way Iris's `uPred` is
monotone in its resource. -/

/-- `Heap.Sub h h'`: `h'` is `h` extended with cells that `h` does not own. -/
@[expose] def Sub (h h' : Heap) : Prop :=
  ∃ rest, PartialCommMonoid.Compatible h rest ∧ h' = h ∪ rest

namespace Sub

@[refl]
theorem refl (h : Heap) : Heap.Sub h h :=
  ⟨∅,
    PartialCommMonoid.compatible_comm
      (PartialCommMonoid.compatible_empty_left h),
    (PartialCommMonoid.union_empty h).symm⟩

theorem trans {h₁ h₂ h₃ : Heap} (hSub₁₂ : Heap.Sub h₁ h₂)
    (hSub₂₃ : Heap.Sub h₂ h₃) : Heap.Sub h₁ h₃ := by
  obtain ⟨rest₁, hCompatible₁, rfl⟩ := hSub₁₂
  obtain ⟨rest₂, hCompatible₂, rfl⟩ := hSub₂₃
  have ⟨_, hCompatible⟩ :=
    (PartialCommMonoid.compatible_assoc h₁ rest₁ rest₂).mp
      ⟨hCompatible₁, hCompatible₂⟩
  exact ⟨rest₁ ∪ rest₂, hCompatible,
    PartialCommMonoid.union_assoc hCompatible₁ hCompatible₂⟩

theorem of_empty (h : Heap) : Heap.Sub empty h :=
  ⟨h, PartialCommMonoid.compatible_empty_left h,
    (PartialCommMonoid.empty_union h).symm⟩

theorem union_left {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) :
    Heap.Sub h₁ (h₁ ∪ h₂) :=
  ⟨h₂, hCompatible, rfl⟩

theorem union_right {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) :
    Heap.Sub h₂ (h₁ ∪ h₂) :=
  ⟨h₁, PartialCommMonoid.compatible_comm hCompatible,
    PartialCommMonoid.union_comm_of_compatible hCompatible⟩

/-- An extension of a split heap splits the same way, the extra cells going to
the right-hand side. -/
theorem split {h₁ h₂ h' : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hSub : Heap.Sub (h₁ ∪ h₂) h') :
    ∃ h₂', PartialCommMonoid.Compatible h₁ h₂' ∧
      h' = h₁ ∪ h₂' ∧ Heap.Sub h₂ h₂' := by
  obtain ⟨rest, hCompatibleRest, rfl⟩ := hSub
  have ⟨hCompatible₂, hCompatible₁⟩ :=
    (PartialCommMonoid.compatible_assoc h₁ h₂ rest).mp
      ⟨hCompatible, hCompatibleRest⟩
  exact ⟨h₂ ∪ rest, hCompatible₁,
    PartialCommMonoid.union_assoc hCompatible hCompatibleRest,
    ⟨rest, hCompatible₂, rfl⟩⟩

/-- A heap disjoint from an extension is disjoint from the heap extended. -/
theorem disjoint_of_sub {h h' frame : Heap} (hSub : Heap.Sub h h')
    (hCompatible : PartialCommMonoid.Compatible h' frame) :
    PartialCommMonoid.Compatible h frame := by
  obtain ⟨rest, hCompatibleRest, rfl⟩ := hSub
  have ⟨hRestFrame, hRestFrame'⟩ :=
    (PartialCommMonoid.compatible_assoc h rest frame).mp
      ⟨hCompatibleRest, hCompatible⟩
  have ⟨hFrame, _⟩ :=
    (PartialCommMonoid.compatible_assoc rest frame h).mp
      ⟨hRestFrame,
        PartialCommMonoid.compatible_comm hRestFrame'⟩
  exact PartialCommMonoid.compatible_comm hFrame

/-- Extending on one side of a union extends the union. -/
theorem union_mono_left {h h' frame : Heap} (hSub : Heap.Sub h h')
    (hCompatible : PartialCommMonoid.Compatible h' frame) :
    Heap.Sub (h ∪ frame) (h' ∪ frame) := by
  obtain ⟨rest, hCompatibleRest, rfl⟩ := hSub
  have ⟨hRestFrame, hRestFrame'⟩ :=
    (PartialCommMonoid.compatible_assoc h rest frame).mp
      ⟨hCompatibleRest, hCompatible⟩
  have hFrameRest := PartialCommMonoid.compatible_comm hRestFrame
  have hFrameRest' :
      PartialCommMonoid.Compatible h (frame ∪ rest) := by
    rw [← PartialCommMonoid.union_comm_of_compatible hRestFrame]
    exact hRestFrame'
  have ⟨hCompatibleFrame, hCompatibleCombined⟩ :=
    (PartialCommMonoid.compatible_assoc h frame rest).mpr
      ⟨hFrameRest, hFrameRest'⟩
  refine ⟨rest, hCompatibleCombined, ?_⟩
  calc
    (h ∪ rest) ∪ frame = h ∪ (rest ∪ frame) :=
      PartialCommMonoid.union_assoc hCompatibleRest hCompatible
    _ = h ∪ (frame ∪ rest) := congrArg (h ∪ ·)
      (PartialCommMonoid.union_comm_of_compatible hRestFrame)
    _ = (h ∪ frame) ∪ rest :=
      (PartialCommMonoid.union_assoc
        hCompatibleFrame hCompatibleCombined).symm

/-- Two extensions of compatible heaps extend their union. -/
theorem union_mono {A B h₁ h₂ : Heap}
    (hSub₁ : Heap.Sub A h₁) (hSub₂ : Heap.Sub B h₂)
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) :
    Heap.Sub (A ∪ B) (h₁ ∪ h₂) := by
  have hAh₂ : PartialCommMonoid.Compatible A h₂ :=
    Heap.Sub.disjoint_of_sub hSub₁ hCompatible
  have hAB : PartialCommMonoid.Compatible A B :=
    PartialCommMonoid.compatible_comm
      (Heap.Sub.disjoint_of_sub hSub₂
        (PartialCommMonoid.compatible_comm hAh₂))
  have hStep₁ : Heap.Sub (B ∪ A) (h₂ ∪ A) :=
    Heap.Sub.union_mono_left hSub₂ (PartialCommMonoid.compatible_comm hAh₂)
  have hStep₂ : Heap.Sub (A ∪ B) (A ∪ h₂) := by
    rw [PartialCommMonoid.union_comm_of_compatible hAB,
      PartialCommMonoid.union_comm_of_compatible hAh₂]
    exact hStep₁
  exact hStep₂.trans (Heap.Sub.union_mono_left hSub₁ hCompatible)

end Sub

theorem mem_of_sub {address : Loc} {h h' : Heap} (hSub : Heap.Sub h h')
    (hMem : address ∈ h) : address ∈ h' := by
  obtain ⟨rest, -, rfl⟩ := hSub
  exact mem_union.mpr (Or.inl hMem)

/-- Two heaps that both own the first byte of a run are not disjoint. -/
theorem not_compatible_of_sub_bytes {address : Loc} {bs bs' : List Byte}
    {h₁ h₂ : Heap} (hLength : 0 < bs.length) (hLength' : 0 < bs'.length)
    (hSub₁ : Heap.Sub (bytes address bs) h₁)
    (hSub₂ : Heap.Sub (bytes address bs') h₂) :
    ¬ PartialCommMonoid.Compatible h₁ h₂ := fun hCompatible =>
  hCompatible address
    (mem_of_sub hSub₁ (mem_bytes.mpr ⟨0, hLength, rfl⟩))
    (mem_of_sub hSub₂ (mem_bytes.mpr ⟨0, hLength', rfl⟩))

/-! ## Reading, writing and releasing runs -/

/-- The `n` bytes from `address` on, if the heap holds them all.  This is the
definedness guard of every operation: an operation on bytes the heap does not
hold is *stuck* rather than erroneous. -/
def readBytes (h : Heap) (address : Loc) : Nat → Option (List Byte)
  | 0 => some []
  | n + 1 =>
      match h.lookup address, h.readBytes (address.add 1) n with
      | some b, some rest => some (b :: rest)
      | _, _ => none

private theorem readBytes_eq_some {h : Heap} {address : Loc} {bs : List Byte}
    (hLookup : ∀ i (hi : i < bs.length), h.lookup (address.add i) = some bs[i]) :
    h.readBytes address bs.length = some bs := by
  induction bs generalizing address with
  | nil => rfl
  | cons b rest ih =>
      have hFirst := hLookup 0 (by simp)
      rw [Loc.add_zero] at hFirst
      have hRest : h.readBytes (address.add 1) rest.length = some rest :=
        ih fun i hi => by
          rw [Loc.add_add, Nat.add_comm]
          exact hLookup (i + 1) (by simpa using hi)
      simp only [List.length_cons, readBytes, hFirst, hRest, List.getElem_cons_zero]

/-- The empty heap holds no byte. -/
theorem readBytes_empty_succ (address : Loc) (n : Nat) :
    readBytes empty address (n + 1) = none := by
  have hLookup : (empty : Heap).lookup address = none :=
    lookup_eq_none.mpr fun hMem => Finmap.notMem_empty hMem
  simp only [readBytes, hLookup]

/-- A heap extending a run holds that run. -/
theorem readBytes_of_sub {address : Loc} {bs : List Byte} {h : Heap}
    (hSub : Heap.Sub (bytes address bs) h) :
    h.readBytes address bs.length = some bs := by
  obtain ⟨rest, -, rfl⟩ := hSub
  apply readBytes_eq_some
  intro i hi
  rw [lookup_union_left (mem_bytes.mpr ⟨i, hi, rfl⟩), lookup_bytes_add hi]

/-- Overwrite the bytes from `address` on with `bs`. -/
def writeBytes (h : Heap) (address : Loc) (bs : List Byte) : Heap :=
  bytes address bs ∪ h

theorem writeBytes_union (h₁ h₂ : Heap) (address : Loc) (bs : List Byte) :
    writeBytes (h₁ ∪ h₂) address bs = writeBytes h₁ address bs ∪ h₂ :=
  (union_assoc _ _ _).symm

/-- Overwriting a run with one of the same length replaces it. -/
theorem writeBytes_bytes_union {address : Loc} {bs bs' : List Byte} (rest : Heap)
    (hLength : bs'.length = bs.length) :
    writeBytes (bytes address bs ∪ rest) address bs' = bytes address bs' ∪ rest := by
  unfold writeBytes
  apply ext_lookup
  intro other
  by_cases hMem : other ∈ bytes address bs'
  · rw [lookup_union_left hMem, lookup_union_left hMem]
  · have hMem' : other ∉ bytes address bs := fun hOld =>
      hMem ((mem_bytes_of_length_eq hLength).mpr hOld)
    rw [lookup_union_right hMem, lookup_union_right hMem,
      lookup_union_right hMem']

/-- Release the `n` bytes from `address` on: the addresses go away, so what a
heap still holds is exactly what has not been freed. -/
def freeBytes (h : Heap) (address : Loc) : Nat → Heap
  | 0 => h
  | n + 1 => (h.erase address).freeBytes (address.add 1) n

private theorem lookup_freeBytes_of_not {h : Heap} {address other : Loc}
    {n : Nat} (hRange : ¬ ∃ i, i < n ∧ other = address.add i) :
    (freeBytes h address n).lookup other = h.lookup other := by
  induction n generalizing h address with
  | zero => rfl
  | succ n ih =>
      have hNe : other ≠ address := fun hEq =>
        hRange ⟨0, Nat.succ_pos n, by rw [Loc.add_zero]; exact hEq⟩
      have hRest : ¬ ∃ i, i < n ∧ other = (address.add 1).add i := by
        rintro ⟨i, hi, hEq⟩
        exact hRange ⟨i + 1, by omega, by rw [hEq, Loc.add_add, Nat.add_comm]⟩
      simp only [freeBytes]
      rw [ih hRest, lookup_erase_ne hNe]

private theorem lookup_freeBytes_of_mem {h : Heap} {address other : Loc}
    {n : Nat} (hRange : ∃ i, i < n ∧ other = address.add i) :
    (freeBytes h address n).lookup other = none := by
  induction n generalizing h address with
  | zero => obtain ⟨i, hi, -⟩ := hRange; omega
  | succ n ih =>
      obtain ⟨i, hi, rfl⟩ := hRange
      simp only [freeBytes]
      cases i with
      | zero =>
          rw [Loc.add_zero, lookup_freeBytes_of_not]
          · exact lookup_eq_none.mpr fun hMem => (mem_erase.mp hMem).1 rfl
          · rintro ⟨j, -, hEq⟩
            have := congrArg Prod.snd hEq
            simp at this
            omega
      | succ j =>
          exact ih ⟨j, by omega, by rw [Loc.add_add, Nat.add_comm]⟩

/-- Releasing a run removes exactly that run. -/
theorem freeBytes_bytes_union {address : Loc} {bs : List Byte} {rest : Heap}
    (hCompatible : PartialCommMonoid.Compatible (bytes address bs) rest) :
    freeBytes (bytes address bs ∪ rest) address bs.length = rest := by
  apply ext_lookup
  intro other
  by_cases hRange : ∃ i, i < bs.length ∧ other = address.add i
  · rw [lookup_freeBytes_of_mem hRange]
    exact (lookup_eq_none.mpr fun hRest =>
      hCompatible other (mem_bytes.mpr hRange) hRest).symm
  · rw [lookup_freeBytes_of_not hRange,
      lookup_union_right fun hMem => hRange (mem_bytes.mp hMem)]

/-! ## Allocation -/

/-- The allocation identifier this heap will hand out next: one past every
identifier it uses.  Allocation is deterministic, which is what lets a program
be *run* and not only related to its outcomes. -/
def freshBase (h : Heap) : AllocId :=
  (h.keys.image Prod.fst).sup id + 1

/-- The address the next allocation starts at.  Its offset is `0`, which every
alignment divides: allocations are suitably aligned for any type at their base. -/
def freshLoc (h : Heap) : Loc := (freshBase h, 0)

@[simp] theorem freshLoc_snd (h : Heap) : (freshLoc h).2 = 0 := by
  simp [freshLoc]

theorem not_mem_freshBase {h : Heap} {address : Loc}
    (hBase : address.1 = freshBase h) : address ∉ h := by
  intro hMem
  have hMemKeys : address ∈ h.keys := Finmap.mem_keys.mpr hMem
  have hImage : freshBase h ∈ h.keys.image Prod.fst :=
    Finset.mem_image.mpr ⟨_, hMemKeys, hBase⟩
  have hLe : freshBase h ≤ (h.keys.image Prod.fst).sup id :=
    Finset.le_sup (f := fun a : AllocId => a) hImage
  have hSucc : (h.keys.image Prod.fst).sup id + 1 ≤
      (h.keys.image Prod.fst).sup id := hLe
  exact Nat.not_succ_le_self _ hSucc

/-- The run a fresh allocation occupies is disjoint from everything the heap
already owns. -/
theorem compatible_fresh (h : Heap) (bs : List Byte) :
    PartialCommMonoid.Compatible (bytes (freshLoc h) bs) h := by
  intro address hFresh hMem
  obtain ⟨i, -, rfl⟩ := mem_bytes.mp hFresh
  exact not_mem_freshBase (h := h) rfl hMem

end Heap

end Aeneas.Std
