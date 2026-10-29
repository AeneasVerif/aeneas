module

public import Aeneas.Std.Heap.Repr

/-! Concrete heap operations. Representations and encodings are supplied explicitly.
Borrow restoration authority belongs to the caller, not to the byte store. -/

@[expose] public section

namespace Aeneas.Std

universe u v

def update {α : Type u} {β : Type v} [DecidableEq α]
    (f : α → β) (key : α) (value : β) : α → β :=
  fun k => if k = key then value else f k

abbrev BasePtr := Usize

structure RawPtr (ty : Type u) : Type u where
  base : BasePtr
  index : Usize

instance : Inhabited (RawPtr ty) := ⟨⟨⟨0⟩, ⟨0⟩⟩⟩

/-- Pointer constness is erased; cell permissions authorize access. -/
abbrev MutRawPtr (ty : Type u) := RawPtr ty
abbrev ConstRawPtr (ty : Type u) := RawPtr ty

structure Block where
  repr : List (Cell U8)
  alignment : Alignment
  owned : Bool

structure Heap where
  allocations : BasePtr → Option Block
  next : BasePtr

namespace Block

def bytes (block : Block) : Vector (Cell U8) block.repr.length :=
  ⟨block.repr.toArray, by simp⟩

end Block

namespace Heap

variable {ty : Type u}

def empty : Heap := ⟨fun _ => none, ⟨0⟩⟩

def cells (s : Heap) (base : BasePtr) : Option (List (Cell U8)) :=
  (s.allocations base).map Block.repr

def allocated (s : Heap) (base : BasePtr) : Bool :=
  ((s.allocations base).map Block.owned).getD false

def alignment (s : Heap) (base : BasePtr) : Option Alignment :=
  (s.allocations base).map Block.alignment

def Aligned (repr : Repr ty) (s : Heap) (base : BasePtr) : Prop :=
  match s.allocations base with
  | some block => repr.align.val ∣ block.alignment.val
  | none => False

def Inv (s : Heap) : Prop :=
  ∀ base, s.next.val ≤ base.val → s.allocations base = none

def storeRepr (s : Heap) (base : BasePtr) (bytes : List (Cell U8)) : Heap :=
  { s with allocations := update s.allocations base ((s.allocations base).map fun block =>
      { block with repr := bytes }) }

def remove (s : Heap) (base : BasePtr) : Heap :=
  { s with allocations := update s.allocations base none }

/-- The greatest identifier is the exhausted-counter sentinel, never a live base.
Checking the slot also prevents overwriting an allocation in a malformed input heap. -/
def createRepr (s : Heap) (block : Block) : Option (BasePtr × Heap) :=
  if s.next.val + 1 < 2 ^ UScalarTy.numBits .Usize ∧
      block.repr.length < 2 ^ UScalarTy.numBits .Usize then
    match s.allocations s.next with
    | none => some (s.next,
        { allocations := update s.allocations s.next (some block)
          next := ⟨BitVec.ofNat _ (s.next.val + 1)⟩ })
    | some _ => none
  else none

def alloc (repr : Repr ty) (count : Nat) (s : Heap) :
    Option (RawPtr ty × Heap) :=
  if count * repr.size < 2 ^ UScalarTy.numBits .Usize then
    match s.createRepr
        ⟨(repr.create (Vector.replicate count (.shared 0 none))).toList, repr.align, true⟩ with
    | some (base, s₁) => some (⟨base, ⟨0⟩⟩, s₁)
    | none => none
  else none

/-- Allocate supplied encodings. Their typed validity is checked when they are read. -/
def newBlock (repr : Repr ty) (data : List (Vector U8 repr.size))
    (own : Bool) (s : Heap) : Option (RawPtr ty × Heap) :=
  match s.createRepr
      ⟨(repr.create (data.toArray.toVector.map (Cell.shared 0 ∘ some))).toList,
        repr.align, own⟩ with
  | some (base, s₁) => some (⟨base, ⟨0⟩⟩, s₁)
  | none => none

def newSharedExposure (repr : Repr ty) (data : List (Vector U8 repr.size))
    (s : Heap) : Option (RawPtr ty × Heap) :=
  match s.createRepr
      ⟨(repr.create (data.toArray.toVector.map (Cell.shared 1 ∘ some))).toList,
        repr.align, false⟩ with
  | some (base, s₁) => some (⟨base, ⟨0⟩⟩, s₁)
  | none => none

def extent (repr : Repr ty) (s : Heap) (base : BasePtr) : Option Nat :=
  match s.allocations base with
  | some block =>
    if repr.align.val ∣ block.alignment.val then some (block.repr.length / repr.size)
    else none
  | none => none

def read (repr : Repr ty) (p : RawPtr ty) (s : Heap) : Option ty :=
  match s.allocations p.base with
  | some block =>
    if repr.align.val ∣ block.alignment.val then repr.read block.bytes p.index.val
    else none
  | none => none

def readRange (repr : Repr ty) (p : RawPtr ty) (count : Nat) (s : Heap) :
    Option (List ty) :=
  match s.allocations p.base with
  | some block =>
    if repr.align.val ∣ block.alignment.val ∧ (count = 0 ∨ 0 < repr.size) ∧
        (p.index.val + count) * repr.size ≤ block.repr.length then
      (List.range count).mapM fun i => repr.read block.bytes (p.index.val + i)
    else none
  | none => none

/-- Commit an entire byte transformation only if it succeeds. Alignment,
allocation authority, and byte length are preserved. -/
def modify (repr : Repr ty) (p : RawPtr ty)
    (change : ∀ {r}, Vector (Cell U8) r → Option (Vector (Cell U8) r))
    (s : Heap) : Option Heap :=
  match s.allocations p.base with
  | some block =>
    if repr.align.val ∣ block.alignment.val then
      match change block.bytes with
      | some bytes => some (s.storeRepr p.base bytes.toList)
      | none => none
    else none
  | none => none

def write (repr : Repr ty) (p : RawPtr ty) (value : ty)
    (data : Vector U8 repr.size) (decoded : repr.decode data = some value)
    (s : Heap) : Option Heap :=
  modify repr p (fun bytes => repr.write bytes p.index.val value data decoded) s

def borrow (repr : Repr ty) (p : RawPtr ty) (s : Heap) : Option Heap :=
  modify repr p (fun bytes => repr.borrow bytes p.index.val) s

def endBorrow (repr : Repr ty) (p : RawPtr ty) (value : ty)
    (data : Vector U8 repr.size) (decoded : repr.decode data = some value)
    (s : Heap) : Option Heap :=
  modify repr p (fun bytes => repr.endBorrow bytes p.index.val value data decoded) s

def share (repr : Repr ty) (p : RawPtr ty) (s : Heap) : Option Heap :=
  modify repr p (fun bytes => repr.share bytes p.index.val) s

def endShare (repr : Repr ty) (p : RawPtr ty) (s : Heap) : Option Heap :=
  modify repr p (fun bytes => repr.endShare bytes p.index.val) s

/-- Range operations compose byte transformations before committing the block. -/
def modifyRange (repr : Repr ty) (p : RawPtr ty) (count : Nat)
    (change : ∀ {r}, Vector (Cell U8) r → Nat → Option (Vector (Cell U8) r))
    (s : Heap) : Option Heap :=
  modify repr p (fun bytes =>
    if (count = 0 ∨ 0 < repr.size) ∧ (p.index.val + count) * repr.size ≤ bytes.size then
      (List.range count).foldlM change bytes
    else none) s

def borrowRange (repr : Repr ty) (p : RawPtr ty) (count : Nat) (s : Heap) : Option Heap :=
  modifyRange repr p count (fun bytes i => repr.borrow bytes (p.index.val + i)) s

def shareRange (repr : Repr ty) (p : RawPtr ty) (count : Nat) (s : Heap) : Option Heap :=
  modifyRange repr p count (fun bytes i => repr.share bytes (p.index.val + i)) s

def endShareRange (repr : Repr ty) (p : RawPtr ty) (count : Nat) (s : Heap) : Option Heap :=
  modifyRange repr p count (fun bytes i => repr.endShare bytes (p.index.val + i)) s

/-- Each supplied encoding must decode; restoration still requires the caller's authority. -/
def endBorrowRange (repr : Repr ty) (p : RawPtr ty)
    (data : List (Vector U8 repr.size)) (s : Heap) : Option Heap :=
  modifyRange repr p data.length (fun bytes i =>
    match data[i]? with
    | some encoding =>
      match h : repr.decode encoding with
      | some value => repr.endBorrow bytes (p.index.val + i) value encoding h
      | none => none
    | none => none) s

/-- Both endpoints may be one-past, but the result must fit the pointer index. -/
def offset (repr : Repr ty) (p : RawPtr ty) (count : Int) (s : Heap) :
    Option (RawPtr ty) :=
  match extent repr s p.base with
  | some n =>
    let target := (p.index.val : Int) + count
    if p.index.val ≤ n ∧ 0 ≤ target ∧ target ≤ n ∧
        target < (2 ^ UScalarTy.numBits .Usize : Nat) then
      some ⟨p.base, ⟨BitVec.ofNat _ target.toNat⟩⟩
    else none
  | none => none

/-- Cleanup covers the entire allocation, including any trailing bytes. -/
def freeBlock (repr : Repr ty) (p : RawPtr ty) (count : Nat) (own : Bool)
    (s : Heap) : Option Heap :=
  match s.allocations p.base with
  | some block =>
    if p.index.val = 0 ∧ block.owned = own ∧
        repr.align.val ∣ block.alignment.val ∧ block.repr.length = count * repr.size ∧
        block.repr.all (fun cell => cell.depth == some 0) then
      some (s.remove p.base)
    else none
  | none => none

/-- End the exposure only after its shared permissions have returned to depth one. -/
def endSharedExposure (repr : Repr ty) (p : RawPtr ty) (count : Nat)
    (s : Heap) : Option Heap :=
  match s.allocations p.base with
  | some block =>
    if p.index.val = 0 ∧ block.owned = false ∧
        repr.align.val ∣ block.alignment.val ∧ block.repr.length = count * repr.size ∧
        block.repr.all (fun cell => cell.depth == some 1) then
      some (s.remove p.base)
    else none
  | none => none

end Heap
end Aeneas.Std
