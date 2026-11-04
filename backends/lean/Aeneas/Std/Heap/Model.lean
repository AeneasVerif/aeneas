module

public import Aeneas.Std.Heap.Repr

/-! Finite explicit views of an unknown implicit safe heap. Ghost IDs never recycle;
numerical addresses may. Safe continuation authority is not a byte permission. -/

@[expose] public section

namespace Aeneas.Std

universe u v

def update {α : Type u} {β : Type v} [DecidableEq α]
    (f : α → β) (key : α) (value : β) : α → β :=
  fun k => if k = key then value else f k

structure Block where
  bptr : BasePtr
  root : Nat
  repr : List Cell
  owned : Bool
  active : Bool := true
  alive : Bool := true

structure Heap where
  allocations : Nat → Option Block
  next : Nat

def Block.bytes (block : Block) : Vector Cell block.repr.length :=
  ⟨block.repr.toArray, by simp⟩

namespace Heap

variable {ty : Type}

def empty : Heap := ⟨fun _ => none, 0⟩

def ptrEq (_s : Heap) (p : RawPtr T) (q : RawPtr U) : Option Bool :=
  some (p.address == q.address)

def cells (s : Heap) (id : Nat) : Option (List Cell) :=
  (s.allocations id).bind fun block => if block.active then some block.repr else none

def allocated (s : Heap) (id : Nat) : Bool :=
  ((s.allocations id).map fun block => block.active && block.owned).getD false

def live (s : Heap) (block : Block) : Bool :=
  block.active && ((s.allocations block.root).map Block.alive).getD false

def bounded (block : Block) : Bool :=
  block.bptr.val > 0 &&
    block.bptr.val + block.repr.length < 2 ^ UScalarTy.numBits .Usize

def overlaps (a b : Block) : Bool :=
  a.bptr.val < b.bptr.val + b.repr.length &&
    b.bptr.val < a.bptr.val + a.repr.length

def validByte (s : Heap) : Byte → Bool
  | .uninit | .data _ => true
  | .pointer p lane => lane < pointerWidth && (s.allocations p.provenance).isSome

def validBlock (s : Heap) (block : Block) : Bool :=
  bounded block &&
    (match s.allocations block.root with
    | some root =>
        root.root == block.root &&
        root.bptr.val ≤ block.bptr.val &&
        block.bptr.val + block.repr.length ≤ root.bptr.val + root.repr.length &&
        (!block.active || root.alive)
    | none => false) &&
    block.repr.all (fun cell => match cell with
      | .borrowed => true
      | .shared _ byte => validByte s byte)

def compatible (a b : Block) : Bool :=
  !a.active || !b.active ||
    a.repr.zipIdx.all (fun (x, i) =>
      b.repr.zipIdx.all (fun (y, j) =>
        a.bptr.val + i != b.bptr.val + j || x.compatible y))

/-- The executable part checks all issued IDs; `Inv` also excludes hidden entries
outside that finite prefix. Constructors preserve the latter from a valid input. -/
def check (s : Heap) : Bool :=
  (List.range s.next).all fun i =>
    match s.allocations i with
    | none => false
    | some a => validBlock s a &&
        (List.range s.next).all (fun j =>
          if i = j then true else
            match s.allocations j with
            | some b =>
                (!(a.root == i && b.root == j && a.alive && b.alive && overlaps a b)) &&
                  compatible a b
            | none => false)

def Inv (s : Heap) : Prop :=
  (∀ id, s.next ≤ id → s.allocations id = none) ∧ s.check = true

def storeRepr (s : Heap) (id : Nat) (bytes : List Cell) : Heap :=
  { s with allocations := update s.allocations id ((s.allocations id).map fun block =>
      { block with repr := bytes }) }

def commit (s : Heap) : Option Heap :=
  if s.check then some s else none

def noAliases (s : Heap) (id root : Nat) : Bool :=
  (List.range s.next).all fun j =>
    j == id || ((s.allocations j).map fun block =>
      !block.active || block.root != root).getD true

def ownershipAvailable (s : Heap) (root : Nat) (bptr : BasePtr) (length : Nat) : Bool :=
  ((s.allocations root).map fun block =>
    block.root == root && block.owned && !block.active && block.alive &&
      block.bptr == bptr && block.repr.length == length && s.noAliases root root).getD false

/-- Fresh ghost identity and caller-supplied concrete placement. Joint nondeterministic
placement/encoding is implemented by the `State` relations, not by this witness checker. -/
def createRepr (s : Heap) (block : Block) : Option (Nat × Heap) :=
  match s.allocations s.next with
  | none =>
      let s₁ := { allocations := update s.allocations s.next (some block), next := s.next + 1 }
      (commit s₁).map fun s₁ => (s.next, s₁)
  | some _ => none

def newBlock (repr : Repr ty) (data : List (Vector Byte repr.size))
    (own : Bool) (bptr : BasePtr) (root : Option Nat) (s : Heap) :
    Option (RawPtr ty × Heap) :=
  if repr.align.val ∣ bptr.val &&
      (!own || (match root with
        | none => true
        | some id => s.ownershipAvailable id bptr (data.length * repr.size))) then
    (s.createRepr ⟨bptr, root.getD s.next, repr.create data 0, own, true, true⟩).map fun (id, s₁) =>
      (⟨id, bptr⟩, s₁)
  else none

def newSharedExposure (repr : Repr ty) (data : List (Vector Byte repr.size))
    (bptr : BasePtr) (root : Option Nat) (s : Heap) : Option (RawPtr ty × Heap) :=
  if repr.align.val ∣ bptr.val then
    (s.createRepr ⟨bptr, root.getD s.next, repr.create data 1, false, true, true⟩).map fun (id, s₁) =>
      (⟨id, bptr⟩, s₁)
  else none

def alloc (repr : Repr ty) (count : Nat) (bptr : BasePtr) (s : Heap) :
    Option (RawPtr ty × Heap) :=
  if repr.align.val ∣ bptr.val then
    (s.createRepr
      ⟨bptr, s.next, List.replicate (count * repr.size) (.shared 0 .uninit), true, true, true⟩).map
        fun (id, s₁) => (⟨id, bptr⟩, s₁)
  else none

def Aligned (repr : Repr ty) (s : Heap) (id : Nat) : Prop :=
  match s.allocations id with
  | some block => repr.align.val ∣ block.bptr.val
  | none => False

def extent (repr : Repr ty) (s : Heap) (id : Nat) : Option Nat := do
  let block ← s.allocations id
  if s.live block && repr.align.val ∣ block.bptr.val then
    some (block.repr.length / repr.size)
  else none

def read (repr : Repr ty) (p : RawPtr ty) (s : Heap) : Option ty := do
  let block ← s.allocations p.provenance
  if s.live block && block.bptr.val ≤ p.address.val && repr.align.val ∣ p.address.val then
    repr.read block.bytes (p.offsetFrom block.bptr)
  else none

def readRange (repr : Repr ty) (p : RawPtr ty) (count : Nat) (s : Heap) :
    Option (List ty) := do
  let block ← s.allocations p.provenance
  if s.live block && block.bptr.val ≤ p.address.val && repr.align.val ∣ p.address.val &&
      (count = 0 ∨ 0 < repr.size) &&
      p.address.val + count * repr.size ≤ block.bptr.val + block.repr.length then
    (List.range count).mapM fun i =>
      repr.read block.bytes (p.offsetFrom block.bptr + i * repr.size)
  else none

/-- Length-preserving, atomic selected-view update, checked against every alias.
Only this view's permissions authorize the transformation. -/
def modify (repr : Repr ty) (p : RawPtr ty)
    (change : ∀ {r}, Vector Cell r → Nat → Option (Vector Cell r))
    (s : Heap) : Option Heap := do
  let block ← s.allocations p.provenance
  if s.live block && block.bptr.val ≤ p.address.val && repr.align.val ∣ p.address.val then
    let bytes ← change block.bytes (p.offsetFrom block.bptr)
    commit (s.storeRepr p.provenance bytes.toList)
  else none

def write (repr : Repr ty) (p : RawPtr ty) (value : ty)
    (data : Vector Byte repr.size) (encoded : repr.encode value data)
    (s : Heap) : Option Heap :=
  modify repr p (fun bytes i => repr.write bytes i value data encoded) s

def borrow (repr : Repr ty) (p : RawPtr ty) (s : Heap) : Option Heap :=
  modify repr p (fun bytes i => repr.borrow bytes i) s

def endBorrow (repr : Repr ty) (p : RawPtr ty)
    (data : Vector Byte repr.size) (s : Heap) : Option Heap :=
  modify repr p (fun bytes i => repr.endBorrow bytes i data) s

def share (repr : Repr ty) (p : RawPtr ty) (s : Heap) : Option Heap :=
  modify repr p (fun bytes i => repr.share bytes i) s

def endShare (repr : Repr ty) (p : RawPtr ty) (s : Heap) : Option Heap :=
  modify repr p (fun bytes i => repr.endShare bytes i) s

def modifyRange (repr : Repr ty) (p : RawPtr ty) (count : Nat)
    (change : ∀ {r}, Vector Cell r → Nat → Option (Vector Cell r))
    (s : Heap) : Option Heap :=
  modify repr p (fun bytes offset =>
    if (count = 0 ∨ 0 < repr.size) &&
        offset + count * repr.size ≤ bytes.size then
      (List.range count).foldlM (fun bytes i => change bytes (offset + i * repr.size)) bytes
    else none) s

def borrowRange (repr : Repr ty) (p : RawPtr ty) (count : Nat) (s : Heap) : Option Heap :=
  modifyRange repr p count (fun bytes i => repr.borrow bytes i) s

def shareRange (repr : Repr ty) (p : RawPtr ty) (count : Nat) (s : Heap) : Option Heap :=
  modifyRange repr p count (fun bytes i => repr.share bytes i) s

def endShareRange (repr : Repr ty) (p : RawPtr ty) (count : Nat) (s : Heap) : Option Heap :=
  modifyRange repr p count (fun bytes i => repr.endShare bytes i) s

def endBorrowRange (repr : Repr ty) (p : RawPtr ty)
    (data : List (Vector Byte repr.size)) (s : Heap) : Option Heap :=
  modify repr p (fun bytes offset =>
    if (data.length = 0 ∨ 0 < repr.size) &&
        offset + data.length * repr.size ≤ bytes.size then
      (data.zipIdx).foldlM (fun bytes (encoding, i) =>
        repr.endBorrow bytes (offset + i * repr.size) encoding) bytes
    else none) s

/-- Untyped, memmove-style copy preserves initialization and pointer lanes.
Reading an uninitialized representation for copying is not a typed byte read. -/
def copyBytes (source : RawPtr T) (destination : RawPtr U) (count : Nat) (s : Heap) :
    Option Heap := do
  let src ← s.allocations source.provenance
  let dst ← s.allocations destination.provenance
  if s.live src && s.live dst && src.bptr.val ≤ source.address.val &&
      dst.bptr.val ≤ destination.address.val &&
      source.address.val + count ≤ src.bptr.val + src.repr.length &&
      destination.address.val + count ≤ dst.bptr.val + dst.repr.length then
    let sourceOffset := source.offsetFrom src.bptr
    let destinationOffset := destination.offsetFrom dst.bptr
    let data ← (List.range count).mapM fun i =>
      (src.repr[sourceOffset + i]?).bind fun cell => match cell with
        | .shared _ byte => some byte
        | .borrowed => none
    if ((dst.repr.drop destinationOffset).take count).all
        (fun cell => cell.depth == some 0) then
      commit (s.storeRepr destination.provenance
        (dst.repr.take destinationOffset ++ Cell.full data ++
          dst.repr.drop (destinationOffset + count)))
    else none
  else none

/-- Untyped exchange snapshots both representations before changing either.
In particular, self-swap preserves symbolic pointer lanes and uninitialized bytes. -/
def swapBytes (repr : Repr T) (p q : RawPtr T) (s : Heap) : Option Heap := do
    let a ← s.allocations p.provenance
    let b ← s.allocations q.provenance
    let pa := p.address
    let qa := q.address
    if s.live a && s.live b && repr.align.val ∣ pa.val && repr.align.val ∣ qa.val &&
        a.bptr.val ≤ pa.val && b.bptr.val ≤ qa.val &&
        pa.val + repr.size ≤ a.bptr.val + a.repr.length &&
        qa.val + repr.size ≤ b.bptr.val + b.repr.length &&
        (pa.val + repr.size ≤ qa.val ∨ qa.val + repr.size ≤ pa.val ∨ pa = qa) then
      let pi := p.offsetFrom a.bptr
      let qi := q.offsetFrom b.bptr
      let left := (a.repr.drop pi).take repr.size
      let right := (b.repr.drop qi).take repr.size
      if left.all (fun cell => cell.depth == some 0) &&
          right.all (fun cell => cell.depth == some 0) then
        let s₁ := s.storeRepr p.provenance
          (a.repr.take pi ++ right ++ a.repr.drop (pi + repr.size))
        let current ← s₁.allocations q.provenance
        commit (s₁.storeRepr q.provenance
          (current.repr.take qi ++ left ++ current.repr.drop (qi + repr.size)))
      else none
    else none

/-- Arithmetic is deliberately view-bounded; address observation is independent of liveness. -/
def offset (repr : Repr ty) (p : RawPtr ty) (count : Int) (s : Heap) :
    Option (RawPtr ty) := do
  let block ← s.allocations p.provenance
  let target := (p.address.val : Int) + count * repr.size
  if s.live block && block.bptr.val ≤ p.address.val &&
      p.address.val ≤ block.bptr.val + block.repr.length &&
      block.bptr.val ≤ target && target ≤ block.bptr.val + block.repr.length &&
      target < (2 ^ UScalarTy.numBits .Usize : Nat) then
    some ⟨p.provenance, ⟨BitVec.ofNat _ target.toNat⟩⟩
  else none

def distance (repr : Repr ty) (p q : RawPtr ty) (s : Heap) : Option Int := do
  let a ← s.allocations p.provenance
  let b ← s.allocations q.provenance
  let pa := p.address
  let qa := q.address
  let distance := (pa.val : Int) - qa.val
  if s.live a && s.live b && a.root == b.root && 0 < repr.size &&
      a.bptr.val ≤ pa.val && pa.val ≤ a.bptr.val + a.repr.length &&
      b.bptr.val ≤ qa.val && qa.val ≤ b.bptr.val + b.repr.length &&
      distance % repr.size = 0 then some (distance / repr.size) else none

def retire (s : Heap) (id : Nat) : Heap :=
  let allocations := update s.allocations id
    ((s.allocations id).map fun block => { block with active := false })
  { s with allocations }

/-- Return an owned root to implicit safe Rust, without physical deallocation.
The address and allocation lifetime remain observable through retained metadata. -/
def returnOwned (repr : Repr ty) (p : RawPtr ty) (count : Nat) (s : Heap) :
    Option Heap := do
  let block ← s.allocations p.provenance
  let root ← s.allocations block.root
  if s.live block && block.owned && p.address = block.bptr &&
      block.bptr == root.bptr && block.repr.length == root.repr.length &&
      repr.align.val ∣ block.bptr.val && block.repr.length = count * repr.size &&
      block.repr.all (fun cell => cell.depth == some 0) && s.noAliases p.provenance block.root then
    commit (s.retire p.provenance)
  else none

/-- Physical death is distinct from return to safe Rust. This prototype checks
abstract ownership and full byte coverage, not an allocator's original layout. -/
def dealloc (repr : Repr ty) (p : RawPtr ty) (count : Nat) (s : Heap) : Option Heap := do
  let block ← s.allocations p.provenance
  let returned ← returnOwned repr p count s
  let allocations := update returned.allocations block.root
    ((returned.allocations block.root).map fun root => { root with alive := false })
  let s₁ := { returned with allocations }
  commit s₁

/-- Retire a nonowning baseline contribution; never decrement it into a writer.
Positive-depth uninitialized bytes remain protected until matching shares end. -/
def endExposureAt (repr : Repr ty) (p : RawPtr ty) (count depth : Nat) (s : Heap) :
    Option Heap := do
  let block ← s.allocations p.provenance
  if s.live block && !block.owned && p.address = block.bptr &&
      repr.align.val ∣ block.bptr.val && block.repr.length = count * repr.size &&
      block.repr.all (fun cell => cell.depth == some depth) then
    commit (s.retire p.provenance)
  else none

def freeBlock (repr : Repr ty) (p : RawPtr ty) (count : Nat) (own : Bool)
    (s : Heap) : Option Heap :=
  if own then dealloc repr p count s else endExposureAt repr p count 0 s

def endSharedExposure (repr : Repr ty) (p : RawPtr ty) (count : Nat)
    (s : Heap) : Option Heap :=
  endExposureAt repr p count 1 s

end Heap
end Aeneas.Std
