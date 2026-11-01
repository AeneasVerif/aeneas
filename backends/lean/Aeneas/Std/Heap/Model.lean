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

def addresses (s : Heap) : AddressMap :=
  fun id => (s.allocations id).map Block.bptr

def address (s : Heap) (p : RawPtr ty) : Option Usize :=
  p.address s.addresses

def ptrEq (s : Heap) (p : RawPtr T) (q : RawPtr U) : Option Bool := do
  let a ← s.address p
  let b ← s.address q
  some (a == b)

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
  | .pointer p lane => lane < pointerWidth && (s.address p).isSome

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
      (⟨id, ⟨0⟩⟩, s₁)
  else none

def newSharedExposure (repr : Repr ty) (data : List (Vector Byte repr.size))
    (bptr : BasePtr) (root : Option Nat) (s : Heap) : Option (RawPtr ty × Heap) :=
  if repr.align.val ∣ bptr.val then
    (s.createRepr ⟨bptr, root.getD s.next, repr.create data 1, false, true, true⟩).map fun (id, s₁) =>
      (⟨id, ⟨0⟩⟩, s₁)
  else none

def alloc (repr : Repr ty) (count : Nat) (bptr : BasePtr) (s : Heap) :
    Option (RawPtr ty × Heap) :=
  if repr.align.val ∣ bptr.val then
    (s.createRepr
      ⟨bptr, s.next, List.replicate (count * repr.size) (.shared 0 .uninit), true, true, true⟩).map
        fun (id, s₁) => (⟨id, ⟨0⟩⟩, s₁)
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
  let block ← s.allocations p.base
  if s.live block && repr.align.val ∣ block.bptr.val + p.byteOffset.val then
    repr.read s.addresses block.bytes p.byteOffset.val
  else none

def readRange (repr : Repr ty) (p : RawPtr ty) (count : Nat) (s : Heap) :
    Option (List ty) := do
  let block ← s.allocations p.base
  if s.live block && repr.align.val ∣ block.bptr.val + p.byteOffset.val &&
      (count = 0 ∨ 0 < repr.size) &&
      p.byteOffset.val + count * repr.size ≤ block.repr.length then
    (List.range count).mapM fun i =>
      repr.read s.addresses block.bytes (p.byteOffset.val + i * repr.size)
  else none

/-- Length-preserving, atomic selected-view update, checked against every alias.
Only this view's permissions authorize the transformation. -/
def modify (repr : Repr ty) (p : RawPtr ty)
    (change : ∀ {r}, Vector Cell r → Option (Vector Cell r))
    (s : Heap) : Option Heap := do
  let block ← s.allocations p.base
  if s.live block && repr.align.val ∣ block.bptr.val + p.byteOffset.val then
    let bytes ← change block.bytes
    commit (s.storeRepr p.base bytes.toList)
  else none

def write (repr : Repr ty) (p : RawPtr ty) (value : ty)
    (data : Vector Byte repr.size) (encoded : repr.encodes value data)
    (s : Heap) : Option Heap :=
  modify repr p (fun bytes => repr.write bytes p.byteOffset.val value data encoded) s

def borrow (repr : Repr ty) (p : RawPtr ty) (s : Heap) : Option Heap :=
  modify repr p (fun bytes => repr.borrow bytes p.byteOffset.val) s

def endBorrow (repr : Repr ty) (p : RawPtr ty)
    (data : Vector Byte repr.size) (s : Heap) : Option Heap :=
  modify repr p (fun bytes => repr.endBorrow bytes p.byteOffset.val data) s

def share (repr : Repr ty) (p : RawPtr ty) (s : Heap) : Option Heap :=
  modify repr p (fun bytes => repr.share bytes p.byteOffset.val) s

def endShare (repr : Repr ty) (p : RawPtr ty) (s : Heap) : Option Heap :=
  modify repr p (fun bytes => repr.endShare bytes p.byteOffset.val) s

def modifyRange (repr : Repr ty) (p : RawPtr ty) (count : Nat)
    (change : ∀ {r}, Vector Cell r → Nat → Option (Vector Cell r))
    (s : Heap) : Option Heap :=
  modify repr p (fun bytes =>
    if (count = 0 ∨ 0 < repr.size) &&
        p.byteOffset.val + count * repr.size ≤ bytes.size then
      (List.range count).foldlM change bytes
    else none) s

def borrowRange (repr : Repr ty) (p : RawPtr ty) (count : Nat) (s : Heap) : Option Heap :=
  modifyRange repr p count (fun bytes i => repr.borrow bytes (p.byteOffset.val + i * repr.size)) s

def shareRange (repr : Repr ty) (p : RawPtr ty) (count : Nat) (s : Heap) : Option Heap :=
  modifyRange repr p count (fun bytes i => repr.share bytes (p.byteOffset.val + i * repr.size)) s

def endShareRange (repr : Repr ty) (p : RawPtr ty) (count : Nat) (s : Heap) : Option Heap :=
  modifyRange repr p count (fun bytes i => repr.endShare bytes (p.byteOffset.val + i * repr.size)) s

def endBorrowRange (repr : Repr ty) (p : RawPtr ty)
    (data : List (Vector Byte repr.size)) (s : Heap) : Option Heap :=
  modifyRange repr p data.length (fun bytes i =>
    (data[i]?).bind fun encoding =>
      repr.endBorrow bytes (p.byteOffset.val + i * repr.size) encoding) s

/-- Untyped, memmove-style copy preserves initialization and pointer lanes.
Reading an uninitialized representation for copying is not a typed byte read. -/
def copyBytes (source : RawPtr T) (destination : RawPtr U) (count : Nat) (s : Heap) :
    Option Heap := do
  let src ← s.allocations source.base
  let dst ← s.allocations destination.base
  if s.live src && s.live dst &&
      source.byteOffset.val + count ≤ src.repr.length &&
      destination.byteOffset.val + count ≤ dst.repr.length then
    let data ← (List.range count).mapM fun i =>
      (src.repr[source.byteOffset.val + i]?).bind fun cell => match cell with
        | .shared _ byte => some byte
        | .borrowed => none
    if ((dst.repr.drop destination.byteOffset.val).take count).all
        (fun cell => cell.depth == some 0) then
      commit (s.storeRepr destination.base
        (dst.repr.take destination.byteOffset.val ++ Cell.full data ++
          dst.repr.drop (destination.byteOffset.val + count)))
    else none
  else none

/-- Untyped exchange snapshots both representations before changing either.
In particular, self-swap preserves symbolic pointer lanes and uninitialized bytes. -/
def swapBytes (repr : Repr T) (p q : RawPtr T) (s : Heap) : Option Heap := do
    let a ← s.allocations p.base
    let b ← s.allocations q.base
    let pa ← s.address p
    let qa ← s.address q
    if s.live a && s.live b && repr.align.val ∣ pa.val && repr.align.val ∣ qa.val &&
        p.byteOffset.val + repr.size ≤ a.repr.length &&
        q.byteOffset.val + repr.size ≤ b.repr.length &&
        (pa.val + repr.size ≤ qa.val ∨ qa.val + repr.size ≤ pa.val ∨ pa = qa) then
      let left := (a.repr.drop p.byteOffset.val).take repr.size
      let right := (b.repr.drop q.byteOffset.val).take repr.size
      if left.all (fun cell => cell.depth == some 0) &&
          right.all (fun cell => cell.depth == some 0) then
        let s₁ := s.storeRepr p.base
          (a.repr.take p.byteOffset.val ++ right ++ a.repr.drop (p.byteOffset.val + repr.size))
        let current ← s₁.allocations q.base
        commit (s₁.storeRepr q.base
          (current.repr.take q.byteOffset.val ++ left ++
            current.repr.drop (q.byteOffset.val + repr.size)))
      else none
    else none

/-- Arithmetic is deliberately view-bounded; address observation is independent of liveness. -/
def offset (repr : Repr ty) (p : RawPtr ty) (count : Int) (s : Heap) :
    Option (RawPtr ty) := do
  let block ← s.allocations p.base
  let target := (p.byteOffset.val : Int) + count * repr.size
  if s.live block && p.byteOffset.val ≤ block.repr.length &&
      0 ≤ target && target ≤ block.repr.length &&
      target < (2 ^ UScalarTy.numBits .Usize : Nat) then
    some ⟨p.base, ⟨BitVec.ofNat _ target.toNat⟩⟩
  else none

def distance (repr : Repr ty) (p q : RawPtr ty) (s : Heap) : Option Int := do
  let a ← s.allocations p.base
  let b ← s.allocations q.base
  let pa ← s.address p
  let qa ← s.address q
  let distance := (pa.val : Int) - qa.val
  if s.live a && s.live b && a.root == b.root && 0 < repr.size &&
      p.byteOffset.val ≤ a.repr.length && q.byteOffset.val ≤ b.repr.length &&
      distance % repr.size = 0 then some (distance / repr.size) else none

def retire (s : Heap) (id : Nat) : Heap :=
  let allocations := update s.allocations id
    ((s.allocations id).map fun block => { block with active := false })
  { s with allocations }

/-- Return an owned root to implicit safe Rust, without physical deallocation.
The address and allocation lifetime remain observable through retained metadata. -/
def returnOwned (repr : Repr ty) (p : RawPtr ty) (count : Nat) (s : Heap) :
    Option Heap := do
  let block ← s.allocations p.base
  let root ← s.allocations block.root
  if s.live block && block.owned && p.byteOffset.val = 0 &&
      block.bptr == root.bptr && block.repr.length == root.repr.length &&
      repr.align.val ∣ block.bptr.val && block.repr.length = count * repr.size &&
      block.repr.all (fun cell => cell.depth == some 0) && s.noAliases p.base block.root then
    commit (s.retire p.base)
  else none

/-- Physical death is distinct from return to safe Rust. This prototype checks
abstract ownership and full byte coverage, not an allocator's original layout. -/
def dealloc (repr : Repr ty) (p : RawPtr ty) (count : Nat) (s : Heap) : Option Heap := do
  let block ← s.allocations p.base
  let returned ← returnOwned repr p count s
  let allocations := update returned.allocations block.root
    ((returned.allocations block.root).map fun root => { root with alive := false })
  let s₁ := { returned with allocations }
  commit s₁

/-- Retire a nonowning baseline contribution; never decrement it into a writer.
Positive-depth uninitialized bytes remain protected until matching shares end. -/
def endExposureAt (repr : Repr ty) (p : RawPtr ty) (count depth : Nat) (s : Heap) :
    Option Heap := do
  let block ← s.allocations p.base
  if s.live block && !block.owned && p.byteOffset.val = 0 &&
      repr.align.val ∣ block.bptr.val && block.repr.length = count * repr.size &&
      block.repr.all (fun cell => cell.depth == some depth) then
    commit (s.retire p.base)
  else none

def freeBlock (repr : Repr ty) (p : RawPtr ty) (count : Nat) (own : Bool)
    (s : Heap) : Option Heap :=
  if own then dealloc repr p count s else endExposureAt repr p count 0 s

def endSharedExposure (repr : Repr ty) (p : RawPtr ty) (count : Nat)
    (s : Heap) : Option Heap :=
  endExposureAt repr p count 1 s

end Heap
end Aeneas.Std
