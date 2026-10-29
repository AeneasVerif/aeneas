module

public import Lean
public import Batteries.Data.List.Basic

/-! Instrumented byte memory. Byte contents and permissions have a canonical projection;
typed values and their validity are relational observations of the instrumented state.
The implementation of the instrumentation is deliberately abstract. -/

@[expose] public section

namespace Aeneas.Std

universe u v

def update {α : Type u} {β : Type v} [DecidableEq α]
    (f : α → β) (key : α) (value : β) : α → β :=
  fun k => if k = key then value else f k

abbrev BasePtr := Nat

inductive Permission where
  | shared (depth : Nat)
  | uninitialized
  | borrowed
  deriving DecidableEq

@[simp] def Permission.writable : Permission → Prop
  | .shared 0 | .uninitialized => True
  | _ => False

inductive Cell (ty : Type u) where
  | shared (depth : Nat) (value : ty)
  | uninitialized
  | borrowed

@[simp] def Cell.permission : Cell ty → Permission
  | .shared depth _ => .shared depth
  | .uninitialized => .uninitialized
  | .borrowed => .borrowed

def Cell.writable (c : Cell ty) : Prop := c.permission.writable

def Cell.read : Cell ty → Option ty
  | .shared _ value => some value
  | _ => none

def Cell.full (values : List ty) : List (Cell ty) :=
  values.map (Cell.shared 0)

structure RawPtr (ty : Type u) where
  base : BasePtr
  index : Nat
  deriving Inhabited

/-- Rust distinguishes `*mut T` and `*const T`, but neither type alone grants access.
This model currently erases pointer constness: heap-cell permissions authorize reads and writes,
and conversions must respect the originating borrows, and raw-pointer casting does not
change permissions. We could later refine the model to characterize updates through a const
pointer as UB. -/
abbrev MutRawPtr (ty : Type u) := RawPtr ty
abbrev ConstRawPtr (ty : Type u) := RawPtr ty

structure Heap (Repr : Type v) where
  cells : BasePtr → Option Repr
  allocated : BasePtr → Bool
  next : BasePtr

/-- A caller-supplied byte codec. Its domain records which values the finite encoding
supports; no finite codec for every value of every Lean type is assumed. Pointer validity
additionally depends on the instrumented layout, not just this byte decoder. -/
structure ByteCodec (ty : Type u) where
  byteLength : Nat
  encode : ty → List (BitVec 8)
  decode : List (BitVec 8) → Option ty
  supports : ty → Prop
  encode_length : ∀ value, (encode value).length = byteLength
  roundTrip : ∀ value, supports value → decode (encode value) = some value

inductive MemoryKind where
  | integer
  | pointer
  | other
  deriving DecidableEq

/-- Byte intervals are half-open. Same-type zero-sized cells retain distinct logical
indices; exclusive borrowing of zero-sized cells is not provided. -/
def CellsDisjoint (size : Type u → Nat) (T : Type u) (i : Nat)
    (U : Type u) (j : Nat) : Prop :=
  (T = U ∧ i ≠ j) ∨
  (T ≠ U ∧ (size T = 0 ∨ size U = 0)) ∨
  (0 < size T ∧ 0 < size U ∧
    ((i + 1) * size T ≤ j * size U ∨ (j + 1) * size U ≤ i * size T))

/-- An abstract instrumented layout. `view` is partial and single-valued, but need not
exist at every type or survive an overlapping update. `setCell` is relational and updates
one typed index atomically. It is an internal operation: raw access checks byte permissions,
whereas borrow restoration is reserved to the matching translated continuation.

The byte projection uses `BitVec 8`, the payload of Rust `u8`, to avoid importing the
effectful scalar library into the memory-effect definition. -/
structure Layout where
  Repr : Type (u + 1)
  byteLength : Type u → Nat
  kind : Type u → MemoryKind
  bytes : Repr → List (BitVec 8)
  permission : Repr → Nat → Option Permission
  extent : (ty : Type u) → Repr → Nat
  view : (ty : Type u) → Repr → Nat → Cell ty → Prop
  setCell : (ty : Type u) → Nat → Option (Cell ty) → Repr → Repr → Prop
  create : (ty : Type u) → List (Cell ty) → Repr → Prop
  permission_bounds : ∀ r b, (permission r b).isSome = (b < (bytes r).length)
  extent_bytes : ∀ ty r, 0 < byteLength ty →
    extent ty r = (bytes r).length / byteLength ty
  view_unique : ∀ ty r i a b, view ty r i a → view ty r i b → a = b
  view_bound : ∀ ty r i c, view ty r i c → i < extent ty r
  view_permission : ∀ ty r i c, view ty r i c →
    ∀ b, i * byteLength ty ≤ b → b < (i + 1) * byteLength ty →
      permission r b = some c.permission
  create_exists : ∀ ty cs, ∃ r, create ty cs r
  create_extent : ∀ ty cs r, create ty cs r → extent ty r = cs.length
  create_bytes : ∀ ty cs r, create ty cs r →
    (bytes r).length = cs.length * byteLength ty
  create_view : ∀ ty cs r, create ty cs r →
    ∀ i (hi : i < cs.length), view ty r i cs[i]
  set_none : ∀ ty i r r', setCell ty i none r r' ↔ r' = r
  set_exists : ∀ ty i r, i < extent ty r →
    ∀ c, ∃ r', setCell ty i (some c) r r'
  set_bound : ∀ ty i c r r', setCell ty i (some c) r r' → i < extent ty r
  set_view : ∀ ty i c r r', setCell ty i (some c) r r' → view ty r' i c
  set_extent : ∀ ty i c r r', setCell ty i c r r' →
    ∀ U, extent U r' = extent U r
  set_bytes_length : ∀ ty i c r r', setCell ty i c r r' →
    (bytes r').length = (bytes r).length
  set_outside : ∀ ty i c r r', setCell ty i c r r' →
    ∀ b, b < i * byteLength ty ∨ (i + 1) * byteLength ty ≤ b →
      (bytes r')[b]? = (bytes r)[b]? ∧ permission r' b = permission r b
  set_frame : ∀ ty i c r r', setCell ty i c r r' →
    ∀ U j, CellsDisjoint byteLength ty i U j →
      ∀ value, view U r' j value ↔ view U r j value
  set_borrow_type : ∀ ty i r r', setCell ty i (some .borrowed) r r' →
    ∀ U j, ty ≠ U → ¬ CellsDisjoint byteLength ty i U j →
      ∀ value, ¬ view U r' j value
  set_integer_pointer : ∀ ty i depth value r r',
    setCell ty i (some (.shared depth value)) r r' → kind ty = .integer →
    ∀ U j, kind U = .pointer → ¬ CellsDisjoint byteLength ty i U j →
      ∀ c, ¬ view U r' j c

namespace Layout

/-- Executable shape of the partial relational observation. Failure neither grants
permission nor permits write-back to modify the representation. -/
noncomputable def decode (m : Layout.{u}) (ty : Type u) (r : m.Repr)
    (i : Nat) : Option (Cell ty) :=
  open Classical in
  if h : ∃ c, m.view ty r i c then some h.choose else none

theorem decode_eq_some {m : Layout.{u}} {ty : Type u} {r : m.Repr}
    {i : Nat} {c : Cell ty} : m.decode ty r i = some c ↔ m.view ty r i c := by
  classical
  unfold decode
  split
  · rename_i h
    constructor
    · intro he
      exact Option.some.inj he ▸ h.choose_spec
    · intro hc
      exact congrArg some (m.view_unique ty r i _ _ h.choose_spec hc)
  · rename_i h
    constructor
    · intro he
      cases he
    · intro hc
      exact (h ⟨c, hc⟩).elim

theorem disjoint_same (m : Layout.{u}) (ty : Type u) {i j : Nat} (h : i ≠ j) :
    CellsDisjoint m.byteLength ty i ty j := .inl ⟨rfl, h⟩

theorem set_decode_frame {m : Layout.{u}} {ty U : Type u} {i j : Nat}
    {c : Option (Cell ty)} {r r' : m.Repr} (h : m.setCell ty i c r r')
    (hd : CellsDisjoint m.byteLength ty i U j) :
    m.decode U r' j = m.decode U r j := by
  classical
  unfold decode
  have he : (∃ value, m.view U r' j value) ↔ ∃ value, m.view U r j value :=
    exists_congr fun value => m.set_frame ty i c r r' h U j hd value
  by_cases hv : ∃ value, m.view U r j value
  · have hv' := he.mpr hv
    simp only [dite_eq_left hv, dite_eq_left hv']
    exact congrArg some (m.view_unique U r j _ _
      ((m.set_frame ty i c r r' h U j hd _).mp hv'.choose_spec) hv.choose_spec)
  · have hv' : ¬ ∃ value, m.view U r' j value := fun h => hv (he.mp h)
    simp [hv, hv']

/-- Matching a concrete codec is a client obligation, not a universal codec axiom.
The instrumentation may reject a byte-valid value (notably a pointer overwritten as an int). -/
def Realizes (m : Layout.{u}) (ty : Type u) (codec : ByteCodec ty) : Prop :=
  codec.byteLength = m.byteLength ty ∧
  ∀ r i depth value, m.view ty r i (.shared depth value) →
    codec.supports value ∧
    ((m.bytes r).drop (i * codec.byteLength)).take codec.byteLength = codec.encode value

def Views (m : Layout.{u}) (ty : Type u) (r : m.Repr) (start : Nat)
    (cs : List (Cell ty)) : Prop :=
  ∀ i (hi : i < cs.length), m.view ty r (start + i) cs[i]

/-- Bulk updates are just composition of single-index updates. -/
inductive Updates (m : Layout.{u}) (ty : Type u) :
    Nat → List (Cell ty) → m.Repr → m.Repr → Prop where
  | nil (i r) : Updates m ty i [] r r
  | cons {i c cs r r₁ r₂} :
      m.setCell ty i (some c) r r₁ →
      Updates m ty (i + 1) cs r₁ r₂ →
      Updates m ty i (c :: cs) r r₂

end Layout

namespace Heap

variable {Repr : Type v}

def empty : Heap Repr := ⟨fun _ => none, fun _ => false, 0⟩

def Inv (s : Heap Repr) : Prop :=
  ∀ base ≥ s.next, s.cells base = none ∧ s.allocated base = false

def storeRepr (s : Heap Repr) (base : BasePtr) (r : Repr) : Heap Repr :=
  { s with cells := update s.cells base (some r) }

def createRepr (s : Heap Repr) (r : Repr) (own : Bool) : Heap Repr :=
  { cells := update s.cells s.next (some r)
    allocated := update s.allocated s.next own
    next := s.next + 1 }

def remove (s : Heap Repr) (base : BasePtr) : Heap Repr :=
  { s with cells := update s.cells base none, allocated := update s.allocated base false }

noncomputable def observe (m : Layout.{u}) (s : Heap m.Repr) (p : RawPtr ty) : Option (Cell ty) :=
  (s.cells p.base).bind fun r => m.decode ty r p.index

def extent (m : Layout.{u}) (s : Heap m.Repr) (ty : Type u) (base : BasePtr) : Option Nat :=
  (s.cells base).map (m.extent ty)

def Writable (m : Layout.{u}) (ty : Type u) (r : m.Repr) (i : Nat) : Prop :=
  i < m.extent ty r ∧
  (∀ b, i * m.byteLength ty ≤ b → b < (i + 1) * m.byteLength ty →
    ∃ permission, m.permission r b = some permission ∧ permission.writable) ∧
  ∀ c, m.view ty r i c → c.writable

/-- `none` is an exact no-op, including for unavailable typed values. -/
def writeBack (m : Layout.{u}) (p : RawPtr ty) (c : Option (Cell ty))
    (s₀ s₁ : Heap m.Repr) : Prop :=
  match c with
  | none => s₁ = s₀
  | some _ => ∃ r r', s₀.cells p.base = some r ∧ m.setCell ty p.index c r r' ∧
      s₁ = s₀.storeRepr p.base r'

def replaceRange (m : Layout.{u}) (s₀ : Heap m.Repr) (p : RawPtr ty)
    (old new : List (Cell ty)) (s₁ : Heap m.Repr) : Prop :=
  if old = [] then new = [] ∧ s₁ = s₀ else
    old.length = new.length ∧
    ∃ r r', s₀.cells p.base = some r ∧ m.Views ty r p.index old ∧
      m.Updates ty p.index new r r' ∧ s₁ = s₀.storeRepr p.base r'

def newCells (m : Layout.{u}) (cs : List (Cell ty)) (own : Bool)
    (s₀ : Heap m.Repr) (p : RawPtr ty) (s₁ : Heap m.Repr) : Prop :=
  s₀.Inv ∧ p = ⟨s₀.next, 0⟩ ∧
    ∃ r, m.create ty cs r ∧ s₁ = s₀.createRepr r own

def alloc (m : Layout.{u}) {ty : Type u} (count : Nat) :=
  newCells m (ty := ty) (List.replicate count .uninitialized) true

def newBlock (m : Layout.{u}) (values : List ty) (own : Bool) :=
  newCells m (Cell.full values) own

def newSharedExposure (m : Layout.{u}) (values : List ty) :=
  newCells m (values.map (Cell.shared 1)) false

/-- Pointer movement uses allocation extent, not the availability of typed values. -/
def offset (m : Layout.{u}) (p : RawPtr ty) (count : Int)
    (s₀ : Heap m.Repr) (result : RawPtr ty) (s₁ : Heap m.Repr) : Prop :=
  (∃ n, s₀.extent m ty p.base = some n ∧ p.index ≤ n ∧ result.index ≤ n) ∧
    result.base = p.base ∧ (result.index : Int) = (p.index : Int) + count ∧ s₁ = s₀

def read (m : Layout.{u}) (p : RawPtr ty)
    (s₀ : Heap m.Repr) (value : ty) (s₁ : Heap m.Repr) : Prop :=
  (∃ r depth, s₀.cells p.base = some r ∧ m.view ty r p.index (.shared depth value)) ∧ s₁ = s₀

/-- Raw writes check canonical byte permissions even if typed decoding is unavailable. -/
def write (m : Layout.{u}) (p : RawPtr ty) (value : ty)
    (s₀ : Heap m.Repr) (_ : Unit) (s₁ : Heap m.Repr) : Prop :=
  ∃ r r', s₀.cells p.base = some r ∧ Writable m ty r p.index ∧
    m.setCell ty p.index (some (.shared 0 value)) r r' ∧
    s₁ = s₀.storeRepr p.base r'

def borrowRange (m : Layout.{u}) (p : RawPtr ty) (count : Nat)
    (s₀ : Heap m.Repr) (values : List ty) (s₁ : Heap m.Repr) : Prop :=
  values.length = count ∧ (values = [] ∨ 0 < m.byteLength ty) ∧
    replaceRange m s₀ p (Cell.full values) (List.replicate count .borrowed) s₁

/-- Privileged restoration at the original type, invoked by the matching continuation. -/
def endBorrowRange (m : Layout.{u}) (p : RawPtr ty) (values : List ty)
    (s₀ : Heap m.Repr) (_ : Unit) (s₁ : Heap m.Repr) : Prop :=
  replaceRange m s₀ p (List.replicate values.length .borrowed) (Cell.full values) s₁

def shareRange (m : Layout.{u}) (p : RawPtr ty) (count : Nat)
    (s₀ : Heap m.Repr) (values : List ty) (s₁ : Heap m.Repr) : Prop :=
  values.length = count ∧ ∃ depth,
    replaceRange m s₀ p (values.map (Cell.shared depth))
      (values.map (Cell.shared (depth + 1))) s₁

def endShareRange (m : Layout.{u}) (p : RawPtr ty) (values : List ty)
    (s₀ : Heap m.Repr) (_ : Unit) (s₁ : Heap m.Repr) : Prop :=
  ∃ depth, replaceRange m s₀ p (values.map (Cell.shared (depth + 1)))
    (values.map (Cell.shared depth)) s₁

def Whole (m : Layout.{u}) (s : Heap m.Repr) (p : RawPtr ty) (cs : List (Cell ty)) : Prop :=
  ∃ r, s.cells p.base = some r ∧ m.extent ty r = cs.length ∧ m.Views ty r 0 cs ∧
    (m.bytes r).length = cs.length * m.byteLength ty

def freeBlock (m : Layout.{u}) (p : RawPtr ty) (count : Nat) (own : Bool)
    (s₀ : Heap m.Repr) (_ : Unit) (s₁ : Heap m.Repr) : Prop :=
  p.index = 0 ∧ s₀.allocated p.base = own ∧
    (∃ cs, Whole m s₀ p cs ∧ cs.length = count ∧ ∀ c ∈ cs, c.writable) ∧
    s₁ = s₀.remove p.base

def endSharedExposure (m : Layout.{u}) (p : RawPtr ty) (values : List ty)
    (s₀ : Heap m.Repr) (_ : Unit) (s₁ : Heap m.Repr) : Prop :=
  p.index = 0 ∧ s₀.allocated p.base = false ∧
    Whole m s₀ p (values.map (Cell.shared 1)) ∧ s₁ = s₀.remove p.base

end Heap
end Aeneas.Std
