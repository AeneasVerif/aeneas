module

public import Lean
public import Batteries.Data.List.Basic

/-! Typed explicit memory, separate from allocation cleanup authority.

Each base stores one abstract representation. A typed pointer selects an interpretation;
offsets count cells, not bytes. Cells track initialization and borrow permissions.
`allocated` records only the right to recover allocation ownership or deallocate.
Views instead use a matching backward computation for cleanup.

`Heap` and its operations are parametric in the representation model. No representation
implementation, byte layout, or alignment convention is fixed here.

Pointer equality, pointer-integer conversions, byte layouts, and higher-order store are not
provided by this model. Raw-pointer mutability is erased; access is checked at the pointee. -/

@[expose] public section

namespace Aeneas.Std

universe u v

def update {α : Type u} {β : Type v} [DecidableEq α]
    (f : α → β) (key : α) (value : β) : α → β :=
  fun k => if k = key then value else f k

abbrev BasePtr := Nat

/-- `none`: borrowed; `some 0`: full access; positive depth: shared read access. -/
abbrev Frac := Option Nat

inductive Cell (ty : Type u) where
  | val (f : Frac) (value : ty)
  | uninitialized

def Cell.writable : Cell ty → Prop
  | .val (some 0) _ | .uninitialized => True
  | _ => False

/-- Only initialized cells with a remaining permission expose a value. -/
def Cell.read : Cell ty → Option ty
  | .val (some _) value => some value
  | _ => none

/-- Same access state and readable value; borrowed payloads are hidden. -/
def Cell.ReadEquivalent : Cell ty → Cell ty → Prop
  | .val none _, .val none _ => True
  | .val (some f) x, .val (some g) y => f = g ∧ x = y
  | .uninitialized, .uninitialized => True
  | _, _ => False

/-- A raw update may change writable cells, carrying all other cells through unchanged.
This describes the observable update, not authorization of a same-value write at a footprint. -/
def Cell.WriteCompatible (old new : Cell ty) : Prop :=
  old.writable ∨ old = new

def Cell.full (values : List ty) : List (Cell ty) :=
  values.map (.val (some 0))

def Cell.borrowed (values : List ty) : List (Cell ty) :=
  values.map (.val none)

def Cell.shared (fraction : Nat) (values : List ty) : List (Cell ty) :=
  values.map (.val (some fraction))

structure RawPtr (ty : Type u) where
  base : BasePtr
  offset : Nat
  deriving Inhabited

/-- Extraction aliases, not distinct permission-bearing pointer types. -/
abbrev MutRawPtr (ty : Type u) := RawPtr ty
abbrev ConstRawPtr (ty : Type u) := RawPtr ty

/-- Compatibility argument of the existing, unsupported scalar-pointer cast wrapper only. -/
inductive Mutability where
  | Mut
  | Const

def RawPtr.shift (p : RawPtr ty) (count : Nat) : RawPtr ty :=
  ⟨p.base, p.offset + count⟩

structure Heap (Repr : Type v) where
  cells : BasePtr → Option Repr
  allocated : BasePtr → Bool
  next : BasePtr

def RoundTrip {Repr : Type v}
    (represent : (ty : Type u) → List (Cell ty) → Repr)
    (interpret : (ty : Type u) → Repr → Option (List (Cell ty))) : Prop :=
  ∀ ty cs, interpret ty (represent ty cs) = some cs

/-- Every successful interpretation is entirely uninitialized; success is not implied. -/
def Uninitialized {Repr : Type v}
    (interpret : (ty : Type u) → Repr → Option (List (Cell ty))) (r : Repr) : Prop :=
  ∀ ty cs, interpret ty r = some cs → ∀ c ∈ cs, c = .uninitialized

/-- An authorized read observation, including failure. Hidden interpretation payloads are
not observations. The index is intentionally partial: absence means the read cannot succeed. -/
def readCell {Repr : Type v}
    (interpret : (ty : Type u) → Repr → Option (List (Cell ty)))
    (ty : Type u) (r : Repr) (index : Nat) : Option ty :=
  (interpret ty r).bind fun cs => cs[index]?.bind Cell.read

/-- Re-encoding a view after varying only its unreadable payloads cannot change any
authorized read at another type. This includes success/failure, and applies to arbitrary
initial representations, not just those originally produced by `represent`.
Consequently, a layout cannot hide read-observable padding outside its typed information. -/
def ReadLaw {Repr : Type v}
    (represent : (ty : Type u) → List (Cell ty) → Repr)
    (interpret : (ty : Type u) → Repr → Option (List (Cell ty))) : Prop :=
  ∀ (T : Type u) (r : Repr) (old new : List (Cell T)),
    interpret T r = some old →
    List.Forall₂ Cell.ReadEquivalent old new →
    ∀ (U : Type u) (index : Nat),
      readCell interpret U r index = readCell interpret U (represent T new) index

/-- A permitted update through `T` preserves every protected cell visible through `U`:
its value, fraction, and continued interpretability. No equality between differently
typed cell indices is assumed. A failed `U` interpretation gives no access rights.
Precise overlap authorization and outside-footprint locality are separate obligations;
this law constrains updates observable through the current whole-representation API. -/
def WriteLaw {Repr : Type v}
    (represent : (ty : Type u) → List (Cell ty) → Repr)
    (interpret : (ty : Type u) → Repr → Option (List (Cell ty))) : Prop :=
  ∀ (T : Type u) (r : Repr) (old new : List (Cell T)),
    interpret T r = some old →
    List.Forall₂ Cell.WriteCompatible old new →
    ∀ (U : Type u) (cs : List (Cell U)), interpret U r = some cs →
      ∀ (index : Nat) (hi : index < cs.length), ¬ cs[index].writable →
        ((interpret U (represent T new)).bind fun updated => updated[index]?) = some cs[index]

/-- Representation laws and a total typed, cell-count allocator.

A simple intended consistency example stores a type tag and its list of cells, with
interpretation returning `none` at every different type. Round-trip then recovers the
stored list; the read law hides borrowed payloads, and the write law preserves protected
cells. Fresh storage carries the requested type tag and uninitialized cells, including
an empty list when the count is zero. This is an informal example, not a checked instance;
the interface does not require type tags or rule out compatible cross-type views. -/
structure Layout where
  Repr : Type (u + 1)
  represent : (ty : Type u) → List (Cell ty) → Repr
  interpret : (ty : Type u) → Repr → Option (List (Cell ty))
  roundTrip : RoundTrip represent interpret
  readLaw : ReadLaw represent interpret
  writeLaw : WriteLaw represent interpret
  fresh : (ty : Type u) → Nat → Repr
  fresh_interpret : ∀ ty count,
    interpret ty (fresh ty count) = some (List.replicate count .uninitialized)
  fresh_uninitialized : ∀ ty count, Uninitialized interpret (fresh ty count)

namespace Heap

variable {Repr : Type v}

def empty : Heap Repr := ⟨fun _ => none, fun _ => false, 0⟩

def Inv (s : Heap Repr) : Prop :=
  ∀ base ≥ s.next, s.cells base = none ∧ s.allocated base = false

def load (interpret : (ty : Type u) → Repr → Option (List (Cell ty)))
    (s : Heap Repr) (ty : Type u) (base : BasePtr) : Option (List (Cell ty)) :=
  (s.cells base).bind (interpret ty)

def store (represent : (ty : Type u) → List (Cell ty) → Repr)
    (s : Heap Repr) (ty : Type u) (base : BasePtr) (cs : List (Cell ty)) : Heap Repr :=
  { s with cells := update s.cells base (some (represent ty cs)) }

def replaceRange (m : Layout.{u}) (s₀ : Heap m.Repr) (p : RawPtr ty)
    (old new : List (Cell ty)) (s₁ : Heap m.Repr) : Prop :=
  if old = [] then new = [] ∧ s₁ = s₀ else
    old.length = new.length ∧
    ∃ before after,
      before.length = p.offset ∧
      s₀.load m.interpret ty p.base = some (before ++ old ++ after) ∧
      s₁ = s₀.store m.represent ty p.base (before ++ new ++ after)

def createRepr (s : Heap Repr) (r : Repr) (ownAllocation : Bool) : Heap Repr :=
  { cells := update s.cells s.next (some r)
    allocated := update s.allocated s.next ownAllocation
    next := s.next + 1 }

def create (m : Layout.{u}) (s : Heap m.Repr) (cs : List (Cell ty))
    (ownAllocation : Bool) : Heap m.Repr :=
  s.createRepr (m.represent ty cs) ownAllocation

def remove (s : Heap Repr) (base : BasePtr) : Heap Repr :=
  { s with cells := update s.cells base none, allocated := update s.allocated base false }

def alloc (m : Layout.{u}) (count : Nat) (s₀ : Heap m.Repr)
    (p : RawPtr ty) (s₁ : Heap m.Repr) : Prop :=
  s₀.Inv ∧ p = ⟨s₀.next, 0⟩ ∧
  ∃ r, Uninitialized m.interpret r ∧
    m.interpret ty r = some (List.replicate count .uninitialized) ∧
    s₁ = s₀.createRepr r true

def newBlock (m : Layout.{u}) (values : List ty) (ownAllocation : Bool)
    (s₀ : Heap m.Repr) (p : RawPtr ty) (s₁ : Heap m.Repr) : Prop :=
  s₀.Inv ∧ p = ⟨s₀.next, 0⟩ ∧ s₁ = s₀.create m (Cell.full values) ownAllocation

def add (m : Layout.{u}) (p : RawPtr ty) (count : Nat)
    (s₀ : Heap m.Repr) (result : RawPtr ty) (s₁ : Heap m.Repr) : Prop :=
  (∃ cs, s₀.load m.interpret ty p.base = some cs ∧ p.offset + count ≤ cs.length) ∧
  result = p.shift count ∧ s₁ = s₀

def read (m : Layout.{u}) (p : RawPtr ty)
    (s₀ : Heap m.Repr) (value : ty) (s₁ : Heap m.Repr) : Prop :=
  (∃ before after fraction,
    before.length = p.offset ∧
    s₀.load m.interpret ty p.base =
      some (before ++ [.val (some fraction) value] ++ after)) ∧ s₁ = s₀

def write (m : Layout.{u}) (p : RawPtr ty) (value : ty)
    (s₀ : Heap m.Repr) (_ : Unit) (s₁ : Heap m.Repr) : Prop :=
  ∃ old : Cell ty, old.writable ∧
    replaceRange m s₀ p [old] [.val (some 0) value] s₁

def borrowRange (m : Layout.{u}) (p : RawPtr ty) (count : Nat)
    (s₀ : Heap m.Repr) (values : List ty) (s₁ : Heap m.Repr) : Prop :=
  values.length = count ∧
  replaceRange m s₀ p (Cell.full values) (Cell.borrowed values) s₁

def endBorrowRange (m : Layout.{u}) (p : RawPtr ty) (values : List ty)
    (s₀ : Heap m.Repr) (_ : Unit) (s₁ : Heap m.Repr) : Prop :=
  ∃ original : List ty,
    replaceRange m s₀ p (Cell.borrowed original) (Cell.full values) s₁

def shareRange (m : Layout.{u}) (p : RawPtr ty) (count : Nat)
    (s₀ : Heap m.Repr) (values : List ty) (s₁ : Heap m.Repr) : Prop :=
  values.length = count ∧ ∃ fraction,
    replaceRange m s₀ p (Cell.shared fraction values) (Cell.shared (fraction + 1) values) s₁

/-- Only the matching backward computation may invoke this operation. -/
def endShareRange (m : Layout.{u}) (p : RawPtr ty) (values : List ty)
    (s₀ : Heap m.Repr) (_ : Unit) (s₁ : Heap m.Repr) : Prop :=
  ∃ fraction,
    replaceRange m s₀ p (Cell.shared (fraction + 1) values) (Cell.shared fraction values) s₁

def newSharedView (m : Layout.{u}) (values : List ty)
    (s₀ : Heap m.Repr) (p : RawPtr ty) (s₁ : Heap m.Repr) : Prop :=
  s₀.Inv ∧ p = ⟨s₀.next, 0⟩ ∧ s₁ = s₀.create m (Cell.shared 1 values) false

def freeBlock (m : Layout.{u}) (p : RawPtr ty) (count : Nat) (ownAllocation : Bool)
    (s₀ : Heap m.Repr) (_ : Unit) (s₁ : Heap m.Repr) : Prop :=
  p.offset = 0 ∧ s₀.allocated p.base = ownAllocation ∧
  (∃ cs, s₀.load m.interpret ty p.base = some cs ∧
    cs.length = count ∧ ∀ c ∈ cs, c.writable) ∧ s₁ = s₀.remove p.base

def endSharedView (m : Layout.{u}) (p : RawPtr ty) (original : List ty)
    (s₀ : Heap m.Repr) (_ : Unit) (s₁ : Heap m.Repr) : Prop :=
  p.offset = 0 ∧ s₀.allocated p.base = false ∧
  s₀.load m.interpret ty p.base = some (Cell.shared 1 original) ∧ s₁ = s₀.remove p.base

end Heap
end Aeneas.Std
