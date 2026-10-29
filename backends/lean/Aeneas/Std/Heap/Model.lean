module

public import Aeneas.Std.Heap.Axioms.Representation

/-! Instrumented byte memory. Byte contents and permissions have a canonical projection;
typed values and their validity are relational observations of the instrumented state.
The implementation of the instrumentation is deliberately abstract. -/

@[expose] public section

namespace Aeneas.Std

universe u v

namespace Block

/-- Executable shape of the partial relational observation. Failure neither grants
permission nor permits write-back to modify the representation. -/
noncomputable def decode (ty : Type u) (r : Std.Block.{u})
    (i : Nat) : Option (Cell ty) :=
  open Classical in
  if h : ∃ c, Std.Block.view ty r i c then some h.choose else none

theorem decode_eq_some {ty : Type u} {r : Std.Block.{u}}
    {i : Nat} {c : Cell ty} : Std.Block.decode ty r i = some c ↔ Std.Block.view ty r i c := by
  classical
  unfold decode
  split
  · rename_i h
    constructor
    · intro he
      exact Option.some.inj he ▸ h.choose_spec
    · intro hc
      exact congrArg some (Std.Block.view_unique ty r i _ _ h.choose_spec hc)
  · rename_i h
    constructor
    · intro he
      cases he
    · intro hc
      exact (h ⟨c, hc⟩).elim

theorem disjoint_same (ty : Type u) {i j : Nat} (h : i ≠ j) :
    CellsDisjoint ty i ty j := .inl ⟨rfl, h⟩

theorem set_decode_frame {ty U : Type u} {i j : Nat}
    {c : Option (Cell ty)} {r r' : Std.Block.{u}} (h : Std.Block.setCell ty i c r r')
    (hd : CellsDisjoint ty i U j) :
    Std.Block.decode U r' j = Std.Block.decode U r j := by
  classical
  unfold decode
  have he : (∃ value, Std.Block.view U r' j value) ↔ ∃ value, Std.Block.view U r j value :=
    exists_congr fun value => Std.Block.set_frame ty i c r r' h U j hd value
  by_cases hv : ∃ value, Std.Block.view U r j value
  · have hv' := he.mpr hv
    simp only [dite_eq_left hv, dite_eq_left hv']
    exact congrArg some (Std.Block.view_unique U r j _ _
      ((Std.Block.set_frame ty i c r r' h U j hd _).mp hv'.choose_spec) hv.choose_spec)
  · have hv' : ¬ ∃ value, Std.Block.view U r' j value := fun h => hv (he.mp h)
    simp [hv, hv']

/-- Byte correctness is a client obligation, not an unconditional encoding axiom.
The instrumentation may reject a byte-valid value (notably a pointer overwritten as an int). -/
def Realizes (ty : Type u) : Prop :=
  ∀ r i depth value, Std.Block.view ty r i (.shared depth (some value)) →
    (Heap.repr ty).supports value ∧
    (((Std.Block.bytes r).drop (i * Heap.size ty)).take (Heap.size ty)).map Cell.read =
      ((Heap.repr ty).encode value).map some

def Views (ty : Type u) (r : Std.Block.{u}) (start : Nat)
    (cs : List (Cell ty)) : Prop :=
  ∀ i (hi : i < cs.length), Std.Block.view ty r (start + i) cs[i]

/-- Bulk updates are just composition of single-index updates. -/
inductive Updates (ty : Type u) :
    Nat → List (Cell ty) → Std.Block.{u} → Std.Block.{u} → Prop where
  | nil (i r) : Updates ty i [] r r
  | cons {i c cs r r₁ r₂} :
      Std.Block.setCell ty i (some c) r r₁ →
      Updates ty (i + 1) cs r₁ r₂ →
      Updates ty i (c :: cs) r r₂

end Block

namespace Heap

variable {Block : Type v}

def empty : Heap Block := ⟨fun _ => none, 0⟩

def cells (s : Heap Block) (base : BasePtr) : Option Block :=
  (s.allocations base).map Allocation.repr

def allocated (s : Heap Block) (base : BasePtr) : Bool :=
  ((s.allocations base).map Allocation.owned).getD false

def alignment (s : Heap Block) (base : BasePtr) : Option Alignment :=
  (s.allocations base).map Allocation.alignment

def Aligned (ty : Type u) (s : Heap Std.Block.{u}) (base : BasePtr) : Prop :=
  ∃ a, s.alignment base = some a ∧ (Heap.align ty).val ∣ a.val

def Inv (s : Heap Block) : Prop :=
  ∀ base ≥ s.next, s.allocations base = none

def storeRepr (s : Heap Block) (base : BasePtr) (r : Block) : Heap Block :=
  { s with allocations := update s.allocations base ((s.allocations base).map fun a => { a with repr := r }) }

def createRepr (s : Heap Block) (r : Block) (own : Bool) (alignment : Alignment) : Heap Block :=
  { allocations := update s.allocations s.next (some ⟨r, alignment, own⟩)
    next := s.next + 1 }

def remove (s : Heap Block) (base : BasePtr) : Heap Block :=
  { s with allocations := update s.allocations base none }

noncomputable def observe (s : Heap Std.Block.{u}) (p : RawPtr ty) : Option (Cell ty) :=
  open Classical in
  if Aligned ty s p.base then (s.cells p.base).bind fun r => Std.Block.decode ty r p.index else none

noncomputable def extent (s : Heap Std.Block.{u}) (ty : Type u) (base : BasePtr) : Option Nat :=
  open Classical in
  if Aligned ty s base then (s.cells base).map (Std.Block.extent ty) else none

def Writable (ty : Type u) (r : Std.Block.{u}) (i : Nat) : Prop :=
  i < Std.Block.extent ty r ∧
  (∀ b, i * Heap.size ty ≤ b → b < (i + 1) * Heap.size ty →
    ∃ byte, (Std.Block.bytes r)[b]? = some byte ∧ byte.writable) ∧
  ∀ c, Std.Block.view ty r i c → c.writable

/-- `none` is an exact no-op, including for unavailable typed values. -/
def writeBack (p : RawPtr ty) (c : Option (Cell ty))
    (s₀ s₁ : Heap Std.Block.{u}) : Prop :=
  match c with
  | none => s₁ = s₀
  | some _ => ∃ r r', s₀.cells p.base = some r ∧ Aligned ty s₀ p.base ∧ Std.Block.setCell ty p.index c r r' ∧
      s₁ = s₀.storeRepr p.base r'

def replaceRange (s₀ : Heap Std.Block.{u}) (p : RawPtr ty)
    (old new : List (Cell ty)) (s₁ : Heap Std.Block.{u}) : Prop :=
  if old = [] then new = [] ∧ s₁ = s₀ else
    old.length = new.length ∧
    ∃ r r', s₀.cells p.base = some r ∧ Aligned ty s₀ p.base ∧ Std.Block.Views ty r p.index old ∧
      Std.Block.Updates ty p.index new r r' ∧ s₁ = s₀.storeRepr p.base r'

def newCells (cs : List (Cell ty)) (own : Bool)
    (s₀ : Heap Std.Block.{u}) (p : RawPtr ty) (s₁ : Heap Std.Block.{u}) : Prop :=
  s₀.Inv ∧ p = ⟨s₀.next, 0⟩ ∧
    ∃ r, Std.Block.create ty cs r ∧ s₁ = s₀.createRepr r own (Heap.align ty)

def alloc {ty : Type u} (count : Nat) :=
  newCells (ty := ty) (List.replicate count (.shared 0 none)) true

def newBlock (values : List ty) (own : Bool) :=
  newCells (Cell.full values) own

def newSharedExposure (values : List ty) :=
  newCells (values.map (Cell.shared 1 ∘ some)) false

/-- Pointer movement uses allocation extent, not the availability of typed values. -/
def offset (p : RawPtr ty) (count : Int)
    (s₀ : Heap Std.Block.{u}) (result : RawPtr ty) (s₁ : Heap Std.Block.{u}) : Prop :=
  (∃ n, s₀.extent ty p.base = some n ∧ p.index ≤ n ∧ result.index ≤ n) ∧
    result.base = p.base ∧ (result.index : Int) = (p.index : Int) + count ∧ s₁ = s₀

def read (p : RawPtr ty)
    (s₀ : Heap Std.Block.{u}) (value : ty) (s₁ : Heap Std.Block.{u}) : Prop :=
  (∃ r depth, s₀.cells p.base = some r ∧ Aligned ty s₀ p.base ∧
    Std.Block.view ty r p.index (.shared depth (some value))) ∧ s₁ = s₀

/-- Raw writes check canonical byte permissions even if typed decoding is unavailable. -/
def write (p : RawPtr ty) (value : ty)
    (s₀ : Heap Std.Block.{u}) (_ : Unit) (s₁ : Heap Std.Block.{u}) : Prop :=
  ∃ r r', s₀.cells p.base = some r ∧ Aligned ty s₀ p.base ∧ Writable ty r p.index ∧
    Std.Block.setCell ty p.index (some (.shared 0 (some value))) r r' ∧
    s₁ = s₀.storeRepr p.base r'

def borrowRange (p : RawPtr ty) (count : Nat)
    (s₀ : Heap Std.Block.{u}) (values : List ty) (s₁ : Heap Std.Block.{u}) : Prop :=
  values.length = count ∧ (values = [] ∨ 0 < Heap.size ty) ∧
    replaceRange s₀ p (Cell.full values) (List.replicate count .borrowed) s₁

/-- Privileged restoration at the original type, invoked by the matching continuation. -/
def endBorrowRange (p : RawPtr ty) (values : List ty)
    (s₀ : Heap Std.Block.{u}) (_ : Unit) (s₁ : Heap Std.Block.{u}) : Prop :=
  replaceRange s₀ p (List.replicate values.length .borrowed) (Cell.full values) s₁

def shareRange (p : RawPtr ty) (count : Nat)
    (s₀ : Heap Std.Block.{u}) (values : List ty) (s₁ : Heap Std.Block.{u}) : Prop :=
  values.length = count ∧ ∃ depth,
    replaceRange s₀ p (values.map (Cell.shared depth ∘ some))
      (values.map (Cell.shared (depth + 1) ∘ some)) s₁

def endShareRange (p : RawPtr ty) (values : List ty)
    (s₀ : Heap Std.Block.{u}) (_ : Unit) (s₁ : Heap Std.Block.{u}) : Prop :=
  ∃ depth, replaceRange s₀ p (values.map (Cell.shared (depth + 1) ∘ some))
    (values.map (Cell.shared depth ∘ some)) s₁

def Whole (s : Heap Std.Block.{u}) (p : RawPtr ty) (cs : List (Cell ty)) : Prop :=
  ∃ r, s.cells p.base = some r ∧ Aligned ty s p.base ∧ Std.Block.extent ty r = cs.length ∧ Std.Block.Views ty r 0 cs ∧
    (Std.Block.bytes r).length = cs.length * Heap.size ty

def freeBlock (p : RawPtr ty) (count : Nat) (own : Bool)
    (s₀ : Heap Std.Block.{u}) (_ : Unit) (s₁ : Heap Std.Block.{u}) : Prop :=
  p.index = 0 ∧ s₀.allocated p.base = own ∧
    (∃ cs, Whole s₀ p cs ∧ cs.length = count ∧ ∀ c ∈ cs, c.writable) ∧
    s₁ = s₀.remove p.base

def endSharedExposure (p : RawPtr ty) (values : List ty)
    (s₀ : Heap Std.Block.{u}) (_ : Unit) (s₁ : Heap Std.Block.{u}) : Prop :=
  p.index = 0 ∧ s₀.allocated p.base = false ∧
    Whole s₀ p (values.map (Cell.shared 1 ∘ some)) ∧ s₁ = s₀.remove p.base

end Heap
end Aeneas.Std
