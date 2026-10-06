module
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.SliceDef
public import Aeneas.Std.Primitives
public import Aeneas.Std.Heap
public import Aeneas.SepLogic.Basic
@[expose] public section

open Aeneas SepLogic

namespace Aeneas.Std

inductive Mutability where
| Mut | Const

/-- A Rust raw pointer: an allocation identifier and an offset into it. -/
structure RawPtr (T : Type) (M : Mutability) where
  base : AllocId
  offset : Nat
  deriving Inhabited, DecidableEq

abbrev MutRawPtr (T : Type) := RawPtr T .Mut
abbrev ConstRawPtr (T : Type) := RawPtr T .Const

namespace RawPtr

def addr (q : RawPtr T M) : Loc := (q.base, q.offset)

def add (q : RawPtr T M) (i : Nat) : RawPtr T M :=
  ⟨q.base, q.offset + i⟩

def toConst (q : MutRawPtr T) : ConstRawPtr T :=
  ⟨q.base, q.offset⟩

/-- `q` owns the `values.length` slots from `q` on. -/
def pointsToRange (q : RawPtr T M) (values : List T) : IProp :=
  owns (Heap.rangeHeap q.addr values)

def pointsTo (q : RawPtr T M) (value : T) : IProp :=
  owns (Heap.singleton q.addr value)

end RawPtr

instance instPointsToRawPtr {T : Type} {M : Mutability} :
    PointsTo (RawPtr T M) T := ⟨RawPtr.pointsTo⟩

notation:50 q:50 " ↦* " values:50 => RawPtr.pointsToRange q values

def RawPtr.allocArray {β : Type} (values : List T) (mk : Loc → β) : Result β :=
  Result.guardedModify (fun _ => True) fun h _ =>
    (mk (Heap.freshLoc h), Heap.freshHeap h values)

def RawPtr.materialize (values : List T) : Result (RawPtr T M) :=
  RawPtr.allocArray values fun l => ⟨l.1, l.2⟩

def MutRawPtr.alloc (value : T) : Result (MutRawPtr T) :=
  RawPtr.allocArray [value] fun l => ⟨l.1, l.2⟩

namespace RawPtr

structure Readable (q : RawPtr T M) (h : Heap) : Prop where
  contains : Heap.contains h T q.addr

def read (q : RawPtr T M) : Result T :=
  Result.guardedModify (fun h => q.Readable h) fun h hReadable =>
    (Heap.read q.addr h hReadable.contains, h)

end RawPtr

def MutRawPtr.write (q : MutRawPtr T) (value : T) : Result Unit :=
  Result.guardedModify (fun h => Heap.contains h T q.addr) fun h hContains =>
    ((), Heap.update q.addr value h hContains)

def MutRawPtr.free (q : MutRawPtr T) : Result Unit :=
  Result.guardedModify (fun h => Heap.contains h T q.addr) fun h hContains =>
    ((), Heap.free q.addr h hContains)

def MutRawPtr.mut_to_raw (value : T) : Result (MutRawPtr T) :=
  MutRawPtr.alloc value

def MutRawPtr.end_mut_to_raw (q : MutRawPtr T) : Result T := do
  let value ← q.read
  MutRawPtr.free q
  pure value

inductive ScalarKind where
| Signed (ty : IScalarTy)
| Unsigned (ty : UScalarTy)

class IsScalar (T : Type) where
  isScalar : (∃ ty, T = UScalar ty) ∨ (∃ ty, T = IScalar ty)
  size : Usize
  toBytes : Slice T → Result (Slice U8)
  fromBytes : Slice U8 → Result (Slice T)

/-- Unsupported: changing the element type requires reinterpreting the typed heap. -/
def RawPtr.cast_scalar {T} {M} (T' : Type) (M' : Mutability)
    [IsScalar T] [IsScalar T'] (_ : RawPtr T M) :
    Result (RawPtr T' M') :=
  .fail .undef

/-- A bounded mutable view into a heap allocation, modelling `&mut [T]`. -/
structure Buffer (T : Type) where
  base : AllocId
  offset : Nat
  length : Nat
  deriving Inhabited, DecidableEq

namespace Buffer

def ptr (b : Buffer T) : MutRawPtr T :=
  ⟨b.base, b.offset⟩

def pointsTo (b : Buffer T) (values : List T) : IProp :=
  iprop(⌜values.length = b.length⌝ ∗ b.ptr ↦* values)

end Buffer

instance instPointsToBuffer {T : Type} :
    PointsTo (Buffer T) (List T) := ⟨Buffer.pointsTo⟩

end Aeneas.Std
