module
public import Aeneas.Std.Delab
public import Aeneas.Std.Heap
public import Aeneas.SepLogic.IProp
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Scalar.Notations
public import Aeneas.Std.SliceDef
public import Aeneas.Data.List.List
public import Aeneas.Std.WP
public import Aeneas.Std.Primitives
public import Aeneas.SepLogic.Lemmas
public import Aeneas.SepLogic.Delab
public import Aeneas.SepLogic.Tactic.IFrame
public import Aeneas.SepLogic.Tactic.IIntro
public import Aeneas.SepLogic.Tactic.IRewrite
public import Aeneas.SepLogic.Tactic.ISimp
public import Aeneas.Tactic.Step.Init
@[expose] public section

open Aeneas SepLogic

namespace Aeneas.Std

/-! ### START Trusted definitions -/

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

def retype (q : RawPtr T M) : RawPtr U M' :=
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

def RawPtr.allocArray {β : Type} (values : List T) (mk : MutRawPtr T → β) : Result β :=
  Result.guardedModify (fun _ => True) fun h _ =>
    (mk ⟨(Heap.freshLoc h).1, (Heap.freshLoc h).2⟩, Heap.freshHeap h values)

def RawPtr.materialize (values : List T) : Result (RawPtr T M) :=
  RawPtr.allocArray values fun q => q.retype

def MutRawPtr.alloc (value : T) : Result (MutRawPtr T) :=
  RawPtr.allocArray [value] id

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

def MutRawPtr.freeRange (q : MutRawPtr T) : Nat → Result Unit
  | 0 => pure ()
  | n + 1 => do
      MutRawPtr.free q
      MutRawPtr.freeRange (q.add 1) n

def MutRawPtr.fillRange (q : MutRawPtr T) (value : T) : Nat → Result Unit
  | 0 => pure ()
  | n + 1 => do
      MutRawPtr.write q value
      MutRawPtr.fillRange (q.add 1) value n

def MutRawPtr.copyRange (dst : MutRawPtr T) (src : RawPtr T M) : Nat → Result Unit
  | 0 => pure ()
  | n + 1 => do
      let value ← src.read
      MutRawPtr.write dst value
      MutRawPtr.copyRange (dst.add 1) (src.add 1) n

def RawPtr.compareRange [DecidableEq T]
    (left : RawPtr T M₁) (right : RawPtr T M₂) : Nat → Result Bool
  | 0 => pure true
  | n + 1 => do
      let x ← left.read
      let y ← right.read
      if x = y then
        (left.add 1).compareRange (right.add 1) n
      else
        pure false

def MutRawPtr.takeRange (q : MutRawPtr T) : Nat → Result (List T)
  | 0 => pure []
  | n + 1 => do
      let value ← q.read
      MutRawPtr.free q
      let rest ← MutRawPtr.takeRange (q.add 1) n
      pure (value :: rest)

inductive ScalarKind where
| Signed (ty : IScalarTy)
| Unsigned (ty : UScalarTy)

class IsScalar (T : Type) where
  isScalar : (∃ ty, T = UScalar ty) ∨ (∃ ty, T = IScalar ty)
  size : Usize

/-- Keeps the address. Only casts between scalars of the same size are supported:
`add` counts in slots of the pointee type. -/
def RawPtr.cast_scalar {T} {M} (T' : Type) (M' : Mutability)
    [IsScalar T] [IsScalar T'] (p : RawPtr T M) :
    Result (RawPtr T' M') :=
  if IsScalar.size (T := T) = IsScalar.size (T := T') then .ok p.retype
  else .fail .undef

/-! ### END Trusted definitions -/

namespace RawPtr

def singleton (q : RawPtr T M) (value : T) : Heap :=
  Heap.singleton q.addr value

def contains (h : Heap) (q : RawPtr T M) : Prop :=
  Heap.contains h T q.addr

end RawPtr

instance {ty} : IsScalar (UScalar ty) where
  isScalar := by simp
  size := ⟨BitVec.ofNat _ (ty.numBits / 8)⟩

instance {ty} : IsScalar (IScalar ty) where
  isScalar := by simp
  size := ⟨BitVec.ofNat _ (ty.numBits / 8)⟩

open WP

namespace RawPtr

@[simp] theorem base_add (q : RawPtr T M) (i : Nat) :
    (q.add i).base = q.base := rfl

@[simp] theorem offset_add (q : RawPtr T M) (i : Nat) :
    (q.add i).offset = q.offset + i := rfl

@[simp] theorem add_zero (q : RawPtr T M) : q.add 0 = q := rfl

@[simp] theorem base_toConst (q : MutRawPtr T) : q.toConst.base = q.base := rfl

@[simp] theorem offset_toConst (q : MutRawPtr T) : q.toConst.offset = q.offset := rfl

@[simp] theorem addr_toConst (q : MutRawPtr T) : q.toConst.addr = q.addr := rfl

@[simp] theorem base_retype (q : RawPtr T M) : (q.retype : RawPtr U M').base = q.base := rfl

@[simp] theorem offset_retype (q : RawPtr T M) :
    (q.retype : RawPtr U M').offset = q.offset := rfl

@[simp] theorem addr_retype (q : RawPtr T M) : (q.retype : RawPtr U M').addr = q.addr := rfl

theorem addr_add (q : RawPtr T M) (i : Nat) :
    (q.add i).addr = q.addr.add i := rfl

theorem add_add (q : RawPtr T M) (i j : Nat) :
    (q.add i).add j = q.add (i + j) := by
  simp [add, Nat.add_assoc]

end RawPtr

theorem RawPtr.pointsTo_eq_singleton (q : RawPtr T M) (value : T) :
    (q ↦ value) = owns (Heap.singleton q.addr value) := rfl

theorem RawPtr.pointsTo_eq_range (q : RawPtr T M) (value : T) :
    (q ↦ value) = (q ↦* [value]) := by
  rw [RawPtr.pointsTo_eq_singleton, RawPtr.pointsToRange, Heap.rangeHeap_singleton]

@[simp] theorem RawPtr.pointsTo_toConst (q : MutRawPtr T) (value : T) :
    (q.toConst ↦ value) = (q ↦ value) := rfl

@[simp] theorem RawPtr.pointsToRange_toConst (q : MutRawPtr T) (values : List T) :
    (q.toConst ↦* values) = (q ↦* values) := rfl

@[simp] theorem RawPtr.pointsTo_retype (q : RawPtr T M) (value : T) :
    ((q.retype : RawPtr T M') ↦ value) = (q ↦ value) := rfl

@[simp] theorem RawPtr.pointsToRange_retype (q : RawPtr T M) (values : List T) :
    ((q.retype : RawPtr T M') ↦* values) = (q ↦* values) := rfl

namespace RawPtr

theorem pointsToRange_append (q : RawPtr T M) (xs ys : List T) :
    q ↦* (xs ++ ys) ⊣⊢ q ↦* xs ∗ (q.add xs.length) ↦* ys := by
  rw [pointsToRange, pointsToRange, pointsToRange, addr_add,
    Heap.rangeHeap_append q.addr xs ys]
  exact owns_union _ _ (Heap.compatible_rangeHeap_append q.addr xs ys)

theorem pointsToRange_split (q : RawPtr T M) (values : List T) (i : Nat) :
    q ↦* values ⊣⊢
      q ↦* values.take i ∗ (q.add (values.take i).length) ↦* values.drop i := by
  conv_lhs => rw [← List.take_append_drop i values]
  exact pointsToRange_append q (values.take i) (values.drop i)

theorem pointsToRange_eq_take_get_drop {q : RawPtr T M} {values : List T} {i : Nat}
    (hIndex : i < values.length) :
    (q ↦* values) =
      iprop(q ↦* values.take i ∗
        ((q.add i) ↦ values[i] ∗ (q.add (i + 1)) ↦* values.drop (i + 1))) := by
  have hTake : (values.take i).length = i := by simp; omega
  have hSplit := bientails_eq (pointsToRange_split q values i)
  rw [hTake] at hSplit
  rw [hSplit, List.drop_eq_getElem_cons hIndex,
    show values[i] :: values.drop (i + 1)
      = [values[i]] ++ values.drop (i + 1) from rfl,
    bientails_eq
      (pointsToRange_append (q.add i) [values[i]] (values.drop (i + 1))),
    ← pointsTo_eq_range]
  rfl

theorem pointsToRange_cons (q : RawPtr T M) (value : T) (rest : List T) :
    (q ↦* (value :: rest)) = iprop(q ↦ value ∗ (q.add 1) ↦* rest) := by
  rw [show (value :: rest) = [value] ++ rest from rfl,
    bientails_eq (pointsToRange_append q [value] rest), ← pointsTo_eq_range]
  rfl

@[simp] theorem pointsToRange_nil (q : RawPtr T M) :
    (q ↦* ([] : List T)) = emp :=
  bientails_eq ⟨fun _ _ => trivial, fun h _ => Heap.Sub.of_empty h⟩

end RawPtr

theorem RawPtr.pointsTo_exclusive (q : RawPtr T M) (value₁ value₂ : T) :
    q ↦ value₁ ∗ q ↦ value₂ ⊢ ⌜False⌝ := by
  rw [RawPtr.pointsTo_eq_singleton, RawPtr.pointsTo_eq_singleton]
  exact owns_singleton_exclusive q.addr value₁ value₂

namespace RawPtr

@[simp]
theorem not_contains_empty (q : RawPtr T M) :
    ¬ RawPtr.contains (∅ : Heap) q :=
  Heap.not_contains_empty q.addr

theorem contains_of_pointsTo {q : RawPtr T M} {value : T} {h : Heap}
    (hPointsTo : (q ↦ value) h) : RawPtr.contains h q :=
  Heap.contains_of_sub hPointsTo

theorem addr_injective {q r : RawPtr T M} (hEq : q.addr = r.addr) : q = r := by
  cases q
  cases r
  have hBase := congrArg Prod.fst hEq
  have hOffset := congrArg Prod.snd hEq
  simp only [RawPtr.addr] at hBase hOffset
  simp_all

theorem disjoint_singleton {q r : RawPtr T M} {value₁ value₂ : T} (hNe : q ≠ r) :
    PartialCommMonoid.Compatible (q.singleton value₁) (r.singleton value₂) :=
  Heap.disjoint_singleton fun hEq => hNe (addr_injective hEq)

end RawPtr

@[step]
theorem RawPtr.allocArray.spec {β : Type} (values : List T) (mk : MutRawPtr T → β)
    (post : β → IProp)
    (hPost : ∀ q : MutRawPtr T, q ↦* values ⊢ post (mk q)) :
    ⦃ emp ⦄ RawPtr.allocArray values mk ⦃ result => post result⦄ := by
  apply ispec_guardedModify
  intro h _ frame hCompatible
  have hFresh :
      PartialCommMonoid.Compatible
        (Heap.rangeHeap (Heap.freshLoc (h ∪ frame)) values) (h ∪ frame) :=
    Heap.compatible_freshLoc _ _
  obtain ⟨hFreshH, hFreshFrame⟩ :=
    (PartialCommMonoid.compatible_assoc
      (Heap.rangeHeap (Heap.freshLoc (h ∪ frame)) values) h frame).mpr
        ⟨hCompatible, hFresh⟩
  exact ⟨trivial, _, hFreshFrame,
    (PartialCommMonoid.union_assoc hFreshH hFreshFrame).symm,
    hPost _ _ (Heap.Sub.union_left hFreshH)⟩

@[step]
theorem RawPtr.materialize.spec (values : List T) :
    ⦃ emp ⦄ RawPtr.materialize (M := M) values
      ⦃ p => p ↦* values⦄ :=
  RawPtr.allocArray.spec _ _ _ fun _ => entails_refl _

@[step]
theorem MutRawPtr.alloc.spec (value : T) :
    ⦃ emp ⦄ MutRawPtr.alloc value ⦃ q => q ↦ value⦄ :=
  RawPtr.allocArray.spec _ _ _ fun q => by
    rw [RawPtr.pointsTo_eq_range]
    exact entails_refl _

namespace RawPtr

theorem readable_of_pointsTo {q : RawPtr T M} {value : T} {h : Heap}
    (hPointsTo : (q ↦ value) h) : q.Readable h :=
  ⟨Heap.contains_of_sub hPointsTo⟩

@[step]
theorem read.spec (q : RawPtr T M) (value : T) :
    ⦃ q ↦ value ⦄ q.read
      ⦃ result => ⌜result = value⌝ ∗ q ↦ value⦄ := by
  apply ispec_guardedModify
  intro h hPointsTo frame hCompatible
  have hPointsToFrame : (q ↦ value) (h ∪ frame) :=
    (q ↦ value).up_closed hPointsTo (Heap.Sub.union_left hCompatible)
  have hReadable : q.Readable (h ∪ frame) :=
    readable_of_pointsTo hPointsToFrame
  refine ⟨hReadable, h, hCompatible, rfl, ?_⟩
  exact (sep_pure_l _ _ h).mpr
    ⟨Heap.read_of_sub hPointsToFrame hReadable.contains, hPointsTo⟩

end RawPtr

@[step]
theorem MutRawPtr.write.spec (q : MutRawPtr T) (oldValue newValue : T) :
    ⦃ q ↦ oldValue ⦄ q.write newValue ⦃ q ↦ newValue⦄ := by
  apply ispec_guardedModify
  intro h hPointsTo frame hCompatible
  obtain ⟨rest, hCompatibleRest, rfl⟩ := hPointsTo
  have hContainsSlot := Heap.contains_singleton q.addr oldValue
  have hContains : Heap.contains (Heap.singleton q.addr oldValue ∪ rest) T q.addr :=
    Heap.contains_union_left hContainsSlot
  refine ⟨Heap.contains_union_left hContains,
    Heap.update q.addr newValue _ hContains,
    Heap.disjoint_update_left hCompatible hContains, ?_, ?_⟩
  · simpa only [show Heap.contains_union_left hContains =
        Heap.contains_union_left (h₂ := frame) hContains from rfl] using
      Heap.update_union_left q.addr newValue hContains
  · have hCompatibleNew :
        PartialCommMonoid.Compatible (Heap.singleton q.addr newValue) rest := by
      have hUpdated := Heap.disjoint_update_left (value := newValue)
        hCompatibleRest hContainsSlot
      rwa [Heap.update_singleton] at hUpdated
    rw [show hContains = Heap.contains_union_left hContainsSlot from
      Subsingleton.elim _ _, Heap.update_union_left q.addr newValue hContainsSlot,
      Heap.update_singleton]
    exact Heap.Sub.union_left hCompatibleNew

@[step]
theorem MutRawPtr.free.spec (q : MutRawPtr T) (value : T) :
    ⦃ q ↦ value ⦄ q.free ⦃ emp⦄ := by
  apply ispec_guardedModify
  intro h hPointsTo frame hCompatible
  have hContains : Heap.contains h T q.addr := Heap.contains_of_sub hPointsTo
  refine ⟨Heap.contains_union_left hContains, Heap.free q.addr h hContains,
    Heap.disjoint_free_left hCompatible hContains, ?_, trivial⟩
  simpa only [show Heap.contains_union_left hContains =
      Heap.contains_union_left (h₂ := frame) hContains from rfl] using
    Heap.free_union_left q.addr hCompatible hContains

@[step]
theorem MutRawPtr.freeRange.spec (q : MutRawPtr T) (values : List T) :
    ⦃ q ↦* values ⦄ q.freeRange values.length ⦃ emp⦄ := by
  induction values generalizing q with
  | nil =>
      simp only [List.length_nil, MutRawPtr.freeRange]
      simp only [RawPtr.pointsToRange_nil]
      change ispec emp (Result.ok ()) (fun _ => emp)
      rw [ispec_ok]
      iframe
  | cons value rest ih =>
      simp only [List.length_cons, MutRawPtr.freeRange, RawPtr.pointsToRange_cons]
      apply WP.ispec_bind (MutRawPtr.free.spec q value)
      · iframe
      · intro _
        simpa using ih (q := q.add 1)

namespace RawPtr

theorem take_set (values : List T) (i : Nat) (value : T) :
    (values.set i value).take i = values.take i := by
  apply List.ext_getElem (by simp)
  intro n h₁ _
  have hn : n < i := by simp at h₁; omega
  simp only [List.getElem_take, List.getElem_set,
    if_neg (show ¬ i = n by omega)]

theorem drop_set (values : List T) (i : Nat) (value : T) :
    (values.set i value).drop (i + 1) = values.drop (i + 1) := by
  apply List.ext_getElem (by simp)
  intro n _ _
  simp only [List.getElem_drop, List.getElem_set,
    if_neg (show ¬ i = i + 1 + n by omega)]

theorem read.spec_range (q : RawPtr T M) (values : List T) (i : Nat)
    (hIndex : i < values.length) :
    ⦃ q ↦* values ⦄ (q.add i).read
      ⦃ result => ⌜result = values[i]⌝ ∗ q ↦* values⦄ := by
  rw [pointsToRange_eq_take_get_drop hIndex]
  apply WP.ispec_mono (read.spec (q.add i) values[i]) <;> iframe

theorem read.spec_frame (q : RawPtr T M) (value : T) (H : IProp) :
    ⦃ q ↦ value ∗ H ⦄ q.read
      ⦃ result => ⌜result = value⌝ ∗ (q ↦ value ∗ H)⦄ := by
  apply WP.ispec_mono (read.spec q value) <;> iframe

end RawPtr

theorem MutRawPtr.write.spec_range (q : MutRawPtr T) (values : List T)
    (i : Nat) (value : T) (hIndex : i < values.length) :
    ⦃ q ↦* values ⦄ MutRawPtr.write (q.add i) value
      ⦃ q ↦* values.set i value⦄ := by
  rw [RawPtr.pointsToRange_eq_take_get_drop hIndex,
    RawPtr.pointsToRange_eq_take_get_drop
      (show i < (values.set i value).length by simpa using hIndex),
    RawPtr.take_set, RawPtr.drop_set, List.getElem_set_self]
  apply WP.ispec_mono (MutRawPtr.write.spec (q.add i) values[i] value) <;> iframe

/-- An operation on the slots `[i, i + ws.length)` of a range, which may also use `R`,
acts on the whole range. -/
theorem RawPtr.ispec_segment {α : Type} (q : RawPtr T M) (values ws : List T) (i : Nat)
    (hBounds : i + ws.length ≤ values.length) (R : IProp) (m : Result α) (Q : α → IProp)
    (hm : ⦃ (q.add i) ↦* (values.drop i).take ws.length ∗ R ⦄ m
      ⦃ r => (q.add i) ↦* ws ∗ Q r ⦄) :
    ⦃ q ↦* values ∗ R ⦄ m ⦃ r => q ↦* values.setSlice! i ws ∗ Q r ⦄ := by
  have hTake : (values.take i).length = i := by simp; omega
  have hMid : ((values.drop i).take ws.length).length = ws.length := by simp; omega
  have hSplit : (q ↦* values) = iprop(q ↦* values.take i ∗
      ((q.add i) ↦* (values.drop i).take ws.length ∗
        (q.add (i + ws.length)) ↦* values.drop (i + ws.length))) := by
    conv_lhs => rw [← List.take_append_drop i values,
      ← List.take_append_drop ws.length (values.drop i)]
    rw [bientails_eq (RawPtr.pointsToRange_append _ _ _), hTake,
      bientails_eq (RawPtr.pointsToRange_append _ _ _), hMid, RawPtr.add_add,
      List.drop_drop]
  have hSet : (q ↦* values.setSlice! i ws) = iprop(q ↦* values.take i ∗
      ((q.add i) ↦* ws ∗ (q.add (i + ws.length)) ↦* values.drop (i + ws.length))) := by
    have hMin : min ws.length (values.length - i) = ws.length := by omega
    rw [List.setSlice!, hMin, List.take_length, List.append_assoc,
      bientails_eq (RawPtr.pointsToRange_append _ _ _), hTake,
      bientails_eq (RawPtr.pointsToRange_append _ _ _), RawPtr.add_add]
  rw [hSplit, hSet]
  apply WP.ispec_mono hm <;> iframe

@[step]
theorem MutRawPtr.fillRange.spec (q : MutRawPtr T) (values : List T) (value : T) :
    ⦃ q ↦* values ⦄ q.fillRange value values.length
      ⦃ q ↦* List.replicate values.length value⦄ := by
  induction values generalizing q with
  | nil =>
      simp only [List.length_nil, MutRawPtr.fillRange]
      simp only [RawPtr.pointsToRange_nil, List.replicate_zero]
      change ispec emp (Result.ok ()) (fun _ => emp)
      rw [ispec_ok]
      iframe
  | cons old rest ih =>
      simp only [List.length_cons, List.replicate_succ, MutRawPtr.fillRange,
        RawPtr.pointsToRange_cons]
      apply WP.ispec_bind (MutRawPtr.write.spec q old value)
      · iframe
      · intro _
        apply WP.ispec_mono (ih (q := q.add 1)) <;> iframe

@[step]
theorem MutRawPtr.copyRange.spec (dst : MutRawPtr T) (src : RawPtr T M)
    (dstValues srcValues : List T)
    (hLength : dstValues.length = srcValues.length) :
    ⦃ dst ↦* dstValues ∗ src ↦* srcValues ⦄
      MutRawPtr.copyRange dst src srcValues.length
      ⦃ dst ↦* srcValues ∗ src ↦* srcValues⦄ := by
  induction srcValues generalizing dst src dstValues with
  | nil =>
      obtain rfl : dstValues = [] := by simpa using hLength
      simp only [List.length_nil, MutRawPtr.copyRange, RawPtr.pointsToRange_nil]
      apply (ispec_ok _).2
      iframe
  | cons value rest ih =>
      obtain ⟨old, oldRest, rfl⟩ : ∃ old oldRest, dstValues = old :: oldRest := by
        cases dstValues
        · simp at hLength
        · exact ⟨_, _, rfl⟩
      have hRest : oldRest.length = rest.length := by simpa using hLength
      simp only [List.length_cons, MutRawPtr.copyRange,
        RawPtr.pointsToRange_cons]
      apply WP.ispec_bind
        (F := iprop(dst ↦ old ∗ (dst.add 1) ↦* oldRest ∗
          (src.add 1) ↦* rest))
        (RawPtr.read.spec src value)
      · change
          iprop((dst ↦ old ∗ (dst.add 1) ↦* oldRest) ∗
            (src ↦ value ∗ (src.add 1) ↦* rest)) ⊢
          iprop(src ↦ value ∗
            (dst ↦ old ∗ (dst.add 1) ↦* oldRest ∗
              (src.add 1) ↦* rest))
        iframe
      · intro readValue
        iintro hRead
        subst readValue
        apply WP.ispec_bind
          (F := iprop((dst.add 1) ↦* oldRest ∗ src ↦ value ∗
            (src.add 1) ↦* rest))
          (MutRawPtr.write.spec dst old value)
        · iframe
        · intro _
          apply WP.ispec_mono
            (ih (dst := dst.add 1) (src := src.add 1) (dstValues := oldRest) hRest)
          · iframe
          apply postWand_intro
          intro _
          change
            iprop(((dst.add 1) ↦* rest ∗ (src.add 1) ↦* rest) ∗
              (dst ↦ value ∗ src ↦ value)) ⊢
            iprop((dst ↦ value ∗ (dst.add 1) ↦* rest) ∗
              (src ↦ value ∗ (src.add 1) ↦* rest))
          iframe

@[step]
theorem RawPtr.compareRange.spec [DecidableEq T]
    (left : RawPtr T M₁) (right : RawPtr T M₂)
    (leftValues rightValues : List T)
    (hLength : leftValues.length = rightValues.length) :
    ⦃ left ↦* leftValues ∗ right ↦* rightValues ⦄
      left.compareRange right leftValues.length
      ⦃ result => ⌜result = decide (leftValues = rightValues)⌝ ∗
        (left ↦* leftValues ∗ right ↦* rightValues)⦄ := by
  induction leftValues generalizing left right rightValues with
  | nil =>
      obtain rfl : rightValues = [] := by simpa using hLength.symm
      simp only [List.length_nil, RawPtr.compareRange,
        RawPtr.pointsToRange_nil]
      apply (ispec_ok _).2
      iframe
  | cons x leftRest ih =>
      obtain ⟨y, rightRest, rfl⟩ : ∃ y rightRest, rightValues = y :: rightRest := by
        cases rightValues
        · simp at hLength
        · exact ⟨_, _, rfl⟩
      have hRest : leftRest.length = rightRest.length := by simpa using hLength
      simp only [List.length_cons, RawPtr.compareRange,
        RawPtr.pointsToRange_cons]
      apply WP.ispec_bind
        (F := iprop((left.add 1) ↦* leftRest ∗ right ↦ y ∗
          (right.add 1) ↦* rightRest))
        (RawPtr.read.spec left x)
      · iframe
      · intro readX
        iintro hReadX
        subst readX
        apply WP.ispec_bind
          (F := iprop(left ↦ x ∗ (left.add 1) ↦* leftRest ∗
            (right.add 1) ↦* rightRest))
          (RawPtr.read.spec right y)
        · iframe
        · intro readY
          iintro hReadY
          subst readY
          by_cases hxy : x = y
          · subst y
            simp only [List.cons.injEq, true_and]
            apply WP.ispec_mono
              (ih (left := left.add 1) (right := right.add 1) (rightValues := rightRest) hRest)
              <;> iframe
          · simp only [if_neg hxy]
            apply (ispec_ok _).2
            simp only [List.cons.injEq, hxy, false_and]
            iframe

@[step]
theorem MutRawPtr.mut_to_raw.spec (value : T) :
    ⦃ emp ⦄ MutRawPtr.mut_to_raw value ⦃ q => q ↦ value⦄ :=
  MutRawPtr.alloc.spec value

@[step]
theorem MutRawPtr.takeRange.spec (q : MutRawPtr T) (values : List T) :
    ⦃ q ↦* values ⦄ MutRawPtr.takeRange q values.length
      ⦃ result => ⌜result = values⌝⦄ := by
  induction values generalizing q with
  | nil =>
      simp only [List.length_nil, MutRawPtr.takeRange]
      simp only [RawPtr.pointsToRange_nil]
      change ispec emp (Result.ok []) (fun result => ⌜result = []⌝)
      rw [ispec_ok]
      simp
  | cons value rest ih =>
      simp only [List.length_cons, MutRawPtr.takeRange,
        RawPtr.pointsToRange_cons]
      apply WP.ispec_bind
        (F := (q.add 1) ↦* rest)
        (RawPtr.read.spec q value)
      · iframe
      · intro readValue
        iintro hRead
        subst readValue
        apply WP.ispec_bind
          (F := (q.add 1) ↦* rest)
          (MutRawPtr.free.spec q value)
        · iframe
        · intro _
          apply WP.ispec_bind (F := emp) (ih (q := q.add 1))
          · iframe
          intro result
          apply (ispec_ok _).2
          iintro hResult
          subst result
          iframe

theorem MutRawPtr.takeRange.spec_of_length (q : MutRawPtr T)
    (values : List T) (n : Nat) (hLength : values.length = n) :
    ⦃ q ↦* values ⦄ MutRawPtr.takeRange q n
      ⦃ result => ⌜result = values⌝⦄ := by
  subst n
  exact MutRawPtr.takeRange.spec q values

@[step]
theorem MutRawPtr.end_mut_to_raw.spec {value : T} (q : MutRawPtr T) :
    ⦃ q ↦ value ⦄ MutRawPtr.end_mut_to_raw q
      ⦃ result => ⌜result = value⌝⦄ := by
  unfold MutRawPtr.end_mut_to_raw
  apply WP.ispec_bind (RawPtr.read.spec q value)
  · iframe
  · intro readValue
    iintro hRead
    subst readValue
    apply WP.ispec_bind (MutRawPtr.free.spec q value)
    · iframe
    · intro _
      apply (ispec_ok _).2
      iframe

@[step]
theorem RawPtr.cast_scalar.spec [IsScalar T] [IsScalar T'] (p : RawPtr T M)
    (hSize : IsScalar.size (T := T) = IsScalar.size (T := T')) :
    ⦃ emp ⦄ RawPtr.cast_scalar T' M' p ⦃ q => ⌜q = p.retype⌝⦄ := by
  simp only [RawPtr.cast_scalar, hSize, ↓reduceIte]
  apply (ispec_ok _).2
  iframe

namespace IsScalar

@[simp]
theorem size_u8 : size (T := U8) = 1#usize := by
  change (⟨BitVec.ofNat _ 1⟩ : Usize) = 1#usize
  apply UScalar.eq_of_val_eq
  simp [UScalar.val]

@[simp, scalar_tac_simps]
theorem size_val_uscalar (ty : UScalarTy) : (size (T := UScalar ty)).val = ty.numBits / 8 := by
  change (BitVec.ofNat System.Platform.numBits (ty.numBits / 8)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  cases ty <;> rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]

@[simp, scalar_tac_simps]
theorem size_val_iscalar (ty : IScalarTy) : (size (T := IScalar ty)).val = ty.numBits / 8 := by
  change (BitVec.ofNat System.Platform.numBits (ty.numBits / 8)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  cases ty <;> rcases System.Platform.numBits_eq with h | h <;> simp [IScalarTy.numBits, h]

end IsScalar

end Aeneas.Std

namespace Aeneas.Std.IsScalar.Tests

example : (size (T := U128)).val = 16 := by
  rcases System.Platform.numBits_eq with h | h
  · simp [size, UScalar.val, h]
  · simp [size, UScalar.val, h]

example : (size (T := Isize)).val = System.Platform.numBits / 8 := by
  rcases System.Platform.numBits_eq with h | h
  · simp [size, UScalar.val, h]
  · simp [size, UScalar.val, h]

end Aeneas.Std.IsScalar.Tests
