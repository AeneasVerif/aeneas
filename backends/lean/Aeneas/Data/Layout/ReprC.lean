module
public import Aeneas.Data.Layout.EncodeDecode

@[expose] public section

namespace Aeneas
namespace Layout

def alignTupleUp {ts f} (l : Layout (.tuple ts f)) (a : Nat) (ha : a.isPowerOfTwo) : Layout (.tuple ts f) := match ts, l with
| ts, .tuple fo fl sa =>
    let na := max sa.align a;
    let ns := alignUp sa.size na;
    .tuple fo fl ⟨ns, na, by grind, by grind⟩

def alignEnumUp {vs f} (l : Layout (.enum vs f)) (a : Nat) (ha : a.isPowerOfTwo) : Layout (.enum vs f) := match vs, l with
| vs, .enum vt vl d sa =>
    let na := max sa.align a;
    let ns := alignUp sa.size na;
    .enum vt (λ i hi ↦ match vs[i], vl i hi with
      | .tuple _ _, x => x.alignTupleUp a ha
      | _, x  => x -- vacuous case
    ) d ⟨ns, na, by grind, by grind⟩

namespace ReprC

/-! ## Shallow `#[repr(C)]` Tuple / Struct Layout (with Optional Packing) -/

/-- Effective alignment when capped by an optional `#[repr(packed(P))]` bound. -/
@[simp, grind =]
def effAlign (max_align : Option { a : Nat // a.isPowerOfTwo }) (a : Nat) : Nat :=
  match max_align with
  | none => a
  | some ⟨p, _⟩ => min a p

@[simp, grind ←]
lemma effAlign_isPowerOfTwo (max_align : Option { a : Nat // a.isPowerOfTwo })
    {a : Nat} (ha : a.isPowerOfTwo) : (effAlign max_align a).isPowerOfTwo := by
  cases max_align with
  | none => exact ha
  | some p =>
    by_cases h : a ≤ p.val <;> simp [effAlign] <;> grind

/-- Byte offset after placing the first `k` fields sequentially under `#[repr(C)]`,
    starting at initial offset `init_off`. -/
def tupleCursor {n : Nat} (fsize falign : (i : Nat) → i < n → Nat) (init_off : Nat := 0) :
    (k : Nat) → k ≤ n → Nat
  | 0, _ => init_off
  | k + 1, hk =>
    alignUp (tupleCursor fsize falign init_off k (Nat.le_of_succ_le hk)) (falign k hk) + fsize k hk

/-- Byte offset of field `i` under `#[repr(C)]`: current cursor aligned up to `falign i hi`. -/
@[grind =]
def tupleFieldOffset {n : Nat} (fsize falign : (i : Nat) → i < n → Nat) (init_off : Nat := 0)
    (i : Nat) (hi : i < n) : Nat :=
  alignUp (tupleCursor fsize falign init_off i (by omega)) (falign i hi)

@[grind ←] lemma tupleCursor_mono {n : Nat} (fsize falign : (i : Nat) → i < n → Nat)
    (init_off : Nat) (h_pos : ∀ i (hi : i < n), 0 < falign i hi) :
    ∀ {k1 k2 : Nat} (hk1 : k1 ≤ n) (hk2 : k2 ≤ n), k1 ≤ k2 →
      tupleCursor fsize falign init_off k1 hk1 ≤ tupleCursor fsize falign init_off k2 hk2
  | 0, 0, _, _, _ => Nat.le_refl _
  | _ + 1, 0, _, _, h => nomatch h
  | k1, k2 + 1, hk1, hk2, hle => by
    rcases Nat.of_le_succ hle with h | rfl
    · have := tupleCursor_mono fsize falign init_off h_pos hk1 (by omega) h
      simp [tupleCursor]; grind
    · rfl

grind_pattern tupleCursor_mono => tupleCursor fsize falign init_off k1 _, tupleCursor fsize falign init_off k2 _

lemma init_off_le_tupleCursor {n : Nat} (fsize falign : (i : Nat) → i < n → Nat)
    (init_off : Nat) (h_pos : ∀ i (hi : i < n), 0 < falign i hi)
    (k : Nat) (hk : k ≤ n) :
    init_off ≤ tupleCursor fsize falign init_off k hk :=
  tupleCursor_mono fsize falign init_off h_pos (Nat.zero_le n) hk (Nat.zero_le k)

grind_pattern init_off_le_tupleCursor => tupleCursor fsize falign init_off k hk

lemma init_off_le_tupleFieldOffset {n : Nat} (fsize falign : (i : Nat) → i < n → Nat)
    (init_off : Nat) (h_pos : ∀ i (hi : i < n), 0 < falign i hi)
    (i : Nat) (hi : i < n) :
    init_off ≤ tupleFieldOffset fsize falign init_off i hi := by
  grind

grind_pattern init_off_le_tupleFieldOffset => tupleFieldOffset fsize falign init_off i hi

lemma tupleFieldOffset_mono {n : Nat} (fsize falign : (i : Nat) → i < n → Nat)
    (init_off : Nat) (h_pos : ∀ i (hi : i < n), 0 < falign i hi)
    {a b : Nat} (ha : a < n) (hb : b < n) (hab : a < b) :
    tupleFieldOffset fsize falign init_off a ha + fsize a ha ≤ tupleFieldOffset fsize falign init_off b hb := by
  have h1 : tupleFieldOffset fsize falign init_off a ha + fsize a ha = tupleCursor fsize falign init_off (a + 1) ha := rfl
  grind

grind_pattern tupleFieldOffset_mono => tupleFieldOffset fsize falign init_off a ha, tupleFieldOffset fsize falign init_off b hb

lemma tupleFieldOffset_le_end {n : Nat} (fsize falign : (i : Nat) → i < n → Nat)
    (init_off : Nat) (h_pos : ∀ i (hi : i < n), 0 < falign i hi)
    (i : Nat) (hi : i < n) :
    tupleFieldOffset fsize falign init_off i hi + fsize i hi ≤ tupleCursor fsize falign init_off n (Nat.le_refl n) :=
  tupleCursor_mono fsize falign init_off h_pos hi (Nat.le_refl n) hi

grind_pattern tupleFieldOffset_le_end => tupleFieldOffset fsize falign init_off i hi

/-- Total `SizeAndAlign` of a `#[repr(C)]` tuple/struct with field sizes `fsize`,
    effective field alignments `falign`, and initial offset `init_off`. -/
@[grind =]
def tupleSizeAndAlign {n : Nat} (fsize falign : (i : Nat) → i < n → Nat)
    (init_off : Nat := 0) (h_align : ∀ i (hi : i < n), (falign i hi).isPowerOfTwo) : SizeAndAlign :=
  let A := natMax n falign 1
  let sz := alignUp (tupleCursor fsize falign init_off n (Nat.le_refl _)) A
  ⟨sz, A, by grind, by grind⟩

lemma tupleSizeAndAlign_size_eq_natMax : ∀ {n : Nat} (fsize falign : (i : Nat) → i < n → Nat)
    (h_align : ∀ i (hi : i < n), (falign i hi).isPowerOfTwo),
    let sa := tupleSizeAndAlign fsize falign 0 h_align
    sa.size = natMax n (λ x hx ↦ alignUp (tupleFieldOffset fsize falign 0 x hx + fsize x hx) sa.align) 0
  | 0, _, _, _ => by simp [tupleSizeAndAlign, tupleCursor, natMax]
  | m + 1, fsize, falign, h_align => by
    intro sa
    apply Nat.le_antisymm
    · trans; swap
      apply le_natMax (i := m)
      grind
      trivial
    · apply lub_natMax; grind
      grind

/-- All fields of a tuple layout are placed at byte offset `≥ min_off`
    (leaving `[0 ..< min_off)` untouched as prefix padding). -/
def TupleMinOffset (min_off : Nat) : {t : MType} → Layout t → Prop
  | .tuple ts _, .tuple vfo _ _ => ∀ j (hj : j < ts.length), min_off ≤ vfo j hj
  | _, _ => True

@[simp, grind =]
lemma tupleMinOffset_tuple (min_off : Nat) {ts : List MType} {f : TupleFlags}
    (vfo : (idx : Nat) → idx < ts.length → Nat)
    (vfl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
    (sa : SizeAndAlign) :
    TupleMinOffset min_off (.tuple vfo vfl sa : Layout (.tuple ts f)) = (∀ j (hj : j < ts.length), min_off ≤ vfo j hj) := rfl

@[simp, grind .]
lemma tupleMinOffset_zero {t : MType} (cl : Layout t) : TupleMinOffset 0 cl := by
  cases cl <;> simp [TupleMinOffset]

/-- Shallow `#[repr(C)]` layout for a tuple/struct given arbitrary layouts for its fields,
    with an optional `max_align` cap for `#[repr(C, packed(N))]` and an optional initial
    cursor `init_off` (used e.g. for `#[repr(primitive)]` enum variants after the tag). -/
@[grind =]
def mkTuple (ts : List MType) {f : TupleFlags}
    (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
    (max_align : Option { a : Nat // a.isPowerOfTwo } := none)
    (init_off : Nat := 0) :
    Layout (.tuple ts f) :=
  let fsize : (idx : Nat) → idx < ts.length → Nat := λ idx h ↦ (fl idx h).size
  let falign : (idx : Nat) → idx < ts.length → Nat :=
    λ idx h ↦ effAlign max_align (fl idx h).size_and_align.align
  .tuple (tupleFieldOffset fsize falign init_off) fl (tupleSizeAndAlign fsize falign init_off (by grind))

@[simp, grind ←]
lemma mkTuple_minOffset (ts : List MType) {f : TupleFlags}
    (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
    (max_align : Option { a : Nat // a.isPowerOfTwo } := none)
    (init_off : Nat := 0) :
    TupleMinOffset init_off (mkTuple ts (f := f) fl max_align init_off) := by
  grind

-- having a packed(n) where n is greater than the existing alignment has no effect
@[grind =]
lemma mkTuple_large_packed_nop ts {f : TupleFlags} fl (a : { a : Nat // a.isPowerOfTwo }) (init_off : Nat := 0)
  (hge : a.val ≥ (mkTuple ts (f := f) fl .none init_off).size_and_align.align) :
  mkTuple ts (f := f) fl (.some a) init_off = mkTuple ts (f := f) fl .none init_off := by grind

@[grind ←]
lemma mkTuple_packed_bounds_align ts {f : TupleFlags} fl (a : { a : Nat // a.isPowerOfTwo }) (init_off : Nat := 0) :
  (mkTuple ts (f := f) fl (max_align := .some a) init_off).size_and_align.align ≤ ↑a := by
  grind [lub_natMax]

/-! ## Shallow `#[repr(C)]` and `#[repr(primitive)]` Enum Layouts -/

/-- Shifts a tuple variant's field offsets right by `payload_off` and sets its `SizeAndAlign` to `sa`,
    leaving prefix bytes `[0 ..< min_off + payload_off)` as padding for the discriminant tag. -/
def padVariantLayout : {t : MType} → Layout t → Nat → SizeAndAlign → Layout t
  | .tuple _ _, .tuple vfo vfl _, payload_off, sa =>
      .tuple (λ j hj ↦ payload_off + vfo j hj) vfl sa
  | _, l, _, _ => l

@[simp]
lemma padVariantLayout_size_and_align {t : MType} (ht : t.isTuple) (cl : Layout t)
    (payload_off : Nat) (sa : SizeAndAlign) :
    (padVariantLayout cl payload_off sa).size_and_align = sa :=
  match t, ht, cl with
  | .int _, h, _ | .enum _ _, h, _ => nomatch h
  | .tuple _ _, _, .tuple _ _ _ => rfl

grind_pattern padVariantLayout_size_and_align => padVariantLayout cl payload_off sa

@[simp]
lemma padVariantLayout_size {t : MType} (ht : t.isTuple) (cl : Layout t)
    (payload_off : Nat) (sa : SizeAndAlign) :
    (padVariantLayout cl payload_off sa).size = sa.size := by
  rw [← size_known, padVariantLayout_size_and_align ht]

/-- Shared core for `#[repr(C)]` (`mkEnum`) and `#[repr(primitive)]` (`mkEnumPrimitive`) enum layouts.
    - When `shift_payload = true` (`#[repr(C)]` / `#[repr(C, Int)]`), variants are shifted by `alignUp tagTy.size A`.
    - When `shift_payload = false` (`#[repr(Int)]`), we assume variants already place their fields at `≥ tagTy.size`
      (e.g. via `mkTuple ts fl max_align tagTy.size`), so `payload_off = 0` and only their outer `SizeAndAlign` is padded to `sa`. -/
def mkEnumCore (tagTy : IUScalarTy) (shift_payload : Bool) (vs : List MType) {f : EnumFlags}
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx]) :
    Layout (.enum vs f) :=
  let fsa : (idx : Nat) → idx < vs.length → SizeAndAlign := λ idx h ↦ (cl idx h).size_and_align
  let A := natMax vs.length (λ i hi ↦ (fsa i hi).align) tagTy.reasonablyAligned.align
  let payload_off := if shift_payload then alignUp tagTy.size A else 0
  let min_sz := if shift_payload then 0 else tagTy.size
  let max_var_sz := natMax vs.length (λ i hi ↦ (fsa i hi).size) min_sz
  let sz := alignUp (payload_off + max_var_sz) A
  let sa : SizeAndAlign := ⟨sz, A, by grind, by grind⟩
  let vl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx] := λ idx h ↦ padVariantLayout (cl idx h) payload_off sa
  let vt : (idx : Nat) → idx < vs.length → List TagToWrite := λ idx _ ↦ [⟨0, tagTy, IUScalar.fromBv (BitVec.ofNat tagTy.numBits idx)⟩]
  let discr : Discriminator := .read 0 tagTy (λ bv ↦ if bv.toNat < vs.length then .known bv.toNat else .invalid)
  .enum vt vl discr sa

/-- `#[repr(C)]` (and `#[repr(C, Int)]`) layout for an enum given layouts for its tuple variants. -/
@[grind =]
def mkEnum (tagTy : IUScalarTy := .unsigned .Usize) (vs : List MType) {f : EnumFlags}
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx]) :
    Layout (.enum vs f) :=
  mkEnumCore tagTy true vs cl

/-- `#[repr(Int)]` (`#[repr(primitive)]`, e.g. `#[repr(u8)]`, `#[repr(i8)]`) layout for an enum,
    given tuple variant layouts whose fields have already been laid out after the tag
    (e.g. via `mkTuple ts fl max_align tagTy.size`). -/
@[grind =]
def mkEnumPrimitive (tagTy : IUScalarTy) (vs : List MType) {f : EnumFlags}
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx]) :
    Layout (.enum vs f) :=
  mkEnumCore tagTy false vs cl

/-! ## Deep `#[repr(C)]` Layout (`mk`) -/

/-- Constructs the "deep `#[repr(C)]`" layout for an `MType` (which lays out all subthings according to `#[repr(C)]` as well). -/
def mk : (ty : MType) → Layout ty
  | .int ty => .int ty.reasonablyAligned ty.reasonablyAligned_isReasonable
  | .tuple ts _ => mkTuple ts (λ idx h ↦ mk ts[idx]) none
  | .enum vs _ => mkEnum (.unsigned .Usize) vs (λ idx h ↦ mk vs[idx])
termination_by ty => sizeOf ty
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem (List.getElem_mem h); omega

end ReprC
end Layout
end Aeneas
