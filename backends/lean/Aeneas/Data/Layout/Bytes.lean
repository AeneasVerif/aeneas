module
public import Aeneas.Data.Byte
@[expose] public section

namespace Aeneas

/-! ## Abstract Bytes and Definedness Relation (`le_defined`)
    Following MiniRust's `spec/lang/representation.md`. -/

inductive AbstractByte where
  | uninit
  | init (data : Byte)
deriving DecidableEq

namespace AbstractByte

@[simp]
def data : AbstractByte → Option Byte
  | .uninit => none
  | .init b => some b

/-- Returns whether `self` is less or as defined as `other` (`b1 <= b2`). -/
@[grind =]
def le_defined (self other : AbstractByte) : Prop :=
  match self, other with
  -- `Uninit <= _`: initializing something makes it "more defined".
  | .uninit, _ => True
  -- Among initialized bytes (without provenance), data must be equal.
  | .init data1, .init data2 => data1 = data2
  -- Nothing else is related.
  | _, _ => False

end AbstractByte

abbrev Bytes (n : Nat) := Vector AbstractByte n

namespace Bytes

def uninit (n : Nat) : Bytes n := Vector.replicate n .uninit

/-- The order on `Bytes` is bytewise `le_defined`. -/
def le_defined {n : Nat} (self other : Bytes n) : Prop :=
  ∀ (i : Nat) (_ : i < n), (self[i]).le_defined (other[i])

def subslice_with_length {n : Nat} (bytes : Bytes n) (offset length : Nat) (h : offset + length ≤ n) : Bytes length :=
  Vector.ofFn λ i ↦ bytes[offset + i.val]'(by omega)

def write_subslice_at_index {n m : Nat} (bytes : Bytes n) (offset : Nat) (subslice : Bytes m) : Bytes n :=
  Vector.ofFn λ j ↦
    if h : offset ≤ j.val ∧ j.val < offset + m then subslice[j.val - offset]'(by omega) else bytes[j.val]

def toData {n : Nat} (bytes : Bytes n) : Option (Vector Byte n) :=
  if h : ∀ (i : Nat) (_ : i < n), (bytes[i]).data.isSome
  then some (Vector.ofFn λ i ↦ (bytes[i.val]).data.get (h i.val i.isLt))
  else none

end Bytes

/-- On `Option`, `none <= _`, and `some v1 <= some v2` iff `v1 = v2`. -/
def Option.le_defined {α : Type u} (self other : Option α) : Prop :=
  match self, other with
  | none, _ => True
  | some l, some r => l = r
  | _, _ => False

/-! ## Lemmas -/

namespace AbstractByte

@[simp, grind ←] theorem le_defined_uninit (b : AbstractByte) : AbstractByte.uninit.le_defined b := trivial
@[simp, grind ←] theorem le_defined_refl (b : AbstractByte) : b.le_defined b := by cases b <;> simp [le_defined]

@[simp, grind =] theorem le_defined_uninit_elim {a : AbstractByte} :
    (AbstractByte.le_defined a .uninit) = (a = .uninit) := by
  ext; constructor <;> intros h
  · cases a; all_goals simp [le_defined] at h ⊢
  · subst a; trivial

@[simp, grind =] theorem le_defined_init_elim (b : AbstractByte) {d} :
    (AbstractByte.le_defined (.init d) b) = (.init d = b) := by
  ext; constructor <;> intros h
  · cases b; all_goals (simp [le_defined] at h ⊢ <;> trivial)
  · subst b; trivial

end AbstractByte

namespace Bytes

/-! ### Basic Lemmas on `Bytes` Operations -/

@[simp, grind ←] theorem le_defined_refl {n : Nat} (bs : Bytes n) : bs.le_defined bs :=
  λ i _ ↦ AbstractByte.le_defined_refl bs[i]

@[simp, grind ←] theorem uninit_le_defined {n : Nat} (bs : Bytes n) : (Bytes.uninit n).le_defined bs :=
  by intro i hi; simp [uninit]

@[simp, grind =] theorem uninit_getElem (n : Nat) (j : Nat) (hj : j < n) : (Bytes.uninit n)[j] = .uninit := by
  simp [uninit]

@[simp, grind =]
theorem getElem_subslice_with_length {n : Nat} (bs : Bytes n) (off len : Nat) (h : off + len ≤ n)
    (i : Nat) (hi : i < len) :
    (bs.subslice_with_length off len h)[i] = bs[off + i] := by
  simp [subslice_with_length]

@[simp, grind =]
theorem getElem_write_subslice_at_index {n m : Nat} (bs : Bytes n) (off : Nat) (sub : Bytes m)
    (j : Nat) (hj : j < n) :
    (bs.write_subslice_at_index off sub)[j] =
      if h : off ≤ j ∧ j < off + m then sub[j - off]'(by omega) else bs[j] := by
  simp [write_subslice_at_index]

@[simp, grind =]
theorem subslice_write_subslice_zero {n m : Nat} (bs : Bytes n) (sub : Bytes m) (h : 0 + m ≤ n) :
    (bs.write_subslice_at_index 0 sub).subslice_with_length 0 m h = sub := by
  ext i hi; simp [subslice_with_length, write_subslice_at_index]

@[simp, grind .]
theorem subslice_write_subslice_self {n m : Nat} (bs : Bytes n) (off : Nat) (sub : Bytes m) (h : off + m ≤ n) :
    (bs.write_subslice_at_index off sub).subslice_with_length off m h = sub := by
  ext i hi; simp [subslice_with_length, write_subslice_at_index]

@[grind ←]
theorem subslice_le_defined {n : Nat} {bs1 bs2 : Bytes n} (h_le : bs1.le_defined bs2)
    (off len : Nat) (h : off + len ≤ n) :
    (bs1.subslice_with_length off len h).le_defined (bs2.subslice_with_length off len h) :=
  λ i hi ↦ by simpa [subslice_with_length] using h_le (off + i) (by omega)

@[simp, grind =]
theorem toData_map_init {n : Nat} (v : Vector Byte n) : Bytes.toData (v.map AbstractByte.init) = some v := by
  unfold toData; rw [dif_pos (by intro i hi; simp)]; congr 1; ext i hi; simp

theorem getElem_of_toData {n : Nat} {bs : Bytes n} {v : Vector Byte n}
    (h : bs.toData = some v) (i : Nat) (hi : i < n) : bs[i] = .init v[i] := by
  have eq_init_get : ∀ {b : AbstractByte} (hb : b.data.isSome), b = .init (b.data.get hb)
    | .uninit, hb => by simp at hb
    | .init _, _ => rfl
  unfold toData at h
  split at h
  all_goals grind

grind_pattern getElem_of_toData => bs.toData, some v, bs[i]
grind_pattern getElem_of_toData => bs.toData, some v, v[i]

@[grind →]
theorem eq_of_toData_some_le_defined {n : Nat} {bs1 bs2 : Bytes n} {v : Vector Byte n}
    (h_data : bs1.toData = some v) (h_le : bs1.le_defined bs2) : bs1 = bs2 := by
  ext i hi
  have := h_le i hi
  grind

/-! ### Theory of Folding `write_subslice_at_index` over a List -/

/-- If `j` lies outside every written range `[off x ..< off x + len x)` for `x ∈ xs`,
    folding `write_subslice_at_index` over `xs` leaves byte `j` unchanged (`acc[j]`). -/
theorem foldl_write_subslice_getElem_eq {α : Type u} {n : Nat}
    (xs : List α) (off : α → Nat) {len : α → Nat} (sub : (x : α) → Bytes (len x))
    (acc : Bytes n) (j : Nat) (hj : j < n)
    (h_out : ∀ x ∈ xs, j < off x ∨ off x + len x ≤ j) :
    (xs.foldl (init := acc) λ bs x ↦ bs.write_subslice_at_index (off x) (sub x))[j] = acc[j] := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons, ih _ (by grind)]; grind

/-- If `[off0 ..< off0 + len0)` is disjoint from `[off x ..< off x + len x)` for every `x ∈ xs`,
    folding `write_subslice_at_index` over `xs` preserves that subslice. -/
@[simp] theorem foldl_write_subslice_subslice_eq {α : Type u} {n : Nat}
    (xs : List α) (off : α → Nat) {len : α → Nat} (sub : (x : α) → Bytes (len x))
    (acc : Bytes n) (off0 len0 : Nat) (h0 : off0 + len0 ≤ n)
    (h_disj : ∀ x ∈ xs, ∀ k, off0 ≤ k → k < off0 + len0 → off x ≤ k → k < off x + len x → False) :
    (xs.foldl (init := acc) λ bs x ↦ bs.write_subslice_at_index (off x) (sub x)).subslice_with_length
      off0 len0 h0 =
    acc.subslice_with_length off0 len0 h0 := by
  ext i hi
  simp [subslice_with_length,
    foldl_write_subslice_getElem_eq xs off sub acc (off0 + i) (by omega) (by grind)]

/-- If `xs` has no duplicates and writes pairwise non-overlapping ranges `[off x ..< off x + len x)`,
    reading back `[off x ..< off x + len x)` for any `x ∈ xs` returns `sub x`. -/
theorem foldl_write_subslice_nodup_subslice {α : Type u} {n : Nat}
    (xs : List α) (off : α → Nat) {len : α → Nat} (sub : (x : α) → Bytes (len x))
    (acc : Bytes n) (x : α) (hx : x ∈ xs) (h_nodup : xs.Nodup)
    (h_bound : off x + len x ≤ n)
    (h_disj : ∀ y ∈ xs, x ≠ y → ∀ k, off x ≤ k → k < off x + len x → off y ≤ k → k < off y + len y → False) :
    (xs.foldl (init := acc) λ bs y ↦ bs.write_subslice_at_index (off y) (sub y)).subslice_with_length
      (off x) (len x) h_bound =
    sub x := by
  induction xs generalizing acc with
  | nil => nomatch hx
  | cons y ys ih =>
    rw [List.nodup_cons] at h_nodup
    rcases List.mem_cons.mp hx with rfl | h_in_ys
    · simp [foldl_write_subslice_subslice_eq ys off sub _ (off x) (len x) _ (by grind)]
    · apply ih <;> grind

/-- If `acc.le_defined target` and every written slice `sub x` is `.le_defined` the corresponding
    subslice of `target`, then folding `write_subslice_at_index` over `xs` stays `.le_defined target`. -/
theorem foldl_write_subslice_le_defined {α : Type u} {n : Nat}
    (xs : List α) (off : α → Nat) {len : α → Nat} (sub : (x : α) → Bytes (len x))
    (acc target : Bytes n) (h_acc : acc.le_defined target)
    (h_bounds : ∀ x ∈ xs, off x + len x ≤ n)
    (h_subs : ∀ (x : α) (hx : x ∈ xs),
      (sub x).le_defined (target.subslice_with_length (off x) (len x) (h_bounds x hx))) :
    (xs.foldl (init := acc) λ bs x ↦ bs.write_subslice_at_index (off x) (sub x)).le_defined target := by
  induction xs generalizing acc with
  | nil => exact h_acc
  | cons x xs ih =>
    refine ih _ (λ j hj ↦ ?_) (by grind) (by grind)
    have := h_subs x List.mem_cons_self (j - off x)
    have := h_acc j hj
    grind

/-- Pointwise dichotomy for folding `write_subslice_at_index`: at each byte index `j`,
    either every write leaves `j` untouched (`= acc[j]`), or some write overwrites `j`
    so the final byte at `j` is independent of the initial buffer `acc`. -/
theorem foldl_write_subslice_dichotomy {α : Type u} {n : Nat}
    (xs : List α) (off : α → Nat) {len : α → Nat} (sub : (x : α) → Bytes (len x))
    (j : Nat) (hj : j < n) :
    (∀ b : Bytes n,
      (xs.foldl (init := b) λ bs x ↦ bs.write_subslice_at_index (off x) (sub x))[j] = b[j]) ∨
    (∀ b1 b2 : Bytes n,
      (xs.foldl (init := b1) λ bs x ↦ bs.write_subslice_at_index (off x) (sub x))[j] =
      (xs.foldl (init := b2) λ bs x ↦ bs.write_subslice_at_index (off x) (sub x))[j]) := by
  induction xs with
  | nil => exact .inl (λ _ ↦ rfl)
  | cons x xs ih =>
    rcases ih with h_id | h_const
    · by_cases hjx : off x ≤ j ∧ j < off x + len x
      · exact .inr (λ b1 b2 ↦ by simp only [List.foldl_cons, h_id]; simp [write_subslice_at_index, hjx])
      · exact .inl (λ b ↦ by simp only [List.foldl_cons, h_id]; simp [write_subslice_at_index, hjx])
    · exact .inr (λ b1 b2 ↦ h_const _ _)

/-- If both `base` and the slices written on top of `uninit n` are `.le_defined target`,
    then writing those slices on top of `base` is also `.le_defined target`. -/
theorem foldl_write_subslice_overlay_le_defined {α : Type u} {n : Nat}
    (xs : List α) (off : α → Nat) {len : α → Nat} (sub : (x : α) → Bytes (len x))
    (base target : Bytes n)
    (h_base : base.le_defined target)
    (h_over : (xs.foldl (init := Bytes.uninit n) λ bs x ↦ bs.write_subslice_at_index (off x) (sub x)).le_defined target) :
    (xs.foldl (init := base) λ bs x ↦ bs.write_subslice_at_index (off x) (sub x)).le_defined target :=
  λ j hj ↦ by
    rcases foldl_write_subslice_dichotomy xs off sub j hj with h | h
    · rw [h base]; exact h_base j hj
    · rw [h base (Bytes.uninit n)]; exact h_over j hj

end Bytes

namespace Option.le_defined

@[simp, grind ←] theorem Option.le_defined_refl (o : Option α) : Option.le_defined o o := by
  cases o <;> simp [Option.le_defined]
@[simp, grind ←] theorem Option.le_defined_none (o : Option α) : Option.le_defined .none o := by
  cases o <;> simp [Option.le_defined]

@[simp, grind =] theorem eq_of_some {α : Type u} {a : α} {o : Option α} :
    (Option.le_defined (some a) o) = (o = some a) := by
  ext; constructor <;> intros h
  · cases o <;> simp [Option.le_defined] at h; congr 1; exact h.symm
  · subst o; simp [Option.le_defined]

@[grind ←]
theorem map {α β : Type u} {o1 o2 : Option α} (f : α → β) (h : Option.le_defined o1 o2) :
    Option.le_defined (o1.map f) (o2.map f) := by
  cases o1 with
  | none => trivial
  | some a => simp at h ⊢; grind

@[grind ←]
theorem bind {α β : Type u} {o1 o2 : Option α} {f1 f2 : α → Option β}
    (ho : Option.le_defined o1 o2) (hf : ∀ a, o1 = some a → Option.le_defined (f1 a) (f2 a)) :
    Option.le_defined (o1 >>= f1) (o2 >>= f2) := by
  cases o1 with
  | none => trivial
  | some a => simp at ho ⊢; grind

end Option.le_defined

end Aeneas
