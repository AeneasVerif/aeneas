/- Arrays/Slices -/
module
public import Aeneas.Data.List
public import Aeneas.Std.Array.Core
public import Aeneas.Std.Range
public import Aeneas.Std.Core.Ops
public import Aeneas.Std.Core.Ptr
public import Aeneas.Tactic.Simp.SimpScalar.SimpScalar
public import Aeneas.Std.SliceDef
public section

namespace Aeneas.Std

open Result Error core.ops.range WP

local macro_rules
| `(tactic| get_elem_tactic) => `(tactic| grind)

attribute [-simp] List.getElem!_eq_getElem?_getD

/-!
# Slice
-/

/-- We need this to coerce slices to lists without marking `Slice` as reducible.
    Also not that we *do not* want to mark `Slice` as reducible: it triggers issues.
-/
instance (α : Type u) : CoeOut (Slice α) (List α) where
  coe := λ v => v.val

theorem Slice.length_ineq {α : Type u} (s : Slice α) : s.val.length ≤ Usize.max := by
  cases s; simp[*]

@[simp, scalar_tac_simps, simp_scalar_safe, simp_lists_safe]
abbrev Slice.length {α : Type u} (v : Slice α) : Nat := v.val.length

@[simp, scalar_tac_simps, simp_scalar_safe, simp_lists_safe]
abbrev Slice.v {α : Type u} (v : Slice α) : List α := v.val

example {a: Type u} (v : Slice a) : v.length ≤ Usize.max := by
  simp

@[expose] def Slice.new (α : Type u) : Slice α := {
  leng := 0
  list := .nil
  bound := by simp
}

@[simp, simp_lists_safe, scalar_tac_simps, grind =, agrind =]
theorem Slice.new_val (α : Type u) : (Slice.new α).val = [] := rfl

@[rust_fun "core::slice::{[@T]}::len" -canFail -lift]
abbrev Slice.len {α : Type u} (v : SharedBorrow (Slice α)) : Usize :=
  Usize.ofNatCore v.val.val.length (by scalar_tac)

@[simp, scalar_tac_simps, simp_scalar_safe, simp_lists_safe, grind =, agrind =]
theorem Slice.len_val {α : Type u} (v : SharedBorrow (Slice α)) : (Slice.len v).val = v.val.length :=
  by simp

/-! Raw-pointer exposures of slices. The functional slice model has no address: `as_ptr`/`as_mut_ptr`
copy the slice to a fresh shared/exclusive exposure, removed when the borrow ends.
`from_raw_parts` shares cells, allowing raw reads but not writes; `from_raw_parts_mut`
exclusively borrows them, blocking raw access to those cells.
The returned back computations run when the borrow ends. -/

/-- `borrowRange` of `len` cells, as a slice. -/
def RawPtr.borrowSlice {T : Type} (repr : Repr T) (q : RawPtr T) (len : Usize) : Result (Slice T) := do
  let values ← q.borrowRange repr len.val
  if h : values.length ≤ Usize.max then .ok (Slice.from values h) else .fail .undef

/-- Ends the shared exposure created by `as_ptr`: its read-only cells must still hold `s`.
Casting the pointer to mutable cannot authorize writes; the temporary block is removed. -/
def Slice.end_as_ptr {T : Type} (repr : Repr T) (s : Slice T) (p : ConstRawPtr T) : Result Unit := do
  p.endSharedExposure repr s.val

/-- `as_ptr` for the slices of values with a `Pointee` instance. -/
@[expose] def Slice.as_ptr_pointee {T : Type} [Pointee T] (address : BasePtr) (s : SharedBorrow (Slice T)) :
    Result (ConstRawPtr T × Result Unit) :=
  Aeneas.Std.bind (RawPtr.allocSharedExposure (Pointee.repr (T := T)) s.val.val address) fun p =>
    .ok (p, Slice.end_as_ptr (Pointee.repr (T := T)) s.val p)

/-- Ends the mutable exposure of `as_mut_ptr`: the cells become the new slice and their
temporary block is removed. -/
def Slice.end_as_mut_ptr {T : Type} (repr : Repr T) (s : Slice T) (p : MutRawPtr T) : Result (Slice T) := do
  let values ← p.readRange repr s.length
  p.endExposure repr s.length
  if h : values.length ≤ Usize.max then .ok (Slice.from values h) else .fail .undef

/-- `as_mut_ptr` for the slices of values with a `Pointee` instance. -/
@[expose] def Slice.as_mut_ptr_pointee {T : Type} [Pointee T] (address : BasePtr) (s : MutBorrow (Slice T)) :
    Result (MutRawPtr T × Result (Slice T)) :=
  Aeneas.Std.bind (RawPtr.allocExposure (Pointee.repr (T := T)) s.val.val address) fun p =>
    .ok (p, Slice.end_as_mut_ptr (Pointee.repr (T := T)) s.val p)

/-- The element types of the slices which can be exposed as raw memory by `as_ptr` and
`as_mut_ptr`: the types with a `Pointee` instance, and `MaybeUninit T` (see `MaybeUninit.lean`),
which has none since its uninitialized values have no representation. -/
class Exposable (T : Type) where
  as_ptr : BasePtr → SharedBorrow (Slice T) → Result (ConstRawPtr T × Result Unit)
  as_mut_ptr : BasePtr → MutBorrow (Slice T) → Result (MutRawPtr T × Result (Slice T))

@[expose] instance Exposable.ofPointee {T : Type} [Pointee T] : Exposable T where
  as_ptr := Slice.as_ptr_pointee
  as_mut_ptr := Slice.as_mut_ptr_pointee

@[expose, rust_fun "core::slice::{[@T]}::as_ptr" (statefulLifetimes := [0]) (placement := true)]
def Slice.as_ptr {T : Type} [Exposable T] (address : BasePtr) (s : SharedBorrow (Slice T)) :
    Result (ConstRawPtr T × Result Unit) :=
  Exposable.as_ptr address s

@[expose, rust_fun "core::slice::{[@T]}::as_mut_ptr" (statefulLifetimes := [0]) (placement := true)]
def Slice.as_mut_ptr {T : Type} [Exposable T] (address : BasePtr) (s : MutBorrow (Slice T)) :
    Result (MutRawPtr T × Result (Slice T)) :=
  Exposable.as_mut_ptr address s

theorem Slice.as_ptr_eq {T : Type} [Pointee T] (address : BasePtr) (s : SharedBorrow (Slice T)) :
    Slice.as_ptr address s =
      Aeneas.Std.bind (RawPtr.allocSharedExposure (Pointee.repr (T := T)) s.val.val address) fun p =>
        .ok (p, Slice.end_as_ptr (Pointee.repr (T := T)) s.val p) := rfl

theorem Slice.as_mut_ptr_eq {T : Type} [Pointee T] (address : BasePtr) (s : MutBorrow (Slice T)) :
    Slice.as_mut_ptr address s =
      Aeneas.Std.bind (RawPtr.allocExposure (Pointee.repr (T := T)) s.val.val address) fun p =>
        .ok (p, Slice.end_as_mut_ptr (Pointee.repr (T := T)) s.val p) := rfl

/-- Back function of `from_raw_parts_mut`: ends the borrow of the cells with the final slice. -/
def core.slice.raw.from_raw_parts_mut.back {T : Type} (repr : Repr T) (p : MutRawPtr T) (len : Usize)
    (s : Slice T) : Result Unit :=
  if s.length = len.val then p.endBorrowRange repr s.val else .fail .undef

@[rust_fun "core::slice::raw::from_raw_parts" (statefulLifetimes := [0])]
def core.slice.raw.from_raw_parts {T : Type} [Pointee T] (p : ConstRawPtr T) (len : Usize) :
    Result (SharedBorrow (Slice T) × Result Unit) :=
  Aeneas.Std.bind (p.shareRange (Pointee.repr (T := T)) len.val) fun values =>
  if h : values.length ≤ Usize.max then
    let s := Slice.from values h
    .ok (⟨s⟩, p.endShareRange (Pointee.repr (T := T)) s.val)
  else .fail .undef

@[rust_fun "core::slice::raw::from_raw_parts_mut" (statefulLifetimes := [0])]
def core.slice.raw.from_raw_parts_mut {T : Type} [Pointee T] (p : MutRawPtr T) (len : Usize) :
    Result (MutBorrow (Slice T) × (Slice T → Result Unit)) :=
  Aeneas.Std.bind (p.borrowSlice (Pointee.repr (T := T)) len) fun s =>
    .ok (⟨s⟩, core.slice.raw.from_raw_parts_mut.back (Pointee.repr (T := T)) p len)

instance {α : Type u} : GetElem (Slice α) Nat α (fun a i => i < a.val.length) where
  getElem a i h := getElem a.val i h

@[simp, grind =, agrind =, simp_lists_safe, simp_lists_hyps_simps]
theorem Slice.getElem_Nat_eq {α : Type u} (v : Slice α) (i : Nat) (h : i < v.val.length) :
    v[i] = v.val[i] := rfl

instance {α : Type u} : GetElem? (Slice α) Nat α (fun a i => i < a.val.length) where
  getElem? a i := getElem? a.val i

@[simp, scalar_tac_simps, simp_lists_hyps_simps, simp_lists_safe, grind =, agrind =]
theorem Slice.getElem?_Nat_eq {α : Type u} (v : Slice α) (i : Nat) : v[i]? = v.val[i]? := by rfl

@[simp, scalar_tac_simps, simp_lists_hyps_simps, simp_lists_safe, grind = _, agrind = _]
theorem Slice.getElem!_Nat_eq {α : Type u} [Inhabited α] (v : Slice α) (i : Nat) : v[i]! = v.val[i]! := by
  simp only [getElem!]; split <;> (simp_all [List.getElem!_eq_getElem?_getD]; try rfl)

instance {α : Type u} : GetElem (Slice α) Usize α (fun a i => i.val < a.val.length) where
  getElem a i h := getElem a.val i.val h

@[simp, grind =, agrind =, simp_lists_safe, simp_lists_hyps_simps]
theorem Slice.getElem_Usize_eq {α : Type u} (v : Slice α) (i : Usize) (h : i.val < v.val.length) :
    v[i]'h = v.val[i.val] := rfl

instance {α : Type u} : GetElem? (Slice α) Usize α (fun a i => i < a.val.length) where
  getElem? a i := getElem? a.val i.val

@[simp, scalar_tac_simps, simp_lists_hyps_simps, simp_lists_safe, grind =, agrind =]
theorem Slice.getElem?_Usize_eq {α : Type u} (v : Slice α) (i : Usize) : v[i]? = v.val[i.val]? := by rfl

@[simp, scalar_tac_simps, simp_lists_hyps_simps, simp_lists_safe, grind = _, agrind = _]
theorem Slice.getElem!_Usize_eq {α : Type u} [Inhabited α] (v : Slice α) (i : Usize) : v[i]! = v.val[i.val]! := by
  simp only [getElem!]; split <;> (simp_all [List.getElem!_eq_getElem?_getD]; try rfl)

@[simp, scalar_tac_simps, simp_lists_hyps_simps] abbrev Slice.get? {α : Type u} (v : Slice α) (i : Nat) : Option α := getElem? v i
@[simp, scalar_tac_simps, simp_lists_hyps_simps] abbrev Slice.get! {α : Type u} [Inhabited α] (v : Slice α) (i : Nat) : α := getElem! v i

@[expose] def Slice.setAtNat {α : Type u} (v: Slice α) (i: Nat) (x: α) : Slice α :=
  .from (v.val.set i x) (by have := v.property; simp [*])

@[expose] def Slice.set {α : Type u} (v: Slice α) (i: Usize) (x: α) : Slice α :=
  Slice.setAtNat v i.val x

@[expose] def Slice.set_opt {α : Type u} (v: Slice α) (i: Usize) (x: Option α) : Slice α :=
  .from (v.val.set_opt i.val x) (by have := v.property; simp [*])

@[expose] def Slice.drop {α} (s : Slice α) (i : Usize) : Slice α :=
  .from (s.val.drop i.val) (by scalar_tac)

@[simp, simp_lists_safe]
theorem Slice.getElem!_val_drop {T} (s : Slice T) (i : Usize) :
  (s.drop i).val = s.val.drop i := by
  simp [drop]

@[simp]
abbrev Slice.slice {α : Type u} [Inhabited α] (s : Slice α) (i j : Nat) : List α :=
  s.val.slice i j

@[expose] def Slice.index_usize {α : Type u} (v: SharedBorrow (Slice α)) (i: Usize) :
  Result (SharedBorrow α) :=
  match v.val[i]? with
  | none => fail .arrayOutOfBounds
  | some x => ok (.mk x)

@[expose, rust_fun "core::slice::{[@T]}::is_empty", simp]
def core.slice.Slice.is_empty {T : Type _} (s : SharedBorrow (Slice T)) : Result Bool :=
  ok (s.val.length = 0)

@[step]
theorem core.slice.Slice.is_empty_spec {T : Type _} (s : SharedBorrow (Slice T)) :
  core.slice.Slice.is_empty s ⦃ b => b = (s.val.length = 0) ⦄ := by
  simp only [is_empty, Slice.length, List.length_eq_zero_iff, eq_iff_iff, spec_ok,
    decide_eq_true_eq]

@[step]
theorem Slice.index_usize_spec {α : Type u} (v: SharedBorrow (Slice α)) (i: Usize)
  (hbound : i.val < v.val.length) :
  Slice.index_usize v i ⦃ x => x.val = v.val[i.val] ⦄ := by
  grind [index_usize]

@[simp, scalar_tac_simps, simp_lists_hyps_simps, grind =]
theorem Slice.set_val_eq {α : Type u} (v: Slice α) (i: Usize) (x: α) :
  (v.set i x) = v.val.set i.val x := by
  simp [set, setAtNat]

@[simp, scalar_tac_simps, simp_lists_hyps_simps]
theorem Slice.set_opt_val_eq {α : Type u} (v: Slice α) (i: Usize) (x: Option α) :
  (v.set_opt i x) = v.val.set_opt i.val x := by
  simp [set_opt]


/-- Using `↓` to eagerly simplify combinations of `set` and `getElem!` in expressions like:
`(((l.set i0 x0) ...).set in xn)[j]!`

Otherwise we might lose a lot of time reordering the `set` expressions.
-/
@[simp↓, simp_lists_safe↓]
theorem Slice.getElem!_Usize_set_ne
  {α : Type u} [Inhabited α] (a: Slice α) (i j : Usize) (x: α)
  (h : i.val ≠ j.val) : (a.set i x)[j]! = a[j]!
  := by
  simp only [getElem!_Usize_eq, set_val_eq]; grind

@[simp↓, simp_lists_safe↓]
theorem Slice.getElem_Usize_set_ne
  {α : Type u} (a: Slice α) (i j : Usize) (x: α)
  (h0 : j.val < (a.set i x).length) (h : i.val ≠ j.val) :
  (a.set i x)[j]'h0 = a[j]
  := by
  grind

@[simp↓, simp_lists_safe↓]
theorem Slice.getElem!_Usize_set_eq
  {α : Type u} [Inhabited α] (a: Slice α) (i i' : Usize) (x: α)
  (h : i = i' ∧ i'.val < a.length) : getElem! (a.set i x) i' = x
  := by
  simp only [getElem!_Usize_eq, set_val_eq]; grind

@[simp↓, simp_lists_safe↓]
theorem Slice.getElem_Usize_set_eq
  {α : Type u} (a: Slice α) (i j : Usize) (x: α)
  (h0 : j.val < (a.set i x).length) (h1 : i = j) :
  (a.set i x)[j]'h0 = x
  := by
  grind

/-- Using `↓` to eagerly simplify combinations of `set` and `getElem!` in expressions like:
`(((l.set i0 x0) ...).set in xn)[j]!`

Otherwise we might lose a lot of time reordering the `set` expressions.
-/
@[simp↓, simp_lists_safe↓]
theorem Slice.getElem!_Nat_set_ne
  {α : Type u} [Inhabited α] (a: Slice α) (i : Usize) (j : Nat) (x: α)
  (h : i.val ≠ j) : (a.set i x)[j]! = a[j]!
  := by simp only [getElem!_Nat_eq, set_val_eq]; grind

@[simp↓, simp_lists_safe↓]
theorem Slice.getElem_Nat_set_ne
  {α : Type u} (a: Slice α) (i : Usize) (j : Nat) (x: α)
  (h0 : j < (a.set i x).length) (h1 : i.val ≠ j) :
  (a.set i x)[j]'h0 = a[j]
  := by grind

@[simp↓, simp_lists_safe↓]
theorem Slice.getElem!_Nat_set_eq
  {α : Type u} [Inhabited α] (a: Slice α) (i : Usize) (i' : Nat) (x: α)
  (h : i.val = i' ∧ i' < a.length) : getElem! (a.set i x) i' = x
  := by simp only [getElem!_Nat_eq, set_val_eq]; grind

@[simp↓, simp_lists_safe↓]
theorem Slice.getElem_Nat_set_eq
  {α : Type u} (a: Slice α) (i : Usize) (j : Nat) (x: α)
  (h0 : j < (a.set i x).length) (h1 : i.val = j) :
  (a.set i x)[j]'h0 = x
  := by grind

theorem Slice.Inhabited_getElem_eq_getElem! {α} [Inhabited α] (v : Slice α) (i : ℕ) (hi : i < v.length) :
    v[i] = v[i]! := by
  rw [Slice.getElem!_Nat_eq]
  exact List.Inhabited_getElem_eq_getElem! v.val i hi

theorem Slice.ext_getElem {α} {s1 s2 : Slice α}
    (hlen : s1.length = s2.length)
    (hget : ∀ (i : Nat) (_ : i < s1.length) (_ : i < s2.length), s1[i] = s2[i]) :
    s1 = s2 := by
  apply Slice.ext
  exact List.ext_getElem (by simp_all) fun i h1 h2 => hget i h1 h2

@[simp, scalar_tac_simps, simp_lists_safe, grind =, agrind =]
theorem Slice.set_length {α : Type u} (v: Slice α) (i: Usize) (x: α) :
  (v.set i x).length = v.length := by simp

@[simp, scalar_tac_simps, simp_lists_safe, grind =, agrind =]
theorem Slice.setAtNat_length {α : Type u} (v: Slice α) (i: Nat) (x: α) :
  (v.setAtNat i x).length = v.length := by simp [setAtNat, Slice.length]

@[simp↓, simp_lists_safe↓]
theorem Slice.getElem!_Nat_setAtNat_eq
  {α : Type u} [Inhabited α] (v: Slice α) (i: Nat) (x: α)
  (h : i < v.length) : (v.setAtNat i x).val[i]! = x := by
  simp only [setAtNat]; grind

@[simp↓, simp_lists_safe↓]
theorem Slice.getElem_Nat_setAtNat_eq
  {α : Type u} (v: Slice α) (i: Nat) (x: α)
  (h : i < v.length) :
  (v.setAtNat i x).val[i] = x := by
  simp only [setAtNat]; grind

@[simp↓, simp_lists_safe↓]
theorem Slice.getElem!_Nat_setAtNat_ne
  {α : Type u} [Inhabited α] (v: Slice α) (i j: Nat) (x: α)
  (h : i ≠ j) : (v.setAtNat i x).val[j]! = v.val[j]! := by
  simp only [setAtNat]; grind

@[simp↓, simp_lists_safe↓]
theorem Slice.getElem_Nat_setAtNat_ne
  {α : Type u} (v: Slice α) (i j: Nat) (x: α)
  (h : i ≠ j ∧ j < v.length) :
  (v.setAtNat i x).val[j] = v.val[j] := by
  simp only [setAtNat]; grind

@[expose] def Slice.update {α : Type u} (v: Slice α) (i: Usize) (x: α) : Result (Slice α) :=
  match v.val[i.val]? with
  | none => fail .arrayOutOfBounds
  | some _ =>
    ok (.from (v.val.set i.val x) (by have := v.property; simp [*]))

@[step]
theorem Slice.update_spec {α : Type u} (v: Slice α) (i: Usize) (x : α)
  (hbound : i.val < v.length) :
  v.update i x ⦃ nv => nv = v.set i x ⦄ := by
  simp only [update, set, setAtNat]
  simp at *
  simp [*]

@[expose] def Slice.index_mut_usize {α : Type u} (v: MutBorrow (Slice α)) (i: Usize) :
  Result (MutBorrow α × (α → Slice α)) := do
  let x ← Slice.index_usize (.mk v.val) i
  ok (.mk x.val, Slice.set v.val i)

@[step]
theorem Slice.index_mut_usize_spec {α : Type u} (v: MutBorrow (Slice α)) (i: Usize)
  (hbound : i.val < v.val.length) :
  Slice.index_mut_usize v i ⦃ x back => x.val = v.val[i.val] ∧ back = Slice.set v.val i ⦄ := by
  simp only [index_mut_usize, Bind.bind]
  apply spec_bind (Slice.index_usize_spec (.mk v.val) i hbound)
  intro x hx
  simp [hx]

@[simp, simp_lists_safe]
theorem Slice.update_index_eq α [Inhabited α] (x : Slice α) (i : Usize) (h : i.val < x.val.length) :
  x.set i (x.val[i.val]'h) = x := by
  simp only [Slice.eq_iff, set_val_eq, List.set_getElem_self]

@[expose] def Slice.subslice {α : Type u} (s : Slice α) (r : Range Usize) : Result (Slice α) :=
  -- TODO: not completely sure here
  if r.start.val < r.end.val ∧ r.end.val ≤ s.length then
    ok (.from ( s.val.slice r.start.val r.end.val)
          (by
            have := s.val.slice_length_le r.start.val r.end.val
            scalar_tac))
  else
    fail panic

@[step]
theorem Slice.subslice_spec {α : Type u} [Inhabited α] (s : Slice α) (r : Range Usize)
  (h0 : r.start.val < r.end.val) (h1 : r.end.val ≤ s.val.length) :
  subslice s r ⦃ ns => ns.val = s.slice r.start.val r.end.val ∧
  (∀ i, i + r.start.val < r.end.val → ns[i]! = s[r.start.val + i]!) ⦄
  := by
  simp_all [subslice, length, and_self, slice, spec_ok, true_and]
  intro i _
  have := List.getElem!_slice r.start.val r.end.val i s.val (by scalar_tac)
  simp only [List.getElem!_eq_getElem?_getD] at *
  apply this

@[expose] def Slice.update_subslice {α : Type u} (s : Slice α) (r : Range Usize) (ss : Slice α) : Result (Slice α) :=
  -- TODO: not completely sure here
  if h: r.start.val < r.end.val ∧ r.end.val ≤ s.length ∧ ss.val.length = r.end.val - r.start.val then
    ok (.from ( s.val.setSlice! r.start.val ss.val) (by simp))
  else
    fail panic

@[step]
theorem Slice.update_subslice_spec {α : Type u} [Inhabited α] (a : Slice α) (r : Range Usize) (ss : Slice α)
  (_ : r.start.val < r.end.val) (_ : r.end.val ≤ a.length) (_ : ss.length = r.end.val - r.start.val) :
  update_subslice a r ss ⦃ na =>
    (∀ i, i < r.start.val → na[i]! = a[i]!) ∧
    (∀ i, r.start.val ≤ i → i < r.end.val → na[i]! = ss[i - r.start.val]!) ∧
    (∀ i, r.end.val ≤ i → i < a.length → na[i]! = a[i]!) ⦄ := by
  simp only [update_subslice, length, and_self, ↓reduceDIte, getElem!_Nat_eq,
    spec_ok, *]
  simp_lists

@[expose, rust_fun "core::slice::{[@T]}::reverse" -canFail]
def core.slice.Slice.reverse {T : Type _} (s : MutBorrow (Slice T)) : Slice T :=
  .from (s.val.val.reverse) (by simp)

@[rust_trait "core::slice::index::SliceIndex"]
structure core.slice.index.SliceIndex (Self T Output : Type _) where
  get : Self → SharedBorrow T → Result (Option (SharedBorrow Output))
  get_mut : Self → MutBorrow T → Result (Option (MutBorrow Output) × (Option (MutBorrow Output) → T))
  get_unchecked : Self → ConstRawPtr T → Result (ConstRawPtr Output)
  get_unchecked_mut : Self → MutRawPtr T → Result (MutRawPtr Output)
  index : Self → SharedBorrow T → Result (SharedBorrow Output)
  index_mut : Self → MutBorrow T → Result (MutBorrow Output × (Output → T))

@[expose, rust_fun "core::slice::index::{core::ops::index::Index<[@T], @I, @O>}::index"]
def core.slice.index.Slice.index
  {T I Output : Type _} (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (slice : SharedBorrow (Slice T)) (i : I) : Result (SharedBorrow Output) :=
  inst.index i slice

@[expose, rust_fun "core::slice::{[@T]}::get"]
def core.slice.Slice.get
  {T I Output : Type _} (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (s : SharedBorrow (Slice T)) (i : I) : Result (Option (SharedBorrow Output)) :=
  inst.get i s

@[expose, rust_fun "core::slice::{[@T]}::get_unchecked"]
def core.slice.Slice.get_unchecked
  {T : Type _} {I : Type _} {Output : Type _}
  (SliceIndexInst : core.slice.index.SliceIndex I (Slice T) Output)
  (s : SharedBorrow (Slice T)) (i : I) : Result (SharedBorrow Output) := do
  -- `get_unchecked` is the unchecked counterpart of `get`: in bounds the two
  -- agree, and out of bounds Rust has UB, which we model as `fail .undef`.
  -- (We do not use `SliceIndexInst.get_unchecked`, which is stated over raw
  -- pointers.)
  let o ← SliceIndexInst.get i s
  match o with
  | some x => ok x
  | none => fail .undef

@[expose, rust_fun "core::slice::{[@T]}::get_mut"]
def core.slice.Slice.get_mut
  {T I Output : Type _} (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (s : MutBorrow (Slice T)) (i : I) :
  Result ((Option (MutBorrow Output)) × (Option (MutBorrow Output) → Slice T)) :=
  inst.get_mut i s

@[expose, rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, [@T], [@T]>}::get"]
def core.slice.index.SliceIndexRangeUsizeSlice.get {T : Type _} (r : Range Usize)
  (s : SharedBorrow (Slice T)) : Result (Option (SharedBorrow (Slice T))) :=
  if r.start ≤ r.end ∧ r.end ≤ s.val.length then
    ok (some (.mk (.from (s.val.val.slice r.start r.end) (by scalar_tac))))
  else ok none

@[expose, rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, [@T], [@T]>}::get_mut"]
def core.slice.index.SliceIndexRangeUsizeSlice.get_mut
  {T : Type _} (r : Range Usize) (s : MutBorrow (Slice T)) :
  Result (Option (MutBorrow (Slice T)) × (Option (MutBorrow (Slice T)) → Slice T)) :=
  if r.start ≤ r.end ∧ r.end ≤ s.val.length then
    ok (some (.mk (.from ( s.val.val.slice r.start r.end) (by scalar_tac))),
        fun s' =>
        match s' with
        | none => s.val
        | some s' =>
          if h: s'.val.length = r.end - r.start then
            .from (List.setSlice! s.val.val r.start s'.val.val) (by simp)
          else s.val )
  else ok (none, fun _ => s.val)

@[expose, rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, [@T], [@T]>}::get_unchecked"]
def core.slice.index.SliceIndexRangeUsizeSlice.get_unchecked {T : Type _} :
  Range Usize → ConstRawPtr (Slice T) → Result (ConstRawPtr (Slice T)) :=
  -- Don't know what the model should be - for now we always fail
  fun _ _ => fail .undef

@[expose, rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, [@T], [@T]>}::get_unchecked_mut"]
def core.slice.index.SliceIndexRangeUsizeSlice.get_unchecked_mut {T : Type _} :
  Range Usize → MutRawPtr (Slice T) → Result (MutRawPtr (Slice T)) :=
  -- Don't know what the model should be - for now we always fail
  fun _ _ => fail .undef

@[expose, rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, [@T], [@T]>}::index"]
def core.slice.index.SliceIndexRangeUsizeSlice.index {T : Type _} (r : Range Usize)
  (s : SharedBorrow (Slice T)) : Result (SharedBorrow (Slice T)) :=
  if r.start ≤ r.end ∧ r.end ≤ s.val.length then
    ok (.mk (.from (s.val.val.slice r.start r.end) (by scalar_tac)))
  else fail .panic

@[expose, rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, [@T], [@T]>}::index_mut"]
def core.slice.index.SliceIndexRangeUsizeSlice.index_mut {T : Type _} (r : Range Usize)
  (s : MutBorrow (Slice T)) : Result (MutBorrow (Slice T) × (Slice T → Slice T)) :=
  if r.start ≤ r.end ∧ r.end ≤ s.val.length then
    ok (.mk (.from (s.val.val.slice r.start r.end) (by scalar_tac)),
        /- The back function expects a slice of the same length as the returned subslice.
           We don't enforce this with a guard because we want totality; `setSlice!` handles
           any length gracefully. The model is correct when this condition holds, which is
           always the case for code generated by Aeneas. -/
        fun s' => .from (List.setSlice! s.val.val r.start s') (by simp))
  else fail .panic

/- [core::slice::index::[T]::index_mut] -/
@[expose, rust_fun "core::slice::index::{core::ops::index::IndexMut<[@T], @I, @O>}::index_mut"]
def core.slice.index.Slice.index_mut
  {T I Output : Type _} (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (s : MutBorrow (Slice T)) (i : I) : Result (MutBorrow Output × (Output → Slice T)) :=
  inst.index_mut i s

@[expose, reducible, rust_trait_impl "core::slice::index::SliceIndex<core::ops::range::Range<usize>, [@T], [@T]>"]
def core.slice.index.SliceIndexRangeUsizeSlice (T : Type _) :
  core.slice.index.SliceIndex (Range Usize) (Slice T) (Slice T) := {
  get := core.slice.index.SliceIndexRangeUsizeSlice.get
  get_mut := core.slice.index.SliceIndexRangeUsizeSlice.get_mut
  get_unchecked := core.slice.index.SliceIndexRangeUsizeSlice.get_unchecked
  get_unchecked_mut := core.slice.index.SliceIndexRangeUsizeSlice.get_unchecked_mut
  index := core.slice.index.SliceIndexRangeUsizeSlice.index
  index_mut := core.slice.index.SliceIndexRangeUsizeSlice.index_mut
}

@[expose, rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, [@T], [@T]>}::get"]
def core.slice.index.SliceIndexRangeToUsizeSlice.get
  {T : Type _} (r : core.ops.range.RangeTo Usize) (s : SharedBorrow (Slice T)) :
  Result (Option (SharedBorrow (Slice T))) :=
  if r.end ≤ s.val.length then
    ok (some (.mk (.from (s.val.val.slice 0 r.end) (by scalar_tac))))
  else ok none

@[expose, rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, [@T], [@T]>}::get_mut"]
def core.slice.index.SliceIndexRangeToUsizeSlice.get_mut
  {T : Type _} (r : core.ops.range.RangeTo Usize) (s : MutBorrow (Slice T)) :
  Result ((Option (MutBorrow (Slice T))) × (Option (MutBorrow (Slice T)) → Slice T)) :=
  if r.end ≤ s.val.length then
    ok (some (.mk (.from (s.val.val.slice 0 r.end) (by scalar_tac))),
        fun s' =>
        match s' with
        | none => s.val
        | some s' =>
          if h: s'.val.length = r.end then
            .from (List.setSlice! s.val.val 0 s'.val.val) (by simp)
          else s.val )
  else ok (none, fun _ => s.val)

@[expose, rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, [@T], [@T]>}::get_unchecked"]
def core.slice.index.SliceIndexRangeToUsizeSlice.get_unchecked
  {T : Type _} (_ : core.ops.range.RangeTo Usize) (_ : ConstRawPtr (Slice T)) : Result (ConstRawPtr (Slice T)) :=
  -- TODO: update once we make the model of computation more stateful (for now we just fail)
  fail .undef

@[expose, rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, [@T], [@T]>}::get_unchecked_mut"]
def core.slice.index.SliceIndexRangeToUsizeSlice.get_unchecked_mut
  {T : Type _} (_ : core.ops.range.RangeTo Usize) (_ : MutRawPtr (Slice T)) :
  Result (MutRawPtr (Slice T)) :=
  -- TODO: update once we make the model of computation more stateful (for now we just fail)
  fail .undef

@[expose, rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, [@T], [@T]>}::index"]
def core.slice.index.SliceIndexRangeToUsizeSlice.index
  {T : Type _} (r : core.ops.range.RangeTo Usize) (s : SharedBorrow (Slice T)) :
  Result (SharedBorrow (Slice T)) :=
  if r.end ≤ s.val.length then
    ok (.mk (.from (s.val.val.slice 0 r.end) (by scalar_tac)))
  else fail .panic

@[expose, rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, [@T], [@T]>}::index_mut"]
def core.slice.index.SliceIndexRangeToUsizeSlice.index_mut
  {T : Type _} (r : core.ops.range.RangeTo Usize) (s : MutBorrow (Slice T)) :
  Result ((MutBorrow (Slice T)) × (Slice T → Slice T)) :=
  if r.end ≤ s.val.length then
    ok (.mk (.from (s.val.val.slice 0 r.end) (by scalar_tac)),
        /- The back function expects a slice of the same length as the returned subslice.
           We don't enforce this with a guard because we want totality; `setSlice!` handles
           any length gracefully. The model is correct when this condition holds, which is
           always the case for code generated by Aeneas. -/
        fun s' => .from (List.setSlice! s.val.val 0 s'.val) (by simp))
  else fail .panic

@[expose, reducible, rust_trait_impl "core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, [@T], [@T]>"]
def core.slice.index.SliceIndexRangeToUsizeSlice (T : Type _) :
  core.slice.index.SliceIndex (core.ops.range.RangeTo Usize) (Slice T) (Slice
  T) := {
  get := core.slice.index.SliceIndexRangeToUsizeSlice.get
  get_mut := core.slice.index.SliceIndexRangeToUsizeSlice.get_mut
  get_unchecked := core.slice.index.SliceIndexRangeToUsizeSlice.get_unchecked
  get_unchecked_mut := core.slice.index.SliceIndexRangeToUsizeSlice.get_unchecked_mut
  index := core.slice.index.SliceIndexRangeToUsizeSlice.index
  index_mut := core.slice.index.SliceIndexRangeToUsizeSlice.index_mut
}

/-! ## `SliceIndex<RangeFull, [T]>`

Indexing a slice with `RangeFull` yields the whole slice. -/

@[simp, step_simps, rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get"]
abbrev core.slice.index.SliceIndexRangeFullSlice.get
  {T : Type _} (_ : core.ops.range.RangeFull) (s : SharedBorrow (Slice T)) :
  Result (Option (SharedBorrow (Slice T))) :=
  ok (some s)

@[expose, simp, step_simps, rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_mut"]
def core.slice.index.SliceIndexRangeFullSlice.get_mut
  {T : Type _} (_ : core.ops.range.RangeFull) (s : MutBorrow (Slice T)) :
  Result (Option (MutBorrow (Slice T)) × (Option (MutBorrow (Slice T)) → Slice T)) :=
  ok (some s, fun s' => match s' with | some updated => updated.val | none => s.val)

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_unchecked"]
opaque core.slice.index.SliceIndexRangeFullSlice.get_unchecked
  {T : Type _} (_ : core.ops.range.RangeFull) (s : ConstRawPtr (Slice T)) :
  Result (ConstRawPtr (Slice T)) :=
  fail .undef -- TODO: not sure what it should be

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_unchecked_mut"]
opaque core.slice.index.SliceIndexRangeFullSlice.get_unchecked_mut
  {T : Type _} (_ : core.ops.range.RangeFull) (s : MutRawPtr (Slice T)) :
  Result (MutRawPtr (Slice T)) :=
  fail .undef -- TODO: not sure what it should be

@[expose, simp, step_simps, rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index"]
def core.slice.index.SliceIndexRangeFullSlice.index
  {T : Type _} (_ : core.ops.range.RangeFull) (s : SharedBorrow (Slice T)) :
  Result (SharedBorrow (Slice T)) :=
  ok s

@[expose, simp, step_simps, rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index_mut"]
def core.slice.index.SliceIndexRangeFullSlice.index_mut
  {T : Type _} (_ : core.ops.range.RangeFull) (s : MutBorrow (Slice T)) :
  Result (MutBorrow (Slice T) × (Slice T → Slice T)) :=
  ok (s, fun updated => updated)

@[expose, reducible, rust_trait_impl "core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>"]
def core.slice.index.SliceIndexRangeFullSlice (T : Type _) :
  core.slice.index.SliceIndex core.ops.range.RangeFull (Slice T) (Slice T) := {
  get := core.slice.index.SliceIndexRangeFullSlice.get
  get_mut := core.slice.index.SliceIndexRangeFullSlice.get_mut
  get_unchecked := core.slice.index.SliceIndexRangeFullSlice.get_unchecked
  get_unchecked_mut := core.slice.index.SliceIndexRangeFullSlice.get_unchecked_mut
  index := core.slice.index.SliceIndexRangeFullSlice.index
  index_mut := core.slice.index.SliceIndexRangeFullSlice.index_mut
}

@[expose, rust_trait_impl "core::ops::index::Index<[@T], @I, @O>"]
def core.ops.index.IndexSlice {T I Output : Type _}
  (inst : core.slice.index.SliceIndex I (Slice T) Output) :
  core.ops.index.Index (Slice T) I Output := {
  index := core.slice.index.Slice.index inst
}

@[expose, rust_trait_impl "core::ops::index::IndexMut<[@T], @I, @O>"]
def core.ops.index.IndexMutSlice {T I Output : Type _}
  (inst : core.slice.index.SliceIndex I (Slice T) Output) :
  core.ops.index.IndexMut (Slice T) I Output := {
  indexInst := core.ops.index.IndexSlice inst
  index_mut := core.slice.index.Slice.index_mut inst
}

@[simp, step_simps, rust_fun "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], @T>}::get"]
abbrev core.slice.index.Usize.get
  {T : Type _} (i : Usize) (s : SharedBorrow (Slice T)) : Result (Option (SharedBorrow T)) :=
  ok (s.val[i]?.map SharedBorrow.mk)

@[simp, step_simps, rust_fun "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], @T>}::get_mut"]
abbrev core.slice.index.Usize.get_mut
  {T : Type _} (i : Usize) (s : MutBorrow (Slice T)) :
  Result (Option (MutBorrow T) × (Option (MutBorrow T) → Slice T)) :=
  ok (s.val[i]?.map MutBorrow.mk, fun x => s.val.set_opt i (x.map MutBorrow.val))

@[expose, rust_fun "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], @T>}::get_unchecked"]
def core.slice.index.Usize.get_unchecked
  {T : Type _} : Usize → ConstRawPtr (Slice T) → Result (ConstRawPtr T) :=
  -- We don't have a model for now
  fun _ _ => fail .undef

@[expose, rust_fun "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], @T>}::get_unchecked_mut"]
def core.slice.index.Usize.get_unchecked_mut
  {T : Type _} : Usize → MutRawPtr (Slice T) → Result (MutRawPtr T) :=
  -- We don't have a model for now
  fun _ _ => fail .undef

@[simp, step_simps, rust_fun "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], @T>}::index"]
abbrev core.slice.index.Usize.index {T : Type _} (i : Usize) (s : SharedBorrow (Slice T)) :
  Result (SharedBorrow T) :=
  Slice.index_usize s i

@[simp, step_simps, rust_fun "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], @T>}::index_mut"]
abbrev core.slice.index.Usize.index_mut {T : Type _}
  (i : Usize) (s : MutBorrow (Slice T)) : Result (MutBorrow T × (T → (Slice T))) :=
  Slice.index_mut_usize s i

@[expose, reducible, rust_trait_impl "core::slice::index::SliceIndex<usize, [@T], @T>"]
def core.slice.index.SliceIndexUsizeSlice (T : Type _) :
  core.slice.index.SliceIndex Usize (Slice T) T := {
  get := core.slice.index.Usize.get
  get_mut := core.slice.index.Usize.get_mut
  get_unchecked := core.slice.index.Usize.get_unchecked
  get_unchecked_mut := core.slice.index.Usize.get_unchecked_mut
  index := core.slice.index.Usize.index
  index_mut := core.slice.index.Usize.index_mut
}

@[step]
theorem core.slice.Slice.get_unchecked_SliceIndexUsizeSlice_spec {T s i} [Inhabited T]
  (h : i.val < s.val.length) :
  core.slice.Slice.get_unchecked  (core.slice.index.SliceIndexUsizeSlice T) s i
  ⦃ x => x.val = s.val[i] ⦄ := by
  simp only [core.slice.Slice.get_unchecked, core.slice.index.Usize.get]
  simp [h]

@[expose, rust_fun "core::slice::{[@T]}::copy_from_slice"]
def core.slice.Slice.copy_from_slice {T : Type _} (_ : core.marker.Copy T)
  (s : MutBorrow (Slice T)) (src: SharedBorrow (Slice T)) : Result (Slice T) :=
  if Slice.len (.mk s.val) = Slice.len src then ok src.val
  else fail panic

@[expose, rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, [@T], [@T]>}::get"]
def core.slice.index.SliceIndexRangeFromUsizeSlice.get {T : Type _} (r : core.ops.range.RangeFrom Usize)
  (s : SharedBorrow (Slice T)) : Result (Option (SharedBorrow (Slice T))) :=
  if  r.start ≤ s.val.length then
    ok (some (.mk (s.val.drop r.start)))
  else ok none

@[expose, rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, [@T], [@T]>}::get_mut"]
def core.slice.index.SliceIndexRangeFromUsizeSlice.get_mut
  {T : Type _} (r : core.ops.range.RangeFrom Usize) (s : MutBorrow (Slice T)) :
  Result ((Option (MutBorrow (Slice T))) × (Option (MutBorrow (Slice T)) → Slice T)) :=
  if r.start ≤ s.val.length then
    ok (some (.mk (s.val.drop r.start)),
        fun s' => match s' with
        | none => s.val
        | some s' =>
          if h: s'.val.length + s.val.length - r.start.val ≤ Usize.max then
            .from (s'.val.val ++ s.val.val.drop r.start.val) (by grind)
          else s.val)
  else ok (none, fun _ => s.val)

@[expose, rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, [@T], [@T]>}::get_unchecked"]
def core.slice.index.SliceIndexRangeFromUsizeSlice.get_unchecked {T : Type _} :
  core.ops.range.RangeFrom Usize → ConstRawPtr (Slice T) → Result (ConstRawPtr (Slice T)) :=
  -- We don't have a model for now
  fun _ _ => fail .undef

@[expose, rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, [@T], [@T]>}::get_unchecked_mut"]
def core.slice.index.SliceIndexRangeFromUsizeSlice.get_unchecked_mut {T : Type _} :
  core.ops.range.RangeFrom Usize → MutRawPtr (Slice T) → Result (MutRawPtr (Slice T)) :=
  -- We don't have a model for now
  fun _ _ => fail .undef

@[expose, rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, [@T], [@T]>}::index"]
def core.slice.index.SliceIndexRangeFromUsizeSlice.index {T : Type _}
  (r : core.ops.range.RangeFrom Usize) (s : SharedBorrow (Slice T)) : Result (SharedBorrow (Slice T)) :=
  if r.start.val ≤ s.val.length then
    ok (.mk (s.val.drop r.start))
  else fail .undef

@[expose, rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, [@T], [@T]>}::index_mut"]
def core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut {T : Type _}
  (r : core.ops.range.RangeFrom Usize) (s : MutBorrow (Slice T)) :
  Result ((MutBorrow (Slice T)) × (Slice T → Slice T)) :=
  if r.start ≤ s.val.length then
    let s1 := s.val.drop r.start
    ok ( .mk s1,
         /- The back function expects a slice of the same length as the returned subslice.
            We don't enforce this with a guard because we want totality; `setSlice!` handles
            any length gracefully. The model is correct when this condition holds, which is
            always the case for code generated by Aeneas. -/
         fun s2 => .from (s.val.val.setSlice! r.start s2) (by simp))
  else fail .panic

theorem _SliceIndexRangeFromUsizeSlice.index_mut.test {T} (s : MutBorrow (Slice T)) (r : core.ops.range.RangeFrom Usize) (h : r.start ≤ s.val.length) :
  match (core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut r s).match with
  | .ok (s1, back) =>
    back s1.val = s.val
  | _ => False := by
  unfold core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut
  simp [h]

@[expose, reducible, rust_trait_impl "core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, [@T], [@T]>"]
def core.slice.index.SliceIndexRangeFromUsizeSlice (T : Type _) :
  core.slice.index.SliceIndex (core.ops.range.RangeFrom Usize) (Slice T) (Slice T) := {
  get := core.slice.index.SliceIndexRangeFromUsizeSlice.get
  get_mut := core.slice.index.SliceIndexRangeFromUsizeSlice.get_mut
  get_unchecked :=
    core.slice.index.SliceIndexRangeFromUsizeSlice.get_unchecked
  get_unchecked_mut :=
    core.slice.index.SliceIndexRangeFromUsizeSlice.get_unchecked_mut
  index := core.slice.index.SliceIndexRangeFromUsizeSlice.index
  index_mut :=
    core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut
}

/-- Small helper (this function doesn't model a specific Rust function) -/
@[expose] def Slice.clone {T : Type _} (clone : T → Result T) (s : Slice T) : Result (Slice T) := do
  let s' ← List.clone clone s.val
  ok (.from s'.val (by rw [s'.property]; exact s.property))

theorem Slice.clone_length {T : Type _} {clone : T → Result T} {s s' : Slice T} (h : Slice.clone clone s = ok s') :
  s'.length = s.length := by
  simp [Slice.clone] at h
  cases h2 : List.clone clone ↑s <;> simp_all
  grind

@[step]
theorem Slice.clone_spec {T : Type _} {clone : T → Result T} {s : Slice T} (h : ∀ x ∈ s.val, clone x = ok x) :
  Slice.clone clone s ⦃ s' => s = s' ⦄ := by
  simp only [Slice.clone]
  apply spec_bind (List.clone_spec h)
  intro l' hl'
  simp [hl']

@[expose, rust_fun "core::slice::{[@T]}::split_at"]
def core.slice.Slice.split_at {T : Type _} (s : SharedBorrow (Slice T)) (n : Usize) :
  Result ((SharedBorrow (Slice T)) × (SharedBorrow (Slice T))) :=
  if h0 : n ≤ s.val.length then
    let s0 := (s.val.val.splitAt n.val).fst
    let s1 := (s.val.val.splitAt n.val).snd
    let s0 : Slice T := .from s0 (by scalar_tac)
    let s1 : Slice T := .from s1 (by scalar_tac)
    ok (.mk s0, .mk s1)
  else fail .panic

@[expose, rust_fun "core::slice::{[@T]}::split_at_mut"]
def core.slice.Slice.split_at_mut {T : Type _} (s : MutBorrow (Slice T)) (n : Usize) :
  Result (((MutBorrow (Slice T)) × (MutBorrow (Slice T))) × (((Slice T) × (Slice T)) → Slice T)) :=
  if h0 : n ≤ s.val.length then
    let s0 := (s.val.val.splitAt n.val).fst
    let s1 := (s.val.val.splitAt n.val).snd
    let back (s' : Slice T × Slice T) : Slice T :=
      let s0' := s'.fst
      let s1' := s'.snd
      if h1 : s0'.length = s0.length ∧ s1'.length = s1.length then
        -- TODO: scalar_tac is super slow below
        .from (s0'.val ++ s1'.val) (by have := List.splitAt_length n.val s.val.val; have := s.val.property; simp +zetaDelta at *; grind)
      else s.val
    let s0 : Slice T := .from s0 (by scalar_tac)
    let s1 : Slice T := .from s1 (by scalar_tac)
    ok ((.mk s0, .mk s1), back)
  else fail .panic

/-- **Spec theorem for `core::slice::{[@T]}::split_at`** -/
@[step]
theorem core.slice.Slice.split_at.spec {T : Type _} (s : SharedBorrow (Slice T)) (n : Usize)
    (h : n ≤ s.val.length) :
    core.slice.Slice.split_at s n
      ⦃ (s0 : SharedBorrow (Slice T)) (s1 : SharedBorrow (Slice T)) =>
        s0.val.length = n.val ∧ s1.val.length = s.val.length - n.val ∧
        s0.val.val = s.val.val.take n.val ∧ s1.val.val = s.val.val.drop n.val ⦄ := by
  unfold core.slice.Slice.split_at
  simp only [h, ↓reduceDIte, WP.spec_ok, uncurry'_pair]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp [Slice.length, List.splitAt_eq, List.length_take, List.length_drop, *]

/-- **Spec theorem for `core::slice::{[@T]}::split_at_mut`** -/
-- TODO: ideally the postcondition binder would decompose the result pair as
-- `(s0 : Slice T) (s1 : Slice T) (back : ...)`, but the `⦃ ⦄` notation's
-- `uncurry'` only handles right-associated products, so the left-associated
-- `((Slice T × Slice T) × BackFn)` return type cannot be split into three
-- separate binders. We keep projectors for now.
@[step]
theorem core.slice.Slice.split_at_mut.spec {T : Type _} (s : MutBorrow (Slice T)) (n : Usize)
    (h : n ≤ s.val.length) :
    core.slice.Slice.split_at_mut s n
      ⦃ (res : MutBorrow (Slice T) × MutBorrow (Slice T)) (back : (Slice T × Slice T) → Slice T) =>
        res.1.val.length = n.val ∧ res.2.val.length = s.val.length - n.val ∧
        res.1.val.val = s.val.val.take n.val ∧ res.2.val.val = s.val.val.drop n.val ∧
        (∀ s0' s1', s0'.length = n.val → s1'.length = s.val.length - n.val →
          (back (s0', s1')).val = s0'.val ++ s1'.val ∧
          (back (s0', s1')).length = s.val.length) ⦄ := by
  unfold core.slice.Slice.split_at_mut
  simp only [h, ↓reduceDIte, WP.spec_ok, uncurry'_pair]
  refine ⟨?_, ?_, ?_, ?_, fun s0' s1' hs0' hs1' => ?_⟩
  · simp [Slice.length, List.splitAt_eq]; scalar_tac
  · simp [Slice.length, List.splitAt_eq]
  · simp [List.splitAt_eq]
  · simp [List.splitAt_eq]
  · split_ifs with hcond
    · exact ⟨by grind, by simp [Slice.length, List.length_append]; scalar_tac⟩
    · exfalso; apply hcond
      simp [Slice.length, List.splitAt_eq] at *
      exact ⟨by scalar_tac, by scalar_tac⟩

@[expose, rust_fun "core::slice::{[@T]}::swap"]
def core.slice.Slice.swap {T : Type _} (s : MutBorrow (Slice T)) (a b : Usize) : Result (Slice T) := do
  let av ← Slice.index_usize (.mk s.val) a
  let bv ← Slice.index_usize (.mk s.val) b
  let s1 ← Slice.update s.val a bv.val
  Slice.update s1 b av.val

@[step]
theorem core.slice.Slice.swap_spec {T : Type _} [Inhabited T] (s : MutBorrow (Slice T)) (a b : Usize)
    (ha : a.val < s.val.length) (hb : b.val < s.val.length) :
    core.slice.Slice.swap s a b ⦃ s' =>
      s'.length = s.val.length ∧
      s'.val[a.val]! = s.val.val[b.val]! ∧
      s'.val[b.val]! = s.val.val[a.val]! ∧
      ∀ i, i ≠ a.val → i ≠ b.val → s'.val[i]! = s.val.val[i]! ⦄ := by
  rcases s with ⟨s⟩
  simp only [core.slice.Slice.swap, Bind.bind]
  apply spec_bind (Slice.index_usize_spec (.mk s) a ha); intro av hav
  apply spec_bind (Slice.index_usize_spec (.mk s) b hb); intro bv hbv
  apply spec_bind (Slice.update_spec s a bv.val ha); intro s1 hs1
  have hlen1 : b.val < s1.length := by rw [hs1, Slice.set_length]; exact hb
  apply spec_mono (Slice.update_spec s1 b av.val hlen1); intro s' hs'
  rw [hav] at hs'; rw [hbv] at hs1
  subst hs1 hs'
  simp only [Slice.length, ne_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Slice.set_val_eq, List.length_set]
  · by_cases hab : (↑a : ℕ) = ↑b
    · simp only [Slice.set_val_eq, hab]; grind
    · simp only [Slice.set_val_eq]
      grind
  · simp only [Slice.set_val_eq]; grind
  · intro i hia hib
    simp only [Slice.set_val_eq]
    grind

@[simp, step_simps]
theorem Slice.index_mut_SliceIndexRangeUsizeSliceInst (s : MutBorrow (Slice α)) (r : core.ops.range.Range Usize) :
  core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice α) s r = core.slice.index.SliceIndexRangeUsizeSlice.index_mut r s := by
  rfl

@[simp, step_simps]
theorem Slice.index_SliceIndexRangeUsizeSliceInst (s : SharedBorrow (Slice α)) (r : core.ops.range.Range Usize) :
  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice α) s r = core.slice.index.SliceIndexRangeUsizeSlice.index r s := by
  rfl

@[expose] def Slice.setSlice! {α : Type u} (s : Slice α) (i : ℕ) (s' : List α) : Slice α :=
  .from (s.val.setSlice! i s') (by simp)

@[simp, scalar_tac_simps, simp_scalar_safe, simp_lists_safe, grind =, agrind =]
theorem Slice.setSlice!_length {α : Type u} (s : Slice α) (i : ℕ) (s' : List α) :
  (s.setSlice! i s').length = s.length := by
  simp [Slice.length, Slice.setSlice!, List.length_setSlice!]

@[simp_lists_safe]
theorem Slice.setSlice!_getElem!_prefix {α} [Inhabited α]
  (s : Slice α) (s' : List α) (i j : ℕ) (h : j < i) :
  (s.setSlice! i s')[j]! = s[j]! := by
  simp [Slice.setSlice!, Slice.getElem!_Nat_eq]
  simp_lists

@[simp_lists_safe]
theorem Slice.setSlice!_getElem_prefix {α}
  (s : Slice α) (s' : List α) (i j : ℕ) (h : j < i ∧ j < s.length) :
  (s.setSlice! i s')[j] = s[j] := by
  have hj' : j < (s.setSlice! i s').length := by
    simpa [Slice.setSlice!_length] using h.2
  have h1 : (s.setSlice! i s')[j]? = s[j]? := by
    simp [Slice.getElem?_Nat_eq, Slice.setSlice!]
    simp_lists [List.setSlice!_getElem?_prefix]
  simp only [Slice.getElem?_Nat_eq, List.getElem?_eq_getElem hj', List.getElem?_eq_getElem h.2,
    Option.some.injEq] at h1
  exact h1

@[simp_lists_safe]
theorem Slice.setSlice!_getElem!_middle {α} [Inhabited α]
  (s : Slice α) (s' : List α) (i j : ℕ) (h : i ≤ j ∧ j - i < s'.length ∧ j < s.length) :
  (s.setSlice! i s')[j]! = s'[j - i]! := by
  simp [Slice.setSlice!, Slice.getElem!_Nat_eq]
  simp_lists

@[simp_lists_safe]
theorem Slice.setSlice!_getElem_middle {α}
  (s : Slice α) (s' : List α) (i j : ℕ) (h : i ≤ j ∧ j - i < s'.length ∧ j < s.length) :
  (s.setSlice! i s')[j] = s'[j - i] := by
  have hj' : j < (s.setSlice! i s').length := by
    simpa [Slice.setSlice!_length] using h.2.2
  have hji : j - i < s'.length := h.2.1
  have h1 : (s.setSlice! i s')[j]? = s'[j - i]? := by
    simp [Slice.getElem?_Nat_eq, Slice.setSlice!]
    simp_lists [List.setSlice!_getElem?_middle]
  simp only [Slice.getElem?_Nat_eq, List.getElem?_eq_getElem hj', List.getElem?_eq_getElem hji,
    Option.some.injEq] at h1
  exact h1

theorem Slice.setSlice!_getElem!_suffix {α} [Inhabited α]
  (s : Slice α) (s' : List α) (i j : ℕ) (h : i + s'.length ≤ j) :
  (s.setSlice! i s')[j]! = s[j]! := by
  simp [Slice.setSlice!, Slice.getElem!_Nat_eq]
  simp_lists

theorem Slice.setSlice!_getElem_suffix {α}
  (s : Slice α) (s' : List α) (i j : ℕ) (h : i + s'.length ≤ j ∧ j < s.length) :
  (s.setSlice! i s')[j] = s[j] := by
  have hj' : j < (s.setSlice! i s').length := by
    simpa [Slice.setSlice!_length] using h.2
  have h1 : (s.setSlice! i s')[j]? = s[j]? := by
    simp [Slice.getElem?_Nat_eq, Slice.setSlice!]
    simp_lists [List.setSlice!_getElem?_suffix]
  simp only [Slice.getElem?_Nat_eq, List.getElem?_eq_getElem hj', List.getElem?_eq_getElem h.2,
    Option.some.injEq] at h1
  exact h1

@[simp, simp_lists_safe]
theorem Slice.setSlice!_val (s : Slice α) (i : ℕ) (s' : List α) :
  (s.setSlice! i s').val = s.val.setSlice! i s' := by
  simp [setSlice!]

@[step]
theorem core.slice.index.SliceIndexRangeUsizeSlice.index_mut.step_spec (r : core.ops.range.Range Usize)
  (s : MutBorrow (Slice α))
  (h0 : r.start ≤ r.end) (h1 : r.end ≤ s.val.length) :
  core.slice.index.SliceIndexRangeUsizeSlice.index_mut r s ⦃ (s1 : MutBorrow (Slice α)) (index_mut_back : Slice α → Slice α) =>
  s1.val.val = s.val.val.slice r.start r.end ∧
  s1.val.length = r.end - r.start ∧
  ∀ s2, index_mut_back s2 = s.val.setSlice! r.start.val s2 ⦄ := by
  simp [index_mut, UScalar.le_equiv, Slice.length]
  split
  . simp [spec_ok, Std.WP.uncurry', true_and]
    simp_lists [Slice.eq_iff]
    grind
  . scalar_tac

@[step]
theorem core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec {α : Type _}
    (r : core.ops.range.Range Usize) (s : SharedBorrow (Slice α)) (h0 : r.start ≤ r.end)
    (h1 : r.end ≤ s.val.length) :
    core.slice.index.SliceIndexRangeUsizeSlice.index r s ⦃ (s1 : SharedBorrow (Slice α)) =>
      s1.val.val = s.val.val.slice r.start r.end ∧
      s1.val.length = r.end - r.start ⦄ := by
  simp only [core.slice.index.SliceIndexRangeUsizeSlice.index, UScalar.le_equiv, Slice.length]
  split
  · simp only [spec_ok]
    simp_lists
    grind
  · simp only [spec_fail]
    scalar_tac

-- RangeTo step specs

@[simp, step_simps]
theorem Slice.index_mut_SliceIndexRangeToUsizeSliceInst (s : MutBorrow (Slice α)) (r : core.ops.range.RangeTo Usize) :
  core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeToUsizeSlice α) s r =
  core.slice.index.SliceIndexRangeToUsizeSlice.index_mut r s := by rfl

@[simp, step_simps]
theorem Slice.index_SliceIndexRangeToUsizeSliceInst (s : SharedBorrow (Slice α)) (r : core.ops.range.RangeTo Usize) :
  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice α) s r =
  core.slice.index.SliceIndexRangeToUsizeSlice.index r s := by rfl

@[step]
theorem core.slice.index.SliceIndexRangeToUsizeSlice.index_mut.step_spec
    (r : core.ops.range.RangeTo Usize) (s : MutBorrow (Slice α)) (h : r.end ≤ s.val.length) :
  core.slice.index.SliceIndexRangeToUsizeSlice.index_mut r s
    ⦃ (s1 : MutBorrow (Slice α)) (back : Slice α → Slice α) =>
      s1.val.val = s.val.val.slice 0 r.end ∧
      s1.val.length = r.«end» ∧
      ∀ s', (back s').val = s.val.val.setSlice! 0 s'.val ⦄ := by
  simp only [index_mut]
  split
  · grind [Std.WP.uncurry']
  · scalar_tac

@[step]
theorem core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec
    (r : core.ops.range.RangeTo Usize) (s : SharedBorrow (Slice α)) (h : r.end ≤ s.val.length) :
  core.slice.index.SliceIndexRangeToUsizeSlice.index r s
    ⦃ (s1 : SharedBorrow (Slice α)) =>
      s1.val.val = s.val.val.slice 0 r.end ∧
      s1.val.length = r.end ⦄ := by
  simp only [index]
  split
  · simp only [spec_ok, Slice.length]
    simp; scalar_tac
  · scalar_tac

-- RangeFrom step specs

@[simp, step_simps]
theorem Slice.index_mut_SliceIndexRangeFromUsizeSliceInst (s : MutBorrow (Slice α)) (r : core.ops.range.RangeFrom Usize) :
  core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeFromUsizeSlice α) s r =
  core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut r s := by rfl

@[simp, step_simps]
theorem Slice.index_SliceIndexRangeFromUsizeSliceInst (s : SharedBorrow (Slice α)) (r : core.ops.range.RangeFrom Usize) :
  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice α) s r =
  core.slice.index.SliceIndexRangeFromUsizeSlice.index r s := by rfl

@[step]
theorem core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut.step_spec
    (r : core.ops.range.RangeFrom Usize) (s : MutBorrow (Slice α)) (h : r.start ≤ s.val.length) :
  core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut r s
    ⦃ (s1 : MutBorrow (Slice α)) (back : Slice α → Slice α) =>
      s1.val.val = s.val.val.drop r.start ∧
      s1.val.length = s.val.length - r.start.val ∧
      ∀ s', (back s').val = s.val.val.setSlice! r.start.val s'.val ⦄ := by
  simp only [index_mut, Slice.drop]
  split
  · simp [spec_ok, Std.WP.uncurry']
  · scalar_tac

@[step]
theorem core.slice.index.SliceIndexRangeFromUsizeSlice.index.step_spec
    (r : core.ops.range.RangeFrom Usize) (s : SharedBorrow (Slice α)) (h : r.start ≤ s.val.length) :
  core.slice.index.SliceIndexRangeFromUsizeSlice.index r s
    ⦃ (s1 : SharedBorrow (Slice α)) =>
      s1.val.val = s.val.val.drop r.start ∧
      s1.val.length = s.val.length - r.start.val ⦄ := by
  simp only [index]
  split
  · simp only [spec_ok, Slice.drop]
    simp [Slice.length, List.length_drop]
  · scalar_tac

@[step]
theorem core.slice.Slice.copy_from_slice.step_spec (copyInst : core.marker.Copy α)
  (s0 : MutBorrow (Slice α)) (s1 : SharedBorrow (Slice α))
  (h : s0.val.length = s1.val.length) :
  core.slice.Slice.copy_from_slice copyInst s0 s1 ⦃ s1' => s1' = s1.val ⦄ := by
  simp only [copy_from_slice]
  simp at h
  simp only [Slice.len]
  simp [h]

@[expose] def Slice.mapM  {α β} (f : α → Result β) (x : Slice α) : Result (Slice β) :=
  do let ⟨l, p⟩ ← List.mapM_with_length f x.val
     ok (.from l (by grind))

@[step]
theorem Slice.mapM_spec {α β} {f : α → Result β} {s : Slice α} {post : Nat → β → Prop}
    (hf : ∀ i (hi : i < Slice.len (.mk s)), f s[i] ⦃ post i ⦄) :
    s.mapM f ⦃ s' => Slice.len (.mk s') = Slice.len (.mk s) ∧
      ∀ i (hi : i < Slice.len (.mk s')), post i s'[i] ⦄ := by
  simp only [mapM]
  apply spec_bind (List.mapM_with_length_spec (post := post) (f := f) (l := s.val) (by
    intros i hi
    simp at *
    apply (hf ⟨i, by grind⟩)
    simp [UScalar.val, hi]))
  intro l' hl'
  simp only [spec_ok]
  constructor
  · grind
  · intros i hi
    grind

-- ============================================================================
-- Slice.fill — overwrite every element with a clone of `v`
-- ============================================================================

/-- Model for `<[T]>::fill(v)`: returns a slice of the same length where every
    element is obtained by calling `clone(v)`. Mirrors Rust stdlib. -/
@[expose, rust_fun "core::slice::{[@T]}::fill"]
def core.slice.Slice.fill {T : Type _} (cloneInst : core.clone.Clone T)
    (s : MutBorrow (Slice T)) (v : T) : Result (Slice T) :=
  do let ⟨l, p⟩ ← List.mapM_with_length (fun _ => cloneInst.clone (.mk v)) s.val.val
     ok (.from l (by grind))

private theorem List.mapM_const_ok {T : Type _} (l : List T)
    {g : Result T} {v : T} (hg : g = ok v) :
    l.mapM (fun _ => g) = ok (List.replicate l.length v) := by
  subst hg
  have : ∀ acc, List.mapM.loop (fun _ => ok v) l acc = ok (acc.reverse ++ List.replicate l.length v) := by
    intro acc; induction l generalizing acc with
    | nil => simp [List.mapM.loop, pure]
    | cons _ _ ih => simp [List.mapM.loop, bind_tc_ok, ih, List.reverse_cons, List.append_assoc, List.replicate_succ]
  simp [List.mapM, this]

@[step]
theorem core.slice.Slice.fill.spec {T : Type _} (cloneInst : core.clone.Clone T)
    (s : MutBorrow (Slice T)) (v : T)
    (hclone : cloneInst.clone (.mk v) ⦃ fun v' => v' = v ⦄) :
    core.slice.Slice.fill cloneInst s v
    ⦃ (s' : Slice T) =>
      s'.length = s.val.length ∧
      s'.val = List.replicate s.val.length v ⦄ := by
  simp only [fill]
  apply spec_bind (List.mapM_with_length_spec (post := fun _ v' => v' = v)
    (f := fun _ => cloneInst.clone (.mk v)) (l := s.val.val) (by intros i hi; exact hclone))
  intro l' hl'
  simp only [spec_ok]
  have hlen := l'.property
  have hrep : l'.val = List.replicate s.val.length v := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i h1 h2
      simp only [List.getElem_replicate]
      exact hl' i h1
  simp [hrep, Slice.length]

end Aeneas.Std
