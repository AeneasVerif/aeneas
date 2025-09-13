/- Vectors -/
import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Aeneas.Std.Scalar
import Aeneas.Std.Slice
import Aeneas.ScalarTac
import Aeneas.Progress.Init

namespace Aeneas

namespace Std

open Result Error

namespace alloc.vec

def Vec (α : Type u) := { l : List α // l.length ≤ Usize.max }

/-- We need this to coerce vectors to lists without marking `Vec` as reducible.
    Also not that we *do not* want to mark `Vec` as reducible: it triggers issues.
-/
instance (α : Type u) : CoeOut (Vec α) (List α) where
  coe := λ v => v.val

instance [BEq α] : BEq (Vec α) := SubtypeBEq _

instance [BEq α] [LawfulBEq α] : LawfulBEq (Vec α) := SubtypeLawfulBEq _

theorem Vec.len_ineq {α : Type u} (v : Vec α) : v.val.length ≤ Usize.max := by
  cases v; simp[*]

@[simp, scalar_tac_simps, simp_scalar_simps, simp_lists_simps]
abbrev Vec.length {α : Type u} (v : Vec α) : Nat := v.val.length

@[simp, scalar_tac_simps, simp_scalar_simps, simp_lists_simps]
abbrev Vec.v {α : Type u} (v : Vec α) : List α := v.val

example {a: Type u} (v : Vec a) : v.length ≤ Usize.max := by
  scalar_tac

abbrev Vec.new (α : Type u): Vec α := ⟨ [], by simp ⟩

instance (α : Type u) : Inhabited (Vec α) := by
  constructor
  apply Vec.new

@[simp]
abbrev Vec.len {α : Type u} (v : Vec α) : Usize :=
  Usize.ofNatCore v.val.length (by scalar_tac)

@[simp, scalar_tac_simps]
theorem Vec.len_val {α : Type u} (v : Vec α) : (Vec.len v).val = v.length :=
  by simp

@[reducible] instance {α : Type u} : GetElem (Vec α) Nat α (fun a i => i < a.val.length) where
  getElem a i h := getElem a.val i h

@[reducible] instance {α : Type u} : GetElem? (Vec α) Nat α (fun a i => i < a.val.length) where
  getElem? a i := getElem? a.val i
  getElem! a i := getElem! a.val i

@[simp, scalar_tac_simps, simp_lists_hyps_simps]
theorem Vec.getElem?_Nat_eq {α : Type u} (v : Vec α) (i : Nat) : v[i]? = v.val[i]? := by rfl

@[simp, scalar_tac_simps, simp_lists_hyps_simps]
theorem Vec.getElem!_Nat_eq {α : Type u} [Inhabited α] (v : Vec α) (i : Nat) : v[i]! = v.val[i]! := by rfl

@[reducible] instance {α : Type u} : GetElem (Vec α) Usize α (fun a i => i < a.val.length) where
  getElem a i h := getElem a.val i.val h

@[reducible] instance {α : Type u} : GetElem? (Vec α) Usize α (fun a i => i < a.val.length) where
  getElem? a i := getElem? a.val i.val
  getElem! a i := getElem! a.val i.val

@[simp, scalar_tac_simps, simp_lists_hyps_simps] theorem Vec.getElem?_Usize_eq {α : Type u} (v : Vec α) (i : Usize) : v[i]? = v.val[i.val]? := by rfl
@[simp, scalar_tac_simps, simp_lists_hyps_simps] theorem Vec.getElem!_Usize_eq {α : Type u} [Inhabited α] (v : Vec α) (i : Usize) : v[i]! = v.val[i.val]! := by rfl

@[simp, scalar_tac_simps, simp_lists_hyps_simps] abbrev Vec.get? {α : Type u} (v : Vec α) (i : Nat) : Option α := getElem? v i
@[simp, scalar_tac_simps, simp_lists_hyps_simps] abbrev Vec.get! {α : Type u} [Inhabited α] (v : Vec α) (i : Nat) : α := getElem! v i

def Vec.set {α : Type u} (v: Vec α) (i: Usize) (x: α) : Vec α :=
  ⟨ v.val.set i.val x, by have := v.property; simp [*] ⟩

def Vec.set_opt {α : Type u} (v: Vec α) (i: Usize) (x: Option α) : Vec α :=
  ⟨ v.val.set_opt i.val x, by have := v.property; simp [*] ⟩

@[simp, scalar_tac_simps, simp_lists_hyps_simps]
theorem Vec.set_val_eq {α : Type u} (v: Vec α) (i: Usize) (x: α) :
  (v.set i x) = v.val.set i.val x := by
  simp [set]

@[simp, scalar_tac_simps, simp_lists_hyps_simps]
theorem Vec.set_opt_val_eq {α : Type u} (v: Vec α) (i: Usize) (x: Option α) :
  (v.set_opt i x) = v.val.set_opt i.val x := by
  simp [set_opt]

@[irreducible]
def Vec.push {α : Type u} (v : Vec α) (x : α) : Result (Vec α)
  :=
  let nlen := List.length v.val + 1
  if h : nlen ≤ U32.max || nlen ≤ Usize.max then
    ok ⟨ List.concat v.val x, by simp; scalar_tac ⟩
  else
    fail maximumSizeExceeded

@[progress]
theorem Vec.push_spec {α : Type u} (v : Vec α) (x : α) (h : v.val.length < Usize.max) :
  ∃ v1, v.push x = ok v1 ∧
  v1.val = v.val ++ [x] := by
  rw [push]; simp
  split <;> simp_all
  scalar_tac

def Vec.insert {α : Type u} (v: Vec α) (i: Usize) (x: α) : Result (Vec α) :=
  if i.val < v.length then
    ok ⟨ v.val.set i x, by have := v.property; simp [*] ⟩
  else
    fail arrayOutOfBounds

@[progress]
theorem Vec.insert_spec {α : Type u} (v: Vec α) (i: Usize) (x: α)
  (hbound : i.val < v.length) :
  ∃ nv, v.insert i x = ok nv ∧ nv.val = v.val.set i x := by
  simp [insert, *]

def Vec.index_usize {α : Type u} (v: Vec α) (i: Usize) : Result α :=
  match v[i.val]? with
  | none => fail .arrayOutOfBounds
  | some x => ok x

@[progress]
theorem Vec.index_usize_spec {α : Type u} [Inhabited α] (v: Vec α) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x, v.index_usize i = ok x ∧ x = v.val[i.val]! := by
  simp only [index_usize]
  simp at *
  simp [*]

def Vec.update {α : Type u} (v: Vec α) (i: Usize) (x: α) : Result (Vec α) :=
  match v.val[i.val]? with
  | none => fail .arrayOutOfBounds
  | some _ =>
    ok ⟨ v.val.set i x, by have := v.property; simp [*] ⟩

@[progress]
theorem Vec.update_spec {α : Type u} (v: Vec α) (i: Usize) (x : α)
  (hbound : i.val < v.length) :
  ∃ nv, v.update i x = ok nv ∧
  nv = v.set i x
  := by
  simp only [update, set]
  simp at *
  split <;> simp_all

@[scalar_tac_simps]
theorem Vec.set_length {α : Type u} (v: Vec α) (i: Usize) (x: α) :
  (v.set i x).length = v.length := by simp

def Vec.index_mut_usize {α : Type u} (v: Vec α) (i: Usize) :
  Result (α × (α → Vec α)) :=
  match Vec.index_usize v i with
  | .ok x =>
    ok (x, Vec.set v i)
  | .fail e => fail e
  | .div => div
  | .brk e => .brk e

@[progress]
theorem Vec.index_mut_usize_spec {α : Type u} [Inhabited α] (v: Vec α) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x, v.index_mut_usize i = ok (x, v.set i) ∧
  x = v.val[i.val]!
  := by
  simp only [index_mut_usize]
  have ⟨ x, h ⟩ := index_usize_spec v i hbound
  simp [h]

/- [alloc::vec::Vec::index]: forward function -/
def Vec.index {T I Output : Type} (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (self : Vec T) (i : I) : Result Output :=
  inst.index i self

/- [alloc::vec::Vec::index_mut]: forward function -/
def Vec.index_mut {T I Output : Type} (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (self : Vec T) (i : I) :
  Result (Output × (Output → Vec T)) :=
  inst.index_mut i self

/- Trait implementation: [alloc::vec::Vec] -/
@[reducible]
def Vec.IndexInst {T I Output : Type}
  (inst : core.slice.index.SliceIndex I (Slice T) Output) :
  core.ops.index.Index (alloc.vec.Vec T) I Output := {
  index := Vec.index inst
}

/- Trait implementation: [alloc::vec::Vec] -/
@[reducible]
def Vec.IndexMutInst {T I Output : Type}
  (inst : core.slice.index.SliceIndex I (Slice T) Output) :
  core.ops.index.IndexMut (alloc.vec.Vec T) I Output := {
  indexInst := Vec.IndexInst inst
  index_mut := Vec.index_mut inst
}

@[simp, progress_simps]
theorem Vec.index_slice_index {α : Type} (v : Vec α) (i : Usize) :
  Vec.index (core.slice.index.SliceIndexUsizeSliceInst α) v i =
  Vec.index_usize v i := by
  simp [Vec.index, Vec.index_usize, Slice.index_usize]
  rfl

@[simp, progress_simps]
theorem Vec.index_mut_slice_index {α : Type} (v : Vec α) (i : Usize) :
  Vec.index_mut (core.slice.index.SliceIndexUsizeSliceInst α) v i =
  index_mut_usize v i := by
  simp only [index_mut, core.slice.index.Usize.index_mut, Slice.index_mut_usize, Bind.bind, bind,
    Slice.index_usize, Slice.getElem?_Usize_eq, index_mut_usize, index_usize, getElem?_Nat_eq]
  cases h:(↑v)[↑i]? <;> simp only [FResult.ok.injEq, Prod.mk.injEq, true_and]; rfl

end alloc.vec

/-- [alloc::slice::{@Slice<T>}::to_vec] -/
def alloc.slice.Slice.to_vec
  {T : Type} (cloneInst : core.clone.Clone T) (s : Slice T) : Result (alloc.vec.Vec T) := do
  Slice.clone cloneInst.clone s

@[progress]
theorem alloc.slice.Slice.to_vec_spec {T : Type} (cloneInst : core.clone.Clone T) (s : Slice T)
  (h : ∀ x ∈ s.val, cloneInst.clone x = ok x) :
  alloc.slice.Slice.to_vec cloneInst s = ok s := by
  simp only [to_vec]
  rw [Slice.clone_spec h]

/- [alloc::vec::from_elem]:
   Source: '/rustc/library/alloc/src/vec/mod.rs', lines 3174:0-3174:55
   Name pattern: [alloc::vec::from_elem] -/
def alloc.vec.from_elem
  {T : Type} (cloneInst : core.clone.Clone T)
  (x : T) (n : Usize) : Result (alloc.vec.Vec T) := do
  let l ← List.clone cloneInst.clone (List.replicate n.val x)
  ok ⟨ l.val, by have := l.property; scalar_tac ⟩

@[progress]
theorem alloc.vec.from_elem_spec {T : Type} (cloneInst : core.clone.Clone T)
  (x : T) (n : Usize) (h : cloneInst.clone x = ok x) :
  ∃ v, alloc.vec.from_elem cloneInst x n = ok v ∧
  v.val = List.replicate n.val x ∧
  v.length = n.val := by
  unfold from_elem
  have ⟨ l, h ⟩ := @List.clone_spec _ cloneInst.clone (List.replicate n.val x) (by intros; simp_all)
  simp [h]

/-- [core::slice::{@Slice<T>}::reverse] -/
def core.slice.Slice.reverse {T : Type} (s : Slice T) : Slice T :=
  ⟨ s.val.reverse, by scalar_tac ⟩

def alloc.vec.Vec.with_capacity (T : Type) (_ : Usize) : alloc.vec.Vec T := Vec.new T

/- [alloc::vec::{alloc::vec::Vec<T, A>}::extend_from_slice] -/
def alloc.vec.Vec.extend_from_slice {T : Type} (cloneInst : core.clone.Clone T)
  (v : alloc.vec.Vec T) (s : Slice T) : Result (alloc.vec.Vec T) :=
  if h : v.length + s.length ≤ Usize.max then do
    match h' : Slice.clone cloneInst.clone s with
    | .ok s' =>
      .ok ⟨ v.val ++ s'.val , by have := Slice.clone_length h'; scalar_tac ⟩
    | .fail e => fail e
    | .div => div
    | .brk e => .brk e
  else fail .panic

/- [alloc::vec::{(core::ops::deref::Deref for alloc::vec::Vec<T, A>)#9}::deref]:
   Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/alloc/src/vec/mod.rs', lines 2624:4-2624:27
   Name pattern: alloc::vec::{core::ops::deref::Deref<alloc::vec::Vec<@T, @A>>}::deref -/
def alloc.vec.Vec.deref {T : Type} (v : alloc.vec.Vec T) : Slice T :=
  ⟨ v.val, v.property ⟩

@[reducible]
def core.ops.deref.DerefVec {T : Type} : core.ops.deref.Deref (alloc.vec.Vec T) (Slice T) := {
  deref := fun v => ok (alloc.vec.Vec.deref v)
}

/- [alloc::vec::{(core::ops::deref::DerefMut for alloc::vec::Vec<T, A>)#10}::deref_mut]:
   Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/alloc/src/vec/mod.rs', lines 2632:4-2632:39
   Name pattern: alloc::vec::{core::ops::deref::DerefMut<alloc::vec::Vec<@T, @A>>}::deref_mut -/
def alloc.vec.Vec.deref_mut {T : Type} (v :  alloc.vec.Vec T) :
   (Slice T) × (Slice T → alloc.vec.Vec T) :=
   (⟨ v.val, v.property ⟩, λ s => ⟨ s.val, s.property ⟩)

/- Trait implementation: [alloc::vec::{(core::ops::deref::DerefMut for alloc::vec::Vec<T, A>)#10}]
   Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/alloc/src/vec/mod.rs', lines 2630:0-2630:49
   Name pattern: core::ops::deref::DerefMut<alloc::vec::Vec<@Self, @>> -/
@[reducible]
def core.ops.deref.DerefMutVec {T : Type} :
  core.ops.deref.DerefMut (alloc.vec.Vec T) (Slice T):= {
  derefInst := core.ops.deref.DerefVec
  deref_mut v := ok (alloc.vec.Vec.deref_mut v)
}

def alloc.vec.Vec.resize {T : Type} (cloneInst : core.clone.Clone T)
  (v : alloc.vec.Vec T) (new_len : Usize) (value : T) : Result (alloc.vec.Vec T) := do
  if new_len.val < v.length then
    ok ⟨ v.val.resize new_len value, by scalar_tac ⟩
  else
    let value ← cloneInst.clone value
    ok ⟨ v.val.resize new_len value, by scalar_tac ⟩

@[progress]
theorem alloc.vec.Vec.resize_spec {T} (cloneInst : core.clone.Clone T)
  (v : alloc.vec.Vec T) (new_len : Usize) (value : T)
  (hClone : cloneInst.clone value = ok value) :
  ∃ nv, alloc.vec.Vec.resize cloneInst v new_len value = ok nv ∧
    nv.val = v.val.resize new_len value := by
  rw [resize]
  split
  . simp
  . simp [*]

@[simp, scalar_tac_simps]
theorem alloc.vec.Vec.set_getElem!_eq α [Inhabited α] (x : alloc.vec.Vec α) (i : Usize) :
  x.set i x[i]! = x := by
  simp only [getElem!_Usize_eq]
  simp only [Vec, set_val_eq, Subtype.eq_iff, List.set_getElem!]

/- [alloc::vec::{core::convert::From<alloc::vec::Vec<T, A>> for alloc::boxed::Box<@Slice<T>>}::from]:
   Source: '/rustc/library/alloc/src/vec/mod.rs', lines 3967:4-3967:33
   Name pattern: [alloc::vec::{core::convert::From<Box<[@T]>, alloc::vec::Vec<@T, @A>>}::from] -/
def alloc.vec.FromBoxSliceVec.from {T : Type} (v : alloc.vec.Vec T) : Result (Slice T) := ok v

@[progress]
theorem alloc.vec.FromBoxSliceVec.from_spec {T : Type} (v : alloc.vec.Vec T) :
  ∃ s, alloc.vec.FromBoxSliceVec.from v = ok s ∧ s.length = v.length ∧ s.val = v.val := by
  simp [alloc.vec.FromBoxSliceVec.from]

/- Trait implementation: [alloc::vec::{core::convert::From<alloc::vec::Vec<T, A>> for alloc::boxed::Box<@Slice<T>>}#39]
   Source: '/rustc/library/alloc/src/vec/mod.rs', lines 3945:0-3945:53
   Name pattern: [core::convert::From<Box<[@T]>, alloc::vec::Vec<@T, @A>>] -/
@[reducible]
def core.convert.FromBoxSliceVec (T : Type) :
  core.convert.From (Slice T) (alloc.vec.Vec T) := {
  from_ := alloc.vec.FromBoxSliceVec.from
}

def alloc.vec.Vec.setSlice! {α : Type u} (s : alloc.vec.Vec α) (i : ℕ) (s' : List α) : alloc.vec.Vec α :=
  ⟨s.val.setSlice! i s', by scalar_tac⟩

@[simp_lists_simps]
theorem alloc.vec.Vec.setSlice!_getElem!_prefix {α} [Inhabited α]
  (s : alloc.vec.Vec α) (s' : List α) (i j : ℕ) (h : j < i) :
  (s.setSlice! i s')[j]! = s[j]! := by
  simp only [Vec.setSlice!, Vec.getElem!_Nat_eq]
  simp_lists

@[simp_lists_simps]
theorem alloc.vec.Vec.setSlice!_getElem!_middle {α} [Inhabited α]
  (s : alloc.vec.Vec α) (s' : List α) (i j : ℕ) (h : i ≤ j ∧ j - i < s'.length ∧ j < s.length) :
  (s.setSlice! i s')[j]! = s'[j - i]! := by
  simp only [Vec.setSlice!, Vec.getElem!_Nat_eq]
  simp_lists

theorem alloc.vec.Vec.setSlice!_getElem!_suffix {α} [Inhabited α]
  (s : alloc.vec.Vec α) (s' : List α) (i j : ℕ) (h : i + s'.length ≤ j) :
  (s.setSlice! i s')[j]! = s[j]! := by
  simp only [Vec.setSlice!, Vec.getElem!_Nat_eq]
  simp_lists


namespace Tests
  example
    (α : Type)
    (slots : alloc.vec.Vec (List α))
    (n : Usize)
    (_ : ∀ i < slots.length, slots.val[i]! = .nil)
    (Hlen : (↑slots.len : ℕ) + (↑n : ℕ) ≤ Usize.max)
    (_ : 0 < (↑n : ℕ))
    (slots1 : alloc.vec.Vec (List α))
    (hEq : (↑slots1 : List (List α)) = (↑slots : List (List α)) ++ [.nil])
    (n1 : Usize)
    (_ : (↑n : ℕ) = (↑n1 : ℕ) + 1)
    (_ : ∀ i < slots1.length, slots.val[i]! = .nil) :
    (↑slots1.len : ℕ) + (↑n1 : ℕ) ≤ Usize.max
    := by
    scalar_tac

  example
    (α : Type)
    (capacity : Usize)
    (dividend divisor : Usize)
    (Hfactor : 0 < (↑dividend : ℕ) ∧
    (↑dividend : ℕ) < (↑divisor : ℕ) ∧
      (↑capacity : ℕ) * (↑dividend : ℕ) ≤ Usize.max ∧
        (↑capacity : ℕ) * (↑dividend : ℕ) ≥ (↑divisor : ℕ))
    (slots : alloc.vec.Vec (List α))
    (h2 : (↑slots.len : ℕ) = (↑(alloc.vec.Vec.new (List α)).len : ℕ) + (↑capacity : ℕ)) :
    (↑(↑divisor : ℕ) : ℤ) ≤
    (↑(↑slots : List (List α)).length : ℤ) * (↑(↑dividend : ℕ) : ℤ)
    := by
    scalar_tac

  example
    (v : alloc.vec.Vec U32)
    (i : Usize)
    (x : U32)
    (i1 : Usize)
    (h : (↑i : ℕ) < v.val.length)
    (_ : x = v[i]!)
    (_ : (↑i1 : ℕ) = (↑i : ℕ) + 1) :
    (↑i : ℕ) + 1 ≤ v.val.length
    := by
    scalar_tac

  attribute [-simp] List.getElem!_eq_getElem?_getD
  example
    (α : Type)
    (slots : alloc.vec.Vec (List α))
    (Hslots : ∀ i < slots.length, slots[i]! = [])
    (slots1 : alloc.vec.Vec (List α))
    (_ : (↑slots1 : List (List α)) = (↑slots : List (List α)) ++ [[]])
    (i : ℕ)
    (hi : i < slots.length) :
    (↑slots : List (List α))[i]! = []
    := by
    simp_lists [*]

end Tests

end Std

end Aeneas
