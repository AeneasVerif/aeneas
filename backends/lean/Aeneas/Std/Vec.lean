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

open Result Error WP

namespace alloc.vec

@[rust_type "alloc::vec::Vec"]
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

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::new" -canFail -lift]
abbrev Vec.new (α : Type u): Vec α := ⟨ [], by simp ⟩

instance (α : Type u) : Inhabited (Vec α) := by
  constructor
  apply Vec.new

@[simp, rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::len" -canFail -lift (keepParams := [true,false])]
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

@[irreducible, rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::push" (keepParams := [true,false])]
def Vec.push {α : Type u} (v : Vec α) (x : α) : Result (Vec α)
  :=
  let nlen := List.length v.val + 1
  if h : nlen ≤ U32.max || nlen ≤ Usize.max then
    ok ⟨ List.concat v.val x, by simp; scalar_tac ⟩
  else
    fail maximumSizeExceeded

@[progress]
theorem Vec.push_spec {α : Type u} (v : Vec α) (x : α) (h : v.val.length < Usize.max) :
  v.push x ⦃ v1 =>
  v1.val = v.val ++ [x] ⦄ := by
  unfold push; grind

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::insert" (keepParams := [true, false])]
def Vec.insert {α : Type u} (v: Vec α) (i: Usize) (x: α) : Result (Vec α) :=
  if i.val < v.length then
    ok ⟨ v.val.set i x, by have := v.property; simp [*] ⟩
  else
    fail arrayOutOfBounds

@[progress]
theorem Vec.insert_spec {α : Type u} (v: Vec α) (i: Usize) (x: α)
  (hbound : i.val < v.length) :
  v.insert i x ⦃ nv => nv.val = v.val.set i x ⦄ := by
  simp [insert, *]

def Vec.index_usize {α : Type u} (v: Vec α) (i: Usize) : Result α :=
  match v[i.val]? with
  | none => fail .arrayOutOfBounds
  | some x => ok x

@[progress]
theorem Vec.index_usize_spec {α : Type u} [Inhabited α] (v: Vec α) (i: Usize)
  (hbound : i.val < v.length) :
  v.index_usize i ⦃ x => x = v.val[i.val]! ⦄ := by
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
  v.update i x ⦃ nv => nv = v.set i x ⦄ := by
  simp only [update, set]
  simp at *
  split <;> simp_all

@[scalar_tac_simps]
theorem Vec.set_length {α : Type u} (v: Vec α) (i: Usize) (x: α) :
  (v.set i x).length = v.length := by simp

def Vec.index_mut_usize {α : Type u} (v: Vec α) (i: Usize) :
  Result (α × (α → Vec α)) :=
  match Vec.index_usize v i with
  | ok x =>
    ok (x, Vec.set v i)
  | fail e => fail e
  | div => div

@[progress]
theorem Vec.index_mut_usize_spec {α : Type u} [Inhabited α] (v: Vec α) (i: Usize)
  (hbound : i.val < v.length) :
  v.index_mut_usize i ⦃ x y => x = v.val[i.val]! ∧ y = v.set i ⦄ := by
  simp only [index_mut_usize]
  have ⟨ x, h ⟩ := spec_imp_exists (index_usize_spec v i hbound)
  simp [h]

@[rust_fun "alloc::vec::{core::ops::index::Index<alloc::vec::Vec<@T>, @I, @O>}::index"
  (keepParams := [true,true,false, true])]
def Vec.index {T I Output : Type} (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (self : Vec T) (i : I) : Result Output :=
  inst.index i self

@[rust_fun "alloc::vec::{core::ops::index::IndexMut<alloc::vec::Vec<@T>, @I, @O>}::index_mut"
  (keepParams := [true,true,false, true])]
def Vec.index_mut {T I Output : Type} (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (self : Vec T) (i : I) :
  Result (Output × (Output → Vec T)) :=
  inst.index_mut i self

@[reducible,
  rust_trait_impl "core::ops::index::Index<alloc::vec::Vec<@T>, @T, @O>" (keepParams := [true, true, false, true])]
def Vec.Index {T I Output : Type}
  (inst : core.slice.index.SliceIndex I (Slice T) Output) :
  core.ops.index.Index (alloc.vec.Vec T) I Output := {
  index := Vec.index inst
}

@[reducible,
  rust_trait_impl "core::ops::index::IndexMut<alloc::vec::Vec<@T>, @T, @O>" (keepParams := [true, true, false, true])]
def Vec.IndexMut {T I Output : Type}
  (inst : core.slice.index.SliceIndex I (Slice T) Output) :
  core.ops.index.IndexMut (alloc.vec.Vec T) I Output := {
  indexInst := Vec.Index inst
  index_mut := Vec.index_mut inst
}

@[simp, progress_simps]
theorem Vec.index_slice_index {α : Type} (v : Vec α) (i : Usize) :
  Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i =
  Vec.index_usize v i := by
  simp [Vec.index, Vec.index_usize, Slice.index_usize]
  rfl

@[simp, progress_simps]
theorem Vec.index_mut_slice_index {α : Type} (v : Vec α) (i : Usize) :
  Vec.index_mut (core.slice.index.SliceIndexUsizeSlice α) v i =
  index_mut_usize v i := by
  simp [Vec.index_mut, Vec.index_mut_usize, Slice.index_mut_usize]
  rfl

end alloc.vec

@[rust_fun "alloc::slice::{[@T]}::to_vec"]
def alloc.slice.Slice.to_vec
  {T : Type} (cloneInst : core.clone.Clone T) (s : Slice T) : Result (alloc.vec.Vec T) := do
  Slice.clone cloneInst.clone s

@[progress]
theorem alloc.slice.Slice.to_vec_spec {T : Type} (cloneInst : core.clone.Clone T) (s : Slice T)
  (h : ∀ x ∈ s.val, cloneInst.clone x = ok x) :
  alloc.slice.Slice.to_vec cloneInst s ⦃ s' => s = s'⦄ := by
  simp only [to_vec]
  exact (Slice.clone_spec h)

@[rust_fun "alloc::slice::{[@T]}::into_vec" -canFail -lift (keepParams := [true, false])]
def alloc.slice.Slice.into_vec
  {T : Type} (s: Slice T) : (alloc.vec.Vec T) := s

@[rust_fun "alloc::vec::from_elem"]
def alloc.vec.from_elem
  {T : Type} (cloneInst : core.clone.Clone T)
  (x : T) (n : Usize) : Result (alloc.vec.Vec T) := do
  let l ← List.clone cloneInst.clone (List.replicate n.val x)
  ok ⟨ l.val, by have := l.property; scalar_tac ⟩

@[progress]
theorem alloc.vec.from_elem_spec {T : Type} (cloneInst : core.clone.Clone T)
  (x : T) (n : Usize) (h : cloneInst.clone x = ok x) :
  alloc.vec.from_elem cloneInst x n ⦃ v =>
  v.val = List.replicate n.val x ∧
  v.length = n.val ⦄ := by
  unfold from_elem
  have ⟨ l, h ⟩ := spec_imp_exists (@List.clone_spec _ cloneInst.clone (List.replicate n.val x) (by intros; simp_all))
  simp [h]

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::with_capacity" -canFail -lift]
def alloc.vec.Vec.with_capacity (T : Type) (_ : Usize) : alloc.vec.Vec T := Vec.new T

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::extend_from_slice" (keepParams := [true, false])]
def alloc.vec.Vec.extend_from_slice {T : Type} (cloneInst : core.clone.Clone T)
  (v : alloc.vec.Vec T) (s : Slice T) : Result (alloc.vec.Vec T) :=
  if h : v.length + s.length ≤ Usize.max then do
    match h' : Slice.clone cloneInst.clone s with
    | ok s' =>
      ok ⟨ v.val ++ s'.val , by have := Slice.clone_length h'; scalar_tac ⟩
    | fail e => fail e
    | div => div
  else fail .panic

@[rust_fun "alloc::vec::{core::ops::deref::Deref<alloc::vec::Vec<@T>, [@T]>}::deref"
           -canFail -lift (keepParams := [true, false])]
def alloc.vec.Vec.deref {T : Type} (v : alloc.vec.Vec T) : Slice T :=
  ⟨ v.val, v.property ⟩

@[reducible, rust_trait_impl "core::ops::deref::Deref<alloc::vec::Vec<@T>, [@T]>" (keepParams := [true, false])]
def core.ops.deref.DerefVec {T : Type} : core.ops.deref.Deref (alloc.vec.Vec T) (Slice T) := {
  deref := fun v => ok (alloc.vec.Vec.deref v)
}

@[rust_fun "alloc::vec::{core::ops::deref::DerefMut<alloc::vec::Vec<@T>, [@T]>}::deref_mut"
           -canFail (keepParams := [true, false])]
def alloc.vec.Vec.deref_mut {T : Type} (v :  alloc.vec.Vec T) :
   (Slice T) × (Slice T → alloc.vec.Vec T) :=
   (⟨ v.val, v.property ⟩, λ s => ⟨ s.val, s.property ⟩)

@[reducible, rust_trait_impl "core::ops::deref::DerefMut<alloc::vec::Vec<@T>, [@T]>" (keepParams := [true, false])]
def core.ops.deref.DerefMutVec {T : Type} :
  core.ops.deref.DerefMut (alloc.vec.Vec T) (Slice T):= {
  derefInst := core.ops.deref.DerefVec
  deref_mut v := ok (alloc.vec.Vec.deref_mut v)
}

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::resize" (keepParams := [true,false])]
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
  alloc.vec.Vec.resize cloneInst v new_len value ⦃ nv =>
    nv.val = v.val.resize new_len value ⦄ := by
  rw [resize]
  split
  . simp
  . simp [*]

@[simp, scalar_tac_simps]
theorem alloc.vec.Vec.set_getElem!_eq α [Inhabited α] (x : alloc.vec.Vec α) (i : Usize) :
  x.set i x[i]! = x := by
  simp only [getElem!_Usize_eq]
  simp only [Vec, set_val_eq, Subtype.ext_iff, List.set_getElem!]

@[rust_fun
  "alloc::vec::{core::convert::From<alloc::vec::Vec<@T>, [@T; @N]>}::from"]
def alloc.vec.FromVecArray.from
  {T : Type} {N : Std.Usize} (a: Array T N) : Result (alloc.vec.Vec T) :=
  ok ⟨ a.val, by scalar_tac ⟩

@[reducible, rust_trait_impl
  "core::convert::From<alloc::vec::Vec<@T>, [@T; @N]>"]
def core.convert.FromVecArray (T : Type) (N : Std.Usize) : core.convert.From
  (alloc.vec.Vec T) (Array T N) := {
  from_ := alloc.vec.FromVecArray.from
}

/- Source: '/rustc/library/alloc/src/vec/mod.rs', lines 3967:4-3967:33 -/
@[rust_fun "alloc::vec::{core::convert::From<Box<[@T]>, alloc::vec::Vec<@T>>}::from" (keepParams := [true,false])]
def alloc.vec.FromBoxSliceVec.from {T : Type} (v : alloc.vec.Vec T) : Result (Slice T) := ok v

@[progress]
theorem alloc.vec.FromBoxSliceVec.from_spec {T : Type} (v : alloc.vec.Vec T) :
  alloc.vec.FromBoxSliceVec.from v ⦃ s => s.length = v.length ∧ s.val = v.val⦄ := by
  simp [alloc.vec.FromBoxSliceVec.from]

@[reducible, rust_trait_impl "core::convert::From<Box<[@T]>, alloc::vec::Vec<@T>>" (keepParams := [true, false])]
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

@[rust_fun "alloc::vec::{core::clone::Clone<alloc::vec::Vec<@T>>}::clone"
    (keepParams := [true, false]) (keepTraitClauses := [true, false])]
def alloc.vec.CloneVec.clone {T : Type} (cloneInst : core.clone.Clone T)
  (v : alloc.vec.Vec T) : Result (alloc.vec.Vec T) :=
  Slice.clone cloneInst.clone v

@[reducible, rust_trait_impl "core::clone::Clone<alloc::vec::Vec<@T>>"
    (keepParams := [true, false]) (keepTraitClauses := [true, false])]
def core.clone.CloneallocvecVec {T : Type} (cloneInst : core.clone.Clone T) :
  core.clone.Clone (alloc.vec.Vec T) := {
  clone := alloc.vec.CloneVec.clone cloneInst
}

@[rust_fun
  "alloc::vec::partial_eq::{core::cmp::PartialEq<alloc::vec::Vec<@T>, alloc::vec::Vec<@U>>}::eq"
  (keepParams := [true, true, false, false])]
def alloc.vec.partial_eq.PartialEqVec.eq
  {T : Type} {U : Type} (PartialEqInst : core.cmp.PartialEq T U)
  (v0 : alloc.vec.Vec T) (v1 : alloc.vec.Vec U) : Result Bool :=
  if v0.length = v1.length then
    List.allM (fun (x0, x1) => PartialEqInst.eq x0 x1) (List.zip v0.val v1.val)
  else .ok false

@[rust_fun
  "alloc::vec::partial_eq::{core::cmp::PartialEq<alloc::vec::Vec<@T>, alloc::vec::Vec<@U>>}::ne"
  (keepParams := [true, true, false, false])]
def alloc.vec.partial_eq.PartialEqVec.ne
  {T : Type} {U : Type} (PartialEqInst : core.cmp.PartialEq T U)
  (v0 : alloc.vec.Vec T) (v1 : alloc.vec.Vec U) : Result Bool :=
  if v0.length = v1.length then
    List.anyM (fun (x0, x1) => PartialEqInst.ne x0 x1) (List.zip v0.val v1.val)
  else .ok true

@[reducible,
  rust_trait_impl
    "core::cmp::PartialEq<alloc::vec::Vec<@T>, alloc::vec::Vec<@U>>"
    (keepParams := [true, true, false, false])]
def core.cmp.PartialEqVec {T : Type} {U : Type}
 (PartialEqInst : core.cmp.PartialEq T U) :
  core.cmp.PartialEq (alloc.vec.Vec T) (alloc.vec.Vec U) := {
  eq := alloc.vec.partial_eq.PartialEqVec.eq PartialEqInst
  ne := alloc.vec.partial_eq.PartialEqVec.ne PartialEqInst
}

@[rust_fun "alloc::vec::{core::fmt::Debug<alloc::vec::Vec<@T>>}::fmt"
  (keepParams := [true, false])]
def alloc.vec.DebugVec.fmt
  {T : Type} (_DebugInst : core.fmt.Debug T) :
  alloc.vec.Vec T → core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  -- TODO: more precise model
  -- We should call the fmt function on the elements of the vector
  fun _ fmt => .ok (.Ok (), fmt)

@[reducible,
  rust_trait_impl "core::fmt::Debug<alloc::vec::Vec<@T>>" (keepParams := [true, false])]
def core.fmt.DebugVec {T : Type} (DebugInst : core.fmt.Debug
  T) : core.fmt.Debug (alloc.vec.Vec T) := {
  fmt := alloc.vec.DebugVec.fmt DebugInst
}

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
