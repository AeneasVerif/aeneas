module

public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

namespace Aeneas.SLPoC

/-!
# Partial commutative monoids

Two flavours are needed.

* `PartialCommMonoid` is a *class*: it equips a type that already has `∅` and
  `∪` with a compatibility relation and the monoid laws.  The heap of
  `Aeneas.SLPoC.Heap` is its only instance.
* `PCM` is a *structure*: a partial commutative monoid carried as data, the way
  `FStar.PCM` is in F\*.  A heap cell stores one of these together with a value
  of its carrier, and a reference is indexed by it, so it has to be a value and
  not a class instance.

The second flavour is what lets a single allocation be split into disjoint
structural fragments — non-overlapping ranges of an array, for instance —
because two heaps may then own *fragments* of the same cell and compose them.
-/

/-- A partial commutative monoid (PCM), represented by a total union operation
whose meaningful inputs are selected by `Compatible`. -/
class PartialCommMonoid (α : Type u) [EmptyCollection α] [Union α] where
  Compatible : α → α → Prop
  compatible_comm {a b : α} : Compatible a b → Compatible b a
  compatible_empty_left (a : α) : Compatible ∅ a
  compatible_assoc (a b c : α) :
    Compatible a b ∧ Compatible (a ∪ b) c ↔
      Compatible b c ∧ Compatible a (b ∪ c)
  union_assoc {a b c : α} :
    Compatible a b → Compatible (a ∪ b) c →
      a ∪ b ∪ c = a ∪ (b ∪ c)
  empty_union (a : α) : ∅ ∪ a = a
  union_empty (a : α) : a ∪ ∅ = a
  union_comm_of_compatible {a b : α} :
    Compatible a b → a ∪ b = b ∪ a

/-! ## Partial commutative monoids as data

`op` is total: like `PartialCommMonoid.union` its value outside `Composable` is
irrelevant.  `isOne` is a *decision procedure* for being the unit; a PCM is
stored in a heap cell whose carrier is an arbitrary Lean type, so nothing about
it would be decidable otherwise, and the heap needs this one test to say how
many of its cells still own something. -/

/-- A partial commutative monoid carried as data, in the style of `FStar.PCM`.
-/
structure PCM (α : Type) where
  /-- The values that may be composed. -/
  Composable : α → α → Prop
  /-- The composition; its value outside `Composable` is irrelevant. -/
  op : α → α → α
  /-- The unit: owning it is owning nothing. -/
  one : α
  /-- Decides `· = one`. -/
  isOne : α → Bool
  composable_comm : ∀ {x y : α}, Composable x y → Composable y x
  op_comm : ∀ {x y : α}, Composable x y → op x y = op y x
  composable_one : ∀ x : α, Composable x one
  op_one : ∀ x : α, op x one = x
  assoc_left : ∀ {x y z : α}, Composable y z → Composable x (op y z) →
    Composable x y ∧ Composable (op x y) z ∧ op x (op y z) = op (op x y) z
  assoc_right : ∀ {x y z : α}, Composable x y → Composable (op x y) z →
    Composable y z ∧ Composable x (op y z) ∧ op x (op y z) = op (op x y) z
  isOne_iff : ∀ x : α, isOne x = true ↔ x = one

namespace PCM

variable {α : Type} (p : PCM α)

theorem one_composable (x : α) : p.Composable p.one x :=
  p.composable_comm (p.composable_one x)

theorem one_op (x : α) : p.op p.one x = x := by
  rw [p.op_comm (p.one_composable x), p.op_one]

@[simp]
theorem isOne_one : p.isOne p.one = true :=
  (p.isOne_iff p.one).mpr rfl

/-- `x` is a fragment of `v`: some frame completes it into `v`.  This is the
`compatible` of `FStar.PCM`, and what a points-to assertion claims of the value
a cell actually holds. -/
def Compatible (x v : α) : Prop :=
  ∃ frame, p.Composable x frame ∧ p.op x frame = v

variable {p}

theorem Compatible.refl (x : α) : p.Compatible x x :=
  ⟨p.one, p.composable_one x, p.op_one x⟩

theorem Compatible.one (v : α) : p.Compatible p.one v :=
  ⟨v, p.one_composable v, p.one_op v⟩

/-- Fragments of a fragment are fragments. -/
theorem Compatible.trans {x y v : α} (hxy : p.Compatible x y)
    (hyv : p.Compatible y v) : p.Compatible x v := by
  obtain ⟨f₁, hComposable₁, rfl⟩ := hxy
  obtain ⟨f₂, hComposable₂, rfl⟩ := hyv
  obtain ⟨hComposable, hComposable', hEq⟩ :=
    p.assoc_right hComposable₁ hComposable₂
  exact ⟨p.op f₁ f₂, hComposable', hEq⟩

/-- Fragments of composable values are themselves composable: this is what
makes a points-to assertion exclusive when its PCM says so. -/
theorem Compatible.composable {x y u v : α} (hx : p.Compatible x u)
    (hy : p.Compatible y v) (hComposable : p.Composable u v) :
    p.Composable x y := by
  obtain ⟨f, hxf, rfl⟩ := hx
  obtain ⟨g, hyg, rfl⟩ := hy
  obtain ⟨hfyg, hxw, -⟩ := p.assoc_right hxf hComposable
  obtain ⟨-, hygf, hEq⟩ := p.assoc_right hyg (p.composable_comm hfyg)
  rw [p.op_comm hfyg, ← hEq] at hxw
  exact (p.assoc_left hygf hxw).1

/-- Composing on the left of a fragment keeps it a fragment. -/
theorem Compatible.op_left {x y v : α} (hComposable : p.Composable x y)
    (hCompatible : p.Compatible (p.op x y) v) : p.Compatible x v :=
  Compatible.trans ⟨y, hComposable, rfl⟩ hCompatible

variable (p)

/-- `x` owns its whole cell: no frame beyond the unit composes with it.  This is
what deallocation requires, and what makes a points-to assertion exclusive. -/
def Exclusive (x : α) : Prop :=
  ∀ frame, p.Composable x frame → frame = p.one

variable {p}

/-- An exclusive fragment *is* the value of its cell. -/
theorem Exclusive.eq_of_compatible {x v : α} (hExclusive : p.Exclusive x)
    (hCompatible : p.Compatible x v) : v = x := by
  obtain ⟨frame, hComposable, rfl⟩ := hCompatible
  rw [hExclusive frame hComposable, p.op_one]

/-- A frame-preserving update: `f` rewrites the value of a cell whose owner
holds a fragment satisfying `Owns`, and every frame survives unchanged.  This is
`FStar.PCM.frame_preserving_upd`, phrased on the update of the whole cell so
that the frame rule falls out of `op`. -/
structure FramePreserving (p : PCM α) (Owns : α → Prop) (f : α → α) : Prop where
  /-- The result still composes with every frame the argument composed with. -/
  composable : ∀ {a b : α}, Owns a → p.Composable a b → p.Composable (f a) b
  /-- Updating the whole cell updates the owned part and leaves the frame. -/
  op : ∀ {a b : α}, Owns a → p.Composable a b → f (p.op a b) = p.op (f a) b

end PCM

/-! ## The exclusive PCM

The building block every array cell uses: a fragment either owns a cell
outright or owns nothing at all. -/

/-- Exclusive ownership of a value: `unowned` is the unit. -/
inductive Exclusive (α : Type) where
  | unowned
  | owned (value : α)
  deriving DecidableEq, Inhabited

namespace Exclusive

variable {α : Type}

/-- Whether this fragment owns anything. -/
def isOwned : Exclusive α → Bool
  | .unowned => false
  | .owned _ => true

/-- `Prop`-valued `isOwned`, usable as the guard of a heap operation: it
reduces to `True` or `False` on a constructor, so a dependent match on the
fragment computes. -/
def IsOwned : Exclusive α → Prop
  | .unowned => False
  | .owned _ => True

@[simp]
theorem isOwned_unowned : (Exclusive.unowned : Exclusive α).isOwned = false := rfl

@[simp]
theorem isOwned_owned (value : α) : (Exclusive.owned value).isOwned = true := rfl

theorem isOwned_eq_true_iff {e : Exclusive α} :
    e.isOwned = true ↔ e.IsOwned := by
  cases e <;> simp [isOwned, IsOwned]

/-- The owned value.  No default is invented: the caller supplies the proof that
there is one, and the match on it computes. -/
def get : (e : Exclusive α) → e.IsOwned → α
  | .owned value, _ => value

@[simp]
theorem get_owned (value : α) (hOwned : (Exclusive.owned value).IsOwned) :
    (Exclusive.owned value).get hOwned = value := rfl

def Composable : Exclusive α → Exclusive α → Prop
  | .owned _, .owned _ => False
  | _, _ => True

def op : Exclusive α → Exclusive α → Exclusive α
  | .unowned, y => y
  | .owned value, _ => .owned value

@[simp] theorem op_unowned_left (y : Exclusive α) :
    Exclusive.op .unowned y = y := rfl

@[simp] theorem op_owned_left (value : α) (y : Exclusive α) :
    Exclusive.op (.owned value) y = .owned value := rfl

theorem op_unowned_right (x : Exclusive α) : Exclusive.op x .unowned = x := by
  cases x <;> rfl

theorem isOwned_op (x y : Exclusive α) :
    (Exclusive.op x y).isOwned = (x.isOwned || y.isOwned) := by
  cases x <;> cases y <;> rfl

theorem composable_comm {x y : Exclusive α} (hComposable : Composable x y) :
    Composable y x := by
  cases x <;> cases y <;> simp_all [Composable]

theorem op_comm {x y : Exclusive α} (hComposable : Composable x y) :
    op x y = op y x := by
  cases x <;> cases y <;> simp_all [Composable, op]

theorem composable_unowned (x : Exclusive α) : Composable x .unowned := by
  cases x <;> trivial

/-- Exclusivity: a frame composing with an owned fragment owns nothing. -/
theorem eq_unowned_of_composable {x y : Exclusive α} (hComposable : Composable x y)
    (hOwned : x.IsOwned) : y = .unowned := by
  cases x <;> cases y <;> simp_all [Composable, IsOwned]

end Exclusive

/-! ## Initialization

A freshly allocated slot is owned but holds no value yet; writing to it makes
it readable. -/

/-- Whether an allocated slot has been written. -/
inductive InitState (α : Type) where
  | uninitialized
  | initialized (value : α)
  deriving Inhabited

namespace InitState

variable {α : Type}

/-- `Prop`-valued initialization test, usable as the guard of a read. -/
def IsInitialized : InitState α → Prop
  | .uninitialized => False
  | .initialized _ => True

/-- The value written to the slot; the guard makes the match compute. -/
def get : (s : InitState α) → s.IsInitialized → α
  | .initialized value, _ => value

@[simp]
theorem get_initialized (value : α) (hInit : (InitState.initialized value).IsInitialized) :
    (InitState.initialized value).get hInit = value := rfl

end InitState

namespace Exclusive

variable {α : Type}

/-- The guard of a read through a fragment: the slot is owned *and* written. -/
def IsInit : Exclusive (InitState α) → Prop
  | .owned state => state.IsInitialized
  | .unowned => False

/-- The value read through an owned, initialized fragment. -/
def getInit : (e : Exclusive (InitState α)) → e.IsInit → α
  | .owned state, hInit => state.get hInit

@[simp]
theorem getInit_owned (value : α)
    (hInit : (Exclusive.owned (InitState.initialized value)).IsInit) :
    (Exclusive.owned (InitState.initialized value)).getInit hInit = value := rfl

/-- Reading an owned, initialized fragment returns the value it was given. -/
theorem getInit_eq : ∀ (e : Exclusive (InitState α)) (hInit : e.IsInit)
    (value : α), e = .owned (.initialized value) → e.getInit hInit = value := by
  rintro e hInit value rfl
  rfl

theorem isOwned_of_isInit {e : Exclusive (InitState α)} (hInit : e.IsInit) :
    e.IsOwned := by
  cases e with
  | unowned => exact hInit.elim
  | owned state => trivial

end Exclusive

/-! ## Fragments of an allocation

The carrier of the PCM an allocation is made with: a map from indices to
exclusive fragments, finitely supported so that owning nothing is decidable —
which is what `PCM.isOne` needs. -/

/-- A finitely supported map from indices to exclusive fragments: the pointwise
lifting of the exclusive PCM. -/
structure Frags (α : Type) where
  /-- The fragment owned at each index. -/
  get : Nat → Exclusive α
  /-- The indices this fragment owns. -/
  support : Finset Nat
  mem_support : ∀ i, i ∈ support ↔ (get i).isOwned = true

namespace Frags

variable {α : Type}

@[ext]
theorem ext {x y : Frags α} (hGet : ∀ i, x.get i = y.get i) : x = y := by
  obtain ⟨getX, supportX, hX⟩ := x
  obtain ⟨getY, supportY, hY⟩ := y
  have hEq : getX = getY := funext hGet
  subst hEq
  have : supportX = supportY := by
    apply Finset.ext
    intro i
    rw [hX i, hY i]
  subst this
  rfl

/-- Owning nothing. -/
def one : Frags α where
  get _ := .unowned
  support := ∅
  mem_support := by simp [Exclusive.isOwned]

@[simp] theorem get_one (i : Nat) : (Frags.one : Frags α).get i = .unowned := rfl

@[simp] theorem support_one : (Frags.one : Frags α).support = ∅ := rfl

def Composable (x y : Frags α) : Prop :=
  ∀ i, Exclusive.Composable (x.get i) (y.get i)

def op (x y : Frags α) : Frags α where
  get i := Exclusive.op (x.get i) (y.get i)
  support := x.support ∪ y.support
  mem_support := by
    intro i
    simp only [Finset.mem_union, x.mem_support i, y.mem_support i,
      Exclusive.isOwned_op, Bool.or_eq_true]

@[simp]
theorem get_op (x y : Frags α) (i : Nat) :
    (Frags.op x y).get i = Exclusive.op (x.get i) (y.get i) := rfl

/-- Owning nothing is decidable: the support is empty. -/
def isOne (x : Frags α) : Bool := x.support = ∅

theorem isOne_iff (x : Frags α) : x.isOne = true ↔ x = Frags.one := by
  constructor
  · intro hEmpty
    have hSupport : x.support = ∅ := by
      simpa [isOne] using hEmpty
    apply Frags.ext
    intro i
    have hNotMem : i ∉ x.support := by simp [hSupport]
    have := x.mem_support i
    cases hGet : x.get i with
    | unowned => rfl
    | owned value =>
        exact absurd (this.mpr (by simp [hGet])) hNotMem
  · rintro rfl
    simp [isOne]

theorem composable_comm {x y : Frags α} (hComposable : Composable x y) :
    Composable y x :=
  fun i => Exclusive.composable_comm (hComposable i)

theorem op_comm {x y : Frags α} (hComposable : Composable x y) :
    op x y = op y x :=
  Frags.ext fun i => Exclusive.op_comm (hComposable i)

theorem composable_one (x : Frags α) : Composable x Frags.one :=
  fun _ => Exclusive.composable_unowned _

theorem op_one (x : Frags α) : op x Frags.one = x :=
  Frags.ext fun _ => Exclusive.op_unowned_right _

/-! ### Ranges

The fragment an array range owns: `ofList lo values` owns exactly the indices
`[lo, lo + values.length)`, holding `values` there. -/

def ofList (lo : Nat) (values : List α) : Frags α where
  get i :=
    if hMem : lo ≤ i ∧ i - lo < values.length then .owned (values[i - lo]'hMem.2)
    else .unowned
  support := (Finset.range values.length).image (lo + ·)
  mem_support := by
    intro i
    simp only [Finset.mem_image, Finset.mem_range]
    by_cases hMem : lo ≤ i ∧ i - lo < values.length
    · simp only [dif_pos hMem, Exclusive.isOwned_owned, iff_true]
      exact ⟨i - lo, hMem.2, by omega⟩
    · simp only [dif_neg hMem, Exclusive.isOwned_unowned, Bool.false_eq_true,
        iff_false]
      rintro ⟨k, hk, rfl⟩
      exact hMem ⟨by omega, by omega⟩

theorem get_ofList_of_mem {lo i : Nat} {values : List α}
    (hMem : lo ≤ i ∧ i - lo < values.length) :
    (ofList lo values).get i = .owned (values[i - lo]'hMem.2) :=
  dif_pos hMem

theorem get_ofList_of_not_mem {lo i : Nat} {values : List α}
    (hMem : ¬ (lo ≤ i ∧ i - lo < values.length)) :
    (ofList lo values).get i = .unowned :=
  dif_neg hMem

@[simp]
theorem ofList_nil (lo : Nat) : ofList lo ([] : List α) = Frags.one :=
  Frags.ext fun i => get_ofList_of_not_mem (by simp)

theorem isOwned_ofList {lo i : Nat} {values : List α}
    (hMem : lo ≤ i ∧ i - lo < values.length) :
    ((ofList lo values).get i).IsOwned := by
  rw [get_ofList_of_mem hMem]; trivial

/-- Splitting and joining a range: the two halves own disjoint indices. -/
theorem composable_ofList_append (lo : Nat) (xs ys : List α) :
    Composable (ofList lo xs) (ofList (lo + xs.length) ys) := by
  intro i
  by_cases hx : lo ≤ i ∧ i - lo < xs.length
  · rw [get_ofList_of_mem hx, get_ofList_of_not_mem (by omega)]
    trivial
  · rw [get_ofList_of_not_mem hx]
    trivial

theorem op_ofList_append (lo : Nat) (xs ys : List α) :
    op (ofList lo xs) (ofList (lo + xs.length) ys) = ofList lo (xs ++ ys) := by
  apply Frags.ext
  intro i
  rw [get_op]
  by_cases hx : lo ≤ i ∧ i - lo < xs.length
  · rw [get_ofList_of_mem hx, get_ofList_of_not_mem (by omega),
      get_ofList_of_mem (values := xs ++ ys) (by simp; omega),
      Exclusive.op_owned_left]
    congr 1
    exact (List.getElem_append_left (bs := ys) hx.2).symm
  · by_cases hy : lo + xs.length ≤ i ∧ i - (lo + xs.length) < ys.length
    · rw [get_ofList_of_not_mem hx, get_ofList_of_mem hy,
        get_ofList_of_mem (values := xs ++ ys) (by simp; omega),
        Exclusive.op_unowned_left]
      congr 1
      rw [List.getElem_append_right (by omega)]
      congr 1
      omega
    · rw [get_ofList_of_not_mem hx, get_ofList_of_not_mem hy,
        get_ofList_of_not_mem (values := xs ++ ys) (by simp; omega)]
      rfl

/-! ### Updates -/

/-- Overwrite the fragment at one index. -/
def set (i : Nat) (e : Exclusive α) (x : Frags α) : Frags α where
  get j := if j = i then e else x.get j
  support := if e.isOwned = true then Insert.insert i x.support else x.support.erase i
  mem_support := by
    intro j
    by_cases hj : j = i
    · subst hj
      cases he : e.isOwned <;> simp [he]
    · cases he : e.isOwned <;> simp [hj, x.mem_support j]

@[simp]
theorem get_set (i : Nat) (e : Exclusive α) (x : Frags α) (j : Nat) :
    (set i e x).get j = if j = i then e else x.get j := rfl

/-- Release the fragments on `[lo, lo + n)`: this is what deallocation does. -/
def release (lo n : Nat) (x : Frags α) : Frags α where
  get j := if lo ≤ j ∧ j < lo + n then .unowned else x.get j
  support := x.support.filter fun j => ¬ (lo ≤ j ∧ j < lo + n)
  mem_support := by
    intro j
    rw [Finset.mem_filter, x.mem_support j]
    by_cases hj : lo ≤ j ∧ j < lo + n
    · rw [if_pos hj]; simp [hj]
    · rw [if_neg hj]; simp [hj]

@[simp]
theorem get_release (lo n : Nat) (x : Frags α) (j : Nat) :
    (release lo n x).get j =
      if lo ≤ j ∧ j < lo + n then .unowned else x.get j := rfl

theorem release_ofList (lo : Nat) (values : List α) :
    release lo values.length (ofList lo values) = Frags.one := by
  apply Frags.ext
  intro j
  rw [get_release]
  by_cases hj : lo ≤ j ∧ j < lo + values.length
  · rw [if_pos hj]; rfl
  · rw [if_neg hj, get_ofList_of_not_mem (by omega)]; rfl

end Frags

/-- The PCM an allocation is made with: pointwise exclusive ownership of its
indices. -/
def PCM.frags (α : Type) : PCM (Frags α) where
  Composable := Frags.Composable
  op := Frags.op
  one := Frags.one
  isOne := Frags.isOne
  composable_comm := Frags.composable_comm
  op_comm := Frags.op_comm
  composable_one := Frags.composable_one
  op_one := Frags.op_one
  assoc_left := by
    intro x y z hComposableYZ hComposable
    refine ⟨fun i => ?_, fun i => ?_, Frags.ext fun i => ?_⟩ <;>
      · have h₁ := hComposableYZ i
        have h₂ := hComposable i
        cases hx : x.get i <;> cases hy : y.get i <;> cases hz : z.get i <;>
          simp_all [Exclusive.Composable, Exclusive.op]
  assoc_right := by
    intro x y z hComposableXY hComposable
    refine ⟨fun i => ?_, fun i => ?_, Frags.ext fun i => ?_⟩ <;>
      · have h₁ := hComposableXY i
        have h₂ := hComposable i
        cases hx : x.get i <;> cases hy : y.get i <;> cases hz : z.get i <;>
          simp_all [Exclusive.Composable, Exclusive.op]
  isOne_iff := Frags.isOne_iff

namespace Frags

variable {α : Type}

/-- What is stored where a fragment owns: exactly what the fragment owns. -/
theorem compatible_get {x v : Frags α}
    (hCompatible : (PCM.frags α).Compatible x v) {j : Nat}
    (hOwned : (x.get j).IsOwned) : v.get j = x.get j := by
  obtain ⟨frame, hComposable, rfl⟩ := hCompatible
  show (Frags.op x frame).get j = x.get j
  rw [get_op, Exclusive.eq_unowned_of_composable (hComposable j) hOwned,
    Exclusive.op_unowned_right]

/-- Writing one index is frame preserving as soon as that index is owned. -/
theorem framePreserving_set (i : Nat) (value : α) :
    (PCM.frags α).FramePreserving (fun x => (x.get i).IsOwned)
      (Frags.set i (.owned value)) where
  composable := by
    intro a b hOwns hComposable
    show Frags.Composable _ _
    intro j
    by_cases hj : j = i
    · subst hj
      rw [get_set, if_pos rfl,
        Exclusive.eq_unowned_of_composable (hComposable j) hOwns]
      exact Exclusive.composable_unowned _
    · rw [get_set, if_neg hj]
      exact hComposable j
  op := by
    intro a b hOwns hComposable
    show Frags.set i (.owned value) (Frags.op a b)
      = Frags.op (Frags.set i (.owned value) a) b
    apply Frags.ext
    intro j
    by_cases hj : j = i
    · subst hj
      rw [get_set, if_pos rfl, get_op, get_set, if_pos rfl,
        Exclusive.eq_unowned_of_composable (hComposable j) hOwns,
        Exclusive.op_unowned_right]
    · rw [get_set, if_neg hj, get_op, get_op, get_set, if_neg hj]

/-- Releasing a range is frame preserving as soon as that range is owned. -/
theorem framePreserving_release (lo n : Nat) :
    (PCM.frags α).FramePreserving
      (fun x => ∀ j, lo ≤ j → j < lo + n → (x.get j).IsOwned)
      (Frags.release lo n) where
  composable := by
    intro a b hOwns hComposable
    show Frags.Composable _ _
    intro j
    by_cases hj : lo ≤ j ∧ j < lo + n
    · rw [get_release, if_pos hj]
      trivial
    · rw [get_release, if_neg hj]
      exact hComposable j
  op := by
    intro a b hOwns hComposable
    show Frags.release lo n (Frags.op a b) = Frags.op (Frags.release lo n a) b
    apply Frags.ext
    intro j
    by_cases hj : lo ≤ j ∧ j < lo + n
    · rw [get_release, if_pos hj, get_op, get_release, if_pos hj,
        Exclusive.eq_unowned_of_composable (hComposable j) (hOwns j hj.1 hj.2),
        Exclusive.op_unowned_left]
    · rw [get_release, if_neg hj, get_op, get_op, get_release, if_neg hj]

end Frags

end Aeneas.SLPoC
