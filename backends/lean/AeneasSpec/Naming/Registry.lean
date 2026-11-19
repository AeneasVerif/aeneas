module

public import AeneasSpec.Naming.Escape
public import Mathlib.Data.List.Induction

/-!
# Registering names

Aeneas registers the name of every definition it writes, and reports a clash when two identifiers
get the same name (cf. `names_maps_add`). How strictly a name is checked depends on the identifier
(`Strictness`). Keywords are registered first, as strict identifiers.

The check is not symmetric: a lax name (a field) is checked against the strict names registered
before it, but a strict name (a type) is not checked against the lax names registered before it.
This is harmless in Lean, where fields are qualified by their structure.

## Main statements

* `clashes_eq_nil_iff`: no clash is reported iff the names that are checked against each other are
  different.
* `nodup_denote`: if no clash is reported, the definitions that are not lax have different names in
  Lean, if no component looks quoted.
-/

@[expose] public section

namespace Aeneas.Spec.Naming

/-- How strictly the name of an identifier is checked (cf. `strict_collisions`,
`allow_collisions`). -/
inductive Strictness
  /-- Keywords and types: also checked against the lax names registered after them. -/
  | strict
  /-- Functions, globals, variants, constructors, trait declarations and impls. -/
  | normal
  /-- Fields and the items of trait declarations, which Lean finds from the type: they may share
  names with each other and with normal identifiers. -/
  | lax
  deriving DecidableEq, Repr

/-- A name registered with strictness `s` is checked against a name registered after it with
strictness `t`. -/
def Strictness.Checked : Strictness → Strictness → Prop
  | .strict, _ => True
  | .normal, t => t ≠ .lax
  | .lax, _ => False

instance : DecidableRel Strictness.Checked := fun s t => by
  cases s <;> unfold Strictness.Checked <;> infer_instance

/-- The registered names (cf. `names_maps`). -/
structure Registry (Id : Type*) where
  /-- The names that are not lax (`names_map`). -/
  names : List (Id × LeanName) := []
  /-- The strict names (`strict_names_map`). -/
  strictNames : List (Id × LeanName) := []
  /-- The lax names (`unsafe_names_map`). -/
  laxNames : List (Id × LeanName) := []
  /-- The reported clashes: an identifier already registered, the new one, and their name. -/
  clashes : List (Id × Id × LeanName) := []

variable {Id : Type*}

/-- The clashes of `n`, the name of `id`, with the names in `m`. -/
def clashesWith (m : List (Id × LeanName)) (id : Id) (n : LeanName) : List (Id × Id × LeanName) :=
  (m.filter (·.2 == n)).map fun p => (p.1, id, n)

/-- Register the name `n` of `id` (cf. `names_maps_add`). -/
def Registry.add (r : Registry Id) : Strictness → Id → LeanName → Registry Id
  | .strict, id, n =>
    { r with names := (id, n) :: r.names, strictNames := (id, n) :: r.strictNames,
             clashes := r.clashes ++ clashesWith r.strictNames id n ++ clashesWith r.names id n }
  | .normal, id, n =>
    { r with names := (id, n) :: r.names, clashes := r.clashes ++ clashesWith r.names id n }
  | .lax, id, n =>
    { r with laxNames := (id, n) :: r.laxNames,
             clashes := r.clashes ++ clashesWith r.strictNames id n }

/-- Register the names in order. -/
def register (l : List (Strictness × Id × LeanName)) : Registry Id :=
  l.foldl (fun r x => r.add x.1 x.2.1 x.2.2) {}

theorem register_append (l : List (Strictness × Id × LeanName)) (x : Strictness × Id × LeanName) :
    register (l ++ [x]) = (register l).add x.1 x.2.1 x.2.2 := by
  simp [register, List.foldl_append]

theorem mem_names {l : List (Strictness × Id × LeanName)} {p : Id × LeanName} :
    p ∈ (register l).names ↔ ∃ s, s ≠ .lax ∧ (s, p.1, p.2) ∈ l := by
  induction l using List.reverseRecOn with
  | nil => simp [register]
  | append_singleton l x ih =>
    obtain ⟨s, id, n⟩ := x
    rw [register_append]
    cases s <;> simp [Registry.add, ih] <;> aesop

theorem mem_strictNames {l : List (Strictness × Id × LeanName)} {p : Id × LeanName} :
    p ∈ (register l).strictNames ↔ (.strict, p.1, p.2) ∈ l := by
  induction l using List.reverseRecOn with
  | nil => simp [register]
  | append_singleton l x ih =>
    obtain ⟨s, id, n⟩ := x
    rw [register_append]
    cases s <;> simp [Registry.add, ih, Prod.ext_iff, or_comm]

theorem clashesWith_eq_nil {m : List (Id × LeanName)} {id : Id} {n : LeanName} :
    clashesWith m id n = [] ↔ ∀ p ∈ m, p.2 ≠ n := by
  simp [clashesWith, List.filter_eq_nil_iff]

/-- No clash is reported iff the names checked against each other are different. -/
theorem clashes_eq_nil_iff (l : List (Strictness × Id × LeanName)) :
    (register l).clashes = [] ↔ l.Pairwise fun a b => a.1.Checked b.1 → a.2.2 ≠ b.2.2 := by
  induction l using List.reverseRecOn with
  | nil => simp [register]
  | append_singleton l x ih =>
    obtain ⟨t, id, n⟩ := x
    rw [register_append, List.pairwise_append, ← ih]
    simp only [List.pairwise_singleton, List.mem_singleton, forall_eq, true_and]
    cases t <;>
      simp only [Registry.add, List.append_eq_nil_iff, clashesWith_eq_nil, Prod.forall,
        mem_names, mem_strictNames, Strictness.Checked] <;>
      aesop

/-- If no clash is reported, the names that are not lax are different. -/
theorem nodup_names {l : List (Strictness × Id × LeanName)} (h : (register l).clashes = []) :
    ((l.filter (·.1 ≠ .lax)).map (·.2.2)).Nodup := by
  rw [clashes_eq_nil_iff] at h
  rw [List.Nodup, List.pairwise_map]
  refine (h.filter _).imp_of_mem fun {a b} ha hb hab => hab ?_
  simp only [List.mem_filter, decide_eq_true_eq] at ha hb
  have := ha.2
  have := hb.2
  cases ha' : a.1 <;> cases hb' : b.1 <;> simp_all [Strictness.Checked]

/-- If no clash is reported, the definitions that are not lax have different names in Lean, if no
component looks quoted. -/
theorem nodup_denote (isKeyword : String → Bool) (qualified : Bool)
    {l : List (Strictness × Id × LeanName)} (h : (register l).clashes = [])
    (hq : ∀ x ∈ l, ∀ c ∈ x.2.2, looksQuoted c = false) :
    ((l.filter (·.1 ≠ .lax)).map fun x => (escape isKeyword qualified x.2.2).map Atom.denote).Nodup
    := by
  have := nodup_names h
  rw [List.map_congr_left (g := (·.2.2)) fun x hx =>
    denote_escape (hq x (List.mem_of_mem_filter hx))]
  exact this

/-- A type is not checked against a field registered before it. -/
example : (register [(.lax, 0, ["u32"]), (.strict, 1, ["u32"])]).clashes = [] := by
  simp [clashes_eq_nil_iff, Strictness.Checked]

/-- A field is checked against a type registered before it. -/
example : (register [(.strict, 0, ["u32"]), (.lax, 1, ["u32"])]).clashes ≠ [] := by
  simp [clashes_eq_nil_iff, Strictness.Checked]

end Aeneas.Spec.Naming
