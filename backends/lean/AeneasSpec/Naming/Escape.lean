module

public import AeneasSpec.Naming.Basic

/-!
# Escaping names

A component of a name that is not a valid Lean identifier is printed between French quotes, as
`«x-y»` (cf. `escape_name`). This is needed for components containing `-`, and for keywords used as
a whole name: `end` is printed `«end»`, but `Foo.end` is printed as is.

A component that already looks quoted is printed as is. So `«end»` and `end` are printed the same,
and Lean reads both as `end`, while Aeneas, which compares the unescaped names, sees two different
names.

## Main statements

* `escape_legal`: escaped names are legal Lean syntax.
* `denote_escape`: Lean reads an escaped name as the name, if no component looks quoted.
* `denote_escapeAtom_quote`: a component that looks quoted is read as another component.
-/

@[expose] public section

namespace Aeneas.Spec.Naming

/-- A printed component of a name. -/
inductive Atom
  /-- Printed as is. -/
  | plain (s : String)
  /-- Printed between French quotes: `«s»`. -/
  | quoted (s : String)
  deriving DecidableEq, Repr

/-- `s` is of the form `«..»` (cf. `is_quoted_name`). -/
def looksQuoted (s : String) : Bool :=
  match s.toList with
  | '«' :: r => r.getLast? == some '»'
  | _ => false

/-- `s` without its first and last characters. -/
def unquote (s : String) : String :=
  String.ofList (s.toList.drop 1).dropLast

namespace Atom

/-- The text of an atom. -/
def print : Atom → String
  | .plain s => s
  | .quoted s => "«" ++ s ++ "»"

/-- The component Lean reads. -/
def denote : Atom → String
  | .plain s => if looksQuoted s then unquote s else s
  | .quoted s => s

/-- The atom is legal Lean syntax, where `bare` means that it is a whole name: then it cannot be a
keyword. -/
def Legal (isKeyword : String → Bool) (bare : Bool) : Atom → Prop
  | .plain s => looksQuoted s ∨ ('-' ∉ s.toList ∧ (bare → isKeyword s = false))
  | .quoted s => '»' ∉ s.toList

end Atom

variable (isKeyword : String → Bool)

/-- Escape a component; `bare` means that it is a whole name. -/
def escapeAtom (bare : Bool) (s : String) : Atom :=
  if looksQuoted s then .plain s
  else if '-' ∈ s.toList || (bare && isKeyword s) then .quoted s
  else .plain s

/-- Escape a name (cf. `escape_name`). `qualified` means that the name is printed after a dot, as in
`x.end`, where keywords are legal. -/
def escape (qualified : Bool) (n : LeanName) : List Atom :=
  n.map (escapeAtom isKeyword (!qualified && n.length == 1))

variable {isKeyword}

/-- Escaped components are legal, if they don't contain `»`. -/
theorem escapeAtom_legal {bare : Bool} {s : String} (hs : '»' ∉ s.toList) :
    (escapeAtom isKeyword bare s).Legal isKeyword bare := by
  unfold escapeAtom
  split
  · exact .inl ‹_›
  · split
    · exact hs
    · rename_i h
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, not_or, not_and,
        Bool.not_eq_true] at h
      exact .inr ⟨h.1, h.2⟩

/-- Escaped names are legal, if their components don't contain `»`. -/
theorem escape_legal {qualified : Bool} {n : LeanName} (hn : ∀ c ∈ n, '»' ∉ c.toList) :
    ∀ a ∈ escape isKeyword qualified n, a.Legal isKeyword (!qualified && n.length == 1) := by
  simp only [escape, List.mem_map]
  rintro _ ⟨c, hc, rfl⟩
  exact escapeAtom_legal (hn c hc)

/-- Lean reads an escaped component as the component, if it does not look quoted. -/
theorem denote_escapeAtom {bare : Bool} {s : String} (hs : looksQuoted s = false) :
    (escapeAtom isKeyword bare s).denote = s := by
  unfold escapeAtom
  simp only [hs, Bool.false_eq_true, ite_false]
  split <;> simp [Atom.denote, hs]

/-- Lean reads an escaped name as the name, if no component looks quoted. -/
theorem denote_escape {qualified : Bool} {n : LeanName} (hn : ∀ c ∈ n, looksQuoted c = false) :
    (escape isKeyword qualified n).map Atom.denote = n := by
  simp only [escape, List.map_map]
  conv_rhs => rw [← List.map_id n]
  exact List.map_congr_left fun c hc => denote_escapeAtom (hn c hc)

/-- Names whose components don't look quoted are escaped to different names. -/
theorem escape_inj {qualified : Bool} {n₁ n₂ : LeanName} (h₁ : ∀ c ∈ n₁, looksQuoted c = false)
    (h₂ : ∀ c ∈ n₂, looksQuoted c = false)
    (h : (escape isKeyword qualified n₁).map Atom.denote =
      (escape isKeyword qualified n₂).map Atom.denote) : n₁ = n₂ := by
  rwa [denote_escape h₁, denote_escape h₂] at h

/-- A component that looks quoted is read as another component: `«s»` and `s` are read the same,
although they are different names for Aeneas. -/
theorem denote_escapeAtom_quote {bare : Bool} (s : String) :
    (escapeAtom isKeyword bare ("«" ++ s ++ "»")).denote = s := by
  have hq : looksQuoted ("«" ++ s ++ "»") = true := by
    simp [looksQuoted, String.toList_append]
  simp [escapeAtom, hq, Atom.denote, unquote, String.toList_append]

end Aeneas.Spec.Naming
