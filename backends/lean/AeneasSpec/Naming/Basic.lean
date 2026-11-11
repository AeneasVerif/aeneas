module

public import Mathlib.Data.List.Basic

/-!
# Names of the Lean definitions

How Aeneas names the Lean definitions it writes (cf. `ExtractBase.ml`, Lean backend). The name of an
item is computed from its Rust path:

1. the `rename` attribute, if present, replaces the last identifier (`rename`);
2. for an item of the crate being translated, the crate name is dropped (`dropCrate`);
3. each path element is printed (`PathElem.print`), and becomes a component of the Lean name;
4. suffixes are added: `constructor`, `default`, `Blanket`, `impl` (`baseFunName`), and the loop
   suffixes (`withLoop`).

The names are then registered, which reports clashes (`AeneasSpec.Naming.Registry`), and escaped
when printed (`AeneasSpec.Naming.Escape`).

Printing types is not modelled: how an `impl` block, or the self type and trait of a trait impl,
appear in names is taken as given.

## Main statements

* `withLoop_inj`: the loops of a function, and their bodies, have names distinct from each other
  and from the function.
-/

@[expose] public section

namespace Aeneas.Spec.Naming

/-- A Lean name, as the list of its components: `Foo.bar` is `["Foo", "bar"]`. Aeneas computes
names as dot-separated strings and compares them as strings, which is the same when no component
contains a dot. -/
abbrev LeanName := List String

/-- An element of a Rust path (cf. Charon's `path_elem`). Monomorphization suffixes are left out:
they don't appear in names. -/
inductive PathElem
  /-- An identifier. The disambiguator tells apart items of the same name in the same scope, such
  as two items declared in different blocks of a function. It is usually `0`. -/
  | ident (s : String) (disambiguator : ℕ)
  /-- An `impl` block, shown as `name`. For an inherent impl `impl<T> a::Foo<T>`, this is the name
  of the self type without its module path: `Foo` (`U32` for `impl u32`), with the generic
  arguments that are not variables. `blanket` means a trait impl `impl<T> Trait for T`. -/
  | impl (name : String) (blanket : Bool)
  /-- The item exists for the given compilation target only (for example `x86_64`). -/
  | target (t : String)
  deriving DecidableEq, Repr

/-- A Rust path, from the crate down (cf. Charon's `name`). -/
abbrev RustPath := List PathElem

/-- How a path element shows up in a Lean name (cf. Charon's `pattern_elem_to_string` with
`TkName`): a non-zero disambiguator is appended with an underscore. -/
def PathElem.print : PathElem → String
  | .ident s d => if d = 0 then s else s ++ "_" ++ toString d
  | .impl n _ => n
  | .target t => t

/-- `l` with `x` inserted before its last element. -/
def insertBeforeLast {α : Type*} (x : α) (l : List α) : List α :=
  l.dropLast ++ x :: l.getLast?.toList

/-- The path without its target suffix, and the target (cf. `extract_target_suffix`). -/
def stripTarget (p : RustPath) : RustPath × Option String :=
  match p.getLast? with
  | some (.target t) => (p.dropLast, some t)
  | _ => (p, none)

/-- Replace the last identifier with `r`, keeping a target suffix (cf. `rename_llbc_name`). -/
def rename (r : String) (p : RustPath) : RustPath :=
  (stripTarget p).1.dropLast ++ .ident r 0 :: ((stripTarget p).2.map .target).toList

/-- Drop the crate name, which is the first element of the path, if it is `crate`. A path of one
element is kept (cf. `ctx_prepare_name`). -/
def dropCrate (crate : String) : RustPath → RustPath
  | [e] => [e]
  | .ident c d :: p => if c = crate then p else .ident c d :: p
  | p => p

/-- Append `s` to the last component. -/
def appendLast (s : String) (n : LeanName) : LeanName :=
  n.dropLast ++ n.getLast?.toList.map (· ++ s)

/-- What Aeneas knows about an item for naming it. -/
structure ItemMeta where
  /-- The Rust path. -/
  path : RustPath
  /-- The `rename` attribute (`#[aeneas::rename("..")]` or `#[charon::rename("..")]`). -/
  rename? : Option String := none
  /-- Whether the item belongs to the crate being translated. -/
  isLocal : Bool := true
  deriving DecidableEq, Repr

namespace ItemMeta

variable (crate : String) (m : ItemMeta)

/-- The path, renamed if the item has a `rename` attribute (cf. `opt_rename_llbc_name`). -/
def renamed : RustPath :=
  m.rename?.elim m.path (rename · m.path)

/-- Print a path as a Lean name, dropping the crate if the item is local (cf.
`ctx_compute_simple_name`). -/
def print (p : RustPath) : LeanName :=
  (if m.isLocal then dropCrate crate p else p).map PathElem.print

end ItemMeta

/-! ### Types -/

/-- The name of a type, or of a trait declaration (cf. `ctx_compute_type_name`,
`ctx_compute_trait_decl_name`). -/
def typeName (crate : String) (m : ItemMeta) : LeanName :=
  m.print crate m.renamed

/-- A variant of an enum. -/
structure Variant where
  name : String
  rename? : Option String := none

/-- The name of a variant: it is in the namespace of its type (cf. `ctx_compute_variant_name`). -/
def variantName (crate : String) (m : ItemMeta) (v : Variant) : LeanName :=
  typeName crate m ++ [v.rename?.getD v.name]

/-- The constructor of a structure (cf. `ctx_compute_struct_constructor`). -/
def structConstructorName (crate : String) (m : ItemMeta) : LeanName :=
  typeName crate m ++ ["mk"]

/-- A field of a structure. -/
structure Field where
  /-- The name, if the field has one. -/
  name? : Option String
  rename? : Option String := none

/-- The name of the `i`-th field (cf. `ctx_compute_field_name`). The field is not qualified by the
type: Lean finds it from the type of the structure. A field without a name gets an underscore. -/
def fieldName (f : Field) (i : ℕ) : String :=
  let s := f.rename?.getD (f.name?.getD (toString i))
  if f.name?.isNone then "_" ++ s else s

/-! ### Trait implementations -/

/-- How a trait impl is named (cf. `ctx_compute_trait_impl_name_raw`). The name does not depend on
where the impl is defined. -/
inductive TraitImplNaming
  /-- The impl has a `rename` attribute. -/
  | renamed (r : String)
  /-- A blanket impl `impl<T> Trait<..> for T`, given the name of the trait with its generic
  arguments. -/
  | blanket (traitName : LeanName)
  /-- An impl for a type, given the name of the self type, and the components of the name of the
  trait with its generic arguments other than the self type. -/
  | ofSelf (selfName : LeanName) (traitName : List String)
  deriving DecidableEq, Repr

/-- The name of a trait impl. For `impl a::Trait<u32> for b::Foo`, it is `Foo.Insts.TraitU32`. -/
def traitImplName : TraitImplNaming → LeanName
  | .renamed r => [r]
  | .blanket t => t ++ ["Blanket"]
  | .ofSelf s t => s ++ ["Insts", String.join (t.map String.capitalize)]

/-! ### Functions and globals -/

/-- Naming options (cf. `Config.ml`). -/
structure Config where
  /-- Always put methods in an `impl` namespace (`-method-names-in-impl-namespace`). -/
  methodNamesInImplNamespace : Bool := false

/-- Where a function or global comes from (cf. `extractable_item_source`). -/
inductive FunSource
  /-- A function or global defined by the user. -/
  | plain
  /-- A function rustc makes from an ADT constructor used as a function. -/
  | adtConstructor
  /-- The default implementation of a method in a trait declaration. -/
  | traitDefault
  /-- An item of a trait impl, given the impl and the item's name in the trait. -/
  | traitImplItem (impl : TraitImplNaming) (item : String)
  deriving DecidableEq, Repr

/-- The method is in a blanket impl: the last two elements are a blanket impl and the method (cf.
`is_blanket_method`). -/
def isBlanketMethod (p : RustPath) : Bool :=
  match (stripTarget p).1.reverse with
  | _ :: .impl _ true :: [] => true
  | _ => false

/-- The penultimate element is an `impl` block. -/
def inImpl (p : RustPath) : Bool :=
  match p.reverse with
  | _ :: .impl _ _ :: _ => true
  | _ => false

/-- Print the path of a function or global, adding `Blanket` before the last component of a method
of a blanket impl (cf. `ctx_fun_global_name_to_extract_string`). -/
def printFunPath (crate : String) (m : ItemMeta) (p : RustPath) : LeanName :=
  if isBlanketMethod p then insertBeforeLast "Blanket" (m.print crate p) else m.print crate p

/-- The name of a function or global, without the loop suffixes (cf.
`ctx_compute_fun_global_name_no_suffix`). `projector n` means that `n` is the projector of a field
of a structure, which a method of the same name would clash with; the method is then put in an
`impl` namespace. -/
def baseFunName (cfg : Config) (crate : String) (projector : LeanName → Bool) (m : ItemMeta) :
    FunSource → LeanName
  | .traitImplItem impl item =>
    let tgt := (stripTarget m.path).2.map fun t => t.map fun c => if c = '-' then '_' else c
    appendLast (tgt.elim "" ("_" ++ ·)) (traitImplName impl ++ [item])
  | src =>
    let p := m.renamed ++ match src with
      | .adtConstructor => [.ident "constructor" 0]
      | .traitDefault => [.ident "default" 0]
      | _ => []
    let n := printFunPath crate m p
    let nImpl := printFunPath crate m (insertBeforeLast (.ident "impl" 0) p)
    if cfg.methodNamesInImplNamespace then (if inImpl p then nImpl else n)
    else if projector n then nImpl else n

/-! ### Loops -/

/-- A loop of a function, which Aeneas translates to a separate function. -/
structure LoopRef where
  /-- The position of the loop in the tree of loops of the function: `[0]` is the first outermost
  loop, `[0, 1]` the second loop inside it (cf. `loop_pos`). -/
  pos : List ℕ
  /-- The body of the loop, rather than the loop. -/
  body : Bool
  deriving DecidableEq, Repr

/-- The suffix for the loop at `pos` (cf. `default_fun_loop_suffix`). It omits the position if the
function has only one loop. -/
def loopTag (numLoops : ℕ) (pos : List ℕ) : String :=
  if numLoops = 1 then "_loop" else String.join (pos.map fun i => "_loop" ++ toString i)

/-- Add the loop suffixes to the name of a function (cf. `default_fun_suffix`): `f_loop0` for the
loop at `[0]`, and `f_loop0.body` for its body. -/
def withLoop (numLoops : ℕ) : Option LoopRef → LeanName → LeanName
  | none, n => n
  | some l, n => appendLast (loopTag numLoops l.pos) n ++ if l.body then ["body"] else []

/-- The name of a function or of one of its loops (cf. `ctx_compute_fun_name`). -/
def funName (cfg : Config) (crate : String) (projector : LeanName → Bool) (m : ItemMeta)
    (src : FunSource) (numLoops : ℕ) (loop : Option LoopRef) : LeanName :=
  withLoop numLoops loop (baseFunName cfg crate projector m src)

/-- The termination measure of a function or loop (cf. `ctx_compute_termination_measure_name`). -/
def terminationMeasureName (cfg : Config) (crate : String) (projector : LeanName → Bool)
    (m : ItemMeta) (src : FunSource) (numLoops : ℕ) (loop : Option LoopRef) : LeanName :=
  appendLast "_terminates" (funName cfg crate projector m src numLoops loop)

/-- The termination proof of a function or loop (cf. `ctx_compute_decreases_proof_name`). -/
def decreasesProofName (cfg : Config) (crate : String) (projector : LeanName → Bool)
    (m : ItemMeta) (src : FunSource) (numLoops : ℕ) (loop : Option LoopRef) : LeanName :=
  appendLast "_decreases" (funName cfg crate projector m src numLoops loop)

/-! ### Loop names are distinct -/

section LoopTag

/-- Digits followed by something that is not a digit determine the digits. -/
private theorem digits_append_inj {d₁ d₂ r₁ r₂ : List Char} (hd₁ : ∀ c ∈ d₁, c.isDigit)
    (hd₂ : ∀ c ∈ d₂, c.isDigit) (hr₁ : ∀ c ∈ r₁.head?, ¬ c.isDigit)
    (hr₂ : ∀ c ∈ r₂.head?, ¬ c.isDigit) (h : d₁ ++ r₁ = d₂ ++ r₂) : d₁ = d₂ ∧ r₁ = r₂ := by
  rcases List.append_eq_append_iff.1 h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl⟩
  · cases a with
    | nil => simp
    | cons c a => exact absurd (hd₂ c (by simp)) (hr₁ c (by simp))
  · cases a with
    | nil => simp
    | cons c a => exact absurd (hd₁ c (by simp)) (hr₂ c (by simp))

/-- The characters of the loop tag for the positions `ps`. -/
private theorem toList_loopTag (ps : List ℕ) :
    (String.join (ps.map fun i => "_loop" ++ toString i)).toList =
      ps.flatMap fun i => "_loop".toList ++ Nat.toDigits 10 i := by
  simp [String.toList_join, List.flatMap_map]

private theorem flatMap_loopTag_inj {ps qs : List ℕ}
    (h : (ps.flatMap fun i => "_loop".toList ++ Nat.toDigits 10 i) =
      qs.flatMap fun i => "_loop".toList ++ Nat.toDigits 10 i) : ps = qs := by
  induction ps generalizing qs with
  | nil => cases qs <;> simp_all
  | cons p ps ih =>
    cases qs with
    | nil => simp at h
    | cons q qs =>
      simp only [List.flatMap_cons, List.append_assoc, List.append_cancel_left_eq] at h
      have head (l : List ℕ) : ∀ c ∈ (l.flatMap fun i => "_loop".toList ++ Nat.toDigits 10 i).head?,
          ¬ c.isDigit := by
        cases l <;> simp
      have digit (n : ℕ) : ∀ c ∈ Nat.toDigits 10 n, c.isDigit := fun _ hc =>
        Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
      obtain ⟨hpq, hr⟩ := digits_append_inj (digit p) (digit q) (head ps) (head qs) h
      have : p = q := by
        rw [← Nat.ofDigitChars_ten_toDigits (n := p), hpq, Nat.ofDigitChars_ten_toDigits]
      rw [this, ih hr]

/-- Different positions give different loop tags: the positions can be read back from the tag. -/
theorem loopTag_inj {n : ℕ} (hn : n ≠ 1) {ps qs : List ℕ} (h : loopTag n ps = loopTag n qs) :
    ps = qs := by
  simp only [loopTag, hn, ite_false] at h
  have h := congrArg String.toList h
  rw [toList_loopTag, toList_loopTag] at h
  exact flatMap_loopTag_inj h

/-- The positions of loops are never empty, so their tags are not empty either. -/
theorem loopTag_ne_empty {n : ℕ} {ps : List ℕ} (hps : ps ≠ []) : loopTag n ps ≠ "" := by
  intro h
  have h := congrArg String.toList h
  unfold loopTag at h
  split at h
  · simp at h
  · obtain ⟨p, ps, rfl⟩ := List.exists_cons_of_ne_nil hps
    rw [toList_loopTag] at h
    simp at h

end LoopTag

private theorem appendLast_inj {n : LeanName} (hn : n ≠ []) {s t : String}
    (h : appendLast s n = appendLast t n) : s = t := by
  obtain ⟨n, x, rfl⟩ := List.eq_nil_or_concat n |>.resolve_left hn
  simpa [appendLast] using h

private theorem appendLast_ne {n : LeanName} (hn : n ≠ []) {s : String} (hs : s ≠ "") :
    appendLast s n ≠ n := by
  obtain ⟨n, x, rfl⟩ := List.eq_nil_or_concat n |>.resolve_left hn
  simpa [appendLast] using hs

/-- The loops of a function, and their bodies, have names distinct from each other and from the
function. If the function has a single loop, the tag of the loop has no position, which is enough as
there is a single position. -/
theorem withLoop_inj {n : LeanName} (hn : n ≠ []) {numLoops : ℕ} {l₁ l₂ : Option LoopRef}
    (hpos : ∀ l ∈ l₁, l.pos ≠ []) (hpos₂ : ∀ l ∈ l₂, l.pos ≠ [])
    (hone : numLoops = 1 → ∀ a ∈ l₁, ∀ b ∈ l₂, a.pos = b.pos)
    (h : withLoop numLoops l₁ n = withLoop numLoops l₂ n) : l₁ = l₂ := by
  have len (s : String) : (appendLast s n).length = n.length := by
    obtain ⟨n, x, rfl⟩ := List.eq_nil_or_concat n |>.resolve_left hn
    simp [appendLast]
  cases l₁ with
  | none =>
    cases l₂ with
    | none => rfl
    | some b =>
      have hb := hpos₂ b rfl
      cases hbody : b.body <;> simp only [withLoop, hbody] at h
      · exact absurd h.symm (by simpa using appendLast_ne hn (loopTag_ne_empty hb))
      · simpa [len] using congrArg List.length h
  | some a =>
    cases l₂ with
    | none =>
      have ha := hpos a rfl
      cases hbody : a.body <;> simp only [withLoop, hbody] at h
      · exact absurd h (by simpa using appendLast_ne hn (loopTag_ne_empty ha))
      · simpa [len] using congrArg List.length h
    | some b =>
      have hbody : a.body = b.body := by
        have := congrArg List.length h
        cases ha : a.body <;> cases hb : b.body <;> simp [withLoop, ha, hb, len] at this ⊢
      have htag : loopTag numLoops a.pos = loopTag numLoops b.pos := by
        apply appendLast_inj hn
        simpa [withLoop, hbody] using h
      have : a.pos = b.pos := by
        by_cases h1 : numLoops = 1
        · exact hone h1 a rfl b rfl
        · exact loopTag_inj h1 htag
      cases a; cases b; simp_all

end Aeneas.Spec.Naming
