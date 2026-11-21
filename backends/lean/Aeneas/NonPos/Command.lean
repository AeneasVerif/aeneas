module
public import Lean
public import Aeneas.NonPos.Top
public import Aeneas.NonPos.Tactic

@[expose] public section
/-!
# `nonpos_structure`: the command

With `Top.lean` and section 1 of `Tactic.lean`, this file is the trusted surface of the library:
the `nonpos_structure` command, a thin wrapper around `Fix` (section 1), and what the `nonpos_cont`
tactic, which proves the condition of each structure, is expected to do (section 2).

It imports `NonPos/Tactic.lean`, of which only section 1 is part of the trusted surface: the
command uses the rest only to prove the `simp` lemmas it states (`nonpos_proj_mk`) and, after
the definitions of a group, to prove lemmas about them for the tactic (`elabGroupLemmas`).  Every
proof the tactic builds is checked by the kernel.
-/

namespace NonPos
open Lean Elab Command Term Meta

/-! ## 1. The `nonpos_structure` command

```
nonpos_structure Bla (Self : Type) : Type 1 where
  to_num : Self → Result I32
  add : ∀ {Other : Type} (inst : Bla Other), Other → Self → Result I32
```
(and `mutual ... end` around several of them) produces, for a group `G` named after its first
structure:

* `G.I`, the index type of the group: an inductive with one constructor `G.I.Bla (Self : Type)` per
  structure, carrying its parameters;
* `Bla.Fields (Bla : Type → Type 1) (Self : Type) : Type 1 := (Self → Result I32) ×' (∀ ..., Bla Other → ...) ×' PUnit`:
  the fields *as written*, with the structure names as parameters;
* `G.F : G.I → (G.I → Type 1) → Type 1`, dispatching to the `Fields`;
* `Bla Self := Fix G.F (.Bla Self)`;
* `Bla.mk to_num add (h : FixFunctor.cond ⟨to_num, add, ⟨⟩⟩) := Fix.fold G.F _ h`;
* `Bla.to_num d := (Fix.unfold G.F d).1`, `Bla.add d := (Fix.unfold G.F d).2.1`, each with the
  type as written, and the `simp` lemmas `Bla.to_num_mk`, `Bla.add_mk` (a projection of `mk` is
  the field), stated here and proved by the tactic `nonpos_proj_mk` of `NonPos/Tactic.lean`;
* then, by `elabGroupLemmas` (section 2), the lemmas of `NonPos/Tactic.lean` (section 4 there).

The command never inspects the field types: `FixFunctor (G.F k)` is found by instance search, which can
only succeed through the instances of section 3 of `Top.lean`, and the types of `mk` and the
projections are the user's own, checked by the kernel against `Fix`. -/

syntax nonposField := ident " : " term
syntax nonposStructureCore :=
  declModifiers "nonpos_structure " ident bracketedBinder* " : " term " where " manyIndent(nonposField)
syntax (name := nonposStructure) nonposStructureCore : command

meta structure StructStx where
  name : Ident
  params : Array (Ident × Term)
  univ : Term
  fields : Array (Ident × Term)
  deriving Inhabited

meta def parseStruct (stx : Syntax) : CommandElabM StructStx := do
  let core := stx[0]                                   -- the `nonposStructureCore` node
  let name : Ident := ⟨core[2]⟩                        -- `ident`
  let params ← core[3].getArgs.flatMapM fun b => do    -- `bracketedBinder*`, one `(x, T)` per name
    match b with
    | `(bracketedBinder| ($ids* : $ty)) => return ids.map fun i => (⟨i⟩, ty)
    | `(bracketedBinder| {$ids* : $ty}) => return ids.map fun i => (⟨i⟩, ty)
    | _ => throwErrorAt b "nonpos_structure: unsupported binder"
  let fields := core[7].getArgs.map fun field =>           -- `manyIndent(nonposField)`
    ((⟨field[0]⟩ : Ident), (⟨field[2]⟩ : Term))             -- a `nonposField` is `ident " : " term`: [0] [1] [2]
  return { name, params, univ := ⟨core[5]⟩, fields }   -- `univ` is the `term` after " : "

/-- `PUnit` in the universe of `Type v`, so that universes of generated tuples are determined. -/
meta def punitAt (univ : Term) : CommandElabM Term := do
  match univ with
  | `(Type $l:level) => `(PUnit.{$l + 1})
  | _ => `(PUnit.{1})

/-! Helper functions to build syntax from the type parameters of a structure. -/

/-- The type of the structure as a function of its parameters: `(x₁ : T₁) → ... → (xₙ : Tₙ) → Type v`. -/
meta def paramsPi (ps : Array (Ident × Term)) (univ : Term) : CommandElabM Term :=
  ps.foldrM (init := univ) fun (x, T) acc => `(($x:ident : $T) → $acc)
/-- Abstraction over the parameters: `fun x₁ ... xₙ => body`. -/
meta def paramsLam (ps : Array (Ident × Term)) (body : Term) : CommandElabM Term :=
  ps.foldrM (init := body) fun (x, _) acc => `(fun $x:ident => $acc)
/-- The parameters as implicit binders `{x₁ : T₁} ... {xₙ : Tₙ}` (for `mk` and the projections). -/
meta def implicitBinders (ps : Array (Ident × Term)) : CommandElabM (Array (TSyntax ``Parser.Term.bracketedBinder)) :=
  ps.mapM fun (x, T) => `(bracketedBinder| {$x:ident : $T})
/-- The parameters as explicit binders `(x₁ : T₁) ... (xₙ : Tₙ)` (for `G.I`, `Fields` and the structure itself). -/
meta def explicitBinders (ps : Array (Ident × Term)) : CommandElabM (Array (TSyntax ``Parser.Term.bracketedBinder)) :=
  ps.mapM fun (x, T) => `(bracketedBinder| ($x:ident : $T))
/-- The `j`-th component of a right-nested product: `t.2.2. ... .1`, with `j` times `.2`. -/
meta def projN (t : Term) : Nat → CommandElabM Term
  | 0 => `(@PProd.fst _ _ $t)
  | j + 1 => do projN (← `(@PProd.snd _ _ $t)) j

/-- See Examples.lean for examples of what this command produces for the `Example1` and `A`/`B` examples.
Comments throughout point to the corresponding definitions in that file. -/
meta def elabGroup (ss : Array StructStx) : CommandElabM Unit := do
  let g := ss[0]!.name -- Name the group after the first structure
  -- Make an identifier for three definitions we will produce:
  let idx := mkIdentFrom g (g.getId ++ `I)
  let fId := mkIdentFrom g (g.getId ++ `F)
  let shapeId := mkIdentFrom g (g.getId ++ `shape)
  let univ := ss[0]!.univ
  let ctor (s : StructStx) : Term := ⟨mkNode ``Parser.Term.dotIdent #[mkAtom ".", s.name]⟩ -- helper function for names: `.Bla`
  -- the index `.Bla x₁ ... xₙ` of a structure at its parameters (used as a pattern and as a term)
  let idxOf (s : StructStx) : CommandElabM Term := `($(ctor s) $(s.params.map (·.1))*)
  -- I
  let ctors ← ss.mapM fun s => do `(Parser.Command.ctor| | $(s.name):ident $(← explicitBinders s.params)*)
  elabCommand (← `(inductive $idx where $ctors*))  -- `Example1.I`, `A.I`: an inductive with one ctr for each structure, taking its parameters
  -- Fields of each structure, with the structures of the group as parameters
  for s in ss do
    let fieldsId := mkIdentFrom s.name (s.name.getId ++ `Fields)
    let famBinders ← ss.mapM fun s' => do `(bracketedBinder| ($(s'.name):ident : $(← paramsPi s'.params univ)))
    let body ← s.fields.foldrM (init := ← punitAt univ) fun (_, τ) acc => `($τ ×' $acc)
    elabCommand (← `(noncomputable abbrev $fieldsId $famBinders* $(← explicitBinders s.params)* : $univ := $body))
      -- `Example1.Fields`, `A.Fields`, `B.Fields`
  -- The functor of the group and its shape
  let fAlts ← ss.mapM fun s => do
    let fieldsId := mkIdentFrom s.name (s.name.getId ++ `Fields)
    let fams ← ss.mapM fun s' => do paramsLam s'.params (← `(X $(← idxOf s')))
    let args := s.params.map (·.1)
    `(Parser.Term.matchAltExpr| | $(← idxOf s), X => $fieldsId $fams* $args*)
  elabCommand (← `(noncomputable abbrev $fId : $idx → ($idx → $univ) → $univ $fAlts:matchAlt*))
    -- `Example1.F`, `A.F`
  let shapeAlts ← ss.mapM fun s => do
    `(Parser.Term.matchAltExpr| | $(← idxOf s) => inferInstance)
  elabCommand (← `(@[reducible] noncomputable instance $shapeId:ident : ∀ k, FixFunctor ($fId k) $shapeAlts:matchAlt*))
    -- `Example1.shape`, `A.shape`
  -- its runtime implementation, which is never read (assumption 3 of section 5 of `Top.lean`)
  let shapeImplId := mkIdentFrom g (g.getId ++ `shapeImpl)
  elabCommand (← `(@[instance_reducible] unsafe def $shapeImplId : ∀ k, FixFunctor ($fId k) := fun _ => FixFunctor.runtime))
  elabCommand (← `(attribute [implemented_by $shapeImplId] $shapeId))  -- `Example1.shapeImpl`, `A.shapeImpl`
  -- The structures (all of them first: `mk` and the projections of one may mention another)
  for s in ss do
    elabCommand (← `(noncomputable abbrev $(s.name):ident $(← explicitBinders s.params)* : $univ :=
      Fix $fId $(← idxOf s)))  -- `Example1`, `A`, `B`
  -- `mk` and the projections
  for s in ss do                                            -- for `A (Self : Type)`     `Example1`:
    let k ← idxOf s                                             -- `.A Self`              `.Example1`
    let impl ← implicitBinders s.params                         -- `{Self : Type}`        nothing
    let args := s.params.map (·.1)                              -- `Self`                 nothing
    let fieldBinders ← explicitBinders s.fields                 -- `(fa : ∀ {O} …)`      `(to_nat : Nat) (f : Example1 → Option Nat)`
    let fieldTuple                                              -- `⟨fa, ⟨⟩⟩`             `⟨to_nat, ⟨f, ⟨⟩⟩⟩`
      ← s.fields.foldrM (init := ← `(⟨⟩)) fun (f, _) acc => `(⟨$f:ident, $acc⟩)
    let mkId := mkIdentFrom s.name (s.name.getId ++ `mk)        -- `A.mk`                 `Example1.mk`
    -- `macro_inline`, so that the fields are not evaluated before `fold` delays them (section 5 of `Top.lean`)
    elabCommand (← `(@[macro_inline] def $mkId $impl* $fieldBinders*
        (h : FixFunctor.cond (G := $fId $k) (X := Fix $fId) $fieldTuple) : $(s.name):ident $args* :=
      Fix.fold $fId $fieldTuple h))  -- `Example1.mk`, `A.mk`, `B.mk`
    let fieldArgs ← s.fields.mapM fun (f, _) => `(@$f:ident)
    for (f, τ) in s.fields, j in List.range s.fields.size do
      let projId := mkIdentFrom f (s.name.getId ++ f.getId)                   -- `A.fa`       `Example1.to_nat`
      elabCommand (← `(def $projId $impl* (d : $(s.name):ident $args*) : $τ :=
        no_implicit_lambda% $(← projN (← `(Fix.unfold $fId d)) j)))  -- `Example1.to_nat`, `Example1.f`, `A.fa`, `B.fb`
      -- its `simp` lemma: the projection of `mk` is the field (proved by `nonpos_proj_mk`, which
      -- adds a lemma `Bla.mk_unfold` the first time: so not elaborated asynchronously, where a proof
      -- may only add declarations named after its theorem)
      let lemmaId := mkIdentFrom f (s.name.getId ++ f.getId.appendAfter "_mk") -- `A.fa_mk`    `Example1.to_nat_mk`
      elabCommand (← `(set_option Elab.async false in @[simp] theorem $lemmaId $impl* $fieldBinders*
          (h : FixFunctor.cond (G := $fId $k) (X := Fix $fId) $fieldTuple) :
          @$projId $args* ($mkId $fieldArgs* h) = @$f := by nonpos_proj_mk))

/-! ## 2. Continuity, and the `nonpos_cont` tactic

The condition `FixFunctor.cond` of a structure is a conjunction of `Cont` facts, one for each field
that takes a dictionary of the group (section 3 of `Top.lean`; `nonpos_cond_simp`, in
`NonPos/Tactic.lean`, unfolds the condition into them).  Aeneas proves the condition of each `mk` it outputs with the tactic `nonpos_cont`, and the
monotonicity obligation of each self-referential instance with
`partial_fixpoint monotonicity Cont.monotone (by nonpos_cont)`.

The tactic is in `NonPos/Tactic.lean` (from section 2 on), which is not part of the trusted surface;
the theorems it applies are the forms of section 1 there.  Every proof it builds is checked by the kernel, so it cannot make a structure
contain anything that does not satisfy the condition.  What it is expected to do, which is checked
by its tests but not guaranteed by this file, is:

* **Completeness:** `nonpos_cont` proves `Cont f` for every function `f` that Aeneas outputs (that
  is, the conditions above), in reasonable time.
* **Lemmas:** a theorem `… → Cont (fun d => body)` tagged `@[nonpos_continuous]` is applied by
  `nonpos_cont` to any goal of the shape of `body`, instead of proving it again from the definitions
  in `body`.  Lemmas are tagged by `nonpos_continuity f` (which Aeneas outputs after each function
  `f` taking a dictionary, and which proves the continuity of `f` in that dictionary), by
  `elabGroupLemmas` (below), and by hand (the operations of a monad).

After the definitions of a group, `nonpos_structure` calls `elabGroupLemmas` of
`NonPos/Tactic.lean` on the same structures, which proves lemmas about them (section 4 there), so
that `nonpos_cont` does not derive them at each use.  It runs after every definition of the group
is made, so it can only add facts about them: theorems, and instances of classes that are
`Prop`s. -/

/-- Elaborate a group, then prove the lemmas of `NonPos/Tactic.lean` about it. -/
meta def elabGroupAndLemmas (stxs : Array Syntax) : CommandElabM Unit := do
  let ss ← stxs.mapM parseStruct
  elabGroup ss
  let ns ← getCurrNamespace
  elabGroupLemmas (ss.map fun s => ns ++ s.name.getId)

@[command_elab nonposStructure] meta def elabNonposStructure : CommandElab := fun stx =>
  elabGroupAndLemmas #[stx]

/-- `mutual nonpos_structure ... nonpos_structure ... end`. -/
@[command_elab Lean.Parser.Command.«mutual»] meta def elabNonposMutual : CommandElab := fun stx => do
  let cmds := stx[1].getArgs
  unless cmds.size > 0 && cmds.all (·.isOfKind ``nonposStructure) do throwUnsupportedSyntax
  elabGroupAndLemmas cmds

end NonPos
