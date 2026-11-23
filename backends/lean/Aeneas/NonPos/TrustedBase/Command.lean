module
public import Lean
public import Aeneas.NonPos.TrustedBase.Definitions
public import Aeneas.NonPos.Tactic


@[expose] public section
namespace NonPos
open Lean Elab Command Term Meta
/-!
This file defines the `nonpos_structure` command.

See ../Tests/Examples.lean for examples of the definitions that this command produces
for example inputs.

The command works by translating the given `nonpos_structure` syntax into the definitions in that
file. It never needs to inspect the actual types of the fields - the instances in Definitions.lean
already handle that.
-/

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

/-- See Examples.lean for examples of what this command produces for the `SimpleNonpos` and `A`/`B` examples.
Comments throughout point to the corresponding definitions in that file. -/
meta def elabGroup (ss : Array StructStx) : CommandElabM Unit := do
  let g := ss[0]!.name -- Name the group after the first structure
  -- Make an identifier for three definitions we will produce:
  let idx := mkIdentFrom g (g.getId ++ `I)
  let fId := mkIdentFrom g (g.getId ++ `F)
  let shapeId := mkIdentFrom g (g.getId ++ `shape)
  let univ := ss[0]!.univ
  let ctor (s : StructStx) : Term := ⟨mkNode ``Parser.Term.dotIdent #[mkAtom ".", s.name]⟩ -- helper function for names: `.Measure`
  -- the index `.Measure x₁ ... xₙ` of a structure at its parameters (used as a pattern and as a term)
  let idxOf (s : StructStx) : CommandElabM Term := `($(ctor s) $(s.params.map (·.1))*)
  -- I
  let ctors ← ss.mapM fun s => do `(Parser.Command.ctor| | $(s.name):ident $(← explicitBinders s.params)*)
  elabCommand (← `(inductive $idx where $ctors*))  -- `SimpleNonpos.I`, `A.I`: an inductive with one ctr for each structure, taking its parameters
  -- Fields of each structure, with the structures of the group as parameters
  for s in ss do
    let fieldsId := mkIdentFrom s.name (s.name.getId ++ `Fields)
    let famBinders ← ss.mapM fun s' => do `(bracketedBinder| ($(s'.name):ident : $(← paramsPi s'.params univ)))
    let body ← s.fields.foldrM (init := ← punitAt univ) fun (_, τ) acc => `($τ ×' $acc)
    elabCommand (← `(noncomputable abbrev $fieldsId $famBinders* $(← explicitBinders s.params)* : $univ := $body))
      -- `SimpleNonpos.Fields`, `A.Fields`, `B.Fields`
  -- The functor of the group and its shape
  let fAlts ← ss.mapM fun s => do
    let fieldsId := mkIdentFrom s.name (s.name.getId ++ `Fields)
    let fams ← ss.mapM fun s' => do paramsLam s'.params (← `(X $(← idxOf s')))
    let args := s.params.map (·.1)
    `(Parser.Term.matchAltExpr| | $(← idxOf s), X => $fieldsId $fams* $args*)
  elabCommand (← `(noncomputable abbrev $fId : $idx → ($idx → $univ) → $univ $fAlts:matchAlt*))
    -- `SimpleNonpos.F`, `A.F`
  let shapeAlts ← ss.mapM fun s => do
    `(Parser.Term.matchAltExpr| | $(← idxOf s) => inferInstance)
  elabCommand (← `(@[reducible] instance $shapeId:ident : ∀ k, FixFunctor ($fId k) $shapeAlts:matchAlt*))
    -- `SimpleNonpos.shape`, `A.shape`
  -- The structures (all of them first: `mk` and the projections of one may mention another)
  for s in ss do
    elabCommand (← `(noncomputable abbrev $(s.name):ident $(← explicitBinders s.params)* : $univ :=
      Fix $fId $(← idxOf s)))  -- `SimpleNonpos`, `A`, `B`
  -- `mk` and the projections
  for s in ss do                                            -- for `A (Self : Type)`     `SimpleNonpos`:
    let k ← idxOf s                                             -- `.A Self`              `.SimpleNonpos`
    let impl ← implicitBinders s.params                         -- `{Self : Type}`        nothing
    let args := s.params.map (·.1)                              -- `Self`                 nothing
    let fieldBinders ← explicitBinders s.fields                 -- `(fa : ∀ {O} …)`      `(to_nat : Nat) (f : SimpleNonpos → Option Nat)`
    let fieldTuple                                              -- `⟨fa, ⟨⟩⟩`             `⟨to_nat, ⟨f, ⟨⟩⟩⟩`
      ← s.fields.foldrM (init := ← `(⟨⟩)) fun (f, _) acc => `(⟨$f:ident, $acc⟩)
    let mkId := mkIdentFrom s.name (s.name.getId ++ `mk)        -- `A.mk`                 `SimpleNonpos.mk`
    -- `macro_inline`, so that the fields are not evaluated before `foldDelayed` delays them (`TrustedBase/Definitions.lean`, where `foldDelayed` is)
    elabCommand (← `(@[macro_inline] def $mkId $impl* $fieldBinders*
        (h : FixFunctor.cond (G := $fId $k) (X := Fix $fId) $fieldTuple) : $(s.name):ident $args* :=
      Fix.foldDelayed $fId (fun _ => $fieldTuple) h))  -- `SimpleNonpos.mk`, `A.mk`, `B.mk`
    let fieldArgs ← s.fields.mapM fun (f, _) => `(@$f:ident)
    for (f, τ) in s.fields, j in List.range s.fields.size do
      let projId := mkIdentFrom f (s.name.getId ++ f.getId)                   -- `A.fa`       `SimpleNonpos.to_nat`
      elabCommand (← `(def $projId $impl* (d : $(s.name):ident $args*) : $τ :=
        no_implicit_lambda% $(← projN (← `(Fix.unfold $fId d)) j)))  -- `SimpleNonpos.to_nat`, `SimpleNonpos.f`, `A.fa`, `B.fb`
      -- its `simp` lemma: the projection of `mk` is the field (proved by `nonpos_proj_mk`, which
      -- adds a lemma `Measure.mk_unfold` the first time: so not elaborated asynchronously, where a proof
      -- may only add declarations named after its theorem)
      let lemmaId := mkIdentFrom f (s.name.getId ++ f.getId.appendAfter "_mk") -- `A.fa_mk`    `SimpleNonpos.to_nat_mk`
      elabCommand (← `(set_option Elab.async false in @[simp] theorem $lemmaId $impl* $fieldBinders*
          (h : FixFunctor.cond (G := $fId $k) (X := Fix $fId) $fieldTuple) :
          @$projId $args* ($mkId $fieldArgs* h) = @$f := by nonpos_proj_mk))

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
