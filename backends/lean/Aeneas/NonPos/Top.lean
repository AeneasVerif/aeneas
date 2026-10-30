module
public import Lean
public import Aeneas.NonPos.Proofs

@[expose] public section
/-!
# `nonpos_structure`: the top-level file

This file is the whole trusted surface of the library.  It contains, and only contains:

1. the *statements* that pin down the imported constants (`Dom`, `Cont`, `Shape`, `Fix`, ...);
2. the `nonpos_structure` command, a thin wrapper around `Fix`;
3. the statements of the continuity theorems, one per form of term;
4. the `nonpos_cont` tactic, a thin wrapper around those theorems.

Proofs live in `NonPos/Proofs.lean` and the definitions of the constants in `NonPos/Model/`;
neither needs to be read.  Every theorem below is proved by a one-line reference to `Proofs`.
-/

namespace NonPos
open Lean Elab Command Term Meta
noncomputable section

universe pu v u w w₁ w₂

/-! ## 1. Admissible types, the condition, monads

`Dom A` says the type `A` is admissible; `Cont f` is the condition on functions between admissible
types (the "continuity" of the goal; its definition is not needed here).  Every type is admissible in
a trivial way (`Dom.discrete`, low priority); products and function types are admissible componentwise
and pointwise; `M α` is admissible for a supported monad `M`.  `Pointed A` says `A` has a least
element: this is what makes a plain field of type `A` free of the lifting of section 2. -/

/-! No instance of these classes is registered anywhere but in this file. -/

instance (priority := low) (A : Type w) : Dom A := Dom.discrete A
instance : Dom PUnit.{w+1} := Dom.unit
instance (T : Type w₁) (B : T → Type w₂) [∀ t, Dom (B t)] : Dom ((t : T) → B t) := Dom.pi T B
instance (A : Type w₁) (B : Type w₂) [Dom A] [Dom B] : Dom (A ×' B) := Dom.pprod A B

instance : Pointed PUnit.{w+1} := Pointed.unit
instance (T : Type w₁) (B : T → Type w₂) [∀ t, Dom (B t)] [∀ t, Pointed (B t)] : Pointed ((t : T) → B t) :=
  Pointed.pi T B
instance (A : Type w₁) (B : Type w₂) [Dom A] [Dom B] [Pointed A] [Pointed B] : Pointed (A ×' B) := Pointed.pprod A B

/-- A supported monad `M` carries the chain-complete order that `partial_fixpoint` uses
(`Lean.Order.CCPO (M α)`); `NonPosMonad M` says that `bind` satisfies the condition for it. -/
instance (M : Type u → Type u) [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] (α : Type u) : Dom (M α) :=
  NonPosMonad.dom α
instance (M : Type u → Type u) [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] (α : Type u) : Pointed (M α) :=
  Pointed.monad α
example (M : Type u → Type u) [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] {α β : Type u} :
    Cont (fun p : M α ×' (α → M β) => p.1 >>= p.2) := NonPosMonad.bind_cont

/-! ## 2. Signatures

A group of mutually defined structures is indexed by a type `I`, whose elements are the structures
of the group applied to their parameters (`k : I` is, say, `Bla Self`).  `Fam I = I → Type v` is the
type of families `X k` that the structures range over.  The body of `k` is a functor
`F k : Fam I → Type v`, and `Shape (F k)` says that `F k` is built from the pieces below and from nothing else, and gives the condition `Shape.cond` that
`.mk` requires of a body: trivial on plain fields, pointwise through binders, componentwise on
products, and `Cont` on dictionary binders.  Every binder is treated alike: a `Type` binder, a `Nat`
binder and a dictionary binder are all `Shape.pi`, except that a binder whose type is one of the
structures being defined is `Shape.arr`.  A plain field is `Shape.const` when its type is pointed and
`Shape.data` otherwise; the body of a binder must be pointed (`Shape.Pointed`: no `Shape.data` and no
plain dictionary field in it). -/

section Shapes
variable {I : Type pu}

/-- Data: `A`, any admissible type (`Nat`, `Type`, ordinary structures, ...), as a plain field. -/
instance (priority := low) Shape.data (A : Type w) [Dom A] : Shape (fun _ : (I → Type v) => A) where
  cond _ := True
  sd := Model.Shape.data A
/-- Constant: `A`, a pointed admissible type (`M τ`, a function into one, ...), as a plain field. -/
instance Shape.const (A : Type w) [Dom A] [NonPos.Pointed A] : Shape (fun _ : Fam.{pu, v} I => A) where
  cond _ := True
  sd := Model.Shape.const A
/-- Recursive occurrence: `X k`, as a plain field. -/
instance Shape.var (k : I) : Shape (fun X : Fam.{pu, v} I => X k) where
  cond _ := True
  sd := Model.Shape.var k
/-- Binder: `(t : T) → G t X`, for any type `T` (implicit or explicit, `Type`-valued or not). -/
instance Shape.pi (T : Type w₁) (G : T → Fam.{pu, v} I → Type w₂) [∀ t, Shape (G t)] [∀ t, Shape.Pointed (G t)] :
    Shape (fun X => (t : T) → G t X) where
  cond f := ∀ t, Shape.cond (f t)
  sd := Model.Shape.pi T G
/-- Dictionary binder: `X k → G X`. -/
instance Shape.arr (k : I) (G : Fam.{pu, v} I → Type w) [Shape G] [Shape.Pointed G] :
    Shape (fun X => X k → G X) where
  cond {X} _ f := Cont (inst_1 := Shape.dom (F := G) X) f ∧ ∀ d, Shape.cond (f d)
  sd := Model.Shape.arr k G
/-- Two fields. -/
instance Shape.prod (F : Fam.{pu, v} I → Type w₁) (G : Fam.{pu, v} I → Type w₂) [Shape F] [Shape G] :
    Shape (fun X => F X ×' G X) where
  cond x := Shape.cond x.1 ∧ Shape.cond x.2
  sd := Model.Shape.prod F G

/-! `Shape.Pointed F`: the bodies allowed under a binder.  Every plain field of `F`, at any depth, has
a pointed type: no `Shape.data` field and no plain field of a structure of the group.  For a whole
structure, this is the set of structures that consist of methods and plain fields of pointed type. -/

instance (A : Type w) [Dom A] [Pointed A] : Shape.Pointed (fun _ : Fam.{pu, v} I => A) := ⟨Proofs.pointed_const A⟩
instance (T : Type w₁) (G : T → Fam.{pu, v} I → Type w₂) [∀ t, Shape (G t)] [∀ t, Shape.Pointed (G t)] :
    Shape.Pointed (fun X => (t : T) → G t X) := ⟨Proofs.pointed_pi T G⟩
instance (k : I) (G : Fam.{pu, v} I → Type w) [Shape G] [Shape.Pointed G] :
    Shape.Pointed (fun X => X k → G X) := ⟨Proofs.pointed_arr k G⟩
instance (F : Fam.{pu, v} I → Type w₁) (G : Fam.{pu, v} I → Type w₂) [Shape F] [Shape G]
    [Shape.Pointed F] [Shape.Pointed G] : Shape.Pointed (fun X => F X ×' G X) := ⟨Proofs.pointed_prod F G⟩
end Shapes

/-! ## 3. The fixed point

`Fix F k` is the structure `k` (a structure of the group at its parameters).  A body `x : F k (Fix F)`
satisfying the condition folds into it, and unfolding gives it back.  When `⊥` is total in it
(`Fix.BotTotal`: every plain field of structure `k` is pointed, or is a structure of the group in
which `⊥` is total), it is pointed and a `Lean.Order.CCPO`, so self-referential instances can be
defined with `partial_fixpoint`. -/

/-- The runtime value of every generated `Shape` instance (assumption 3 below: it is never read). -/
@[instance_reducible] unsafe def Shape.runtime {I : Type pu} {F : Fam.{pu, v} I → Type w} : Shape F := unsafeCast ()

section Fix
variable {I : Type pu} (F : I → Fam.{pu, v} I → Type v) [∀ k, Shape (F k)]

instance (k : I) : Dom (Fix F k) := Fix.dom F k

/-! `fold` and `unfold`, and how they run.

In the logic, `fold` and `unfold` are the model's (`Model.Fix.fold`, `Model.Fix.unfold`), and a
dictionary is an element of an inverse-limit domain.  Compiled code never builds that: at runtime a
dictionary is stored as a `Thunk` of the tuple of its fields.  So `fold` stores the tuple
`x : F k (Fix F)` without evaluating it (only its static type changes to `Fix F k`), and `unfold`
forces it (and changes the type back).  The work of `fold` is all in the logic: proving
`Shape.cond x`, and `Fix.unfold_fold` below, which says that unfolding gives back the same tuple.

Why delayed: a self-referential dictionary `d := mk … (f d) …` (defined by `partial_fixpoint`) is
compiled by Lean as a recursive constant, and a field such as `f d` that mentions `d` outside a
lambda would otherwise be evaluated while `d` is being built, which loops.  `fold` and the
generated `mk` are `@[macro_inline]`, so at a call site the tuple ends up under the lambda that
`fold` passes to `foldDelayed`, and is evaluated only when the dictionary is first unfolded.

Compiled code is correct under these assumptions:
1. Every dictionary that exists at runtime was made by `fold`.  This holds because every other
   construction of a value of `Fix F k` (the model's constructions, including the suprema behind
   its `CCPO`) is noncomputable, so the compiler rejects any program that uses one.  A
   self-referential dictionary defined by `partial_fixpoint` is compiled by Lean as a recursive
   definition whose body is a `fold`, so it too is made by `fold`.
2. Compiled code reads a dictionary only through `unfold`.  This holds because the only code that
   uses the model's representation of `Fix F k` is the model, which is never compiled.
3. Compiled code never reads a `Shape` instance.  This holds because its field `cond` is a `Prop`
   and its field `sd` is read only by the model.  The command therefore gives each generated
   `Shape` instance the runtime implementation `Shape.runtime`, which is never inspected.
Under 1 and 2, the dictionary `unfold` receives is a `Thunk` of the tuple `x` that `fold` was given,
and forcing it gives `x`, which is also the logical value of `unfold (fold x h)` by
`Fix.unfold_fold`; so compiled projections compute their logical values. -/

unsafe def Fix.foldDelayedImpl {k : I} (x : Unit → F k (Fix F)) (_ : Shape.cond (x ())) : Fix F k :=
  unsafeCast (Thunk.mk x)
unsafe def Fix.unfoldImpl {k : I} (d : Fix F k) : F k (Fix F) := (unsafeCast d : Thunk (F k (Fix F))).get
/-- `fold` of the tuple `x ()`; at runtime, `x` is stored in a `Thunk` without being called. -/
@[implemented_by Fix.foldDelayedImpl]
noncomputable def Fix.foldDelayed {k : I} (x : Unit → F k (Fix F)) (h : Shape.cond (x ())) : Fix F k :=
  Model.Fix.fold F (x ()) h
@[macro_inline]
def Fix.fold {k : I} (x : F k (Fix F)) (h : Shape.cond x) : Fix F k := Fix.foldDelayed F (fun _ => x) h
@[implemented_by Fix.unfoldImpl]
noncomputable def Fix.unfold {k : I} (d : Fix F k) : F k (Fix F) := Model.Fix.unfold F d

theorem Fix.cond {k : I} (d : Fix F k) : Shape.cond (Fix.unfold F d) := Model.Fix.cond F d
theorem Fix.unfold_fold {k : I} (x : F k (Fix F)) (h : Shape.cond x) :
    Fix.unfold F (Fix.fold F x h) = x := Proofs.unfold_fold F x h

/-! `Shape.BotTotal F G` and `Fix.BotTotal F k`: the structures that are `CCPO`s, so that
`partial_fixpoint` can define self-referential instances of them.  A
structure of group `F` is in this set when each of its plain fields is of pointed type or is a
structure of the group that is itself in the set; `Shape.BotTotal F G` says the same of a body `G`.
This is larger than `Shape.Pointed`, which does not admit plain dictionary fields. -/
instance (G : Fam.{pu, v} I → Type w) [Shape G] [Shape.Pointed G] : Shape.BotTotal F G := Shape.BotTotal.ofPointed F G
instance (G₁ : Fam.{pu, v} I → Type w) (G₂ : Fam.{pu, v} I → Type w₁) [Shape G₁] [Shape G₂]
    [Shape.BotTotal F G₁] [Shape.BotTotal F G₂] : Shape.BotTotal F (fun X => G₁ X ×' G₂ X) := ⟨Proofs.botTotal_prod F G₁ G₂⟩
instance (k : I) [Fix.BotTotal F k] : Shape.BotTotal F (fun X => X k) := ⟨Proofs.botTotal_var F k⟩
instance (k : I) [Shape.BotTotal F (F k)] : Fix.BotTotal F k := Fix.BotTotal.ofShape F k
instance (k : I) [Fix.BotTotal F k] : Pointed (Fix F k) := Fix.pointed F
instance (k : I) [Fix.BotTotal F k] : Lean.Order.CCPO (Fix F k) := Fix.ccpo F k
end Fix

/-! ## 4. The `nonpos_structure` command

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
* `G.F : G.I → Fam G.I → Type 1`, dispatching to the `Fields`;
* `Bla Self := Fix G.F (.Bla Self)`;
* `Bla.mk to_num add (h : Shape.cond ⟨to_num, add, ⟨⟩⟩) := Fix.fold G.F _ h`;
* `Bla.to_num d := (Fix.unfold G.F d).1`, `Bla.add d := (Fix.unfold G.F d).2.1`, each with the
  type as written, and the `simp` lemmas `Bla.to_num_mk`, `Bla.add_mk`.

The command never inspects the field types: `Shape (G.F k)` is found by instance search, which can
only succeed through the instances of section 2, and the types of `mk` and the projections are the
user's own, checked by the kernel against `Fix`. -/

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
  elabCommand (← `(noncomputable abbrev $fId : $idx → Fam $idx → $univ $fAlts:matchAlt*))
    -- `Example1.F`, `A.F`
  let shapeAlts ← ss.mapM fun s => do
    `(Parser.Term.matchAltExpr| | $(← idxOf s) => inferInstance)
  elabCommand (← `(@[reducible] noncomputable instance $shapeId:ident : ∀ k, Shape ($fId k) $shapeAlts:matchAlt*))
    -- `Example1.shape`, `A.shape`
  -- its runtime implementation, which is never read (assumption 3 of section 3)
  let shapeImplId := mkIdentFrom g (g.getId ++ `shapeImpl)
  elabCommand (← `(@[instance_reducible] unsafe def $shapeImplId : ∀ k, Shape ($fId k) := fun _ => Shape.runtime))
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
    let fieldNames := s.fields.map (·.1)                        -- `fa`                   `to_nat f`
    let mkId := mkIdentFrom s.name (s.name.getId ++ `mk)        -- `A.mk`                 `Example1.mk`
    -- `macro_inline`, so that the fields are not evaluated before `fold` delays them (section 3)
    elabCommand (← `(@[macro_inline] def $mkId $impl* $fieldBinders*
        (h : Shape.cond (F := $fId $k) (X := Fix $fId) $fieldTuple) : $(s.name):ident $args* :=
      Fix.fold $fId $fieldTuple h))  -- `Example1.mk`, `A.mk`, `B.mk`
    for (f, τ) in s.fields, j in List.range s.fields.size do
      let projId := mkIdentFrom f (s.name.getId ++ f.getId)                   -- `A.fa`       `Example1.to_nat`
      let lemId := mkIdentFrom f (s.name.getId ++ f.getId.appendAfter "_mk")   -- `A.fa_mk`    `Example1.to_nat_mk`
      elabCommand (← `(def $projId $impl* (d : $(s.name):ident $args*) : $τ :=
        no_implicit_lambda% $(← projN (← `(Fix.unfold $fId d)) j)))  -- `Example1.to_nat`, `Example1.f`, `A.fa`, `B.fb`
      elabCommand (← `(@[simp] theorem $lemId $impl* $fieldBinders*
          (h : Shape.cond (F := $fId $k) (X := Fix $fId) $fieldTuple) :
          @$projId $args* ($mkId $fieldNames* h) = @$f:ident := by
        simp only [$projId:ident, $mkId:ident, Fix.unfold_fold]))  -- `Example1.to_nat_mk`, `Example1.f_mk`, `A.fa_mk`, `B.fb_mk`

@[command_elab nonposStructure] meta def elabNonposStructure : CommandElab := fun stx => do
  elabGroup #[← parseStruct stx]

/-- `mutual nonpos_structure ... nonpos_structure ... end`. -/
@[command_elab Lean.Parser.Command.«mutual»] meta def elabNonposMutual : CommandElab := fun stx => do
  let cmds := stx[1].getArgs
  unless cmds.size > 0 && cmds.all (·.isOfKind ``nonposStructure) do throwUnsupportedSyntax
  elabGroup (← cmds.mapM parseStruct)

/-! ## 5. The forms

Everything the `nonpos_cont` tactic knows is one of the statements below, all of the shape
`Cont (fun d => ‹form›)`.  `D` is the type of the varying dictionary (or tuple of dictionaries).
The list `forms` after the theorems is what the tactic looks up by shape; `const`, `id`, `lam`,
`app` and `app₂` have no shape to look up and are the tactic's own cases.  Continuity facts proved
elsewhere (a monad's own operations, helper functions) are added to the same lookup with the
`@[nonpos_continuous]` attribute, declared at the end of this section. -/


section Cont
variable {D : Type w} [Dom D]

theorem Cont.const {B : Type w₁} [Dom B] (b : B) : Cont (fun _ : D => b) := Proofs.Cont.const b
theorem Cont.id : Cont (fun d : D => d) := Proofs.Cont.id
/-- Lambda: pointwise. -/
theorem Cont.lam {T : Type w₁} {B : T → Type w₂} [∀ t, Dom (B t)] {f : D → (t : T) → B t}
    (h : ∀ t, Cont (fun d => f d t)) : Cont f := Proofs.Cont.lam h
/-- Application to an argument not depending on `d` (a type, a value, a fixed dictionary, ...). -/
theorem Cont.app {T : Type w₁} {B : T → Type w₂} [∀ t, Dom (B t)] {f : D → (t : T) → B t}
    (hf : Cont f) (t : T) : Cont (fun d => f d t) := Proofs.Cont.app hf t
/-- Application to an argument depending on `d`: the function must satisfy the condition. -/
theorem Cont.app₂ {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] {f : D → A → B} {a : D → A}
    (hf : Cont f) (hc : ∀ d, Cont (f d)) (ha : Cont a) : Cont (fun d => f d (a d)) := Proofs.Cont.app₂ hf hc ha
/-- Pairs: the field tuples of a structure, and what a mutual `partial_fixpoint` is packed into. -/
theorem Cont.pair {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] {f : D → A} {g : D → B}
    (hf : Cont f) (hg : Cont g) : Cont (fun d => (⟨f d, g d⟩ : A ×' B)) := Proofs.Cont.pair hf hg
theorem Cont.fst {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] {f : D → A ×' B} (hf : Cont f) :
    Cont (fun d => (f d).1) := Proofs.Cont.fst hf
theorem Cont.snd {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] {f : D → A ×' B} (hf : Cont f) :
    Cont (fun d => (f d).2) := Proofs.Cont.snd hf
theorem Cont.ite {B : Type w₁} [Dom B] (c : Prop) [Decidable c] {t e : D → B}
    (ht : Cont t) (he : Cont e) : Cont (fun d => if c then t d else e d) := Proofs.Cont.ite c ht he
theorem Cont.dite {B : Type w₁} [Dom B] (c : Prop) [Decidable c] {t : c → D → B} {e : ¬c → D → B}
    (ht : ∀ h, Cont (t h)) (he : ∀ h, Cont (e h)) : Cont (fun d => if h : c then t h d else e h d) :=
  Proofs.Cont.dite c ht he
/-- `pure`, `bind`: this is what a supported monad provides. -/
theorem Cont.pure {M : Type u → Type u} [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] {α : Type u} {a : D → α}
    (ha : Cont (inst_1 := Dom.discrete α) a) : Cont (fun d => (pure (a d) : M α)) := Proofs.Cont.pure ha
theorem Cont.bind {M : Type u → Type u} [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] {α β : Type u}
    {m : D → M α} {k : D → α → M β}
    (hm : Cont m) (hk : ∀ a, Cont (fun d => k d a)) : Cont (fun d => m d >>= k d) := Proofs.Cont.bind hm hk

variable {I : Type pu} (F : I → Fam.{pu, v} I → Type v) [∀ k, Shape (F k)]
/-- Projections out of a structure, and `mk` of fields depending on `d`. -/
theorem Cont.unfold {k : I} {f : D → Fix F k} (hf : Cont f) :
    Cont (inst_1 := Shape.dom (F := F k) (Fix F)) (fun d => Fix.unfold F (f d)) := Proofs.Cont.unfold F hf
theorem Cont.fold {k : I} {f : D → F k (Fix F)} (h : ∀ d, Shape.cond (f d))
    (hf : Cont (inst_1 := Shape.dom (F := F k) (Fix F)) f) : Cont (fun d => Fix.fold F (f d) (h d)) :=
  Proofs.Cont.fold F h hf

/-- Fixed points: `partial_fixpoint` elaborates to `Lean.Order.fix`, for functions and for
self-referential dictionaries alike. -/
theorem Cont.fix {α : Type w₁} [Dom α] [Lean.Order.CCPO α] [FixCompat α] {f : D → α → α}
    {hm : ∀ d, Lean.Order.monotone (f d)}
    (hf : Cont (fun p : D ×' α => f p.1 p.2)) : Cont (fun d => Lean.Order.fix (f d) (hm d)) := Proofs.Cont.fix hf
end Cont

/-! `FixCompat α`: the `Dom` and `CCPO` structures on `α` agree.  Holds for `M α`, pointwise, and on
products: exactly the types `partial_fixpoint` recurses through. -/
instance {M : Type u → Type u} [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] (α : Type u) : FixCompat (M α) :=
  FixCompat.monad α
instance {T : Type w₁} {B : T → Type w₂} [∀ t, Dom (B t)] [∀ t, Lean.Order.CCPO (B t)] [∀ t, FixCompat (B t)] :
    FixCompat ((t : T) → B t) := FixCompat.pi
instance {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] [Lean.Order.CCPO A] [Lean.Order.CCPO B]
    [FixCompat A] [FixCompat B] : FixCompat (A ×' B) := FixCompat.pprod
instance {I : Type pu} (F : I → Fam.{pu, v} I → Type v) [∀ k, Shape (F k)] (k : I) [Fix.BotTotal F k] :
    FixCompat (Fix F k) := Fix.fixCompat F k

/-- `partial_fixpoint`'s monotonicity obligation, from the condition: write a self-referential
instance as `def inst : Bla Int := Bla.mk … partial_fixpoint monotonicity Cont.monotone (by nonpos_cont)`. -/
theorem Cont.monotone {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] [Lean.Order.CCPO A] [Lean.Order.CCPO B]
    [FixCompat A] [FixCompat B] {f : A → B} (h : Cont f) : Lean.Order.monotone f := Proofs.Cont.monotone h

/-- The forms the tactic looks up by the shape of the body. -/
meta def forms : List Name :=
  [``Cont.pair, ``Cont.fst, ``Cont.snd, ``Cont.ite, ``Cont.dite,
   ``Cont.pure, ``Cont.bind, ``Cont.unfold, ``Cont.fold, ``Cont.fix]

/-- Gets a DiscrTree key from a theorem name.
Works for theormes that return `… → Cont (fun d => body)` -/
meta def contKeys (declName : Name) : MetaM (Array DiscrTree.Key) := do
  let (_, _, concl) ← forallMetaTelescopeReducing (← inferType (← mkConstWithLevelParams declName))
  let_expr Cont D _ _ _ f := concl | throwError "{declName}: not a `Cont` statement"
  DiscrTree.mkPath (f.beta #[← mkFreshExprMVar D])

/-- The store of tagged theorems: a discrimination tree of their names, keyed by `contKeys`. -/
meta initialize nonposContExt : SimpleScopedEnvExtension (Array DiscrTree.Key × Name) (DiscrTree Name) ←
  registerSimpleScopedEnvExtension { addEntry := fun t (ks, n) => t.insertKeyValue ks n, initial := {} }

/-- `@[nonpos_continuous]` on a theorem `… → Cont (fun d => body)` adds it to the store, keyed by the
shape of `body`.  (It can be used in any file importing this one, but not in this file.) -/
meta initialize registerBuiltinAttribute {
  name := `nonpos_continuous
  descr := "continuity theorem, applied by `nonpos_cont`"
  add := fun decl _ kind => do nonposContExt.add (← MetaM.run' (contKeys decl), decl) kind }

/-- Get continuity lemmas from `forms` and `@[nonpos_continuous]` tagged theorems. -/
meta def getContTheorems : MetaM (DiscrTree Name) := do
  forms.foldlM (init := nonposContExt.getState (← getEnv)) fun t n => return t.insertKeyValue (← contKeys n) n

/-! ## 6. The tactic

`nonpos_cont` on a goal `Cont (fun d => body)` looks up the forms and tagged theorems whose shape is
that of `body` (`getContTheorems`) and applies the first that fits.  The forms without a
shape to index are handled directly: a body not depending on `d` is `Cont.const`, a lambda is
`Cont.lam`, and an application with no matching form is peeled by `Cont.app` (last argument not
depending on `d`) or `Cont.app₂` (last argument depending on `d`; the function is then a projection
of a dictionary, whose condition comes from `Fix.cond`).  A `match` on a scrutinee not depending on
`d` is split by `cases`, and a remaining definition is unfolded (`delta`).  Around this, the loop
introduces binders, turns a `Shape.cond` goal into its conjuncts with `nonpos_cond_simp`, and splits
conjunctions. -/

/-- Inputs an application of `Shape.cond`, and unfolds the functor and Shape instance arguments
so they can be matched against. -/
meta def normCond (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  let_expr Shape.cond I F inst X instX x := e | return e
  let F' ← lambdaTelescope (← whnfR F) fun xs b => do mkLambdaFVars xs (← whnfR b)
  return mkAppN (.const ``Shape.cond e.getAppFn.constLevels!) #[I, F', ← whnfR inst, X, instX, x]

open Tactic in
elab "nonpos_cond_norm" : tactic => withMainContext do
  let mut g ← getMainGoal
  g ← g.change (← normCond (← g.getType))
  for d in ← getLCtx do
    if !d.isImplementationDetail && (← instantiateMVars d.type).isAppOf ``Shape.cond then
      g ← g.changeLocalDecl d.fvarId (← normCond d.type)
  replaceMainGoal [g]

/-- Simplify `Shape.cond` conditions into a conjunction of `Cont` facts, one for each dictionary
binder, dropping the clauses that are `True`.  First `nonpos_cond_norm` rewrites every `Shape.cond`
in the goal and hypotheses (by definitional unfolding, checked by `change`) so that its functor is a
literal lambda and its instance is built from the pieces of section 2; then `simp` unfolds the `cond`
of each piece. -/
macro "nonpos_cond_simp" loc:(Parser.Tactic.location)? : tactic =>
  `(tactic| (nonpos_cond_norm; simp only [Shape.cond, Shape.prod, Shape.pi, Shape.arr, Shape.data, Shape.const,
      Shape.var, true_and, and_true, implies_true, forall_and] $[$loc]?))

/-- `Cont (projection of the dictionary `e`)`, from `Fix.cond e`. -/
macro "nonpos_proj" e:term : tactic =>
  `(tactic| (have h := Fix.cond _ $e; nonpos_cond_simp at h; solve_by_elim [And.left, And.right]))

syntax "nonpos_cont" (num)? : tactic
syntax "nonpos_cont_peel" : tactic

open Tactic in
/-- One step on a goal `Cont (fun d => body)`. -/
meta partial def nonposContStep (tree : DiscrTree Name) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let_expr Cont _ _ _ _ f := ty | throwError "nonpos_cont: not a `Cont` goal:{indentExpr ty}"
  let f ← instantiateMVars f
  let f ← if f.isLambda then pure f else etaExpand f
  let tac ← lambdaTelescope f fun ds body => do
    let d := ds[0]!
    let body := body.consumeMData.headBeta
    let dep (e : Expr) := e.containsFVar d.fvarId!
    if !dep body then return ← `(tactic| exact Cont.const _)
    if ds.size > 1 || body.isLambda then return ← `(tactic| apply Cont.lam)
    if body == d then return ← `(tactic| exact Cont.id)
    if body.isLet then return ← `(tactic| dsimp only)
    if let some info := Meta.isMatcherAppCore? (← getEnv) body then
      let disc := body.getAppArgs[info.getFirstDiscrPos]!
      if !dep disc then
        if disc.isFVar then
          return ← `(tactic| cases $(mkIdent (← disc.fvarId!.getUserName)):ident <;> dsimp only)
        return ← `(tactic| (generalize $(← Term.exprToSyntax disc) = x; cases x <;> dsimp only))
    -- the forms and tagged theorems with the shape of the body
    let pattern := body.replaceFVar d (← mkFreshExprMVar (← inferType d))
    let alts ← (← tree.getMatch pattern).mapM fun n => `(tacticSeq| apply $(mkIdent n):ident)
    `(tactic| first $[| $alts]* | nonpos_cont_peel)
  evalTactic tac

open Tactic in
/-- Peel the last argument of an application, or unfold its head. -/
elab_rules : tactic
  | `(tactic| nonpos_cont_peel) => withMainContext do
    let g ← getMainGoal
    let ty ← instantiateMVars (← g.getType)
    let_expr Cont _ _ _ _ f := ty | throwError "nonpos_cont: not a `Cont` goal"
    let env ← getEnv
    let f ← instantiateMVars f
    let f ← if f.isLambda then pure f else etaExpand f
    let tac ← lambdaTelescope f fun ds body => do
      let d := ds[0]!
      let body := body.consumeMData.headBeta
      let dep (e : Expr) := e.containsFVar d.fvarId!
      let stx (e : Expr) : TacticM Term := do Term.exprToSyntax (← mkLambdaFVars #[d] e)
      let isProj (e : Expr) := e.isAppOfArity ``Fix.unfold 5
      let fn := body.getAppFn
      let args := body.getAppArgs
      let unfoldable := fn.constName?.bind fun c => if (env.find? c).any (·.hasValue) then some c else none
      if args.isEmpty then throwError "nonpos_cont: no form matches {← ppExpr body}"
      let a := args.back!
      let fn' := mkAppN fn args.pop
      if !dep a then
        return ← `(tactic| apply Cont.app (f := $(← stx fn')) (t := $(← Term.exprToSyntax a)))
      if let some u := fn'.find? isProj then
        if a == d && !dep u then return ← `(tactic| nonpos_proj $(← Term.exprToSyntax u.appArg!))
        return ← `(tactic| refine Cont.app₂ (f := $(← stx fn')) (a := $(← stx a)) ?_ (by intro _; nonpos_cont) ?_)
      if let some c := unfoldable then return ← `(tactic| delta $(mkIdent c):ident)
      if a == d then throwError "nonpos_cont: continuity of {← ppExpr fn'} is not known"
      if !dep fn' then
        return ← `(tactic| refine Cont.app₂ (f := $(← stx fn')) (a := $(← stx a)) ?_ (by intro _; nonpos_cont) ?_)
      return ← `(tactic| apply Cont.app₂ (f := $(← stx fn')) (a := $(← stx a)))
    evalTactic tac

open Tactic in
meta partial def nonposContLoop (tree : DiscrTree Name) (fuel : Nat) : TacticM Unit := do
  let gs ← getUnsolvedGoals
  let some g := gs[0]? | return
  if fuel == 0 then throwError "nonpos_cont: no progress on{indentD (← g.withContext do Meta.ppGoal g)}"
  setGoals [g]
  let ty ← g.withContext do whnfR (← instantiateMVars (← g.getType))
  if ty.isForall then evalTactic (← `(tactic| intro))
  else if ty.isAppOf ``Shape.cond then evalTactic (← `(tactic| nonpos_cond_simp))
  else if ty.isAppOf ``Cont then
    try evalTactic (← `(tactic| assumption)) catch _ => nonposContStep tree
  else if ty.isConstOf ``True then evalTactic (← `(tactic| trivial))
  else if ty.isAppOf ``And then evalTactic (← `(tactic| constructor))
  else throwError "nonpos_cont: unexpected goal{indentExpr ty}"
  let gs' ← getUnsolvedGoals
  setGoals (gs' ++ gs.drop 1)
  nonposContLoop tree (fuel - 1)

elab_rules : tactic
  | `(tactic| nonpos_cont) => do nonposContLoop (← getContTheorems) 300
  | `(tactic| nonpos_cont $n:num) => do nonposContLoop (← getContTheorems) n.getNat

/-! ## 7. Axioms

Everything above, with its proofs and model, uses only the standard axioms (no `sorry`, no
axiom of the library's own).  The build fails if this changes. -/

/-- info: 'NonPos.Fix.unfold_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fix.unfold_fold
/-- info: 'NonPos.Cont.fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cont.fold
/-- info: 'NonPos.Cont.fix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cont.fix
/-- info: 'NonPos.Cont.bind' depends on axioms: [Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cont.bind
/-- info: 'NonPos.Cont.monotone' does not depend on any axioms -/
#guard_msgs in #print axioms Cont.monotone

end
end NonPos
