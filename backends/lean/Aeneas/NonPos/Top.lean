module
public import Lean
public import Aeneas.NonPos.Proofs

@[expose] public section
/-!
# `nonpos_structure`: the top-level file

This file is the whole trusted surface of the library.  It contains, and only contains:

1. the *statements* that pin down the imported constants (`Dom`, `Cont`, `Shape`, `Fix`, ...);
2. the `nonpos_structure` command, a thin wrapper around `Fix`;
3. what the `nonpos_cont` tactic, which proves the condition of each structure, is expected to do
   (section 5).

Proofs live in `NonPos/Proofs.lean` and the definitions of the constants in `NonPos/Model/`;
neither needs to be read.  Every theorem below is proved by a one-line reference to `Proofs`.  The
tactic is in `NonPos/Tactic.lean`, which does not need to be read either.
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

/-! `fixRec`: a self-referential dictionary, defined with `partial_fixpoint` once here (in
`fixRecCore`), so that the self-referential impls are plain definitions `fixRec (fun self => mk …) hf`.
The recursive call is under `foldDelayed`, so Lean's compiled code for it (assumption 1) is
evaluated only when the dictionary is unfolded.  Logically `fixRec body hf` is the least fixed point
of `fold ∘ unfold ∘ body`, which is `body` when `body` is a `mk` (by `Fix.unfold_fold`);
`Fix.unfold_fixRec` is what projections use.

`fixRecCore` takes the tuple of fields `x self`, not the dictionary `body self`: the compiler sees
through `Fix F k` to a function type, so it would compile a lambda returning a dictionary with more
arguments than `fixRecCore` applies it to.  `fixRec` is `@[macro_inline]`, so that this lambda is
built at the call site, where `unfold` of the `mk` is a tuple. -/
def Fix.fixRecCore {k : I} [Fix.BotTotal F k] (x : Fix F k → F k (Fix F)) (h : ∀ d, Shape.cond (x d))
    (hx : Cont (inst_1 := Shape.dom (F := F k) (Fix F)) x) : Fix F k :=
  Fix.foldDelayed F (fun _ => x (Fix.fixRecCore x h hx)) (h _)
partial_fixpoint monotonicity by
  letI : FixCompat (Fix F k) := Fix.fixCompat F k
  exact Proofs.Cont.monotone (Proofs.Cont.fold F h hx)
@[macro_inline]
def Fix.fixRec {k : I} [Fix.BotTotal F k] (body : Fix F k → Fix F k) (hf : Cont body) : Fix F k :=
  Fix.fixRecCore F (fun d => Fix.unfold F (body d)) (fun d => Fix.cond F (body d)) (Proofs.Cont.unfold F hf)
theorem Fix.fixRec_eq {k : I} [Fix.BotTotal F k] (body : Fix F k → Fix F k) (hf : Cont body) :
    Fix.fixRec F body hf = Fix.fold F (Fix.unfold F (body (Fix.fixRec F body hf))) (Fix.cond F _) :=
  Fix.fixRecCore.eq_1 F _ _ _
theorem Fix.unfold_fixRec {k : I} [Fix.BotTotal F k] (body : Fix F k → Fix F k) (hf : Cont body) :
    Fix.unfold F (Fix.fixRec F body hf) = Fix.unfold F (body (Fix.fixRec F body hf)) :=
  (congrArg (Fix.unfold F) (Fix.fixRec_eq F body hf)).trans (Fix.unfold_fold F _ _)
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
  type as written, and the `simp` lemmas `Bla.to_num_mk`, `Bla.add_mk` (a projection of `mk` is
  the field), stated here and proved by the tactic `nonpos_proj_mk` of `NonPos/Tactic.lean`;
* then, through the hook of section 5, the lemmas of `NonPos/Tactic.lean` (section 4 there).

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
    let mkId := mkIdentFrom s.name (s.name.getId ++ `mk)        -- `A.mk`                 `Example1.mk`
    -- `macro_inline`, so that the fields are not evaluated before `fold` delays them (section 3)
    elabCommand (← `(@[macro_inline] def $mkId $impl* $fieldBinders*
        (h : Shape.cond (F := $fId $k) (X := Fix $fId) $fieldTuple) : $(s.name):ident $args* :=
      Fix.fold $fId $fieldTuple h))  -- `Example1.mk`, `A.mk`, `B.mk`
    for (f, τ) in s.fields, j in List.range s.fields.size do
      let projId := mkIdentFrom f (s.name.getId ++ f.getId)                   -- `A.fa`       `Example1.to_nat`
      elabCommand (← `(def $projId $impl* (d : $(s.name):ident $args*) : $τ :=
        no_implicit_lambda% $(← projN (← `(Fix.unfold $fId d)) j)))  -- `Example1.to_nat`, `Example1.f`, `A.fa`, `B.fb`

/-! The `simp` lemmas of the projections, `Bla.f_mk : Bla.f (Bla.mk f₁ … fₙ h) = f` for each field
`f`: their statements are built here, from the type of `mk`; their proofs are by the tactic
`nonpos_proj_mk`, which `NonPos/Tactic.lean` implements (it has no implementation here), and are
checked by the kernel. -/

syntax "nonpos_proj_mk" : tactic

/-- `Bla.f_mk` for each field `f` of each structure `Bla` of a group made by `elabGroup`. -/
meta def elabMkLemmas (ss : Array StructStx) : CommandElabM Unit := liftTermElabM do
  for s in ss do
    let bla := (← getCurrNamespace) ++ s.name.getId
    let mkInfo ← getConstInfo (bla ++ `mk)
    forallTelescope mkInfo.type fun xs _ => do  -- `xs` is `ps f₁ … fₙ h`
      let ps := xs.extract 0 (xs.size - s.fields.size - 1)
      let mk ← mkConstWithLevelParams (bla ++ `mk)
      for (f, _) in s.fields, fj in xs.extract ps.size (xs.size - 1) do
        -- `Bla.f ps (Bla.mk ps f₁ … fₙ h) = fⱼ`, proved by `nonpos_proj_mk`, then closed over `xs`
        let eq ← mkEq (mkAppN (← mkConstWithLevelParams (bla ++ f.getId)) (ps.push (mkAppN mk xs))) fj
        let pf ← mkFreshExprSyntheticOpaqueMVar eq
        let [] ← Tactic.run pf.mvarId! (Tactic.evalTactic (← `(tactic| nonpos_proj_mk)))
          | throwError "nonpos_proj_mk did not prove{indentExpr eq}"
        let name := bla ++ f.getId.appendAfter "_mk"
        let type ← mkForallFVars xs eq
        let value ← mkLambdaFVars xs (← instantiateMVars pf)
        addDecl (Declaration.thmDecl { name := name, levelParams := mkInfo.levelParams, type, value })
        addSimpTheorem simpExtension name (post := true) (inv := false) .global (eval_prio default)

/-! ## 5. Continuity, and the `nonpos_cont` tactic

The condition `Shape.cond` of a structure is a conjunction of `Cont` facts, one for each field that
takes a dictionary of the group (`nonpos_cond_simp`, in `NonPos/Tactic.lean`, unfolds it into
them).  Aeneas proves the condition of each `mk` it outputs with the tactic `nonpos_cont`, and the
monotonicity obligation of each self-referential instance with
`partial_fixpoint monotonicity Cont.monotone (by nonpos_cont)`.

The tactic and the continuity theorems it applies are in `NonPos/Tactic.lean`, which is not part of
the trusted surface: every proof it builds is checked by the kernel, so it cannot make a structure
contain anything that does not satisfy the condition.  What it is expected to do, which is checked
by its tests but not guaranteed by this file, is:

* **Completeness:** `nonpos_cont` proves `Cont f` for every function `f` that Aeneas outputs (that
  is, the conditions above), in reasonable time.
* **Lemmas:** a theorem `… → Cont (fun d => body)` tagged `@[nonpos_continuous]` is applied by
  `nonpos_cont` to any goal of the shape of `body`, instead of proving it again from the definitions
  in `body`.  Lemmas are tagged by `nonpos_continuity f` (which Aeneas outputs after each function
  `f` taking a dictionary, and which proves the continuity of `f` in that dictionary), by the hook
  below, and by hand (the operations of a monad).

The hook: after the definitions of a group, `nonpos_structure` runs `nonpos_structure_lemmas` on the
same structures.  Here it does nothing; `NonPos/Tactic.lean` makes it prove lemmas about the
structures (section 4 there), so that `nonpos_cont` does not derive them at each use.  It runs
after every definition of the group is made, so it can only add facts about them: theorems, and
instances of classes that are `Prop`s. -/

syntax (name := nonposStructureLemmas) "nonpos_structure_lemmas " nonposStructureCore* : command

/-- The hook, empty here (see `NonPos/Tactic.lean`). -/
@[command_elab nonposStructureLemmas] meta def elabNonposStructureLemmasNone : CommandElab := fun _ =>
  pure ()

/-- Elaborate a group and its `simp` lemmas, then run the hook on it. -/
meta def elabGroupAndLemmas (stxs : Array Syntax) : CommandElabM Unit := do
  let ss ← stxs.mapM parseStruct
  elabGroup ss
  elabMkLemmas ss
  elabCommand (mkNode ``nonposStructureLemmas #[mkAtom "nonpos_structure_lemmas ", mkNullNode (stxs.map (·[0]))])

@[command_elab nonposStructure] meta def elabNonposStructure : CommandElab := fun stx =>
  elabGroupAndLemmas #[stx]

/-- `mutual nonpos_structure ... nonpos_structure ... end`. -/
@[command_elab Lean.Parser.Command.«mutual»] meta def elabNonposMutual : CommandElab := fun stx => do
  let cmds := stx[1].getArgs
  unless cmds.size > 0 && cmds.all (·.isOfKind ``nonposStructure) do throwUnsupportedSyntax
  elabGroupAndLemmas cmds

/-! ## 6. Axioms

Everything above, with its proofs and model, uses only the standard axioms (no `sorry`, no
axiom of the library's own).  The build fails if this changes. -/

/-- info: 'NonPos.Fix.unfold_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fix.unfold_fold

end
end NonPos
