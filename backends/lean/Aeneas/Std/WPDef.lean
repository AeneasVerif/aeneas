module
public import Aeneas.Std.Primitives
public import Aeneas.Data.Coinductive.ITree
public import Aeneas.Data.Coinductive.Effect
public import Aeneas.Data.Coinductive.ITreeWP
public import Aeneas.SepLogic.IProp
public import Aeneas.SepLogic.Lemmas
public section

namespace Aeneas.Std.WP

open Std Result
open Aeneas.Data.Coinductive
open Aeneas.SepLogic

@[expose] def Post α := (α -> Prop)
@[expose] def Pre := Prop

@[expose] def Wp α := Post α → Pre

@[expose] def wp_return (x:α) : Wp α := fun p => p x

section ResultImplementation

unseal Result

@[expose] section

@[reducible]
def effectWP : EffectWP RustEffect where
  State := Heap
  wp effect C h :=
    match effect with
    | .guardedModify _ pre modify =>
        ∃ hPre : pre h, C (.up (modify h hPre).1) (modify h hPre).2
    | .fail _ => False

instance : EffectWP.Monotone effectWP where
  wp_mono {effect} _ _ hC _ hEvent := by
    cases effect with
    | guardedModify => exact hEvent.imp fun _ hNext => hC _ _ hNext
    | fail => exact hEvent.elim

abbrev rawIwp (total:Bool) (m : Result α) (Q : IPost α) (h : Heap) : Prop :=
  if total then DWP effectWP m (fun value h' => Q value h') h
  else DWLP effectWP m (fun value h' => Q value h') h

def iwp (total:Bool) (m : Result α) (Q : IPost α) : IProp where
  holds owned :=
    ∀ F h, (owns owned ∗ F) h → rawIwp total m (Q ∗+ F) h
  up_closed hWp hSub F h hPre :=
    hWp F h (sep_mono
      (fun _ hOwns => hSub.trans hOwns)
      (entails_refl F) h hPre)

/-- Total-correctness separation-logic specification -/
def ispec (P : IPre) (m : Result α) (Q : IPost α) : Prop :=
  P ⊢ iwp true m Q

/-- Partial-correctness separation-logic specification -/
@[irreducible] def dispec (P : IPre) (m : Result α) (Q : IPost α) : Prop :=
  P ⊢ iwp false m Q

/-- Total-correctness pure specification -/
def spec (m : Result α) (p : Post α) : Prop :=
  ispec emp m (fun value => ⌜p value⌝)

/-- Partial-correctness pure specification -/
def dspec (m : Result α) (p : Post α) : Prop :=
  dispec emp m (fun value => ⌜p value⌝)

end

end ResultImplementation

/-- Variant of `uncurry` used to decompose tuples in post-conditions.

Similar to `uncurry` but delaborated differently:
`uncurry'` is delaborated as `x y => ...` (separate binders), while
`uncurry` is delaborated as `(x, y) => ...` (tuple binder).
We use this in the Hoare triple notation `⦃ ⦄`.

Example: `f 0 ⦃ x y z => ... ⦄` desugars to
`spec (f 0) (uncurry' fun x => uncurry' fun y z => ...)`.
-/

@[expose]
def uncurry' {α β γ : Type _} (p : α → β → γ) : α × β → γ :=
  fun (x, y) => p x y

end Aeneas.Std.WP

/-
We want the notations to live in the namespace `Aeneas`, not `Aeneas.Std.WP`
TODO: use https://github.com/leanprover/lean4/pull/11355
-/
namespace Aeneas

open Std WP Result

/-!
# Hoare triple notation and elaboration
-/

syntax:lead (name := specSyntax)
  atomic("(" term:lead ")" " ⦃" "⇓ ") term+ " => " term " ⦄" : term
syntax:lead (name := specSyntaxPred)
  atomic("(" term:lead ")" " ⦃" "⇓ ") term " ⦄" : term
syntax:lead (name := slSpecSyntax)
  "⦃ " term " ⦄" ppLine term:lead ppLine
  "⦃ " term+ " => " term " ⦄" : term
syntax:lead (name := slSpecSyntaxPred)
  "⦃ " term " ⦄" ppLine term:lead ppLine "⦃ " term " ⦄" : term

open Lean PrettyPrinter

/-- Build a `Std.uncurry` chain wrapping a curried lambda over `xs`.

Given `x0`, ..., `xn` and `body`, generates the (syntactic) term `fun (x0, ..., xn) => body`.
-/
private meta partial def buildPostUncurryLamWith (uncurryName : Name)
    (xs : List Term) (body : Term) : MacroM Term := do
  let uncurryIdent := mkIdent uncurryName
  match xs with
  | [] => pure body
  | [x] => `(fun $x => $body)
  | [a, b] => `($uncurryIdent (fun $a $b => $body))
  | a :: rest =>
    let inner ← buildPostUncurryLamWith uncurryName rest body
    `($uncurryIdent (fun $a => $inner))

/-- Helper to elaborate `binder => body` when binder is a tuple - this supports nested tuples. -/
private meta partial def mkPostBinderFunWith (uncurryName : Name) (depth : Nat)
    (binder : Term) (body : Term) : MacroM Term := do
  match binder with
  | `( ($a, $bs,*) ) =>
    let xs : List Term := a :: bs.getElems.toList
    let mut leafIdents : List Term := []
    let mut wrappedBody := body
    for (x, idx) in xs.zipIdx.reverse do
      match x with
      | `( ($_, $_,*) ) =>
        -- Fresh identifier from depth + index
        let freshIdent := mkIdent $ .mkSimple s!"_p_{depth}_{idx}"
        let inner ← mkPostBinderFunWith uncurryName (depth + 1) x wrappedBody
        wrappedBody ← `($inner $freshIdent)
        leafIdents := freshIdent :: leafIdents
      | _ =>
        leafIdents := x :: leafIdents
    buildPostUncurryLamWith uncurryName leafIdents wrappedBody
  | _ => `(fun $binder => $body)

private meta partial def mkPostSyntaxWith (curryName uncurryName : Name)
    (body : Term) (depth : Nat) (binders : List Term) : MacroM Term := do
  match binders with
  | [] => pure body
  | [x] => mkPostBinderFunWith uncurryName depth x body
  | x :: rest =>
    let rest ← mkPostSyntaxWith curryName uncurryName body (depth + 1) rest
    let inner ← mkPostBinderFunWith uncurryName depth x rest
    let curryIdent := mkIdent curryName
    `($curryIdent $inner)

/-- If `stx` is a bare identifier or a juxtaposition (application) of bare
identifiers — i.e. a binder group like `a b c` — return the identifiers in
order.  Otherwise return `none`, so anonymous constructors `⟨a, b⟩`, tuple
patterns, and other structured terms are left untouched. -/
private meta partial def binderGroupIdents? (stx : Syntax) : Option (Array Term) :=
  if stx.isIdent then some #[⟨stx⟩]
  else if stx.getKind == ``Lean.Parser.Term.app || stx.getKind == Lean.nullKind then
    stx.getArgs.foldlM (init := (#[] : Array Term)) fun acc s =>
      (binderGroupIdents? s).map (acc ++ ·)
  else none

/-- Expand a binder that shares one type ascription across several names —
`(a b c : T)` — into the list of single binders `[(a : T), (b : T), (c : T)]`,
so each name becomes its own product component (exactly as if written
separately).  Tuple/pattern binders `(a, b)`, `(⟨a, b⟩ : T)`, single binders
`(a : T)`, and bare identifiers are returned unchanged. -/
private meta def expandGroupedBinder (binder : Term) : MacroM (List Term) := do
  match binder with
  | `(($e : $t)) =>
    match binderGroupIdents? e.raw with
    | some ids =>
      if ids.size ≤ 1 then pure [binder]
      else ids.toList.mapM fun id => `(($id : $t))
    | none => pure [binder]
  | _ => pure [binder]

/-- Flatten grouped binders across the whole binder list. -/
private meta def expandBinders (xs : List Term) : MacroM (List Term) := do
  let mut out : Array Term := #[]
  for x in xs do
    out := out ++ (← expandGroupedBinder x).toArray
  pure out.toList

/-- Build the postcondition term for `⦃ xs => p ⦄`, expanding grouped binders
into one component per name first. -/
private meta def mkPostWith (curryName uncurryName : Name)
    (binders : Array Term) (body : Term) : MacroM Term := do
  mkPostSyntaxWith curryName uncurryName body 0 (← expandBinders binders.toList)

macro_rules
  | `(($m) ⦃⇓ $result => $Q⦄) => do
      let post ← mkPostWith ``Aeneas.Std.WP.uncurry' ``Aeneas.Std.uncurry #[result] Q
      `(spec $m $post)
  | `(⦃$P⦄ $m ⦃ $result => $Q⦄) => do
      let post ←
        mkPostWith ``Aeneas.Std.WP.uncurry' ``Aeneas.Std.uncurry #[result] (← `(iprop($Q)))
      `(ispec iprop($P) $m $post)

macro_rules
  | `(($m) ⦃⇓ $result $results:term* => $Q⦄) => do
      let post ← mkPostWith ``Aeneas.Std.WP.uncurry' ``Aeneas.Std.uncurry
        (#[result] ++ results) Q
      `(spec $m $post)
  | `(⦃$P⦄ $m ⦃ $result $results:term* => $Q⦄) => do
      let post ← mkPostWith ``Aeneas.Std.WP.uncurry' ``Aeneas.Std.uncurry
        (#[result] ++ results) (← `(iprop($Q)))
      `(ispec iprop($P) $m $post)

macro_rules
  | `(($m) ⦃⇓ $Q:term⦄) =>
      `(spec $m (fun _ => $Q))
  | `(⦃$P⦄ $m ⦃ $Q⦄) =>
      `(ispec iprop($P) $m (fun _ => iprop($Q)))

syntax:lead (name := dspecSyntax)
  atomic("(" term:lead ")" " ⦃" "⇓ ") term+ " => " term " ⦄div" : term
syntax:lead (name := dspecSyntaxPred)
  atomic("(" term:lead ")" " ⦃" "⇓ ") term " ⦄div" : term
syntax:lead (name := slDspecSyntax)
  "⦃ " term " ⦄" ppLine term:lead ppLine
  "⦃ " term+ " => " term " ⦄div" : term
syntax:lead (name := slDspecSyntaxPred)
  "⦃ " term " ⦄" ppLine term:lead ppLine "⦃ " term " ⦄div" : term

macro_rules
  | `(($m) ⦃⇓ $result => $Q⦄div) => do
      let post ← mkPostWith ``Aeneas.Std.WP.uncurry' ``Aeneas.Std.uncurry #[result] Q
      `(dspec $m $post)
  | `(⦃$P⦄ $m ⦃ $result => $Q⦄div) => do
      let post ←
        mkPostWith ``Aeneas.Std.WP.uncurry' ``Aeneas.Std.uncurry #[result] (← `(iprop($Q)))
      `(dispec iprop($P) $m $post)

macro_rules
  | `(($m) ⦃⇓ $result $results:term* => $Q⦄div) => do
      let post ← mkPostWith ``Aeneas.Std.WP.uncurry' ``Aeneas.Std.uncurry
        (#[result] ++ results) Q
      `(dspec $m $post)
  | `(⦃$P⦄ $m ⦃ $result $results:term* => $Q⦄div) => do
      let post ← mkPostWith ``Aeneas.Std.WP.uncurry' ``Aeneas.Std.uncurry
        (#[result] ++ results) (← `(iprop($Q)))
      `(dispec iprop($P) $m $post)

macro_rules
  | `(($m) ⦃⇓ $Q:term⦄div) =>
      `(dspec $m (fun _ => $Q))
  | `(⦃$P⦄ $m ⦃ $Q⦄div) =>
      `(dispec iprop($P) $m (fun _ => iprop($Q)))

/- We use a priority of 55 for the inner term, which is exactly the priority for `|||`.
This way we can expressions like: `x + y ⦃ z => ... ⦄` without having to put parentheses around `x + y`. -/
scoped syntax:54 (name := pureSpecBinders)
  term:55 " ⦃ " term+ " => " term " ⦄" : term
scoped syntax:54 (name := pureSpecPred)
  term:55 " ⦃ " term " ⦄" : term

-- for dspec
scoped syntax:54 (name := pureDspecBinders)
  term:55 " ⦃ " term+ " => " term " ⦄div" : term
scoped syntax:54 (name := pureDspecPred)
  term:55 " ⦃ " term " ⦄div" : term

private meta def mkPurePost (binders : Array Term) (p : Term) : MacroM Term := do
  mkPostWith ``Aeneas.Std.WP.uncurry' ``Aeneas.Std.uncurry binders p

/-- Macro expansion for a single element (may expand to several via a grouped binder) -/
scoped macro_rules (kind := pureSpecBinders)
  | `($m ⦃ $x => $p ⦄) => do
    let post ← mkPurePost #[x] p
    `(Aeneas.Std.WP.spec $m $post)

/-- Macro expansion for multiple elements -/
scoped macro_rules (kind := pureSpecBinders)
  | `($m ⦃ $x $xs:term* => $p ⦄) => do
    let post ← mkPurePost (#[x] ++ xs) p
    `(Aeneas.Std.WP.spec $m $post)

scoped macro_rules (kind := pureDspecBinders)
  | `($m ⦃ $x => $p ⦄div) => do
    let post ← mkPurePost #[x] p
    `(Aeneas.Std.WP.dspec $m $post)

scoped macro_rules (kind := pureDspecBinders)
  | `($m ⦃ $x $xs:term* => $p ⦄div) => do
    let post ← mkPurePost (#[x] ++ xs) p
    `(Aeneas.Std.WP.dspec $m $post)

/-- Macro expansion for predicate with no arrow -/
scoped macro_rules (kind := pureSpecPred)
  | `($m ⦃ $p ⦄) => `(Aeneas.Std.WP.spec $m $p)

scoped macro_rules (kind := pureDspecPred)
  | `($m ⦃ $p ⦄div) => `(Aeneas.Std.WP.dspec $m $p)

end Aeneas
