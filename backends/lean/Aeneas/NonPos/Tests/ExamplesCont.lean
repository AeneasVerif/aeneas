module
public import Aeneas.NonPos.Tests.Test
public import Aeneas.NonPos.TrustedBase.Command

@[expose] public section
/-!
# The forms and the tactic, by example

How `nonpos_cont` (section 2 of `Tactic.lean`) proves a body continuous, shown by proving the same
goals by hand with the forms of `TrustedBase/Definitions.lean`.  Each hand proof lists, in order, the
forms the tactic applies; `nonpos_cont` then does the same goal in one call.  `Measure` is the structure
of `Test.lean` over `Option`:
```
nonpos_structure Measure (Self : Type) : Type 1 where
  size : Self → Option Int
  combine : ∀ {Other : Type} (MeasureInst : Measure Other), Other → Self → Option Int
```
-/
namespace NonPos.ExamplesCont
open NonPos NonPos.Test
noncomputable section

/-! ## 1. Leaves: `const` and `id`

A body that does not mention the varying dictionary `d` is `Cont.const`; `d` itself is `Cont.id`. -/

example : Cont (fun _ : Measure Int => (some 3 : Option Nat)) := Cont.const _
example : Cont (fun d : Measure Int => d) := Cont.id

/-! ## 2. Projections: `unfold`, `fst`, `snd`, `app`

`d.size` is, by definition, `(Fix.unfold Measure.F d).1`.  So a projection out of the varying
dictionary is `Cont.unfold` (the unfolding is continuous in `d`) followed by `Cont.fst`/`Cont.snd`
(a tuple component is continuous).  Applying the method to a fixed argument is `Cont.app`. -/

example : Cont (fun d : Measure Int => d.size) :=
  Cont.fst (Cont.unfold Measure.F Cont.id)
example : Cont (fun d : Measure Int => d.size 1) :=
  Cont.app (f := fun d : Measure Int => d.size) (Cont.fst (Cont.unfold Measure.F Cont.id)) 1

-- the same by the tactic: `Cont.app` is chosen by `nonpos_cont_peel` (the last argument `1` does not
-- mention `d`), then `Cont.fst` and `Cont.unfold` are found in `getContTheorems`, then `Cont.id`.
example : Cont (fun d : Measure Int => d.size 1) := by nonpos_cont

/-! ## 3. A method of a *fixed* dictionary applied to the varying one: `Fix.cond`

`MeasureInst.combine inst o s` with `MeasureInst` fixed and `inst` varying is continuous because `MeasureInst` is a
dictionary: its condition `Fix.cond MeasureInst` says exactly that its `combine` is continuous in its
dictionary argument.  `nonpos_cond_simp` unfolds that condition to its clauses
(the `size` clause is `True`, since `size` has no dictionary argument, and disappears). -/

example {O : Type} (MeasureInst : Measure O) (o : Int) (s : O) : Cont (fun inst : Measure Int => MeasureInst.combine inst o s) := by
  apply Cont.app (f := fun inst : Measure Int => MeasureInst.combine inst o) (t := s)
  apply Cont.app (f := fun inst : Measure Int => MeasureInst.combine inst) (t := o)
  have h := Fix.cond _ MeasureInst
  nonpos_cond_simp at h
  -- h : ∀ (Other : Type), Cont (fun inst : Measure Other => MeasureInst.combine inst)
  exact h Int

-- the tactic: two `Cont.app`, then the last line above, built directly as `((Fix.cond _ MeasureInst).2.1 Int).1`
-- (the condition has the nested shape of the tuple `⟨size, combine, ⟨⟩⟩`, and `combine`'s part is its `.2.1`).
example {O : Type} (MeasureInst : Measure O) (o : Int) (s : O) : Cont (fun inst : Measure Int => MeasureInst.combine inst o s) := by
  nonpos_cont

/-! ## 4. A `do` block: `bind`, `pure`, `lam`

`do let i ← m; k i` is `m >>= fun i => k i`, so a `do` block is nested `Cont.bind`s (here `Cont.option_bind`, the form for `Option`).  Each `bind`
asks for the first action and, for every value `i` of the bound variable, the rest.  The final
`pure (i + j)` does not mention `inst`, hence `Cont.const`. -/

example {O : Type} (MeasureInst : Measure O) (o : O) :
    Cont (fun inst : Measure Int => do let i ← MeasureInst.size o; let j ← inst.size 1; pure (i + j)) := by
  apply Cont.option_bind
  · exact Cont.const _                             -- `MeasureInst.size o` does not mention `inst`
  · intro i
    apply Cont.option_bind
    · exact Cont.app (f := fun d : Measure Int => d.size) (Cont.fst (Cont.unfold Measure.F Cont.id)) 1
    · intro j
      exact Cont.const _

example {O : Type} (MeasureInst : Measure O) (o : O) :
    Cont (fun inst : Measure Int => do let i ← MeasureInst.size o; let j ← inst.size 1; pure (i + j)) := by
  nonpos_cont

/-! ## 5. Building a dictionary from a varying one: `fold`, `pair`

`Measure.mk f g h` is `Fix.fold Measure.F ⟨f, g, ⟨⟩⟩ h`, written as `Fix.foldDelayed Measure.F (fun _ => ⟨f, g, ⟨⟩⟩) h`
(`TrustedBase/Definitions.lean`, where `foldDelayed` is).  `Cont.fold` (here as `Cont.foldDelayed`, the same form for that way of
writing it) asks for the tuple to be continuous in `inst`, which `Cont.pair` splits into the fields; a
field with binders is `Cont.lam` once per binder.
This is the shape of the monotonicity obligation of a self-referential instance
(`def inst := Measure.mk … partial_fixpoint monotonicity Cont.monotone (by nonpos_cont)`). -/

example : Cont (fun inst : Measure Int =>
    Measure.mk (fun s => some s) (fun {O} (MeasureInst : Measure O) o s => MeasureInst.combine inst s o) (by nonpos_cont)) := by
  apply Cont.foldDelayed
  apply Cont.pair
  · exact Cont.const _                             -- `size` does not mention `inst`
  · apply Cont.pair
    · apply Cont.lam; intro O                      -- `{O}`
      apply Cont.lam; intro MeasureInst                -- `(MeasureInst : Measure O)`
      apply Cont.lam; intro o
      apply Cont.lam; intro s
      nonpos_cont                                  -- part 3 again: `MeasureInst.combine inst s o`
    · exact Cont.const _                           -- the `⟨⟩` terminator

/-! ## 6. `if`, `match`, and helper functions

`Cont.ite` needs the condition not to mention `inst`; a `match` on something not mentioning `inst`
is split by `cases` (not a form: it only produces one goal per branch); a helper function with no
form of its own is unfolded (`delta`) so that its body can be analysed. -/

def helper {O : Type} (MeasureInst : Measure O) (o : O) : Option Int := do
  let i ← MeasureInst.size o
  pure (i * 2)

example {O : Type} (b : Bool) (o : O) :
    Cont (fun inst : Measure O => if b then helper inst o else match b with | true => none | false => inst.size o) := by
  apply Cont.ite
  · delta helper                                   -- unfold, then it is a `do` block as in part 4
    apply Cont.option_bind
    · exact Cont.app (f := fun d : Measure O => d.size) (Cont.fst (Cont.unfold Measure.F Cont.id)) o
    · intro i; exact Cont.const _
  · cases b                                        -- the scrutinee `b` does not mention `inst`
    · exact Cont.app (f := fun d : Measure O => d.size) (Cont.fst (Cont.unfold Measure.F Cont.id)) o
    · exact Cont.const _

example {O : Type} (b : Bool) (o : O) :
    Cont (fun inst : Measure O => if b then helper inst o else match b with | true => none | false => inst.size o) := by
  nonpos_cont

/-! ## 7. Recursion: `Cont.fix`

A `partial_fixpoint` definition unfolds (`delta`) to `Lean.Order.fix (fun f => body) hm`;
`Cont.fix` reduces its continuity in `inst` to that of `body` in the pair `⟨inst, f⟩`, where the
recursive call `f` is now an ordinary projection `p.2` of the pair. -/

noncomputable def countdown {O : Type} (MeasureInst : Measure O) (o : O) (n : Nat) : Option Int :=
  match n with
  | 0 => MeasureInst.size o
  | n + 1 => do let _ ← MeasureInst.size o; countdown MeasureInst o n
partial_fixpoint

example {O : Type} (o : O) : Cont (fun inst : Measure O => countdown inst o) := by
  delta countdown                                  -- exposes `Lean.Order.fix (fun f n => …) _`
  apply Cont.fix                                   -- goal: `Cont (fun p : Measure O ×' (Nat → Option Int) => fun n => …)`
  nonpos_cont                                      -- `lam`, `cases n`, `bind`, `snd`, `fst`, ...

example {O : Type} (o : O) : Cont (fun inst : Measure O => countdown inst o) := by nonpos_cont

/-! ## 8. Extending the tactic: `@[nonpos_continuous]`

A proved continuity fact can be added to the lookup.  With `cont_helper` tagged, `helper inst o`
matches it directly and is no longer unfolded; this is how a monad's own operations (`Result.vis`
in `Result.lean`) and library functions join the forms without changing `Tactic.lean`. -/

@[nonpos_continuous]
theorem cont_helper {O : Type} (o : O) : Cont (fun inst : Measure O => helper inst o) := by nonpos_cont

example {O : Type} (o : O) : Cont (fun inst : Measure O => helper inst o >>= fun _ => inst.size o) := by
  nonpos_cont

/-! ## 9. What is rejected

A body that uses the varying dictionary in a way that is not continuous is refused, and the error
names the function whose continuity is unknown.  Here `Option.getD` extracts a value from the
monad and `+ 1` is applied to it, which no form covers:
```
example : Cont (fun inst : Measure Int => (inst.size 1).getD 0 + 1) := by nonpos_cont
-- error: nonpos_cont: continuity of instHAdd.1 is not known
-- error: nonpos_cont: continuity of Option.rec … is not known
```
and correctly so: the result type `Int` has no undefined value, so a method returning it could
only be constant (which is also why a structure has no field of plain data: the pieces of `TrustedBase/Definitions.lean`).  The same body wrapped in the monad,
`do let i ← inst.size 1; pure (i + 1)`, is accepted by part 4. -/

end
end NonPos.ExamplesCont
