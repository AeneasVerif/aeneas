module
public import Aeneas.NonPos.Tests.Test
public import Aeneas.NonPos.Top

@[expose] public section
/-!
# The forms and the tactic, by example

How `nonpos_cont` (section 6 of `Top.lean`) proves a body continuous, shown by proving the same
goals by hand with the forms of section 5.  Each hand proof lists, in order, the forms the tactic
applies; `nonpos_cont` then does the same goal in one call.  `Bla` is the structure of `Test.lean`
over `Option`:
```
nonpos_structure Bla (Self : Type) : Type 1 where
  to_num : Self → Option Int
  add : ∀ {Other : Type} (BlaInst : Bla Other), Other → Self → Option Int
```
-/
namespace NonPos.ExamplesCont
open NonPos NonPos.Test
noncomputable section

/-! ## 1. Leaves: `const` and `id`

A body that does not mention the varying dictionary `d` is `Cont.const`; `d` itself is `Cont.id`. -/

example : Cont (fun _ : Bla Int => (some 3 : Option Nat)) := Cont.const _
example : Cont (fun d : Bla Int => d) := Cont.id

/-! ## 2. Projections: `unfold`, `fst`, `snd`, `app`

`d.to_num` is, by definition, `(Fix.unfold Bla.F d).1`.  So a projection out of the varying
dictionary is `Cont.unfold` (the unfolding is continuous in `d`) followed by `Cont.fst`/`Cont.snd`
(a tuple component is continuous).  Applying the method to a fixed argument is `Cont.app`. -/

example : Cont (fun d : Bla Int => d.to_num) :=
  Cont.fst (Cont.unfold Bla.F Cont.id)
example : Cont (fun d : Bla Int => d.to_num 1) :=
  Cont.app (f := fun d : Bla Int => d.to_num) (Cont.fst (Cont.unfold Bla.F Cont.id)) 1

-- the same by the tactic: `Cont.app` is chosen by `nonpos_cont_peel` (the last argument `1` does not
-- mention `d`), then `Cont.fst` and `Cont.unfold` are found in `getContTheorems`, then `Cont.id`.
example : Cont (fun d : Bla Int => d.to_num 1) := by nonpos_cont

/-! ## 3. A method of a *fixed* dictionary applied to the varying one: `Fix.cond`

`BlaInst.add inst o s` with `BlaInst` fixed and `inst` varying is continuous because `BlaInst` is a
dictionary: its condition `Fix.cond BlaInst` says exactly that its `add` is continuous in its
dictionary argument.  `nonpos_cond_simp` unfolds that condition to its clauses
(the `to_num` clause is `True`, since `to_num` has no dictionary argument, and disappears). -/

example {O : Type} (BlaInst : Bla O) (o : Int) (s : O) : Cont (fun inst : Bla Int => BlaInst.add inst o s) := by
  apply Cont.app (f := fun inst : Bla Int => BlaInst.add inst o) (t := s)
  apply Cont.app (f := fun inst : Bla Int => BlaInst.add inst) (t := o)
  have h := Fix.cond _ BlaInst
  nonpos_cond_simp at h
  -- h : ∀ (Other : Type), Cont (fun inst : Bla Other => BlaInst.add inst)
  exact h Int

-- the tactic: two `Cont.app`, then `nonpos_proj BlaInst`, which is the last four lines above.
example {O : Type} (BlaInst : Bla O) (o : Int) (s : O) : Cont (fun inst : Bla Int => BlaInst.add inst o s) := by
  nonpos_cont

/-! ## 4. A `do` block: `bind`, `pure`, `lam`

`do let i ← m; k i` is `m >>= fun i => k i`, so a `do` block is nested `Cont.bind`s.  Each `bind`
asks for the first action and, for every value `i` of the bound variable, the rest.  The final
`pure (i + j)` is `Cont.pure` of something not mentioning `inst`, hence `Cont.const`. -/

example {O : Type} (BlaInst : Bla O) (o : O) :
    Cont (fun inst : Bla Int => do let i ← BlaInst.to_num o; let j ← inst.to_num 1; pure (i + j)) := by
  apply Cont.bind
  · exact Cont.const _                             -- `BlaInst.to_num o` does not mention `inst`
  · intro i
    apply Cont.bind
    · exact Cont.app (f := fun d : Bla Int => d.to_num) (Cont.fst (Cont.unfold Bla.F Cont.id)) 1
    · intro j
      exact Cont.pure (Cont.const _)

example {O : Type} (BlaInst : Bla O) (o : O) :
    Cont (fun inst : Bla Int => do let i ← BlaInst.to_num o; let j ← inst.to_num 1; pure (i + j)) := by
  nonpos_cont

/-! ## 5. Building a dictionary from a varying one: `fold`, `pair`

`Bla.mk f g h` is `Fix.fold Bla.F ⟨f, g, ⟨⟩⟩ h`.  `Cont.fold` asks for the tuple to be continuous in
`inst`, which `Cont.pair` splits into the fields; a field with binders is `Cont.lam` once per binder.
This is the shape of the monotonicity obligation of a self-referential instance
(`def inst := Bla.mk … partial_fixpoint monotonicity Cont.monotone (by nonpos_cont)`). -/

example : Cont (fun inst : Bla Int =>
    Bla.mk (fun s => some s) (fun {O} (BlaInst : Bla O) o s => BlaInst.add inst s o) (by nonpos_cont)) := by
  apply Cont.fold
  apply Cont.pair
  · exact Cont.const _                             -- `to_num` does not mention `inst`
  · apply Cont.pair
    · apply Cont.lam; intro O                      -- `{O}`
      apply Cont.lam; intro BlaInst                -- `(BlaInst : Bla O)`
      apply Cont.lam; intro o
      apply Cont.lam; intro s
      nonpos_cont                                  -- part 3 again: `BlaInst.add inst s o`
    · exact Cont.const _                           -- the `⟨⟩` terminator

/-! ## 6. `if`, `match`, and helper functions

`Cont.ite` needs the condition not to mention `inst`; a `match` on something not mentioning `inst`
is split by `cases` (not a form: it only produces one goal per branch); a helper function with no
form of its own is unfolded (`delta`) so that its body can be analysed. -/

def helper {O : Type} (BlaInst : Bla O) (o : O) : Option Int := do
  let i ← BlaInst.to_num o
  pure (i * 2)

example {O : Type} (b : Bool) (o : O) :
    Cont (fun inst : Bla O => if b then helper inst o else match b with | true => none | false => inst.to_num o) := by
  apply Cont.ite
  · delta helper                                   -- unfold, then it is a `do` block as in part 4
    apply Cont.bind
    · exact Cont.app (f := fun d : Bla O => d.to_num) (Cont.fst (Cont.unfold Bla.F Cont.id)) o
    · intro i; exact Cont.pure (Cont.const _)
  · cases b                                        -- the scrutinee `b` does not mention `inst`
    · exact Cont.app (f := fun d : Bla O => d.to_num) (Cont.fst (Cont.unfold Bla.F Cont.id)) o
    · exact Cont.const _

example {O : Type} (b : Bool) (o : O) :
    Cont (fun inst : Bla O => if b then helper inst o else match b with | true => none | false => inst.to_num o) := by
  nonpos_cont

/-! ## 7. Recursion: `Cont.fix`

A `partial_fixpoint` definition unfolds (`delta`) to `Lean.Order.fix (fun f => body) hm`;
`Cont.fix` reduces its continuity in `inst` to that of `body` in the pair `⟨inst, f⟩`, where the
recursive call `f` is now an ordinary projection `p.2` of the pair. -/

noncomputable def countdown {O : Type} (BlaInst : Bla O) (o : O) (n : Nat) : Option Int :=
  match n with
  | 0 => BlaInst.to_num o
  | n + 1 => do let _ ← BlaInst.to_num o; countdown BlaInst o n
partial_fixpoint

example {O : Type} (o : O) : Cont (fun inst : Bla O => countdown inst o) := by
  delta countdown                                  -- exposes `Lean.Order.fix (fun f n => …) _`
  apply Cont.fix                                   -- goal: `Cont (fun p : Bla O ×' (Nat → Option Int) => fun n => …)`
  nonpos_cont                                      -- `lam`, `cases n`, `bind`, `snd`, `fst`, ...

example {O : Type} (o : O) : Cont (fun inst : Bla O => countdown inst o) := by nonpos_cont

/-! ## 8. Extending the tactic: `@[nonpos_continuous]`

A proved continuity fact can be added to the lookup.  With `cont_helper` tagged, `helper inst o`
matches it directly and is no longer unfolded; this is how a monad's own operations (`Result.vis`
in `Result.lean`) and library functions join the forms without changing `Top.lean`. -/

@[nonpos_continuous]
theorem cont_helper {O : Type} (o : O) : Cont (fun inst : Bla O => helper inst o) := by nonpos_cont

example {O : Type} (o : O) : Cont (fun inst : Bla O => helper inst o >>= fun _ => inst.to_num o) := by
  nonpos_cont

/-! ## 9. What is rejected

A body that uses the varying dictionary in a way that is not continuous is refused, and the error
names the function whose continuity is unknown.  Here `Option.getD` extracts a value from the
monad and `+ 1` is applied to it, which no form covers:
```
example : Cont (fun inst : Bla Int => (inst.to_num 1).getD 0 + 1) := by nonpos_cont
-- error: nonpos_cont: continuity of instHAdd.1 is not known
-- error: nonpos_cont: continuity of Option.rec … is not known
```
and correctly so: the result type `Int` has no undefined value, so a method returning it could
only be constant (see `Shape.Pointed` in `Top.lean`).  The same body wrapped in the monad,
`do let i ← inst.to_num 1; pure (i + 1)`, is accepted by part 4. -/

end
end NonPos.ExamplesCont
