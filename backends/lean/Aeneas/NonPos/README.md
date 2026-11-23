# The trusted base of `nonpos_structure`

This library defines a command that defines structures which can break the positivity constraint
usually imposed on Lean structures. Here is an example:

```
nonpos_structure Measure (A : Type) : Type 1 where
  size : A → Option Nat
  larger : ∀ B, Measure B → A → B → Option Bool
```

Lean doesn't allow structures to be self-referential in this way, and for good reason:
if you axiomatized `Measure` with a computation rule like `(Measure.mk s l).larger = l`,
it would allow a proof of False. But types like this are perfectly valid in programming
languages, and the elimination rule is necessary. Instead, we will impose a continuity
condition on functions like larger, that restricts how it can use its recursive argument.

This library was implemented by ai. In order to preserve human verifiability, there is a minimal
trusted base with top level statements in the TrustedBase folder.
The `Definitions.lean` file contains statements that pin down the definitions that are used
to implement `nonpos_structure`s, as well as a list of lemmas about continuity which cover
all code that Aeneas can output.
The `Command.lean` file contains the `nonpos_structure` command.
From this trusted base, it is possible to verify that the command will always succeed and
exactly what object the resulting type will represent. It is also possible to verify the
set of functions for which continuity can be proven in principle.
The tactic `nonpos_cont`, which automatically proves continuity, as well as the
`@[nonpos_continuous]` attribute, which adds continuity theorems to be used by the tactic,
are not in the trusted base. However, the Lean kernel will check that their output does
in fact prove continuity, and the tests show empirically that Aeneas output is covered.

<!-- To be written.  What it should cover: -->

## To include


### What the statements guarantee
- `Fix.fold` / `Fix.unfold` are inverse (`unfold_fold`, `fold_unfold`), and what `unfold` gives
  satisfies the condition (`Fix.cond`).
- The order on a structure is the order on its fields (`Fix.le_iff`); with `Fix.instCCPO`, a
  self-referential instance defined by `partial_fixpoint` is the *least* solution for that order, in
  which divergence is least, field by field.  This is what makes the logical value of such an
  instance the one the program computes (the red-team point: a different order would let the logic
  disagree with the program).
- The order of each piece is Lean's own order for that type (pointwise on functions, componentwise
  on pairs, the type's own `CCPO`, e.g. `Result`'s; on `PUnit` there is only one order).
- Soundness does not depend on the `Cont` forms: any proof of `Cont` is checked.  The forms show the
  other direction, that everything Aeneas outputs satisfies the condition.

### No axioms, no `sorry`
- `sorry` is a warning, and CI builds with `--wfail`.
- A new `axiom` produces no warning; the `#guard_msgs in #print axioms axiomCheck` line at the end of
  `Definitions.lean` fails the build if one is used.

### Assumptions about the untrusted files
They are properties of the text of those files, and can be checked by searching it.
- They declare no instance of `FixFunctor` (the pieces of `Definitions.lean` are the only ones, so
  they are what the command finds for a group).
- They declare no `PartialOrder` or `CCPO` instance that would change what Lean finds for functions,
  pairs, `Result`, `PUnit`, or `Fix` (the orders of the pieces, and the `CCPO` that
  `partial_fixpoint` finds at a use site).
- They declare no syntax, macro or elaborator that changes what the text of a trusted file means.
- They declare no compiled implementation (`implemented_by`, `extern`) of what the command
  generates, or of `Fix.fold` / `Fix.unfold`.

### Compiled code
- At runtime a dictionary is a `Thunk` of its tuple of fields: `foldDelayed` stores it, `unfold`
  forces it (the two `unsafe` definitions at the end of `Definitions.lean`).
- Why delayed: a self-referential dictionary `d := mk … (f d) …` is compiled as a recursive constant,
  and a field mentioning `d` outside a lambda would be evaluated while `d` is being built.
- The assumptions, and why they hold:
  1. Every dictionary at runtime was made by `foldDelayed`: every other construction of a `Fix F k`
     is noncomputable, so compiled code cannot use it; a `partial_fixpoint` instance compiles to a
     recursive definition whose body is a `mk`.
  2. Compiled code reads a dictionary only through `unfold`: only the model looks inside the
     representation, and it is never compiled.
- Then `unfold` of a dictionary gives the tuple `foldDelayed` was given, which is its logical value
  by `Fix.unfold_fold`.
