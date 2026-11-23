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