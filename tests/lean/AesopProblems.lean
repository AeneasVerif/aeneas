/- Some problems I would like to solve with Aesop -/
import Base

open Primitives
open Result

namespace AesopProblems

/-#===========================================================================#
  #
  #     Aesop as a boosted simplifier
  #
  #===========================================================================#-/

/- A problem I have is that I often want to simplify expressions in the context, but
   simplifying those expressions often requires something more powerful than [simp].

   Below, all lemmas are written to represent minimal reproductions of goal states
   which I encountered.
 -/

/- Here, I want to simplify the condition in the [if then else] (don't look at
   the content of the branches: in a typical setting I would be proving a property
   about the body of a function).

   The problem is that in order to simplify the condition to ⊤ we need to solve a linear
   arithmetic problem. I would like to be able to call a tactic like [aesop_simp] (with
   variations like [aesop_simp at ...])  to try simplifying sub-expressions in the
   goal. Of course, performance might be an issue, but on the other hand as aesop can
   generate proof scripts, this could give us an easy way to generate parts of proofs.
   Of course, I'm aware that I can give to [simp] a tactic with which to solve
   the preconditions of the rewriting lemmas, but we can imagine more complex
   settings where we actually want to apply rules, and solve the preconditions and
   those rules with specific tactics, etc.
-/
example (x : ℤ) (h : 0 ≤ x) :
  if 0 ≤ x + 1 then ⊤
  else ⊥ := by
  -- Here I have to write by hand the following assertion, which then clutters the context
  have : 0 ≤ x + 1 := by linarith
  simp [*]
  trivial

/- In the same spirit, I encountered this one a lot.

   When manipulating arrays, we often find the following pattern, where we
   access an access of an array (modelled by a list) from which we just
   updated an element. In this situation we essentially use two lemmas, which
   give us that: if [update] and [index] use the same index, then [index]
   evaluates to the updated element, otherwise [index] evaluates to [index] of
   the old array.

   Remark: in case you wonder, I have developed my own library of functions to
   manipulate lists so as never to use the type ℕ (I use ℤ instead) because
   proofs which mix ℤ and ℕ don't behave well. More details on that later.
 -/
example (i j : ℤ) [Inhabited α] (l : List α) (x : α)
  -- The fact that i ≠ j often comes from a set of (linear) equations
  (h1 : i + 1 ≤ j) :
  List.index (List.update l i x) j = List.index l j := by
  -- The lemma we want to use has the precondition i ≠ j, which we have to assert by hand
  have : i ≠ j := by scalar_tac -- this is my "boosted" version of linarith
  -- We can finish with the simplifier (the lemma is actually marked as [simp],
  -- so [simp [*]] would actually be enough.
  simp [List.index_update_ne, *]

/- In case the indices are the same, we use the following lemma (which is also
   marked as [simp] -/
#check List.index_update_eq

/- An interesting thing to note is that in a sense applying [List.index_update_ne] is
   safe. The reason is that when we can apply [List.index_update_eq], the indices are
   syntactically the same (or they are after a call to simp). This means that if
   [List.index (List.update l i x) j] doesn't get simplified to [x] because [i = j], it is
   often safe to assume that we must have [i ≠ j] (and that if we don't manage to prove
   that [i ≠ j] it simply means that we lack some information).
   But maybe this observation is too specific to the problem above...

   Also note that I have many examples which look like the problems I showed above.
 -/

/- Here I am actually not sure: could Aesop solve this? I think yes, modulo
   the fact that we need to instantiate the quantifier in [hi]. -/
example (i : ℤ) (l : List ℤ) (hi : ∀ i, 0 ≤ i → i < l.len → 0 < l.index i)
  (x : ℤ) (hx : 0 < x) :
  ∀ j, 0 ≤ j → j < l.len → 0 < (l.update i x).index j := by
  intro j h1 h2
  if heq : i = j then simp [*]
  else simp [*]

/-#===========================================================================#
  #
  #     Splitting the rules between different sets to have DSL solvers
  #
  #===========================================================================#-/


end AesopProblems
