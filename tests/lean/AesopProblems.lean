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

   Below, all lemmas are written to represent minimal examples of goal states
   which I encounter.
 -/

/- Here, I want to simplify the condition in the [if then else] (don't look at
   the content of the branches: in a typical setting I would be working with
   the body of a function).

   The problem is that simplifying the condition to ⊤, and as a consequence the
   [if then else], requires a linear arithmetic solver. I would like to be able
   to call a tactic like [aesop_simp] (with variations like [aesop_simp at ...])
   to try simplifying sub-expressions in the goal. Of course, performance might
   be an issue, but on the other hand as aesop can generate proof scripts, this
   could give us an easy way to generate parts of proofs.
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
  (h0 : 0 ≤ i) (h1 : i + 1 ≤ j) (h2 : j < ) :
  List.index (List.update l i x) i = List.index l i := by
  -- The lemma we want to use has the precondition i ≠ j, which we have to assert by hand
  have : i ≠ j := by scalar_tac -- this is my "boosted" version of linarith
  -- Here I apply the lemma by hand to give you the reference - it is actually
  -- marked as [simp] so I could finish the proof with the simplifier
  simp [*]


end AesopProblems
