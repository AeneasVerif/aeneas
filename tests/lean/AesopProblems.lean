/- This file lists some problems I would like to solve with Aesop. -/
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

   The issue is that in order to simplify the condition to [⊤] we need to solve a linear
   arithmetic problem. I would like to be able to call a tactic like [aesop_simp] (with
   variations like [aesop_simp at ...]) to try simplifying sub-expressions in the
   goal.

   Of course, I'm aware that I can give to [simp] a tactic with which to solve
   the preconditions of the rewriting lemmas, but we can imagine more complex
   settings where we actually want to apply rules, and solve the preconditions and
   those rules with specific tactics, etc.

   Remark: I'm also aware that performance and stability of proofs which use [aesop] like
   a more powerful [simp] might be an issue, but I believe this is an orthogonal problem
   (and there are some immediate, though maybe sub-optimal solutions, like leverating the
   fact that [aesop] can generate proof scripts).
-/
example (x : ℤ) (h : 0 ≤ x) :
  if 0 ≤ x + 1 then ⊤
  else ⊥ := by
  -- I have to write by hand this assertion, which then clutters the context,
  -- unless I clear it of course (another manual step)
  have : 0 ≤ x + 1 := by linarith
  simp [*]
  trivial

/- In the same spirit, I encountered this one a lot.

   When manipulating arrays (modeled as lists), we often find the following pattern, where
   we access an access of an array from which we just updated an element. In this
   situation we essentially use two lemmas, which give us that: if [update] and [index]
   use the same index, then [index] evaluates to the updated element, otherwise [index]
   evaluates to [index] of the old array.

   Remark: in case you wonder, I have developed my own library of functions to
   manipulate lists so as never to use the type ℕ (I use ℤ instead) because
   proofs which mix ℤ and ℕ don't behave well. More details on that later.
 -/
example (i j : ℤ) [Inhabited α] (l : List α) (x : α)
  -- The fact that i ≠ j often comes from a set of (linear) equations
  (h1 : i + 1 ≤ j) :
  List.index (List.update l i x) j = List.index l j := by
  -- The lemma we want to use has the precondition i ≠ j, which we have to assert by hand
  have : i ≠ j := by scalar_tac -- [scalar_tac] is my "boosted" version of linarith
  -- We can finish with the simplifier (the lemma is actually marked as [simp],
  -- so [simp [*]] would actually be enough.
  simp [List.index_update_ne, *]

/- In case the indices are the same, we use the following lemma (which is also
   marked as [simp] -/
#check List.index_update_eq

/- An interesting thing to note is that in a sense applying [List.index_update_ne] is
   safe. The reason is that when we can apply [List.index_update_eq], the indices are
   often syntactically the same (or they are after a call to [simp]). This means that if
   [List.index (List.update l i x) j] doesn't get simplified to [x] because [i = j], it is
   often safe to assume that we must have [i ≠ j] (and that if we don't manage to prove
   that [i ≠ j] it simply means that we lack some information).
   But maybe this observation is too specific to the problem above...
 -/

/- Here I am actually not sure: could Aesop solve this? I think yes, modulo
   the fact that we need to instantiate the quantifier in [hi]. I would be very
   happy if I could use [aesop] for this, but this may take us quite far
   (especially because I expect performance to not be super good)
   and I would not be that unhappy if I can't (though it would be really cool
   to be able to make [aesop] automatically generate the proof script...).
 -/
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

/- In practice, I need solvers specialized for various sets of problems, and
   I believe I can build many quite powerful such solvers on top of [aesop].

   A typical example is the following one.
 -/

/- A common problem using non-linear arithmetic.

   The issue here is very simple:
   - writing a good non-linear arithmetic solver is hard (and the problem
     is undecidable anyway): I could say a lot about proof breakages which
     happened in the Hacl* proofs and were caused by the fact that Z3 is not
     very good nor stable at reasoning about non-linear arithmetic,
     and in particular because of this exact proof obligation (this proof
     obligation happens a lot more than one might expect).
   - but actually, when it comes to program verification in practice, we can
     come up with pretty simple heuristics which work most of the time.

   Below, we want to always apply [Left.mul_nonneg] then use a tactic like
   [linarith]. But of course, there are a few situations where we might not
   want to do that and still use [aesop] (because we face a non-linear
   arithmetic problem of a different shape). This kind of problems would
   be a good motivation to have the possibility of defining sets of rules,
   and give the possibility of choosing which set to use upon calling [aesop].
 -/
example (x y : ℤ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := by
  apply Left.mul_nonneg <;> assumption

/- More generally speaking, I believe having sets of rules would really open
   the possibility of writing a wide range of specialized and quite efficient
   solvers. For instance, for the problem above I would have [scalar_tac]
   simply call [aesop] with the proper set of rules (also see the section
   about the arithmetic tactics below).

   About stability: marking theorems as rules for [aesop] looks a bit like a sophisticated
   version of SMT patterns. I guess you know what SMT patterns are, but just in case: with
   solvers like Z3 it is possible to annotate lemmas with patterns, which guide an
   automatic instantiation of those lemmas. The issue is that when you use SMT patterns,
   you quickly get very unstable/unpredictable proofs. It actually often happens that by
   annotating a lemma or changing its pattern you end up breaking proofs which seem
   completely unrelated. By giving the possibility of using only a set of rules, we might
   get more stable proofs and also have a tighter control of performance.
 -/

/-#===========================================================================#
  #
  #     Automatic unfolding
  #
  #===========================================================================#-/

/- 

 -/


/-#===========================================================================#
  #
  #     Toward better arithmetic tactics?
  #
  #===========================================================================#-/

/- 

 -/

end AesopProblems
