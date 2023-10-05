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

/- I often encounter the situation where I want to simplify expressions in the context,
   but simplifying those expressions often requires something more powerful than [simp].
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
   settings where we actually want to apply rules, and solve the preconditions of
   those rules with specific tactics, etc.

   Remark: I'm also aware that performance and stability of proofs which use [aesop] like
   a more powerful [simp] might be an issue, but I believe this is an orthogonal problem
   (and there are some immediate, though maybe sub-optimal solutions, like leverating the
   fact that [aesop] can generate proof scripts to use [aesop] a bit like a copilot
   in those situations).
-/
example (x : ℤ) (h : 0 ≤ x) :
  if 0 ≤ x + 1 then ⊤ else ⊥
  := by
  -- I have to write by hand this assertion, which then clutters the context,
  -- unless I clear it of course (another manual step)
  have : 0 ≤ x + 1 := by linarith
  simp [*]
  trivial

/- In the same spirit, I encountered this one a lot.

   When manipulating arrays (modeled as lists), we often find the following pattern, where
   we access an array from which we just updated an element. In this situation we
   essentially use two lemmas, which give us that: if [update] and [index] use the same
   index, then [index] evaluates to the updated element ([List.index_update_ne] in the
   proof below), otherwise [index] evaluates to [index] of the old array ([List.index_update_eq]).

   Remark: in case you wonder, I have developed my own library of functions to
   manipulate lists so as never to use the type ℕ (I use ℤ instead) because
   proofs which mix ℤ and ℕ don't behave well. More details on that later.
 -/
example (i j : ℤ) [Inhabited α] (l : List α) (x : α)
  -- The fact that [i ≠ j] that we use below often comes from a set of (linear) equations
  (h1 : i + 1 ≤ j) :
  List.index (List.update l i x) j = List.index l j := by
  -- The lemma we want to use has the precondition [i ≠ j], which we have to assert by hand
  have : i ≠ j := by scalar_tac -- [scalar_tac] is my "boosted" version of linarith
  -- We can finish with the simplifier (the lemma is actually marked as [simp],
  -- so [simp [*]] would actually be enough).
  simp [List.index_update_ne, *]

/- In case the indices are the same, we use the following lemma (which is also
   marked as [simp] -/
#check List.index_update_eq

/- An interesting thing to note is that in a sense applying [List.index_update_ne] is
   safe. The reason is that when we can apply [List.index_update_eq], the indices are
   often syntactically the same (or they are after a call to [simp]). This means that if
   [List.index (List.update l i x) j] doesn't get simplified to [x] because [i = j], it is
   often safe to assume that we *must* have [i ≠ j] (and that if we don't manage to prove
   [i ≠ j], it simply means that we lack some information in the context).
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

/- About non-linear arithmetic: I did some proofs about a hashmap and we are currently
   working on the proof of the Kyber key encapsulation mechanism (it is a cryptographic
   primitive), and we encounter(ed) a lot of issues because of non-linear arithmetic proof
   obligations, which we think could be automated.

   This includes a lot of things like proving [2 * x ≤ 2 * y] from [x ≤ y],
   proving [x / d + y / d ≤ (x + y) / d], or that [(a * b) / c = a * (b / c)]
   if [c | b] (and losing time because we need to find the proper lemma in
   mathlib and we actually get confused because there are several definitions
   of division: https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/efficiently.20dealing.20with.20.2F.20vs.20.2Ediv), etc.

   I think this is the typical example where [aesop] would shine, because this
   is a situation where we badly need some custom automation, but the automation
   is not complex enough to justify writing a dedicated solver from scratch.
   I would love to discuss this in more details (and get [aesop] to work on
   those proofs!).
 -/

-- I actually don't find this theorem in mathlib, but I've proved it in
-- other proof assistants
theorem add_pos_div_pos_le (x y z : ℤ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) :
  x / z + y / z ≤ (x + y) / z := sorry

example (x y z : ℤ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) :
  2 * (x / z + y / z) ≤ 2 * ((x + y) / z) := by
  apply Int.mul_le_mul_of_nonneg_left <;> try simp
  apply add_pos_div_pos_le <;> assumption
  

/- More generally speaking, I believe having sets of rules would really open
   the possibility of writing a wide range of specialized and quite efficient
   solvers. For instance, for the problems above I would write a set of tactics
   which simply call [aesop] with the proper set of rules (also see the section
   about the arithmetic tactics below). One issue with the examples above is
   that I am confident I can automate them with [aesop], but I would not
   consider all the lemmas I want [aesop] to apply as safe to apply in a general
   setting.

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
  #     Automatic unfolding of definitions
  #
  #===========================================================================#-/

/- I often have the following issue, where I want to unfold some definitions
   (like an invariant), simplify the context at the same time, then call a tactic
   like [scalar_tac].

   At a high level, I would like to be able to write something like what
   people do in Dafny:
   ```
   reveal(inv);
   ```

   or:
   ```
   assert ... by { reveal(inv) }
   ```

   This is also another motivation to have the possibility of defining sets
   of rules.

   Remark: I think [aesop] can easily handle this problem already. I mostly wanted to
   mention it, because it is something I often encounter.
 -/

def inv (ls : List ℤ) : Prop := 0 < ls.len

example (ls : List ℤ) (hinv : inv ls) : 1 ≤ ls.len := by
  simp_all [inv]
  scalar_tac

/- Remark: unfolding definitions is of course not limited to unfolding invariants. -/

/-#===========================================================================#
  #
  #     Toward better arithmetic tactics?
  #
  #===========================================================================#-/

/- I mentioned the fact that I wrote my own library of functions to operate on
   lists, in order never to use ℕ (always ℤ), because proofs which mix ℤ and ℕ
   are tedious.

   The main issue comes from the fact that, if we want to call linarith
   on a goal, we need to convert all the ℕ to ℤ. We can do so by calling
   [zify] and the simplifier, expect when we have substrations.
   Indeed, we have [↑(x - y) = ↑x - ↑y] (where x, y ∈ ℕ) only if we can prove
   that [y ≤ x]. I wonder how [aesop] could help us with that.

   Also, my [scalar_tac] could probably be implemented on top of [aesop].
   It does the following:
   - introduces the bounds for the machine integers (and some other bounds,
     like [0 ≤ l.len] if [l] is a list in the context - note that [List.len]
     is my custom version of [List.length], which returns an [ℤ]). I implemented
     this with typeclasses (I explore the goal, and lookup instances of a specific
     typeclass for all the subterms - it works well in practice).
   - splits on occurrences of [x ≠ y] (because last time I looked it was not
     implemented yet for [linarith]
   - performs a very controled simplification of the context
 -/

example (x : U32) (ls : List α) : 0 ≤ x.val + ls.len := by
  -- This is the preprocessing performed by [scalar_tac], just to show
  -- you what we get.
  --
  -- Side note: you may wonder why we introduce assumptions like: [4294967295 ≤ Usize.max].
  -- This is because as [Usize.max] depends on the architecture, we make it opaque.
  scalar_tac_preprocess
  -- Finishing off the proof
  linarith

/-#===========================================================================#
  #
  #     Not completely related: matching terms with a database of theorems
  #
  #===========================================================================#-/

/- I showed you the [progress] tactic (see example below), which allows to do Hoare-style
   proofs on functions written in an error monad. It works by looking at the goal, looking
   up a theorem (among the theorems we marked with a dedicated attribute) which matches
   the first function call, and applying it.

   I had to implement my own lookup function, which is not very powerful (I map
   function *names* to theorems). It works in most situations, but not when
   we use typeclasses. For instance, I have theorems for operations like [x + y],
   which desugars to [HAdd.hAdd (Scalar ...) x y]. I can't simply map [HAdd.hAdd]
   to the theorem I need because it depends on the type (second argument).
   For now I have a workaround, but I'm not very satisfied with it. I would like to have
   something which gives me all the theorems which match a given term.

   So my question is: what I need is actually similar to what [simp] and [aesop] must
   themselves do. Is there some code in [simp] or [aesop] that I could reuse for this
   purpose?
 -/

def mul2_add1 (x : U32) : Result U32 := do
  let x1 ← x + x
  let x2 ← x1 + 1#u32
  ret x2

theorem mul2_add1_spec2 (x : U32) (h : 2 * ↑x + 1 ≤ U32.max)
  : ∃ y, mul2_add1 x = ret y ∧
  ↑ y = 2 * ↑x + (1 : Int)
  := by
  rw [mul2_add1]
  progress as ⟨ x1 .. ⟩ -- we progress by one step in the goal
  progress as ⟨ x2 .. ⟩
  simp at *; scalar_tac

/-#===========================================================================#
  #
  #     Generating proof drafts
  #
  #===========================================================================#-/

/- I do not want to push you too much in this direction *yet* because this is not
   what we need most at present, but following your ideas to completely
   automate some proofs, I thought it would be nice to use [aesop] to draft
   proofs, for instance by generating scripts which correspond to the structure
   of the proof and that we could later modify.
 -/
def dist (x y : ℤ) : ℤ :=
  if x ≤ y then y - x
  else x - y

example : ∀ x y, 0 ≤ dist x y := by
  simp [dist]
  /- Starting here, the structure of the proof simply follows the shape
     of the theorem (we need to introduce the quantified variables) and the
     structure of [dist]. Everything is very mechanical and guided by the syntax:
     we don't have to think much.

     Something important is that in order to make the proof maintanable,
     we need to introduce names for [x] and [y] (we don't want to use [intros])
     and write the [if ... then ... else ...] (we don't want to use [split]).
     Of course, it is ok if the user needs to clean the proof a bit afterwards,
     for instance by changing the names.
   -/
  intro x y
  if h: x ≤ y then
    /- Here we eventually have to think a bit to finish the proof, but [aesop]
       could simply generate a [sorry] that we would fill later (in the present
       situation, I of course expect [aesop] to finish the proof automatically).

       Provided the proof scripts are not too big and are well structured, this might
       provide a nice way of interacting with [aesop] in the cases it can't
       completely finish the proofs. Instead of simply seeing the unproven goals,
       we would have a partial proof script, which may make it easier to understand
       where we are and why we have to prove the remaining proof obligations.

       Combined with something like the [progress] tactic when doing program
       verification, it could be quite powerful: we could generate the boring
       part of the proof which is a bit verbose, and focus on the interesting bits.
     -/
    simp [h]
  else
    simp [h]
    int_tac

end AesopProblems
