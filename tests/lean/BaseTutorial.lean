/- A tutorial about using Lean to verify properties of programs generated by Aeneas -/
import Base

open Primitives
open Result

namespace Tutorial

/-#===========================================================================#
  #
  #     Simple Arithmetic Example
  #
  #===========================================================================#-/

/- As a first example, let's consider the function below.
 -/

def mul2_add1 (x : U32) : Result U32 := do
  let x1 ← x + x
  let x2 ← x1 + 1#u32
  ok x2

/- There are several things to note.

   # Machine integers
   ==================
   Because Rust programs manipulate machine integers which occupy a fixed
   size in memory, we model integers by using types like [U32], which is
   the type of integers which take their values between 0 and 2^32 - 1 (inclusive).
   [1#u32] is simply the constant 1 (seen as a [U32]).

   You can see a definition or its type by using the [#print] and [#check] commands.
   It is also possible to jump to definitions (right-click + "Go to Definition"
   in VS Code).

   For instance, you can see below that [U32] is defined in terms of a more generic
   type [Scalar] (just move the cursor to the [#print] command below).

 -/
#print U32 -- This shows the definition of [U32]

#check mul2_add1 -- This shows the type of [mul2_add1]
#print mul2_add1 -- This show the full definition of [mul2_add1]

/- # Syntax
   ========
   Because machine integers are bounded, arithmetic operations can fail, for instance
   because of an overflow: this is the reason why the output of [mul2_add1] uses
   the [Result] type. In particular, addition can fail.

   We use a lightweight "do"-notation to write code which calls potentially failing
   functions. In practice, all our function bodies start with a [do] keyword,
   which enables using this lightweight syntax. After the [do], instead of writing
   let-bindings as [let x1 := ...], we write them as: [let x1 ← ...]. We also
   have lightweight notations for common operations like the addition.

   For instance, in [let x1 ← x + x], the [x + x] expression desugars to
   [Scalar.add x x] and the [let x1 ← ...] desugars to a call to [bind].

   The definition of [bind x f] is worth investigating. It simply checks whether
   [x : Result ...] successfully evaluates to some value, in which case it
   calls [f] with this value, and propagates the error otherwise. See the output
   of the [#print] command below.

   *Remark:* in order to type the left-arrow symbol [←] you can type: [\l]. Generally
   speaking, your editor can tell you how to type the symbols you see in Lean
   code. For instance in VS Code, you can simply hover your mouse over the
   symbol and a pop-up window will open displaying all the information you need.
 -/
#print Primitives.bind

/- We show a desugared version of [mul2_add1] below: we remove the syntactic
   sugar, and inline the definition of [bind] to make the matches over the
   results explicit.
 -/
def mul2_add1_desugared (x : U32) : Result U32 :=
  match Scalar.add x x with
  | ok x1 => -- Success case
    match Scalar.add x1 (U32.ofInt 1) with
    | ok x2 => ok x2
    | error => error
  | error => error -- Propagating the errors

/- Now that we have seen how [mul2_add1] is defined precisely, we can prove
   simple properties about it. For instance, what about proving that it evaluates
   to [2 * x + 1]?

   We advise writing specifications in a Hoare-logic style, that is with
   preconditions (requirements which must be satisfied by the inputs upon
   calling the function) and postconditions (properties that we know about
   the output after the function call).

   In the case of [mul2_add1] we could state the theorem as follows.
 -/

theorem mul2_add1_spec
  -- The input
  (x : U32)
  /- The precondition (we give it the name "h" to be able to refer to it in the proof).
     We simply state that [2 * x + 1] must not overflow.

     The ↑ notation ("\u") is used to coerce values. Here, we coerce [x], which is
     a bounded machine integer, to an unbounded mathematical integer, which is
     easier to work with. Note that writing [↑x] is the same as writing [x.val].
   -/
  (h : 2 * ↑x + 1 ≤ U32.max)
  /- The postcondition -/
  : ∃ y, mul2_add1 x = ok y ∧  -- The call succeeds
  ↑ y = 2 * ↑x + (1 : Int)   -- The output has the expected value
  := by
  /- The proof -/
  -- Start by a call to the rewriting tactic to reveal the body of [mul2_add1]
  rw [mul2_add1]
  /- Here we use the fact that if [x + x] doesn't overflow, then the addition
     succeeds and returns the value we expect, as given by the theorem [U32.add_spec].
     Doing this properly requires a few manipulations: we need to instantiate
     the theorem, introduce it in the context, destruct it to introduce [x1], etc.
     We automate this with the [progress] tactic: [progress with th as ⟨ x1 ⟩]
     uses theorem [th], instantiates it properly by looking at the goal, renames
     the output to [x1] and further decomposes the postcondition of [th].

     Note that it is possible to provide more inputs to name the assumptions
     introduced by the postcondition (for instance: [as ⟨ x1, h ⟩]).

     If you look at the goal after the call to [progress], you wil see that:
     - there is a new variable [x1] and an assumption stating that [↑x1 = ↑x + ↑x]
     - the call [x + x] disappeared from the goal: we "progressed" by one step

     Remark: the theorem [U32.add_spec] actually has a precondition, namely that
     the addition doesn't overflow.
     In the present case, [progress] manages to prove this automatically by using
     the fact that [2 * x + 1 < U32.max]. In case [progress] fails to prove a
     precondition, it leaves it as a subgoal.
   -/
  progress with U32.add_spec as ⟨ x1 ⟩
  /- We can call [progress] a second time for the second addition -/
  progress with U32.add_spec as ⟨ x2 ⟩
  /- We are now left with the remaining goal. We do this by calling the simplifier
     then [scalar_tac], a tactic to solve arithmetic problems:
   -/
  simp at *
  scalar_tac

/- The proof above works, but it can actually be simplified a bit. In particular,
   it is a bit tedious to specify that [progress] should use [U32.add_spec], while
   in most situations the theorem to use is obvious by looking at the function.

   For this reason, we provide the possibility of registering theorems in a database
   so that [progress] can automatically look them up. This is done by marking
   theorems with custom attributes, like [pspec] below.

   Theorems in the standard library like [U32.add_spec] have already been marked with such
   attributes, meaning we don't need to tell [progress] to use them.
 -/
@[pspec] -- the [pspec] attribute saves the theorem in a database, for [progress] to use it
theorem mul2_add1_spec2 (x : U32) (h : 2 * ↑x + 1 ≤ U32.max)
  : ∃ y, mul2_add1 x = ok y ∧
  ↑ y = 2 * ↑x + (1 : Int)
  := by
  rw [mul2_add1]
  progress as ⟨ x1⟩ -- [progress] automatically lookups [U32.add_spec]
  progress as ⟨ x2 ⟩ -- same
  simp at *; scalar_tac

/- Because we marked [mul2_add1_spec2] theorem with [pspec], [progress] can
   now automatically look it up. For instance, below:
 -/
-- A dummy function which uses [mul2_add1]
def use_mul2_add1 (x : U32) (y : U32) : Result U32 := do
  let x1 ← mul2_add1 x
  x1 + y

@[pspec]
theorem use_mul2_add1_spec (x : U32) (y : U32) (h : 2 * ↑x + 1 + ↑y ≤ U32.max) :
  ∃ z, use_mul2_add1 x y = ok z ∧
  ↑z = 2 * ↑x + (1 : Int) + ↑y := by
  rw [use_mul2_add1]
  -- Here we use [progress] on [mul2_add1]
  progress as ⟨ x1 ⟩
  progress as ⟨ z ⟩
  scalar_tac


/-#===========================================================================#
  #
  #     Recursion
  #
  #===========================================================================#-/

/- We can have a look at more complex examples, for example recursive functions. -/

/- A custom list type.

   Original Rust code:
   ```
   pub enum CList<T> {
    CCons(T, Box<CList<T>>),
    CNil,
   }
   ```
-/
inductive CList (T : Type) :=
| CCons : T → CList T → CList T
| CNil : CList T

-- Open the [CList] namespace, so that we can write [CCons] instead of [CList.CCons]
open CList

/- A function accessing the ith element of a list.

   Original Rust code:
   ```
   pub fn list_nth<'a, T>(l: &'a CList<T>, i: u32) -> &'a T {
      match l {
          List::CCons(x, tl) => {
              if i == 0 {
                  return x;
              } else {
                  return list_nth(tl, i - 1);
              }
          }
          List::CNil => {
              panic!()
          }
      }
   }
   ```
 -/
divergent def list_nth (T : Type) (l : CList T) (i : U32) : Result T :=
  match l with
  | CCons x tl =>
    if i = 0#u32
    then ok x
    else do
      let i1 ← i - 1#u32
      list_nth T tl i1
  | CNil => fail Error.panic

/- Conversion to Lean's standard list type.

   Note that because we use the suffix "CList.", we can use the notation [l.to_list]
   if [l] has type [CList ...].
 -/
def CList.to_list {α : Type} (x : CList α) : List α :=
  match x with
  | CNil => []
  | CCons hd tl => hd :: tl.to_list

/- Let's prove that [list_nth] indeed accesses the ith element of the list.

   Remark: the parameter [Inhabited T] tells us that we must have an instance of the
   typeclass [Inhabited] for the type [T].  As of today we can only use [index] with
   inhabited types, that is to say types which are not empty (i.e., for which it is
   possible to construct a value - for instance, [Int] is inhabited because we can exhibit
   the value [0: Int]). This is a technical detail.

   Remark: we didn't mention it before, but we advise always writing inequalities
   in the same direction (that is: use [<] and not [>]), because it helps the simplifier.
   More specifically, if you have the assumption that [x > y] in the context, the simplifier
   may not be able to rewrite [y < x] to [⊤].
 -/
theorem list_nth_spec {T : Type} [Inhabited T] (l : CList T) (i : U32)
  -- Precondition: the index is in bounds
  (h : i.val < l.to_list.length)
  -- Postcondition
  : ∃ x, list_nth T l i = ok x ∧
  -- [x] is the ith element of [l] after conversion to [List]
  x = l.to_list.index ↑i
  := by
  -- Here we have to be careful when unfolding the body of [list_nth]: we could
  -- use the [simp] tactic, but it will sometimes loop on recursive definitions.
  rw [list_nth]
  -- Let's simply follow the structure of the function, by first matching on [l]
  match l with
  | CNil =>
    -- We can't get there: we can derive a contradiction from the precondition:
    -- we have that [i < 0] (because [i < CNil.to_list.len]) and at the same
    -- time [0 ≤ i] (because [i] is a [U32] unsigned integer).
    -- First, let's simplify [to_list CNil] to [0]
    simp [CList.to_list] at h
    -- Proving we have a contradiction
    scalar_tac
  | CCons hd tl =>
    -- Simplify the match
    simp only []
    -- Perform a case disjunction on [i].
    -- The notation [hi : ...] allows us to introduce an assumption in the
    -- context, to remember the fact that in the branches we have [i = 0#u32]
    -- and [¬ i = 0#u32].
    if hi: i = 0#u32 then
      -- We can finish the proof simply by using the simplifier.
      -- We decompose the proof into several calls on purpose, so that it is
      -- easier to understand what is going on.
      -- Simplify the condition and the [if then else]
      simp [hi]
      -- Prove the final equality
      simp [CList.to_list]
    else
      -- The interesting branch
      -- Simplify the condition and the [if then else]
      simp [hi]
      -- i0 := i - 1
      progress as ⟨ i1, hi1 ⟩
      -- [progress] can handle recursion
      simp [CList.to_list] at h -- we need to simplify this inequality to prove the precondition
      progress as ⟨ l1 ⟩
      -- Proving the postcondition
      -- We need this to trigger the simplification of [index to.to_list i.val]
      --
      -- Among other things, the call to [simp] below will apply the theorem
      -- [List.index_nzero_cons], which has the precondition [i.val ≠ 0]. [simp]
      -- can automatically use the assumptions/theorems we give it to prove
      -- preconditions when applying rewriting lemmas. In the present case,
      -- by giving it [*] as argument, we tell [simp] to use all the assumptions
      -- to perform rewritings. In particular, it will use [i.val ≠ 0] to
      -- apply [List.index_nzero_cons].
      have : i.val ≠ 0 := by scalar_tac -- Remark: [simp at hi] also works
      simp [CList.to_list, *]

/-#===========================================================================#
  #
  #     Partial Functions
  #
  #===========================================================================#-/

/- Recursive functions may not terminate on all inputs.

   For instance, the function below only terminates on positive inputs (note
   that we switched to signed integers), in which cases it behaves like the
   identity. When we need to define such a potentially partial function,
   we use the [divergent] keyword, which means that the function may diverge
   (i.e., infinitely loop).

   We will skip the details of how [divergent] precisely handles non-termination.
   All you need to know is that the [Result] type has actually 3 cases (we saw
   the first 2 cases in the examples above):
   - [ret]: successful computation
   - [fail]: failure (panic because of overflow, etc.)
   - [div]: the computation doesn't terminate

   If in a theorem we state and prove that:
   ```
   ∃ y, i32_id x = ok x
   ```
   we not only prove that the function doesn't fail, but also that it terminates.

   *Remark*: in practice, whenever Aeneas generates a recursive function, it
   annotates it with the [divergent] keyword.
 -/
divergent def i32_id (x : I32) : Result I32 :=
  if x = 0#i32 then ok 0#i32
  else do
    let x1 ← x - 1#i32
    let x2 ← i32_id x1
    x2 + 1#i32

/- We can easily prove that [i32_id] behaves like the identity on positive inputs -/
theorem i32_id_spec (x : I32) (h : 0 ≤ x.val) :
  i32_id x = ok x := by
  rw [i32_id]
  if hx : x = 0#i32 then
    simp_all
  else
    simp [hx]
    -- x - 1
    progress as ⟨ x1 ⟩
    -- Recursive call
    progress
    -- x2 + 1
    progress as ⟨ x2 ⟩
    -- Postcondition
    scalar_tac
-- Below: we have to prove that the recursive call performed in the proof terminates.
-- Otherwise, we could prove any result we want by simply writing a theorem which
-- uses itself in the proof.
--
-- We first specify a decreasing value. Here, we state that [x], seen as a natural number,
-- decreases at every recursive call.
termination_by x.val.toNat
-- And we now have to prove that it indeed decreases - you can skip this for now.
decreasing_by
  -- We first need to "massage" the goal (in practice, all the proofs of [decreasing_by]
  -- should start with a call to [simp_wf]).
  simp_wf
  -- This is just a linear arithmetic goal so we conclude with [scalar_tac]
  scalar_tac

end Tutorial