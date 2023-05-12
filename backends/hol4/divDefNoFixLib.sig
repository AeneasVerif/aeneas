(* **DEPRECATED**: see divDefLib

   This library defines an older version of DefineDiv, which doesn't use
   fixed-point operator and thus relies on more complex meta functions.

   Define a (group of mutually recursive) function(s) which uses an error
   monad and is potentially divergent.

   We encode divergence in such a way that we don't have to prove that the
   functions we define terminate *upon defining them*, and can do those proofs
   in an extrinsic way later. It works as follows.

   Let's say you want to define the following “even” and “odd” functions
   which operate on *integers*:

   {[
     even (i : int) : bool result = if i = 0 then Return T else odd (i - 1) /\

     odd (i : int) : bool result = if i = 0 then Return F else even (i - 1)
   ]}

   It is easy to prove that the functions terminate provided the input is >= 0,
   but it would require to be able to define those functions in the first place!

   {!DefineDev} consequently does the following.

   It first defines versions of “even” and “odd” which use fuel:
   {[
     even___fuel (n : num) (i : int) : bool result =
       case n of 0 => Diverge
       | SUC m => if i = 0 then Return T else odd___fuel m (i - 1) /\

     odd___fuel (n : num) (i : int) : bool result =
       case n of 0 => Diverge
       | SUC m => if i = 0 then Return F else even___fuel m (i - 1)
   ]}

   Those functions trivially terminate.

   Then, provided we have the following auxiliary definition:
   {[
     is_diverge (r: 'a result) : bool = case r of Diverge => T | _ => F
   ]}

   we can define the following predicates, which tell us whether “even___fuel”
   and “odd___fuel” terminate on some given inputs:
   {[
     even___P i n = ~(is_diverge (even___fuel n i)) /\

     odd___P i n = ~(is_diverge (odd___fuel n i))
   ]}

   We can finally define “even” and “odd” as follows. We use the excluded
   middle to test whether there exists some fuel on which the function
   terminates: if there exists such fuel, we call the "___fuel" versions
   of “even” and “odd” with it (we use the least upper bound, to be more
   precise). Otherwise, we simply return “Diverge”.
   {[
     even i =
       if (?n. even___P i n) then even___fuel ($LEAST (even___P i)) i
       else Diverge /\

     odd i =
       if (?n. odd___P i n) then odd___fuel ($LEAST (odd___P i)) i
       else Diverge
   ]}

   The definitions above happen to satisfy the rewriting theorem we want:
   {[
     even (i : int) : bool result = if i = 0 then Return T else odd (i - 1) /\

     odd (i : int) : bool result = if i = 0 then Return F else even (i - 1)
   ]}

   Moreover, if we prove a lemma which states that they don't evaluate to
   “Diverge” on some given inputs (trivial recursion if we take “i >= 0”
   and reuse the rewriting theorem just above), then we effectively proved
   that the functions terminate on those inputs.

   Remark:
   =======
   {!DefineDiv} introduces all the auxiliary definitions we need and
   automatically performs the proofs. A crucial intermediate lemma
   we need in order to establish the last theorem is that the "___fuel"
   versions of the functions are monotonic in the fuel.
   More precisely:
   {[
     !n m. n <= m ==>
       (!ls i. even___P ls i n ==> even___fuel n ls i n = even___fuel m ls i n) /\
       (!ls i. odd___P ls i n ==> odd___fuel n ls i n = odd___fuel m ls i n)
   ]}
 *)

signature divDefNoFixLib =
sig
  include Abbrev

  val DefineDiv : term quotation -> thm list
end
