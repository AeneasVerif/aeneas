(** This module implements support for loops.

    Throughout the module, we will use the following code as example to
    illustrate what the functions do (this function simply returns a mutable
    borrow to the nth element of a list):
    {[
      pub fn list_nth_mut<'a, T>(mut ls: &'a mut List<T>, mut i: u32) -> &'a mut T {
          loop {
              match ls {
                  List::Nil => {
                      panic!()
                  }
                  List::Cons(x, tl) => {
                      if i == 0 {
                          return x;
                      } else {
                          ls = tl;
                          i -= 1;
                      }
                  }
              }
          }
      }
    ]}

    Upon reaching the loop entry, the environment is as follows (ignoring the
    dummy variables):
    {[
      abs@0 { ML l0 }
      ls -> MB l0 (s2 : loops::List<T>)
      i -> s1 : u32
    ]}

    Upon reaching the [continue] at the end of the first iteration, the
    environment is as follows:
    {[
      abs@0 { ML l0 }
      ls -> MB l4 (s@6 : loops::List<T>)
      i -> s@7 : u32
      _@1 -> MB l0 (loops::List::Cons (ML l1, ML l2))
      _@2 -> MB l2 (@Box (ML l4))                      // tail
      _@3 -> MB l1 (s@3 : T)                           // hd
    ]}

    The fixed point we compute is:
    {[
      abs@0 { ML l0 }
      ls -> MB l1 (s@3 : loops::List<T>)
      i -> s@4 : u32
      abs@fp { // fp: fixed-point
        MB l0
        ML l1
      }
    ]}

    From here, we deduce that [abs@fp { MB l0, ML l1}] is the loop abstraction.
*)

open Contexts
open Cps
open Meta

(** Evaluate a loop.

    The `stl_cm_fun` required as input must be the function to evaluate the loop
    body (i.e., `eval_statement` applied to the loop body). *)
val eval_loop : config -> span -> stl_cm_fun -> stl_cm_fun
