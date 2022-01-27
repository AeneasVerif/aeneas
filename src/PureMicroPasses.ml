(** The following module defines micro-passes which operate on the pure AST *)

open Pure

(** This function computes pretty names for the variables in the pure AST. It
    relies on the "meta"-place information in the AST to generate naming
    constraints.
    
    The way it works is as follows:
    - we only modify the names of the unnamed variables
    - whenever we see an rvalue/lvalue which is exactly an unnamed variable,
      and this value is linked to some meta-place information which contains
      a name and an empty path, we consider we should use this name

    For instance, the following situations happen:
    - let's say we evaluate:
      ```
      match (ls : List<T>) {
        List::Cons(x, hd) => {
          ...
        }
      }
      ```
      
      Actually, in MIR, we get:
      ```
      tmp = discriminant(ls);
      switch tmp {
        0 => {
          x = (ls as Cons).0;
          hd = (ls as Cons).1;
          ...
        }
      }
      ```
      If `ls` maps to a symbolic value upon evaluating the match in symbolic
      mode, we expand this value upon evaluating `tmp = discriminant(ls)`.
      However, at this point, we don't know which should be the names of
      the symbolic values we introduce for the fields of `Cons`! Still,
      the subsequent assignments actually give us the naming information we
      were looking for.
 *)
let compute_pretty_names () = ()
