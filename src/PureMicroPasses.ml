(** The following module defines micro-passes which operate on the pure AST *)

open Errors
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
      tmp := discriminant(ls);
      switch tmp {
        0 => {
          x := (ls as Cons).0;
          hd := (ls as Cons).1;
          ...
        }
      }
      ```
      If `ls` maps to a symbolic value `s0` upon evaluating the match in symbolic
      mode, we expand this value upon evaluating `tmp = discriminant(ls)`.
      However, at this point, we don't know which should be the names of
      the symbolic values we introduce for the fields of `Cons`!
      Let's imagine we have (for the `Cons` branch): `s0 ~~> Cons s1 s2`.
      The assigments lead to the following binding in the evaluation context:
      ```
      x -> s1
      hd -> s2
      ```
      
      When generating the symbolic AST, we save as meta-information that we
      assign `s1` to the place `x` and `s2` to the place `hd`. This way,
      we learn we can use the names `x` and `hd` for the variables which are
      introduced by the match:
      ```
      match ls with
      | Cons x hd -> ...
      | ...
      ```
   - If we write the following in Rust:
     ```
     let x = y + z;
     ```
     
     We get the following MIR:
     ```
     let tmp = y + z;
     ```
     TODO: finish...
   - If we write the following in Rust:
     ```
     let px = &mut x;
     f(px);
     ```
     
     Rustc generates the following MIR:
     ```
     px := &mut x;
     tmp := &mut ( *px ); // "tmp" is actually an anonymous variable
     f(move tmp);
     ```

     As borrows and dereferencements are ignored in the pure paths we generate
     (because they are extracted to the identity), we save as meta-data that
     at some point we assign the value of `px` to `tmp`.
     
     TODO: actually useless, because `tmp` later gets inlined.
   - TODO: inputs and end abstraction...
 *)
let compute_pretty_names () = ()

(** Remove the meta-information *)
let remove_meta (e : expression) : expression =
  let obj =
    object
      inherit [_] map_expression as super

      method! visit_Meta env meta e = super#visit_expression env e
    end
  in
  obj#visit_expression () e
