open CfimAst
open Utils

(** Check if a [statement] contains loops *)
let statement_has_loops (st : statement) : bool =
  let obj =
    object
      inherit [_] iter_statement

      method! visit_Loop _ _ = raise Found
    end
  in
  try
    obj#visit_statement () st;
    false
  with Found -> true

(** Check if a [fun_def] contains loops *)
let fun_def_has_loops (fd : fun_def) : bool = statement_has_loops fd.body
