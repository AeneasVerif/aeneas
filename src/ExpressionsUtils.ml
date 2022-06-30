module E = Expressions

let unop_can_fail (unop : E.unop) : bool =
  match unop with Neg | Cast _ -> true | Not -> false

let binop_can_fail (binop : E.binop) : bool =
  match binop with
  | BitXor | BitAnd | BitOr | Eq | Lt | Le | Ne | Ge | Gt -> false
  | Div | Rem | Add | Sub | Mul -> true
  | Shl | Shr -> raise Errors.Unimplemented
