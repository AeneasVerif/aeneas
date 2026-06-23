include Charon.Utils
include Charon.GAstUtils

(** Structural equality with a physical-equality fast path. [phys_eq a b] is
    equivalent to [a = b] but tries the O(1) physical-equality check [a == b]
    first. *)
let phys_eq (a : 'a) (b : 'a) : bool = a == b || a = b

(** Structural inequality with a physical-equality fast path. [phys_neq a b] is
    equivalent to [a <> b] but skips the structural comparison when the values
    are physically identical. *)
let phys_neq (a : 'a) (b : 'a) : bool = (not (a == b)) && a <> b
