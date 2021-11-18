exception IntegerOverflow of unit

exception Unimplemented of string

let unimplemented msg = raise (Unimplemented ("unimplemented: " ^ msg))

exception Unreachable of string

let unreachable msg = raise (Unreachable ("unreachable: " ^ msg))
