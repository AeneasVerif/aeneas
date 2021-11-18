exception IntegerOverflow of unit

exception Unimplemented of string

let unimplemented msg = raise (Unimplemented ("unimplemented: " ^ msg))
