open Identifiers

type name = string list [@@deriving show, ord]
(** A name such as: `std::collections::vector` (which would be represented as
    [["std"; "collections"; "vector"]]) *)

(* TODO: remove? *)
module NameOrderedType : C.OrderedType with type t = name = struct
  type t = name

  let compare = compare_name

  let to_string = String.concat "::"

  let pp_t = pp_name

  let show_t = show_name
end

module NameMap = C.MakeMap (NameOrderedType)
module NameSet = C.MakeSet (NameOrderedType)

type module_name = name [@@deriving show, ord]

type type_name = name [@@deriving show, ord]

module ImplId = IdGen ()

(** A function name *)
type fun_name =
  | Regular of name  (** "Regular" function name *)
  | Impl of type_name * ImplId.id * string
      (** The function comes from an "impl" block.

          As we may have several "impl" blocks for one type, we need to use
          a block id to disambiguate the functions (in rustc, this identifier
          is called a "disambiguator").
       *)
[@@deriving show, ord]
