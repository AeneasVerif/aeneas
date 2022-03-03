open Identifiers

module Disambiguator = IdGen ()

(** See the comments for [Name] *)
type path_elem = Ident of string | Disambiguator of Disambiguator.id
[@@deriving show, ord]

type name = path_elem list [@@deriving show, ord]
(** A name such as: `std::collections::vector` (which would be represented as
    [[Ident "std"; Ident "collections"; Ident "vector"]])


    A name really is a list of strings. However, we sometimes need to
    introduce unique indices to disambiguate. This mostly happens because
    of "impl" blocks in Rust:
      ```
      impl<T> List<T> {
        ...
      }
      ```
   
    A type in Rust can have several "impl" blocks, and those blocks can
    contain items with similar names. For this reason, we need to disambiguate
    them with unique indices. Rustc calls those "disambiguators". In rustc, this
    gives names like this:
    - `betree_main::betree::NodeIdCounter{impl#0}::new`
    - note that impl blocks can be nested, and macros sometimes generate
      weird names (which require disambiguation):
      `betree_main::betree_utils::_#1::{impl#0}::deserialize::{impl#0}`
   
    Finally, the paths used by rustc are a lot more precise and explicit than
    those we expose in LLBC: for instance, every identifier belongs to a specific
    namespace (value namespace, type namespace, etc.), and is coupled with a
    disambiguator.
   
    On our side, we want to stay high-level and simple: we use string identifiers
    as much as possible, insert disambiguators only when necessary (whenever
    we find an "impl" block, typically) and check that the disambiguator is useless
    in the other situations (i.e., the disambiguator is always equal to 0).
   
    Moreover, the items are uniquely disambiguated by their (integer) ids
    (`TypeDeclId.id`, etc.), and when extracting the code we have to deal with
    name clashes anyway. Still, we might want to be more precise in the future.
   
    Also note that the first path element in the name is always the crate name.
 *)

let to_name (ls : string list) : name = List.map (fun s -> Ident s) ls

(*(* TODO: remove? *)
  module NameOrderedType : C.OrderedType with type t = name = struct
    type t = name

    let compare = compare_name

    let to_string = String.concat "::"

    let pp_t = pp_name

    let show_t = show_name
  end

  module NameMap = C.MakeMap (NameOrderedType)
  module NameSet = C.MakeSet (NameOrderedType)
*)

type module_name = name [@@deriving show, ord]

type type_name = name [@@deriving show, ord]

type fun_name = name [@@deriving show, ord]

(*module ImplId = IdGen ()

  (** A function name *)
  type fun_name =
    | Regular of name  (** "Regular" function name *)
    | Impl of type_name * ImplId.id * string
        (** The function comes from an "impl" block.

            As we may have several "impl" blocks for one type, we need to use
            a block id to disambiguate the functions (in rustc, this identifier
            is called a "disambiguator").
         *)
  [@@deriving show, ord]*)
