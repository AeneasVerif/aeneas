(*** Define the backends we support as an enum *)

type t =
  | Coq
  | Lean
  | FStar
  | HOL4
  | BorrowCheck
      (** Borrow check: no backend. We use this when we only want to
          borrow-check the program *)
[@@deriving ord, sexp]

(* TODO: reactivate HOL4 once traits are parameterized by their associated types *)
let all = [ Coq; Lean; FStar; BorrowCheck ]

let of_string = function
  | "coq" -> Coq
  | "lean" -> Lean
  | "fstar" -> FStar
  | "hol4" -> HOL4
  | "borrow-check" -> BorrowCheck
  | backend -> failwith ("Unknown backend: `" ^ backend ^ "`")

let to_string = function
  | Coq -> "coq"
  | Lean -> "lean"
  | FStar -> "fstar"
  | HOL4 -> "hol4"
  | BorrowCheck -> "borrow-check"

let to_command = function
  | BorrowCheck -> [ "-borrow-check" ]
  | x -> [ "-backend"; to_string x ]

module Map = struct
  (* Hack to be able to include things from the parent module with the same names *)
  type backend_t = t

  let backend_compare = compare

  include Map.Make (struct
    type t = backend_t

    let compare = backend_compare
  end)

  (* Make a new map with one entry per backend, given by `f` *)
  let make (f : backend_t -> 'a) : 'a t =
    List.fold_left (fun map backend -> add backend (f backend) map) empty all

  (* Set this value for all the backends in `backends` *)
  let add_each (backends : backend_t list) (v : 'a) (map : 'a t) : 'a t =
    List.fold_left (fun map backend -> add backend v map) map backends

  (* Updates all the backends in `backends` with `f` *)
  let update_each (backends : backend_t list) (f : 'a -> 'a) (map : 'a t) : 'a t
      =
    List.fold_left
      (fun map backend -> update backend (Option.map f) map)
      map backends
end
