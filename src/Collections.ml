(** The following file redefines several modules like Map or Set. *)

module F = Format

module List = struct
  include List

  (** Split a list at a given index.
  
      `split_at ls i` splits `ls` into two lists where the first list has
      length `i`.
      
      Raise `Failure` if the list is too short.
  *)
  let rec split_at (ls : 'a list) (i : int) =
    if i < 0 then raise (Invalid_argument "split_at take positive integers")
    else if i = 0 then ([], ls)
    else
      match ls with
      | [] ->
          raise
            (Failure "The int given to split_at should be <= the list's length")
      | x :: ls' ->
          let ls1, ls2 = split_at ls' (i - 1) in
          (x :: ls1, ls2)

  (** Pop the last element of a list
     
      Raise `Failure` if the list is empty.
   *)
  let rec pop_last (ls : 'a list) : 'a list * 'a =
    match ls with
    | [] -> raise (Failure "The list is empty")
    | [ x ] -> ([], x)
    | x :: ls ->
        let ls, last = pop_last ls in
        (x :: ls, last)
end

module type OrderedType = sig
  include Map.OrderedType

  val to_string : t -> string

  val pp_t : Format.formatter -> t -> unit

  val show_t : t -> string
end

module type Map = sig
  include Map.S

  val to_string : string option -> ('a -> string) -> 'a t -> string
  (** "Simple" pretty printing function.
  
      Is useful when we need to customize a bit [show_t], but without using
      something as burdensome as [pp_t].
  
      `to_string (Some indent) m` prints `m` by breaking line after every binding
      and inserting `indent`.
   *)

  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit

  val show : ('a -> string) -> 'a t -> string
end

module MakeMap (Ord : OrderedType) : Map with type key = Ord.t = struct
  module Map = Map.Make (Ord)
  include Map

  let to_string indent_opt a_to_string m =
    let indent, break =
      match indent_opt with Some indent -> (indent, "\n") | None -> ("", " ")
    in
    let sep = "," ^ break in
    let ls =
      Map.fold
        (fun key v ls ->
          (indent ^ Ord.to_string key ^ " -> " ^ a_to_string v) :: ls)
        m []
    in
    match ls with
    | [] -> "{}"
    | _ -> "{" ^ break ^ String.concat sep (List.rev ls) ^ break ^ "}"

  let pp (pp_a : Format.formatter -> 'a -> unit) (fmt : Format.formatter)
      (m : 'a t) : unit =
    let pp_string = F.pp_print_string fmt in
    let pp_space () = F.pp_print_space fmt () in
    pp_string "{";
    F.pp_open_box fmt 2;
    Map.iter
      (fun key x ->
        Ord.pp_t fmt key;
        pp_space ();
        pp_string "->";
        pp_space ();
        pp_a fmt x;
        pp_string ",";
        F.pp_print_break fmt 1 0)
      m;
    F.pp_close_box fmt ();
    F.pp_print_break fmt 0 0;
    pp_string "}"

  let show show_a m = to_string None show_a m
end

module type Set = sig
  include Set.S

  val to_string : string option -> t -> string
  (** "Simple" pretty printing function.
  
      Is useful when we need to customize a bit [show_t], but without using
      something as burdensome as [pp_t].
  
      `to_string (Some indent) s` prints `s` by breaking line after every element
      and inserting `indent`.
   *)

  val pp : Format.formatter -> t -> unit

  val show : t -> string
end

module MakeSet (Ord : OrderedType) : Set with type elt = Ord.t = struct
  module Set = Set.Make (Ord)
  include Set

  let to_string indent_opt m =
    let indent, break =
      match indent_opt with Some indent -> (indent, "\n") | None -> ("", " ")
    in
    let sep = "," ^ break in
    let ls = Set.fold (fun v ls -> (indent ^ Ord.to_string v) :: ls) m [] in
    match ls with
    | [] -> "{}"
    | _ -> "{" ^ break ^ String.concat sep (List.rev ls) ^ break ^ "}"

  let pp (fmt : Format.formatter) (m : t) : unit =
    let pp_string = F.pp_print_string fmt in
    pp_string "{";
    F.pp_open_box fmt 2;
    Set.iter
      (fun x ->
        Ord.pp_t fmt x;
        pp_string ",";
        F.pp_print_break fmt 1 0)
      m;
    F.pp_close_box fmt ();
    F.pp_print_break fmt 0 0;
    pp_string "}"

  let show s = to_string None s
end
