(** The following file redefines several modules like Map or Set. *)

module F = Format

module List = struct
  include List

  (** Split a list at a given index.
  
      [split_at ls i] splits [ls] into two lists where the first list has
      length [i].
      
      Raise [Failure] if the list is too short.
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
     
      Raise [Failure] if the list is empty.
   *)
  let rec pop_last (ls : 'a list) : 'a list * 'a =
    match ls with
    | [] -> raise (Failure "The list is empty")
    | [ x ] -> ([], x)
    | x :: ls ->
        let ls, last = pop_last ls in
        (x :: ls, last)

  (** Return the n first elements of the list *)
  let prefix (n : int) (ls : 'a list) : 'a list = fst (split_at ls n)

  (** Iter and link the iterations.

      Iterate over a list, but call a function between every two elements
      (but not before the first element, and not after the last).
   *)
  let iter_link (link : unit -> unit) (f : 'a -> unit) (ls : 'a list) : unit =
    let rec iter ls =
      match ls with
      | [] -> ()
      | [ x ] -> f x
      | x :: y :: ls ->
          f x;
          link ();
          iter (y :: ls)
    in
    iter ls

  (** Fold and link the iterations.

      Similar to {!iter_link} but for fold left operations.
   *)
  let fold_left_link (link : unit -> unit) (f : 'a -> 'b -> 'a) (init : 'a)
      (ls : 'b list) : 'a =
    let rec fold (acc : 'a) (ls : 'b list) : 'a =
      match ls with
      | [] -> acc
      | [ x ] -> f acc x
      | x :: y :: ls ->
          let acc = f acc x in
          link ();
          fold acc (y :: ls)
    in
    fold init ls

  let to_cons_nil (ls : 'a list) : 'a =
    match ls with
    | [ x ] -> x
    | _ -> raise (Failure "The list should have length exactly one")

  let pop (ls : 'a list) : 'a * 'a list =
    match ls with
    | x :: ls' -> (x, ls')
    | _ -> raise (Failure "The list should have length > 0")
end

module type OrderedType = sig
  include Map.OrderedType

  val to_string : t -> string
  val pp_t : Format.formatter -> t -> unit
  val show_t : t -> string
end

(** Ordered string *)
module OrderedString : OrderedType with type t = string = struct
  include String

  let to_string s = s
  let pp_t fmt s = Format.pp_print_string fmt s
  let show_t s = s
end

module type Map = sig
  include Map.S

  val add_list : (key * 'a) list -> 'a t -> 'a t
  val of_list : (key * 'a) list -> 'a t

  (** "Simple" pretty printing function.
  
      Is useful when we need to customize a bit [show_t], but without using
      something as burdensome as [pp_t].
  
      [to_string (Some indent) m] prints [m] by breaking line after every binding
      and inserting [indent].
   *)
  val to_string : string option -> ('a -> string) -> 'a t -> string

  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
  val show : ('a -> string) -> 'a t -> string
end

module MakeMap (Ord : OrderedType) : Map with type key = Ord.t = struct
  module Map = Map.Make (Ord)
  include Map

  let add_list bl m = List.fold_left (fun s (key, e) -> add key e s) m bl
  let of_list bl = add_list bl empty

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

  val add_list : elt list -> t -> t
  val of_list : elt list -> t

  (** "Simple" pretty printing function.
  
      Is useful when we need to customize a bit [show_t], but without using
      something as burdensome as [pp_t].
  
      [to_string (Some indent) s] prints [s] by breaking line after every element
      and inserting [indent].
   *)
  val to_string : string option -> t -> string

  val pp : Format.formatter -> t -> unit
  val show : t -> string
  val pairwise_distinct : elt list -> bool
end

module MakeSet (Ord : OrderedType) : Set with type elt = Ord.t = struct
  module Set = Set.Make (Ord)
  include Set

  let add_list bl s = List.fold_left (fun s e -> add e s) s bl
  let of_list bl = add_list bl empty

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

  let pairwise_distinct ls =
    let s = ref empty in
    let rec check ls =
      match ls with
      | [] -> true
      | x :: ls' ->
          if mem x !s then false
          else (
            s := add x !s;
            check ls')
    in
    check ls
end

(** A map where the bindings are injective (i.e., if two keys are distinct,
    their bindings are distinct).
    
    This is useful for instance when generating mappings from our internal
    identifiers to names (i.e., strings) when generating code, in order to
    make sure that we don't have potentially dangerous collisions.
 *)
module type InjMap = sig
  type key
  type elem
  type t

  val empty : t
  val is_empty : t -> bool
  val mem : key -> t -> bool
  val add : key -> elem -> t -> t
  val singleton : key -> elem -> t
  val remove : key -> t -> t
  val compare : (elem -> elem -> int) -> t -> t -> int
  val equal : (elem -> elem -> bool) -> t -> t -> bool
  val iter : (key -> elem -> unit) -> t -> unit
  val fold : (key -> elem -> 'b -> 'b) -> t -> 'b -> 'b
  val for_all : (key -> elem -> bool) -> t -> bool
  val exists : (key -> elem -> bool) -> t -> bool
  val filter : (key -> elem -> bool) -> t -> t
  val partition : (key -> elem -> bool) -> t -> t * t
  val cardinal : t -> int
  val bindings : t -> (key * elem) list
  val min_binding : t -> key * elem
  val min_binding_opt : t -> (key * elem) option
  val max_binding : t -> key * elem
  val max_binding_opt : t -> (key * elem) option
  val choose : t -> key * elem
  val choose_opt : t -> (key * elem) option
  val split : key -> t -> t * elem option * t
  val find : key -> t -> elem
  val find_opt : key -> t -> elem option
  val find_first : (key -> bool) -> t -> key * elem
  val find_first_opt : (key -> bool) -> t -> (key * elem) option
  val find_last : (key -> bool) -> t -> key * elem
  val find_last_opt : (key -> bool) -> t -> (key * elem) option
  val to_seq : t -> (key * elem) Seq.t
  val to_seq_from : key -> t -> (key * elem) Seq.t
  val add_seq : (key * elem) Seq.t -> t -> t
  val of_seq : (key * elem) Seq.t -> t
  val add_list : (key * elem) list -> t -> t
  val of_list : (key * elem) list -> t
end

(** See {!InjMap} *)
module MakeInjMap (Key : OrderedType) (Elem : OrderedType) :
  InjMap with type key = Key.t with type elem = Elem.t = struct
  module Map = MakeMap (Key)
  module Set = MakeSet (Elem)

  type key = Key.t
  type elem = Elem.t
  type t = { map : elem Map.t; elems : Set.t }

  let empty = { map = Map.empty; elems = Set.empty }
  let is_empty m = Map.is_empty m.map
  let mem k m = Map.mem k m.map

  let add k e m =
    assert (not (Set.mem e m.elems));
    { map = Map.add k e m.map; elems = Set.add e m.elems }

  let singleton k e = { map = Map.singleton k e; elems = Set.singleton e }

  let remove k m =
    match Map.find_opt k m.map with
    | None -> m
    | Some x -> { map = Map.remove k m.map; elems = Set.remove x m.elems }

  let compare f m1 m2 = Map.compare f m1.map m2.map
  let equal f m1 m2 = Map.equal f m1.map m2.map
  let iter f m = Map.iter f m.map
  let fold f m x = Map.fold f m.map x
  let for_all f m = Map.for_all f m.map
  let exists f m = Map.exists f m.map

  (** Small helper *)
  let bindings_to_elems_set (bls : (key * elem) list) : Set.t =
    let elems = List.map snd bls in
    let elems = List.fold_left (fun s e -> Set.add e s) Set.empty elems in
    elems

  (** Small helper *)
  let map_to_elems_set (map : elem Map.t) : Set.t =
    bindings_to_elems_set (Map.bindings map)

  (** Small helper *)
  let map_to_t (map : elem Map.t) : t =
    let elems = map_to_elems_set map in
    { map; elems }

  let filter f m =
    let map = Map.filter f m.map in
    let elems = map_to_elems_set map in
    { map; elems }

  let partition f m =
    let map1, map2 = Map.partition f m.map in
    (map_to_t map1, map_to_t map2)

  let cardinal m = Map.cardinal m.map
  let bindings m = Map.bindings m.map
  let min_binding m = Map.min_binding m.map
  let min_binding_opt m = Map.min_binding_opt m.map
  let max_binding m = Map.max_binding m.map
  let max_binding_opt m = Map.max_binding_opt m.map
  let choose m = Map.choose m.map
  let choose_opt m = Map.choose_opt m.map

  let split k m =
    let l, data, r = Map.split k m.map in
    let l = map_to_t l in
    let r = map_to_t r in
    (l, data, r)

  let find k m = Map.find k m.map
  let find_opt k m = Map.find_opt k m.map
  let find_first k m = Map.find_first k m.map
  let find_first_opt k m = Map.find_first_opt k m.map
  let find_last k m = Map.find_last k m.map
  let find_last_opt k m = Map.find_last_opt k m.map
  let to_seq m = Map.to_seq m.map
  let to_seq_from k m = Map.to_seq_from k m.map

  let rec add_seq s m =
    (* Note that it is important to check that we don't add bindings mapping
     * to the same element *)
    match s () with
    | Seq.Nil -> m
    | Seq.Cons ((k, e), s) ->
        let m = add k e m in
        add_seq s m

  let of_seq s = add_seq s empty
  let add_list ls m = List.fold_left (fun m (key, elem) -> add key elem m) m ls
  let of_list ls = add_list ls empty
end
