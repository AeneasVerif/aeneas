
(* Taken from there:
   https://github.com/mit-plv/koika/blob/master/coq/IdentParsing.v
*)

(*! Frontend | Ltac2-based identifier parsing for prettier notations !*)
Require Import Coq.NArith.NArith Coq.Strings.String.
Require Import Coq.Init.Byte.
Require Import Ltac2.Ltac2.

Import Ltac2.Init.
Import Ltac2.Notations.

Import Coq.Lists.List.ListNotations.
Open Scope list.

Ltac2 compute c :=
  Std.eval_vm None c.

Ltac2 rec array_blit_list pos ls arr :=
  match ls with
  | [] => ()
  | h :: ls => Array.set arr pos h; array_blit_list (Int.add pos 1) ls arr
  end.

Ltac2 array_of_list default len ls :=
  let arr := Array.make len default in
  array_blit_list 0 ls arr;
    arr.

Module Safe.
  Ltac2 string_to_coq_list type coq_of_char s :=
    let rec to_list acc pos :=
        match Int.equal pos 0 with
        | true => acc
        | false =>
          let pos := Int.sub pos 1 in
          let b := coq_of_char (String.get s pos) in
          to_list (constr:(List.cons $b $acc)) pos
        end in
    to_list (constr:(@List.nil $type)) (String.length s).

  Ltac2 coq_string_of_string' coq_string_of_coq_list type coq_of_char s :=
    let bs := string_to_coq_list type coq_of_char s in
    compute constr:($coq_string_of_coq_list $bs).
End Safe.

Module Unsafe.
  Module U := Ltac2.Constr.Unsafe.

  Ltac2 string_to_coq_list type coq_of_char s :=
    let cons := constr:(@cons) in
    let dummy_constr := constr:(tt) in
    let rec to_list acc pos :=
        match Int.equal pos 0 with
        | true => acc
        | false =>
          let pos := Int.sub pos 1 in
          let b := coq_of_char (String.get s pos) in
          to_list (U.make (U.App cons (array_of_list dummy_constr 3 [type; b; acc]))) pos
        end in
    match U.check (to_list constr:(@List.nil $type) (String.length s)) with
    | Val v => v
    | Err exn => Control.throw exn
    end.

  Ltac2 coq_string_of_string' coq_string_of_coq_list type coq_of_char s :=
    let bs := string_to_coq_list type coq_of_char s in
    compute constr:($coq_string_of_coq_list $bs).
End Unsafe.

Import Unsafe.

Module Linear.
  (* char → int →[O(n)] N → ascii *)

  Ltac2 rec int_to_coq_N' n :=
    match Int.equal n 0 with
    | true => constr:(N.zero)
    | false => let n := int_to_coq_N' (Int.sub n 1) in
              constr:(N.succ $n)
    end.

  Ltac2 int_to_coq_N n :=
    let val := int_to_coq_N' n in
    compute val.

  Definition string_of_list_N list_N :=
    String.string_of_list_ascii (List.map Ascii.ascii_of_N list_N).

  Ltac2 coq_string_of_string s :=
    coq_string_of_string' constr:(string_of_list_N) constr:(N) (fun c => int_to_coq_N (Char.to_int c)) s.
End Linear.

Module TestBits.
  (* char → int →[O(log2 n)] N → list bits → _ *)

  Ltac2 int_gt n n' :=
    Int.equal (Int.compare n n') 1.

  Ltac2 rec bits_of_int' pow2s n :=
    match pow2s with
    | [] => []
    | pow2 :: pow2s =>
      match int_gt pow2 n with
      | true => false :: bits_of_int' pow2s n
      | false => true :: bits_of_int' pow2s (Int.sub n pow2)
      end
    end.

  Ltac2 rec bits_of_char c :=
    bits_of_int' [128; 64; 32; 16; 8; 4; 2; 1] (Char.to_int c).

  Ltac2 list_pop fn l :=
    match l with
    | [] => Control.throw Match_failure
    | h :: t => (fn h, t)
    end.

  Ltac2 coq_bool_of_bool b :=
    match b with
    | true => constr:(true)
    | false => constr:(false)
    end.

  Ltac2 map_char_bits c fn :=
    let bs := bits_of_char c in
    let (b0, bs) := list_pop coq_bool_of_bool bs in
    let (b1, bs) := list_pop coq_bool_of_bool bs in
    let (b2, bs) := list_pop coq_bool_of_bool bs in
    let (b3, bs) := list_pop coq_bool_of_bool bs in
    let (b4, bs) := list_pop coq_bool_of_bool bs in
    let (b5, bs) := list_pop coq_bool_of_bool bs in
    let (b6, bs) := list_pop coq_bool_of_bool bs in
    let (b7, bs) := list_pop coq_bool_of_bool bs in
    fn b7 b6 b5 b4 b3 b2 b1 b0.
End TestBits.

Module TestBitsBytes.
  (* char → int →[O(log2 n)] byte *)

  Ltac2 coq_byte_of_char chr :=
    TestBits.map_char_bits
      chr
      (fun b7 b6 b5 b4 b3 b2 b1 b0 =>
         compute constr:(Byte.of_bits ($b7, ($b6, ($b5, ($b4, ($b3, ($b2, ($b1, $b0))))))))).

  Ltac2 coq_string_of_string s :=
    coq_string_of_string' constr:(string_of_list_byte) constr:(Byte.byte) coq_byte_of_char s.
End TestBitsBytes.

Module TestBitsAscii.
  (* char → int →[O(log2 n)] ascii *)

  Ltac2 coq_ascii_of_char chr :=
    TestBits.map_char_bits
      chr
      (fun b7 b6 b5 b4 b3 b2 b1 b0 =>
         constr:(Ascii.Ascii $b0 $b1 $b2 $b3 $b4 $b5 $b6 $b7)).

  Ltac2 coq_string_of_string s :=
    coq_string_of_string' constr:(string_of_list_ascii) constr:(Ascii.ascii) coq_ascii_of_char s.
End TestBitsAscii.

Module LookupTable.
  (* char → int →[O(1)] byte *)

  Ltac2 bytes_list () :=
    [constr:(x00); constr:(x01); constr:(x02); constr:(x03)
     ; constr:(x04); constr:(x05); constr:(x06); constr:(x07)
     ; constr:(x08); constr:(x09); constr:(x0a); constr:(x0b)
     ; constr:(x0c); constr:(x0d); constr:(x0e); constr:(x0f)
     ; constr:(x10); constr:(x11); constr:(x12); constr:(x13)
     ; constr:(x14); constr:(x15); constr:(x16); constr:(x17)
     ; constr:(x18); constr:(x19); constr:(x1a); constr:(x1b)
     ; constr:(x1c); constr:(x1d); constr:(x1e); constr:(x1f)
     ; constr:(x20); constr:(x21); constr:(x22); constr:(x23)
     ; constr:(x24); constr:(x25); constr:(x26); constr:(x27)
     ; constr:(x28); constr:(x29); constr:(x2a); constr:(x2b)
     ; constr:(x2c); constr:(x2d); constr:(x2e); constr:(x2f)
     ; constr:(x30); constr:(x31); constr:(x32); constr:(x33)
     ; constr:(x34); constr:(x35); constr:(x36); constr:(x37)
     ; constr:(x38); constr:(x39); constr:(x3a); constr:(x3b)
     ; constr:(x3c); constr:(x3d); constr:(x3e); constr:(x3f)
     ; constr:(x40); constr:(x41); constr:(x42); constr:(x43)
     ; constr:(x44); constr:(x45); constr:(x46); constr:(x47)
     ; constr:(x48); constr:(x49); constr:(x4a); constr:(x4b)
     ; constr:(x4c); constr:(x4d); constr:(x4e); constr:(x4f)
     ; constr:(x50); constr:(x51); constr:(x52); constr:(x53)
     ; constr:(x54); constr:(x55); constr:(x56); constr:(x57)
     ; constr:(x58); constr:(x59); constr:(x5a); constr:(x5b)
     ; constr:(x5c); constr:(x5d); constr:(x5e); constr:(x5f)
     ; constr:(x60); constr:(x61); constr:(x62); constr:(x63)
     ; constr:(x64); constr:(x65); constr:(x66); constr:(x67)
     ; constr:(x68); constr:(x69); constr:(x6a); constr:(x6b)
     ; constr:(x6c); constr:(x6d); constr:(x6e); constr:(x6f)
     ; constr:(x70); constr:(x71); constr:(x72); constr:(x73)
     ; constr:(x74); constr:(x75); constr:(x76); constr:(x77)
     ; constr:(x78); constr:(x79); constr:(x7a); constr:(x7b)
     ; constr:(x7c); constr:(x7d); constr:(x7e); constr:(x7f)
     ; constr:(x80); constr:(x81); constr:(x82); constr:(x83)
     ; constr:(x84); constr:(x85); constr:(x86); constr:(x87)
     ; constr:(x88); constr:(x89); constr:(x8a); constr:(x8b)
     ; constr:(x8c); constr:(x8d); constr:(x8e); constr:(x8f)
     ; constr:(x90); constr:(x91); constr:(x92); constr:(x93)
     ; constr:(x94); constr:(x95); constr:(x96); constr:(x97)
     ; constr:(x98); constr:(x99); constr:(x9a); constr:(x9b)
     ; constr:(x9c); constr:(x9d); constr:(x9e); constr:(x9f)
     ; constr:(xa0); constr:(xa1); constr:(xa2); constr:(xa3)
     ; constr:(xa4); constr:(xa5); constr:(xa6); constr:(xa7)
     ; constr:(xa8); constr:(xa9); constr:(xaa); constr:(xab)
     ; constr:(xac); constr:(xad); constr:(xae); constr:(xaf)
     ; constr:(xb0); constr:(xb1); constr:(xb2); constr:(xb3)
     ; constr:(xb4); constr:(xb5); constr:(xb6); constr:(xb7)
     ; constr:(xb8); constr:(xb9); constr:(xba); constr:(xbb)
     ; constr:(xbc); constr:(xbd); constr:(xbe); constr:(xbf)
     ; constr:(xc0); constr:(xc1); constr:(xc2); constr:(xc3)
     ; constr:(xc4); constr:(xc5); constr:(xc6); constr:(xc7)
     ; constr:(xc8); constr:(xc9); constr:(xca); constr:(xcb)
     ; constr:(xcc); constr:(xcd); constr:(xce); constr:(xcf)
     ; constr:(xd0); constr:(xd1); constr:(xd2); constr:(xd3)
     ; constr:(xd4); constr:(xd5); constr:(xd6); constr:(xd7)
     ; constr:(xd8); constr:(xd9); constr:(xda); constr:(xdb)
     ; constr:(xdc); constr:(xdd); constr:(xde); constr:(xdf)
     ; constr:(xe0); constr:(xe1); constr:(xe2); constr:(xe3)
     ; constr:(xe4); constr:(xe5); constr:(xe6); constr:(xe7)
     ; constr:(xe8); constr:(xe9); constr:(xea); constr:(xeb)
     ; constr:(xec); constr:(xed); constr:(xee); constr:(xef)
     ; constr:(xf0); constr:(xf1); constr:(xf2); constr:(xf3)
     ; constr:(xf4); constr:(xf5); constr:(xf6); constr:(xf7)
     ; constr:(xf8); constr:(xf9); constr:(xfa); constr:(xfb)
     ; constr:(xfc); constr:(xfd); constr:(xfe); constr:(xff)].

  Ltac2 bytes_table () :=
    array_of_list constr:(Byte.x00) 256 (bytes_list ()).

  Ltac2 byte_of_char bytes_table chr :=
    Array.get bytes_table (Char.to_int chr).

  Ltac2 coq_string_of_string s :=
    let table := bytes_table () in
    coq_string_of_string' constr:(string_of_list_byte) constr:(Byte.byte) (byte_of_char table) s.
End LookupTable.

Module Benchmarking.
  (* Ltac2 rec do_n_times n f := *)
  (*   match Int.equal n 0 with *)
  (*   | true => () *)
  (*   | false => f (); do_n_times (Int.sub n 1) f *)
  (*   end. *)

  (* Ltac2 small () := "aaaaaaaaa". *)
  (* Ltac2 medium () := "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa". *)
  (* Ltac2 large () := "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa". *)

  (* Time Ltac2 Eval (do_n_times 50 (fun () => Linear.coq_string_of_string (small ()))). *)
  (* Time Ltac2 Eval (do_n_times 50 (fun () => TestBitsAscii.coq_string_of_string (small ()))). *)
  (* Time Ltac2 Eval (do_n_times 50 (fun () => TestBitsBytes.coq_string_of_string (small ()))). *)
  (* Time Ltac2 Eval (do_n_times 50 (fun () => LookupTable.coq_string_of_string (small ()))). *)

  (* Time Ltac2 Eval (Linear.coq_string_of_string (medium ())). *)
  (* Time Ltac2 Eval (TestBitsAscii.coq_string_of_string (medium ())). *)
  (* Time Ltac2 Eval (TestBitsBytes.coq_string_of_string (medium ())). *)
  (* Time Ltac2 Eval (LookupTable.coq_string_of_string (medium ())). *)

  (* Time Ltac2 Eval (Linear.coq_string_of_string (large ())). *)
  (* Time Ltac2 Eval (TestBitsAscii.coq_string_of_string (large ())). *)
  (* Time Ltac2 Eval (TestBitsBytes.coq_string_of_string (large ())). *)
  (* Time Ltac2 Eval (LookupTable.coq_string_of_string (large ())). *)
End Benchmarking.

Ltac2 coq_string_of_string := LookupTable.coq_string_of_string.
Ltac2 coq_string_of_ident x := LookupTable.coq_string_of_string (Ident.to_string x).

Ltac2 Type exn ::= [ NoIdentInContext ].

Module TacInTerm.
  (* This is the original implementation, as described in the CoqPL'21 paper. *)
  Definition __Ltac2_MarkedIdent (A: Type) := A.

  Ltac serialize_ident_in_context :=
    ltac2:(match! goal with
           | [ h: __Ltac2_MarkedIdent _ |- _ ] =>
             let coq_string := coq_string_of_ident h in
             exact ($coq_string)
           | [  |- _ ] => Control.throw NoIdentInContext
           end).

  (* `binder_to_string` is useful when converting an identifier to a string but
     also using it as an actual binder. *)
  Notation binder_to_string body a :=
    (match (body: __Ltac2_MarkedIdent _) return string with
     | a => ltac:(serialize_ident_in_context)
     end) (only parsing).

  Notation ident_to_string a :=
    (binder_to_string true a) (only parsing).
End TacInTerm.

Module TC.
  (* This implementation uses typeclasses, which allows it to play better with
     other Coq mechanisms like `Program Definition`; it also makes
     `binder_to_string` unnecessary. *)

  (* The following examples fail with TacInTerm, but work with TC::

        Definition nlet {A P} (vars: list string) (val : A) (body : forall a : A, P a) : P val :=
          let x := val in body x.

        Notation "'Let/n' x := val 'in' body" :=
          (nlet [IdentParsing.TacInTerm.ident_to_string x] val (fun x => body))
            (at level 200, x ident, body at level 200,
             only parsing).
       Definition x := (Let/n a := 1 in a + 1).

       Notation "'Let/n' x := val 'in' body" :=
         (nlet [IdentParsing.binder_to_string val x] val (fun x => body))
           (at level 200, x ident, body at level 200,
            only parsing).
       Program Definition x := (Let/n a := _ in a + 1). *)

  Inductive __Ltac2_Marker := __ltac2_marker.

  Ltac serialize_ident_in_context :=
    ltac2:(match! goal with
           | [ h: __Ltac2_Marker |- _ ] =>
             let coq_string := coq_string_of_ident h in
             exact ($coq_string)
           | [  |- _ ] => Control.throw NoIdentInContext
           end).

  Class __IdentToString := __identToString: string.
  Hint Extern 1 __IdentToString => serialize_ident_in_context : typeclass_instances.

  Notation ident_to_string a :=
    (match __ltac2_marker return __IdentToString with a => _ end).
End TC.

Notation ident_to_string a :=
  (TacInTerm.ident_to_string a) (only parsing).

Notation binder_to_string body a :=
  (TacInTerm.binder_to_string body a) (only parsing).
