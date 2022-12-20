
(* Taken from Iris here:
   https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/proofmode/string_ident.v
*)

From Ltac2 Require Import Ltac2.
From Coq Require Import Strings.String.
From Coq Require Import Init.Byte.

Import List.ListNotations.
Local Open Scope list.

Ltac2 Type exn ::= [ NotStringLiteral(constr) | InvalidIdent(string) ].

Module StringToIdent.

  Ltac2 coq_byte_to_int b :=
    (match! b with
     (* generate this line with python3 -c 'print(" ".join([\'| x%02x => %d\' % (x,x) for x in range(256)]))' *)
     | x00 => 0 | x01 => 1 | x02 => 2 | x03 => 3 | x04 => 4 | x05 => 5 | x06 => 6 | x07 => 7 | x08 => 8 | x09 => 9 | x0a => 10 | x0b => 11 | x0c => 12 | x0d => 13 | x0e => 14 | x0f => 15 | x10 => 16 | x11 => 17 | x12 => 18 | x13 => 19 | x14 => 20 | x15 => 21 | x16 => 22 | x17 => 23 | x18 => 24 | x19 => 25 | x1a => 26 | x1b => 27 | x1c => 28 | x1d => 29 | x1e => 30 | x1f => 31 | x20 => 32 | x21 => 33 | x22 => 34 | x23 => 35 | x24 => 36 | x25 => 37 | x26 => 38 | x27 => 39 | x28 => 40 | x29 => 41 | x2a => 42 | x2b => 43 | x2c => 44 | x2d => 45 | x2e => 46 | x2f => 47 | x30 => 48 | x31 => 49 | x32 => 50 | x33 => 51 | x34 => 52 | x35 => 53 | x36 => 54 | x37 => 55 | x38 => 56 | x39 => 57 | x3a => 58 | x3b => 59 | x3c => 60 | x3d => 61 | x3e => 62 | x3f => 63 | x40 => 64 | x41 => 65 | x42 => 66 | x43 => 67 | x44 => 68 | x45 => 69 | x46 => 70 | x47 => 71 | x48 => 72 | x49 => 73 | x4a => 74 | x4b => 75 | x4c => 76 | x4d => 77 | x4e => 78 | x4f => 79 | x50 => 80 | x51 => 81 | x52 => 82 | x53 => 83 | x54 => 84 | x55 => 85 | x56 => 86 | x57 => 87 | x58 => 88 | x59 => 89 | x5a => 90 | x5b => 91 | x5c => 92 | x5d => 93 | x5e => 94 | x5f => 95 | x60 => 96 | x61 => 97 | x62 => 98 | x63 => 99 | x64 => 100 | x65 => 101 | x66 => 102 | x67 => 103 | x68 => 104 | x69 => 105 | x6a => 106 | x6b => 107 | x6c => 108 | x6d => 109 | x6e => 110 | x6f => 111 | x70 => 112 | x71 => 113 | x72 => 114 | x73 => 115 | x74 => 116 | x75 => 117 | x76 => 118 | x77 => 119 | x78 => 120 | x79 => 121 | x7a => 122 | x7b => 123 | x7c => 124 | x7d => 125 | x7e => 126 | x7f => 127 | x80 => 128 | x81 => 129 | x82 => 130 | x83 => 131 | x84 => 132 | x85 => 133 | x86 => 134 | x87 => 135 | x88 => 136 | x89 => 137 | x8a => 138 | x8b => 139 | x8c => 140 | x8d => 141 | x8e => 142 | x8f => 143 | x90 => 144 | x91 => 145 | x92 => 146 | x93 => 147 | x94 => 148 | x95 => 149 | x96 => 150 | x97 => 151 | x98 => 152 | x99 => 153 | x9a => 154 | x9b => 155 | x9c => 156 | x9d => 157 | x9e => 158 | x9f => 159 | xa0 => 160 | xa1 => 161 | xa2 => 162 | xa3 => 163 | xa4 => 164 | xa5 => 165 | xa6 => 166 | xa7 => 167 | xa8 => 168 | xa9 => 169 | xaa => 170 | xab => 171 | xac => 172 | xad => 173 | xae => 174 | xaf => 175 | xb0 => 176 | xb1 => 177 | xb2 => 178 | xb3 => 179 | xb4 => 180 | xb5 => 181 | xb6 => 182 | xb7 => 183 | xb8 => 184 | xb9 => 185 | xba => 186 | xbb => 187 | xbc => 188 | xbd => 189 | xbe => 190 | xbf => 191 | xc0 => 192 | xc1 => 193 | xc2 => 194 | xc3 => 195 | xc4 => 196 | xc5 => 197 | xc6 => 198 | xc7 => 199 | xc8 => 200 | xc9 => 201 | xca => 202 | xcb => 203 | xcc => 204 | xcd => 205 | xce => 206 | xcf => 207 | xd0 => 208 | xd1 => 209 | xd2 => 210 | xd3 => 211 | xd4 => 212 | xd5 => 213 | xd6 => 214 | xd7 => 215 | xd8 => 216 | xd9 => 217 | xda => 218 | xdb => 219 | xdc => 220 | xdd => 221 | xde => 222 | xdf => 223 | xe0 => 224 | xe1 => 225 | xe2 => 226 | xe3 => 227 | xe4 => 228 | xe5 => 229 | xe6 => 230 | xe7 => 231 | xe8 => 232 | xe9 => 233 | xea => 234 | xeb => 235 | xec => 236 | xed => 237 | xee => 238 | xef => 239 | xf0 => 240 | xf1 => 241 | xf2 => 242 | xf3 => 243 | xf4 => 244 | xf5 => 245 | xf6 => 246 | xf7 => 247 | xf8 => 248 | xf9 => 249 | xfa => 250 | xfb => 251 | xfc => 252 | xfd => 253 | xfe => 254 | xff => 255
     end).

  Ltac2 coq_byte_to_char b :=
    Char.of_int (coq_byte_to_int b).

  Fixpoint coq_string_to_list_byte (s:string): list byte :=
    match s with
    | EmptyString => []
    | String c s => Ascii.byte_of_ascii c :: coq_string_to_list_byte s
    end.

  (* copy a list of Coq byte constrs into a string (already of the right length) *)
  Ltac2 rec coq_byte_list_blit_list (pos:int) (ls: constr) (str: string) :=
    match! ls with
    | nil => ()
    | ?c :: ?ls =>
      let b := coq_byte_to_char c in
      String.set str pos b; coq_byte_list_blit_list (Int.add pos 1) ls str
  end.

  Ltac2 rec coq_string_length (s: constr) :=
    match! s with
    | EmptyString => 0
    | String _ ?s' => Int.add 1 (coq_string_length s')
    | _ => Control.throw (NotStringLiteral(s))
    end.

  Ltac2 compute c :=
    Std.eval_vm None c.

  (* now we have enough to convert a Gallina string in a constr to an Ltac2
  native string *)
  Ltac2 coq_string_to_string (s: constr) :=
    let l := coq_string_length s in
    let str := String.make l (Char.of_int 0) in
    let bytes := compute constr:(coq_string_to_list_byte $s) in
    let _ := coq_byte_list_blit_list 0 bytes str in
    str.

  (* to convert the string to an identifier we have to use the tools from Fresh;
     note we pass Fresh.fresh and empy set of identifiers to avoid, so this
     isn't necessarily fresh in the context, but if that's desired we can always
     do it later with Ltac1's fresh. *)
  Ltac2 ident_from_string (s: string) :=
    match Ident.of_string s with
    | Some id => Fresh.fresh (Fresh.Free.of_ids []) id
    | None => Control.throw (InvalidIdent s)
    end.

  (* [coq_string_to_ident] is the Ltac2 function we want *)
  Ltac2 coq_string_to_ident (s: constr) := ident_from_string (coq_string_to_string s).

  (* We want to wrap this in an Ltac1 API, which requires passing a string to
     Ltac2 and then returning the resulting identifier.

    The only FFI from Ltac1 to Ltac2 is to call an Ltac2 expression that solves
    a goal. We'll solve that goal with `fun (x:unit) => tt` where the name x is
    the desired identifier - Coq remembers the identifier and we can extract it
    with Ltac1 pattern matching. *)

  Ltac2 get_opt o := match o with None => Control.throw Not_found | Some x => x end.

  (** this Ltac solves a goal of the form [unit -> unit] with a function that
  has the appropriate name *)

  Ltac coq_string_to_ident_lambda :=
    ltac2:(s1 |- let s := get_opt (Ltac1.to_constr s1) in
                 let ident := coq_string_to_ident s in
                 clear; (* needed since ident might already be in scope where
                 this is called *)
                 intros $ident;
                 exact tt).
End StringToIdent.

Ltac2 string_to_ident_2 s :=
  StringToIdent.coq_string_to_ident s.

(* Finally we wrap everything up by running coq_string_to_ident_lambda in a new
context using a tactic-in-terms, extracting just the identifier from the
produced lambda, and returning it as an Ltac1 value. *)
Ltac string_to_ident s :=
  let s := (eval cbv in s) in
  let x := constr:(ltac:(StringToIdent.coq_string_to_ident_lambda s) : unit -> unit) in
  match x with
  | (fun (name:_) => _) => name
  end.
