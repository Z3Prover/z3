(* Stand-in for FStar_String (OCaml extraction target of
   FStar.String). Since `char` here is a plain Unicode-code-point int
   (see fStar_Char.ml), strings are treated byte-wise (ASCII/Latin-1
   range); this is sufficient for this project's JSON proof-document
   format, which is pure ASCII. *)

let strlen (s : Prims.string) : Prims.int = Stdlib.String.length s

let list_of_string (s : Prims.string) : FStar_Char.char Prims.list =
  Stdlib.List.init (Stdlib.String.length s) (fun i ->
      Stdlib.Char.code s.[i])

let string_of_list (cs : FStar_Char.char Prims.list) : Prims.string =
  Stdlib.String.init (Stdlib.List.length cs) (fun i ->
      Stdlib.Char.chr (Stdlib.List.nth cs i))
