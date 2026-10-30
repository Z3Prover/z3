(* F* characters are Unicode scalar values, not OCaml byte characters. *)
type char = int

let int_of_char (c : char) : Prims.int = Z.of_int c
