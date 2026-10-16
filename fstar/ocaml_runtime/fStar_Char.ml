(* Stand-in for FStar_Char (OCaml extraction target of FStar.Char).
   F*'s `char` extracts as a plain integer Unicode code point, which
   is why the extracted Z3ProofJson.ml code pattern-matches against
   raw int literals (e.g. `| 45::c::cs' -> ...` for the '-' character)
   -- character code points remain machine integers, unlike Prims.int. *)

type char = int

let int_of_char (c : char) : Prims.int = Z.of_int c
let u32_of_char (c : char) : int = c
