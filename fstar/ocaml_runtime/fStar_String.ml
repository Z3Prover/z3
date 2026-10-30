(* Stand-in for FStar_String (OCaml extraction target of FStar.String),
   with only what the extracted checker uses and no Batteries dependency.

   `strlen` is `List.length (list_of_string s)`. It steps through the string
   exactly as the Cherry runtime's `FStar.String.list_of_string` does: one
   character per lead byte, whose value gives the step (below 0x80: 1 byte,
   below 0xE0: 2, below 0xF0: 3, otherwise 4). On valid UTF-8 this counts the
   code points. On any byte string it is at least the byte length divided by
   4 (every step covers at most 4 bytes), so a malformed string (stray
   continuation bytes, truncated sequences) is never counted as shorter than
   that; both backends give the same count on every input. *)

let strlen (s : string) : Prims.int =
  let n = Stdlib.String.length s in
  let rec go i k =
    if i >= n then k
    else
      let b = Stdlib.Char.code (Stdlib.String.get s i) in
      let w = if b < 0x80 then 1 else if b < 0xE0 then 2 else if b < 0xF0 then 3 else 4 in
      go (i + w) (k + 1) in
  Z.of_int (go 0 0)
