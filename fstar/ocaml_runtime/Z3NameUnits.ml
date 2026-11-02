(* Stand-in for the extraction of Z3NameUnits.fst, which build_ocaml_checker.ps1
   links instead after checking that the extraction is the reviewed definition.
   This is a TRUSTED runtime binding.

   `scan_units s limit` is `FStar.String.strlen s` when that is at most `limit`,
   else -1, for every nat `limit`. It steps over the characters as `strlen` in
   fStar_String.ml does (one per lead byte, of width 1 below 0x80, 2 below 0xE0,
   3 below 0xF0, otherwise 4; a width past the end ends the string) and stops
   before stepping over a character beyond `limit`. It reads one lead byte per
   step, at most `min (strlen s) limit`, never one at or past the end, and
   allocates nothing in the length of the string. `limit` is compared exactly
   (Zarith); one at or above the byte length counts fully. Indices stay below
   `Sys.max_string_length + 4`, far from `max_int`. `scan` also returns the
   number of lead bytes read. *)

let width (b : int) : int =
  if b < 0x80 then 1 else if b < 0xE0 then 2 else if b < 0xF0 then 3 else 4

let scan (s : string) (limit : Z.t) : int * int =
  let n = Stdlib.String.length s in
  let cap = if Z.geq limit (Z.of_int n) then n else Z.to_int limit in
  let rec go i reads =
    if i >= n then (reads, reads)
    else if reads = cap then (-1, reads)
    else go (i + width (Stdlib.Char.code (Stdlib.String.get s i))) (reads + 1) in
  go 0 0

let scan_units (s : string) (limit : Prims.int) : Prims.int = Z.of_int (fst (scan s limit))
