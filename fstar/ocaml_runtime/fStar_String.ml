(* Stand-in for FStar_String (OCaml extraction target of FStar.String),
   with only what the extracted checker uses and no Batteries dependency.

   `list_of_string` decodes the string as the Cherry runtime's
   `FStar.String.list_of_string` (ulib `FStar.String-c.cherry.fst`) does: one
   character per lead byte, whose value gives the step (below 0x80: 1 byte,
   below 0xE0: 2, below 0xF0: 3, otherwise 4). A character is its code point
   (an `int`, FStar.Char's representation), or U+FFFD when the lead byte is a
   continuation byte, 0xC0, 0xC1 or above 0xF4, when a continuation byte is
   missing (also past the end of the string, which is never read), or when the
   value is a surrogate or above U+10FFFF. Overlong 3- and 4-byte forms keep
   their value, as in the Cherry runtime. One difference: the Cherry runtime
   maps the valid scalar U+D7FF to U+FFFD; here it is U+D7FF. The checker uses
   only the length of this list (`Z3UnifiedProof.name_length`), which is the
   same on both runtimes for every byte string. It is a loop, with no stack in
   the length of the string.

   `strlen` is `List.length (list_of_string s)`, by the same steps without
   building the list. On valid UTF-8 this counts the code points. On any byte
   string it is at least the byte length divided by 4 (every step covers at
   most 4 bytes), so a malformed string (stray continuation bytes, truncated
   sequences) is never counted as shorter than that; both backends give the
   same count on every input. *)

let width (b : int) : int =
  if b < 0x80 then 1 else if b < 0xE0 then 2 else if b < 0xF0 then 3 else 4

let list_of_string (s : string) : int list =
  let n = Stdlib.String.length s in
  let byte i = if i < n then Stdlib.Char.code (Stdlib.String.get s i) else 256 in
  let cont i = let b = byte i in if 0x80 <= b && b < 0xC0 then b - 0x80 else -1 in
  let decode i =
    let b = byte i in
    if b < 0x80 then b
    else if b < 0xC2 then 0xFFFD
    else if b < 0xE0 then
      let c1 = cont (i + 1) in
      if c1 < 0 then 0xFFFD else (b - 0xC0) * 64 + c1
    else if b < 0xF0 then
      let c1 = cont (i + 1) and c2 = cont (i + 2) in
      if c1 < 0 || c2 < 0 then 0xFFFD else (b - 0xE0) * 4096 + c1 * 64 + c2
    else if b < 0xF5 then
      let c1 = cont (i + 1) and c2 = cont (i + 2) and c3 = cont (i + 3) in
      if c1 < 0 || c2 < 0 || c3 < 0 then 0xFFFD
      else (b - 0xF0) * 262144 + c1 * 4096 + c2 * 64 + c3
    else 0xFFFD in
  let scalar c = if (0 <= c && c < 0xD800) || (0xE000 <= c && c <= 0x10FFFF) then c else 0xFFFD in
  let rec go i acc =
    if i >= n then Stdlib.List.rev acc
    else go (i + width (byte i)) (scalar (decode i) :: acc) in
  go 0 []

let strlen (s : string) : Prims.int =
  let n = Stdlib.String.length s in
  let rec go i k =
    if i >= n then k
    else go (i + width (Stdlib.Char.code (Stdlib.String.get s i))) (k + 1) in
  Z.of_int (go 0 0)
