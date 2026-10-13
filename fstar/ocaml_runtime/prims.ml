(* Minimal hand-written stand-in for F*'s "Prims" OCaml-extraction runtime
   module. Only the identifiers actually referenced by the extracted
   Z3*.ml files (see extract_full/) are implemented.

   Design choice: "Prims.int" is represented as native OCaml `int`
   (not an arbitrary-precision Zarith value). This matches the
   extracted code itself, which applies OCaml's own `+`/`-`/`*`/`/`/
   `mod`/comparison operators directly to values of type Prims.int
   (e.g. Z3BvTheory.ml's `a - (Prims.pow2 n)`) -- that only type-checks
   if Prims.int *is* OCaml's native int. The practical consequence is
   a 63-bit (signed) ceiling on any integer/bit-vector width handled
   by this checker; documented as a known limitation. *)

type nonrec int = int
type nonrec bool = bool
type nonrec string = string
type nonrec 'a list = 'a list
type nat = int
type pos = int

let int_zero : int = 0
let int_one : int = 1

let of_int (n : int) : int = n

let not (b : bool) : bool = Stdlib.not b

let pow2 (n : int) : int = 1 lsl n
