(* Stand-in for FStar_UInt (OCaml extraction target of FStar.UInt):
   fixed-width modular bit-vector arithmetic over `Prims.int` (which
   is itself plain OCaml `int` here -- see prims.ml). Every operation
   takes the bit-width `n` as its first argument and keeps its result
   normalized to the range [0, 2^n), matching Z3BvTheory.fst's `bv n`
   = `FStar_UInt.uint_t n` representation.

   Known limitation: since Prims.int is a 63-bit OCaml int (not an
   arbitrary-precision Zarith value), this only behaves correctly for
   bit-widths up to about 62. *)

type 'n uint_t = Prims.int

let mask (n : Prims.int) : Prims.int = (1 lsl n) - 1

let to_uint_t (n : Prims.int) (v : Prims.int) : Prims.int =
  let m = mask n in
  v land m

let ones (n : Prims.int) : Prims.int = mask n

let logand (_n : Prims.int) (a : Prims.int) (b : Prims.int) : Prims.int =
  a land b

let logor (_n : Prims.int) (a : Prims.int) (b : Prims.int) : Prims.int =
  a lor b

let logxor (_n : Prims.int) (a : Prims.int) (b : Prims.int) : Prims.int =
  a lxor b

let lognot (n : Prims.int) (a : Prims.int) : Prims.int =
  (Stdlib.lnot a) land (mask n)

let add_mod (n : Prims.int) (a : Prims.int) (b : Prims.int) : Prims.int =
  (a + b) land (mask n)

let sub_mod (n : Prims.int) (a : Prims.int) (b : Prims.int) : Prims.int =
  (a - b) land (mask n)

let mul_mod (n : Prims.int) (a : Prims.int) (b : Prims.int) : Prims.int =
  (a * b) land (mask n)

let udiv (_n : Prims.int) (a : Prims.int) (b : Prims.int) : Prims.int = a / b

let mod1 (_n : Prims.int) (a : Prims.int) (b : Prims.int) : Prims.int =
  a mod b

let shift_left (n : Prims.int) (a : Prims.int) (s : Prims.int) : Prims.int =
  if s >= n then 0 else (a lsl s) land (mask n)

let shift_right (n : Prims.int) (a : Prims.int) (s : Prims.int) : Prims.int =
  if s >= n then 0 else a lsr s

let rotate_left (n : Prims.int) (a : Prims.int) (s : Prims.int) : Prims.int =
  let s = if n = 0 then 0 else s mod n in
  ((a lsl s) lor (a lsr (n - s))) land (mask n)

let rotate_right (n : Prims.int) (a : Prims.int) (s : Prims.int) : Prims.int =
  let s = if n = 0 then 0 else s mod n in
  ((a lsr s) lor (a lsl (n - s))) land (mask n)

let zero_extends (_n : Prims.int) (_k : Prims.int) (a : Prims.int) : Prims.int
    =
  a
