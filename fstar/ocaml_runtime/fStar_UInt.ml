(* Fixed-width modular arithmetic over exact integers. *)

type 'n uint_t = Prims.int

let mask (n : Prims.int) : Prims.int = Z.pred (Prims.pow2 n)

let to_uint_t (n : Prims.int) (v : Prims.int) : Prims.int =
  let m = mask n in
  Z.logand v m

let ones (n : Prims.int) : Prims.int = mask n

let logand (_n : Prims.int) (a : Prims.int) (b : Prims.int) : Prims.int =
  Z.logand a b

let logor (_n : Prims.int) (a : Prims.int) (b : Prims.int) : Prims.int =
  Z.logor a b

let logxor (_n : Prims.int) (a : Prims.int) (b : Prims.int) : Prims.int =
  Z.logxor a b

let lognot (n : Prims.int) (a : Prims.int) : Prims.int =
  Z.logand (Z.lognot a) (mask n)

let add_mod (n : Prims.int) (a : Prims.int) (b : Prims.int) : Prims.int =
  Z.logand (Z.add a b) (mask n)

let sub_mod (n : Prims.int) (a : Prims.int) (b : Prims.int) : Prims.int =
  Z.logand (Z.sub a b) (mask n)

let mul_mod (n : Prims.int) (a : Prims.int) (b : Prims.int) : Prims.int =
  Z.logand (Z.mul a b) (mask n)

let udiv (_n : Prims.int) (a : Prims.int) (b : Prims.int) : Prims.int = Z.ediv a b

let mod1 (_n : Prims.int) (a : Prims.int) (b : Prims.int) : Prims.int =
  Z.erem a b

let mod_ = mod1

let shift_left (n : Prims.int) (a : Prims.int) (s : Prims.int) : Prims.int =
  if Z.geq s n then Z.zero else Z.logand (Z.shift_left a (Z.to_int s)) (mask n)

let shift_right (n : Prims.int) (a : Prims.int) (s : Prims.int) : Prims.int =
  if Z.geq s n then Z.zero else Z.shift_right a (Z.to_int s)

let rotate_left (n : Prims.int) (a : Prims.int) (s : Prims.int) : Prims.int =
  let s = if Z.equal n Z.zero then Z.zero else Z.erem s n in
  Z.logand
    (Z.logor (Z.shift_left a (Z.to_int s)) (Z.shift_right a (Z.to_int (Z.sub n s))))
    (mask n)

let rotate_right (n : Prims.int) (a : Prims.int) (s : Prims.int) : Prims.int =
  let s = if Z.equal n Z.zero then Z.zero else Z.erem s n in
  Z.logand
    (Z.logor (Z.shift_right a (Z.to_int s)) (Z.shift_left a (Z.to_int (Z.sub n s))))
    (mask n)

let zero_extends (_n : Prims.int) (_k : Prims.int) (a : Prims.int) : Prims.int
    =
  a
