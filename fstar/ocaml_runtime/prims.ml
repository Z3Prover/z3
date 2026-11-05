(* The build opens Prims in extracted modules, so these operators must implement
   F*'s unbounded integers rather than OCaml's wrapping machine arithmetic. *)
type int = Z.t
type nonrec bool = bool
type nonrec string = string
type nonrec 'a list = 'a list
type nat = int
type pos = int

let int_zero : int = Z.zero
let int_one : int = Z.one

let of_int (n : Stdlib.Int.t) : int = Z.of_int n
let parse_int (n : string) : int = Z.of_string n
let string_of_int (n : int) : string = Z.to_string n

let strcat (a : string) (b : string) : string = a ^ b

let ( + ) = Z.add
let ( - ) = Z.sub
let ( * ) = Z.mul
let ( / ) = Z.ediv
let ( mod ) = Z.erem
let ( ~- ) = Z.neg
let ( < ) a b = Z.compare a b < 0
let ( <= ) a b = Z.compare a b <= 0
let ( > ) a b = Z.compare a b > 0
let ( >= ) a b = Z.compare a b >= 0

(* Custard's names for the Prims operators. *)
let op_Plus = ( + )
let op_Minus = ( - )
let op_Star = ( * )
let op_Slash = ( / )
let op_Percent = ( mod )
let op_Tilde_Minus = ( ~- )
let op_Less = ( < )
let op_Less_Equals = ( <= )
let op_Greater = ( > )
let op_Greater_Equals = ( >= )

let not (b : bool) : bool = Stdlib.not b

(* Extracted equality types contain algebraic data, not OCaml floats or
   functions. Total comparison skips physically shared subtrees even below
   distinct wrappers; polymorphic equality unfolds them repeatedly. *)
let ( = ) a b = Stdlib.( = ) (Stdlib.compare a b) 0
let ( <> ) a b = Stdlib.not (a = b)

let pow2 (n : int) : int = Z.shift_left Z.one (Z.to_int n)
