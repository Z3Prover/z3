(* Character code points use the extracted machine-word representation. *)

type t = int

let v (x : t) : Prims.int = Z.of_int x
