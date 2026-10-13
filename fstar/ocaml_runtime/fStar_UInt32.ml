(* Stand-in for FStar_UInt32 (OCaml extraction target of
   FStar.UInt32): represented as a plain Prims.int, so `v` (the
   "forget the machine-width refinement" projection) is the
   identity. *)

type t = Prims.int

let v (x : t) : Prims.int = x
