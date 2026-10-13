(* Stand-in for Pulse_Lib_Reference (OCaml extraction target of
   Pulse.Lib.Reference): Pulse's separation-logic `ref` extracts to a
   plain mutable OCaml ref at runtime, with its ghost
   permission/fraction arguments erased to `unit`. The argument
   counts/order here (`alloc () v`, `read r () ()`, `write r v`) match
   exactly what the extracted Z3PulseProofChecker.ml / Z3PulseProof-
   CheckerJson.ml call sites expect. *)

type 'a ref = 'a Stdlib.ref

let alloc (_ : unit) (v : 'a) : 'a ref = Stdlib.ref v
let read (r : 'a ref) (_ : unit) (_ : unit) : 'a = !r
let write (r : 'a ref) (v : 'a) : unit = r := v
