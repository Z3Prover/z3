(* Stand-in for Pulse_Lib_Dv (OCaml extraction target of
   Pulse.Lib.Dv's `unreachable`): the extracted checker only calls
   this on proof-checker branches it has already statically proved,
   via Pulse's type system, can never execute (see the `Pulse_Lib_Dv.
   unreachable ()` call sites gated behind refutable-but-impossible
   pattern matches in Z3PulseProofChecker.ml). A hard failure here
   would indicate either a bug in that static reasoning or a mismatch
   between this hand-written runtime and the verified source. *)

let unreachable (() : unit) : 'a =
  Stdlib.failwith "Pulse_Lib_Dv.unreachable: reached a statically-impossible branch"
