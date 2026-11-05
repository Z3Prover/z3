(* Stand-in for FStar_Pervasives_Native (OCaml extraction target of
   FStar.Pervasives.Native): option/tuple projections only. *)

type nonrec 'a option = 'a option = None | Some of 'a

let fst (p : 'a * 'b) : 'a = Stdlib.fst p
let snd (p : 'a * 'b) : 'b = Stdlib.snd p
