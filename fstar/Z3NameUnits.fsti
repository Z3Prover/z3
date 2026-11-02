module Z3NameUnits

(* The character count of a name within a limit. Both implementations below are
   this definition; extraction realizes it natively by a scan that stops after
   `limit + 1` characters: ocaml_runtime/Z3NameUnits.ml (OCaml, linked instead of
   the extraction of Z3NameUnits.fst) and `z3_name_units_scan` in
   cherry_runtime/kernel.c (Cherry, through Z3NameUnits-c.cherry.fst). Their
   agreement with `FStar.String.strlen` is a trusted runtime binding, tested
   natively against the runtime decoders. *)
val scan_units (s:string) (limit:nat)
  : r:int{r == (if FStar.String.strlen s <= limit then FStar.String.strlen s else -1)}
