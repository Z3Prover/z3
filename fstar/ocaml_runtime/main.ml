(* SMT-LIB input is solved and checked in this executable. *)

let () =
  match Stdlib.Array.to_list Stdlib.Sys.argv with
   | [_; "--version"] -> Stdlib.print_endline (Z3Native.version ()); Stdlib.exit 0
   | _ :: args -> Z3NativeMain.run args
   | [] -> Z3NativeMain.run []
