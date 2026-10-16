let read_all channel =
  let buffer = Buffer.create 4096 in
  (try while true do Buffer.add_channel buffer channel 4096 done
   with End_of_file -> ());
  Buffer.contents buffer

let run args =
  let statistics = ref false and timeout = ref Z.zero and path = ref None in
  let options = [
    "--stats", Arg.Set statistics, " Report phase timings and unique marshaled node counts";
    "--timeout-ms", Arg.String (fun value ->
        try
          let n = Z.of_string value in
          if Z.sign n < 0 || Z.gt n (Z.of_string "4294967295")
          then raise (Arg.Bad "invalid --timeout-ms");
          timeout := n
        with Invalid_argument _ -> raise (Arg.Bad "invalid --timeout-ms")),
      "N Set solver timeout in milliseconds (0 means unlimited)";
  ] in
  let anonymous value =
    match !path with
    | None -> path := Some value
    | Some _ -> raise (Arg.Bad "expected at most one SMT-LIB input file")
  in
  try
    Arg.parse_argv ~current:(ref 0) (Array.of_list ("checker" :: args))
      options anonymous "usage: checker [--stats] [--timeout-ms N] [input.smt2]";
    let input =
      match !path with
      | None | Some "-" -> read_all stdin
      | Some name ->
          let channel = open_in_bin name in
          Fun.protect ~finally:(fun () -> close_in_noerr channel)
            (fun () -> read_all channel)
    in
    let start = Unix.gettimeofday () in
    match Z3Native.solve input !timeout with
    | Z3Native.Sat -> print_endline "SAT"; exit 4
    | Z3Native.Unknown reason ->
        Printf.printf "UNKNOWN %s\n" reason; exit 5
    | Z3Native.Unsat (assertions, proof) ->
        let solved = Unix.gettimeofday () in
        let doc = Z3NativeProof.marshal assertions proof in
        let marshaled = Unix.gettimeofday () in
        let result = Z3ProofDocument.check_document doc in
        let checked = Unix.gettimeofday () in
        if !statistics then
          Printf.eprintf
            "solve_ms=%.3f marshal_ms=%.3f check_ms=%.3f expressions=%d declarations=%d proof_nodes=%d\n%!"
            ((solved -. start) *. 1000.) ((marshaled -. solved) *. 1000.)
            ((checked -. marshaled) *. 1000.) (List.length doc.expressions)
            (List.length doc.declarations) (List.length doc.entries);
        (match result with
         | None -> print_endline "REJECT"; exit 1
         | Some n when Z.equal n Z.zero -> print_endline "ACCEPT"; exit 0
         | Some n -> Printf.printf "PARTIAL %s\n" (Z.to_string n); exit 3)
  with
  | Arg.Help message -> print_string message; exit 0
  | Arg.Bad message -> prerr_string message; exit 2
  | Z3Native.Error message | Z3.Error message | Sys_error message ->
      prerr_endline ("ERROR " ^ message); exit 2
  | Stack_overflow -> prerr_endline "ERROR native checker stack limit exceeded"; exit 2
  | Out_of_memory -> prerr_endline "ERROR native checker ran out of memory"; exit 2
