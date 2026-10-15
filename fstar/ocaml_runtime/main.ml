(* Standalone CLI entry point for the extracted Z3 proof-document
   checker. Build once (see fstar/BUILD_OCAML_CHECKER.md); invoke many
   times, once per proof, with no `fstar.exe` involved at run time:

     checker                 reads a JSON proof document from stdin
     checker <path/to.json>  reads it from the given file instead

   Exit code 0 means `Z3PulseProofCheckerJson.check_proof_json` on the
   input returned `true`; exit code 1 rejects, 2 reports unreadable
   input, and 3 reports a valid resolution DAG with unverified leaves. *)

let read_all (ic : Stdlib.in_channel) : Prims.string =
  let buf = Stdlib.Buffer.create 4096 in
  (try
     while true do
       Stdlib.Buffer.add_channel buf ic 4096
     done
   with End_of_file -> ());
  Stdlib.Buffer.contents buf

let () =
  let strict, args =
    match Stdlib.Array.to_list Stdlib.Sys.argv with
    | _ :: "--check-original-assertions" :: rest -> true, rest
    | _ :: rest -> false, rest
    | [] -> false, []
  in
  let input =
    match args with
    | [] -> read_all Stdlib.stdin
    | [path] ->
        let ic = Stdlib.open_in_bin path in
        let s = read_all ic in
        Stdlib.close_in ic;
        s
    | _ ->
        Stdlib.prerr_endline
          "usage: checker [--check-original-assertions] [path/to/proof.json]";
        Stdlib.exit 2
  in
  let resolution =
    Z3ResolutionProofJson.check_resolution_json_with_inputs strict input in
  if resolution > 0 then (
    Stdlib.Printf.printf "PARTIAL %d\n" resolution;
    Stdlib.exit 3)
  else
    let ok =
      if resolution = 0 then true
      else if resolution = -2 then
        Z3PulseProofCheckerJson.check_proof_json input
      else false
    in
    if ok then (
      Stdlib.print_endline "ACCEPT";
      Stdlib.exit 0)
    else (
      Stdlib.print_endline "REJECT";
      Stdlib.exit 1)
