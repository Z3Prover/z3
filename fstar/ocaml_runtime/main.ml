(* Standalone CLI entry point for the extracted Z3 proof-document
   checker. Build once (see fstar/BUILD_OCAML_CHECKER.md); invoke many
   times, once per proof, with no `fstar.exe` involved at run time:

     checker                 reads a JSON proof document from stdin
     checker <path/to.json>  reads it from the given file instead

   Exit code 0 means `Z3PulseProofCheckerJson.check_proof_json` on the
   input returned `true` (the document parsed and its root proof is
   well-formed per `Z3ProofTheory.fact`/`Z3PulseProofChecker.check_
   proof`); exit code 1 means it returned `false`; exit code 2 means
   the input could not even be read. *)

let read_all (ic : Stdlib.in_channel) : Prims.string =
  let buf = Stdlib.Buffer.create 4096 in
  (try
     while true do
       Stdlib.Buffer.add_channel buf ic 4096
     done
   with End_of_file -> ());
  Stdlib.Buffer.contents buf

let () =
  let input =
    match Stdlib.Sys.argv with
    | [| _ |] -> read_all Stdlib.stdin
    | [| _; path |] ->
        let ic = Stdlib.open_in_bin path in
        let s = read_all ic in
        Stdlib.close_in ic;
        s
    | _ ->
        Stdlib.prerr_endline "usage: checker [path/to/proof.json]";
        Stdlib.exit 2
  in
  let ok = Z3PulseProofCheckerJson.check_proof_json input in
  if ok then (
    Stdlib.print_endline "ACCEPT";
    Stdlib.exit 0)
  else (
    Stdlib.print_endline "REJECT";
    Stdlib.exit 1)
