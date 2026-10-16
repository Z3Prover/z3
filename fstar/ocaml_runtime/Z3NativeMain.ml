let read_all channel =
  let buffer = Buffer.create 4096 in
  (try while true do Buffer.add_channel buffer channel 4096 done
   with End_of_file -> ());
  Buffer.contents buffer

let diagnostic_rule = function
  | Z3UnifiedProof.Unverified name -> name
  | Z3UnifiedProof.ArithmeticFarkas _ -> "arith/farkas"
  | Z3UnifiedProof.RewriteRule -> "rewrite"
  | Z3UnifiedProof.DefAxiom -> "def-axiom"
  | Z3UnifiedProof.Asserted -> "asserted"
  | Z3UnifiedProof.DefinitionIntroduction -> "intro-def"
  | Z3UnifiedProof.ApplyDefinition -> "apply-def"
  | Z3UnifiedProof.Hypothesis -> "hypothesis"
  | Z3UnifiedProof.LemmaRule -> "lemma"
  | Z3UnifiedProof.Reflexivity -> "refl"
  | Z3UnifiedProof.Symmetry -> "symm"
  | Z3UnifiedProof.Transitivity -> "trans"
  | Z3UnifiedProof.TransitivityPath -> "trans*"
  | Z3UnifiedProof.Congruence -> "monotonicity"
  | Z3UnifiedProof.Commutativity -> "commutativity"
  | Z3UnifiedProof.ModusPonens -> "mp"
  | Z3UnifiedProof.ObservationalMP -> "mp~"
  | Z3UnifiedProof.IffObservational -> "iff~"
  | Z3UnifiedProof.UnitResolution -> "unit-resolution"
  | Z3UnifiedProof.AndElimination -> "and-elim"
  | Z3UnifiedProof.NotOrElimination -> "not-or-elim"
  | Z3UnifiedProof.IffTrue -> "iff-true"
  | Z3UnifiedProof.IffFalse -> "iff-false"

let diagnostic_stage = function
  | Z3ProofDocument.LogicalDeclarations -> "logical-declarations"
  | Z3ProofDocument.ExpressionWellFormedness -> "expression-well-formedness"
  | Z3ProofDocument.OriginalAssertions -> "original-assertions"
  | Z3ProofDocument.AssertionScope -> "assertion-scope"
  | Z3ProofDocument.DefinitionCollection -> "definition-collection"
  | Z3ProofDocument.DefinitionCycle -> "definition-cycle"
  | Z3ProofDocument.DefinitionExpansion -> "definition-expansion"
  | Z3ProofDocument.InputClassification -> "input-classification"
  | Z3ProofDocument.ProofEntry -> "proof-entry"
  | Z3ProofDocument.MissingPremise -> "missing-premise"
  | Z3ProofDocument.MissingRoot -> "missing-root"
  | Z3ProofDocument.OpenRoot -> "open-root"
  | Z3ProofDocument.DefinitionFreshness -> "definition-freshness"

let fingerprint judgment =
  let module A = Z3AstTheory in
  let aliases = Hashtbl.create 16 and budget = ref 96 in
  let rec sort depth = function
    | A.BaseSort ("Bool" | "Int" | "Real" as name) -> name
    | A.BaseSort _ -> "U"
    | A.ArraySort (domains, range) ->
        if depth = 0 then "Array"
        else "Array[" ^ String.concat "," (List.map (sort (depth - 1)) domains) ^
             ";" ^ sort (depth - 1) range ^ "]"
  in
  let rec expression depth e =
    if depth = 0 || !budget = 0 then "_" ^ sort 2 (A.get_sort e)
    else (
      decr budget;
      match e with
      | A.Var (index, s) -> "var" ^ Z.to_string index ^ ":" ^ sort 2 s
      | A.Quantifier (kind, _, _, body) ->
          let name = match kind with A.Forall_k -> "forall" | A.Exists_k -> "exists"
                                    | A.Lambda_k -> "lambda" in
          name ^ "(" ^ expression (depth - 1) body ^ ")"
      | A.App (decl, args) ->
          let head =
            if decl.A.interp = Some Z3ValueTheory.op_num_rational then
              match decl.A.int_params with
              | [n; d] ->
                  let number = Z.to_string n ^ "/" ^ Z.to_string d in
                  if String.length number <= 64 then number else "large-numeral"
              | _ -> "malformed-numeral"
            else if decl.A.interp <> None then String.escaped decl.A.decl_name
            else (
              let key = decl.A.decl_name, decl.A.domain, decl.A.range in
              match Hashtbl.find_opt aliases key with
              | Some name -> name
              | None ->
                  let name = "u" ^ string_of_int (Hashtbl.length aliases) in
                  Hashtbl.add aliases key name;
                  name)
          in
          let rec arguments remaining = function
            | [] -> []
            | _ when remaining = 0 -> ["...arity=" ^ string_of_int (List.length args)]
            | value :: rest -> expression (depth - 1) value :: arguments (remaining - 1) rest
          in
          head ^ ":" ^ sort 2 decl.A.range ^
          (if args = [] then "" else "(" ^ String.concat "," (arguments 8 args) ^ ")"))
  in
  match judgment with
  | Z3UnifiedProof.Holds e -> "holds(" ^ expression 5 e ^ ")"
  | Z3UnifiedProof.Equal (left, right) ->
      let left = expression 5 left in
      let right = expression 5 right in
      "eq(" ^ left ^ " -> " ^ right ^ ")"
  | Z3UnifiedProof.Observational (left, right) ->
      let left = expression 5 left in
      let right = expression 5 right in
      "oeq(" ^ left ^ " -> " ^ right ^ ")"

let report_diagnostics doc expected =
  match Z3ProofDocument.diagnose_document doc, expected with
  | Z3ProofDocument.DocumentChecked (pending, obligations), Some actual
      when Z.equal pending actual ->
      let families = Hashtbl.create 32 and total = ref Z.zero in
      List.iter (fun obligation ->
        let key = diagnostic_rule obligation.Z3ProofDocument.obligation_rule,
                  fingerprint obligation.Z3ProofDocument.obligation_conclusion in
        let count, first =
          match Hashtbl.find_opt families key with
          | Some value -> value
          | None -> Z.zero, obligation.Z3ProofDocument.obligation_index in
        let local = obligation.Z3ProofDocument.obligation_count in
        total := Z.add !total local;
        Hashtbl.replace families key (Z.add count local, first)) obligations;
      if not (Z.equal !total pending) then Z3Native.fail "Diagnostic obligation count mismatch";
      Printf.eprintf "diagnostic\tchecked\tpending=%s\tfamilies=%d\n"
        (Z.to_string pending) (Hashtbl.length families);
      Hashtbl.to_seq families |> List.of_seq |>
        List.sort (fun (key1, (n1, _)) (key2, (n2, _)) ->
          let order = Z.compare n2 n1 in if order = 0 then compare key1 key2 else order) |>
        List.iter (fun ((rule, shape), (count, first)) ->
          Printf.eprintf "obligation\t%s\t%s\t%s\t%s\n"
            rule (Z.to_string count) (Z.to_string first) shape)
  | Z3ProofDocument.DocumentRejected (stage, index, source), None ->
      Printf.eprintf "diagnostic\trejected\tstage=%s\tindex=%s%s\n"
        (diagnostic_stage stage) (match index with None -> "-" | Some n -> Z.to_string n)
        (match source with None -> "" | Some e -> "\t" ^ fingerprint (Z3UnifiedProof.Holds e))
  | _ -> Z3Native.fail "Diagnostic result disagrees with document checker"

let run args =
  let statistics = ref false and diagnostics = ref false
  and timeout = ref Z.zero and path = ref None in
  let options = [
    "--stats", Arg.Set statistics, " Report phase timings and unique marshaled node counts";
    "--diagnostics", Arg.Set diagnostics, " Report typed unmet-obligation fingerprints on stderr";
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
      options anonymous "usage: checker [--stats] [--diagnostics] [--timeout-ms N] [input.smt2]";
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
        if !diagnostics then (
          report_diagnostics doc result;
          if !statistics then
            Printf.eprintf "diagnose_ms=%.3f\n%!" ((Unix.gettimeofday () -. checked) *. 1000.));
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
