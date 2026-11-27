let read_all channel =
  let buffer = Buffer.create 4096 in
  let bytes = Bytes.create 4096 in
  let rec read () =
    match input channel bytes 0 (Bytes.length bytes) with
    | 0 -> Buffer.contents buffer
    | n -> Buffer.add_subbytes buffer bytes 0 n; read ()
  in
  read ()

let diagnostic_rule =
  let open Z3UnifiedProofSyntax in
  function
  | Unverified name -> name
  | ArithmeticFarkas _ -> "arith/farkas"
  | ArithmeticBound _ -> "arith/bound"
  | ArithmeticGomory _ -> "arith/lp-gomory"
  | ArithmeticLattice _ -> "arith/lp-integer-lattice"
  | FiniteFieldPac _ -> "th-lemma"
  | RewriteRule -> "rewrite"
  | PullQuantifier -> "pull-quant"
  | DestructiveEqualityResolution | DestructiveEquality -> "der"
  | Skolemization -> "sk"
  | ElimUnused -> "elim-unused"
  | PushQuantifier -> "push-quant"
  | DefAxiom -> "def-axiom"
  | Asserted -> "asserted"
  | DefinitionIntroduction -> "intro-def"
  | ApplyDefinition -> "apply-def"
  | Hypothesis -> "hypothesis"
  | LemmaRule -> "lemma"
  | Reflexivity -> "refl"
  | Symmetry -> "symm"
  | Transitivity -> "trans"
  | TransitivityPath -> "trans*"
  | Congruence -> "monotonicity"
  | Commutativity -> "commutativity"
  | ModusPonens -> "mp"
  | ObservationalMP -> "mp~"
  | IffObservational -> "iff~"
  | UnitResolution -> "unit-resolution"
  | AndElimination -> "and-elim"
  | NotOrElimination -> "not-or-elim"
  | IffTrue -> "iff-true"
  | IffFalse -> "iff-false"
  | QuantifierIntroduction certificate ->
      let root = certificate.binder_root in
      if Z.sign root < 0 || not (Z.fits_int root) then "binder"
      else (match List.nth_opt certificate.binder_entries (Z.to_int root) with
        | Some entry -> entry.binder_name
        | None -> "binder")
  | QuantifierInstantiation _ -> "quant-inst"

let field text =
  String.map (function '\t' | '\r' | '\n' -> ' ' | c -> c) text

let fingerprint judgment =
  let open Z3AstTheory in
  let rec shape depth = function
    | _ when depth = 0 -> "_"
    | App (f, args) ->
        let rec first remaining = function
          | [] -> []
          | _ when remaining = 0 -> ["..."]
          | a :: rest -> shape (depth - 1) a :: first (remaining - 1) rest
        in
        let name = match f.interp with None -> "u" | Some _ -> field f.decl_name in
        name ^ "(" ^ String.concat "," (first 8 args) ^ ")"
    | Var _ -> "var"
    | Quantifier _ -> "binder"
  in
  let open Z3UnifiedProofSyntax in
  match judgment with
  | Holds e -> "holds:" ^ shape 3 e
  | Equal (a, b) -> "eq:" ^ shape 3 a ^ "->" ^ shape 3 b
  | Observational (a, b) -> "obs:" ^ shape 3 a ^ "->" ^ shape 3 b

let report_diagnostics verdict diagnostic =
  let module P = Z3DocumentSyntax in
  let module R = Z3SortedRootDocument in
  match verdict, diagnostic with
  | (R.RootCertified | R.RootUncovered), P.DocumentChecked (n, obligations)
      when Z.equal n Z.zero && obligations = [] ->
      Printf.eprintf "diagnostic\tchecked\tpending=0\tfamilies=0\n"
  | R.RootPending n, P.DocumentChecked (actual, obligations) when Z.equal n actual ->
      let families = Hashtbl.create 32 and total = ref Z.zero in
      List.iter (fun obligation ->
        let key = field (diagnostic_rule obligation.P.obligation_rule),
                  fingerprint obligation.P.obligation_conclusion in
        let count, first = match Hashtbl.find_opt families key with
          | None -> Z.zero, obligation.P.obligation_index
          | Some pair -> pair in
        let local = obligation.P.obligation_count in
        total := Z.add !total local;
        Hashtbl.replace families key (Z.add count local, first)) obligations;
      if not (Z.equal !total n) then Z3Native.fail "Diagnostic obligation count mismatch";
      Printf.eprintf "diagnostic\tchecked\tpending=%s\tfamilies=%d\n"
        (Z.to_string n) (Hashtbl.length families);
      Hashtbl.to_seq families |> List.of_seq |> List.sort compare |>
      List.iter (fun ((rule, shape), (count, first)) ->
        Printf.eprintf "obligation\t%s\t%s\t%s\t%s\n"
          rule (Z.to_string count) (Z.to_string first) shape)
  | R.RootRejected, P.DocumentRejected _ ->
      Printf.eprintf "diagnostic\trejected\tstage=sorted-replay\n"
  | _ -> Z3Native.fail "Diagnostic result disagrees with root verdict"

let result_text = function
  | Z3SortedRootDocument.RootCertified -> "ACCEPT"
  | Z3SortedRootDocument.RootPending n -> "PARTIAL " ^ Z.to_string n
  | Z3SortedRootDocument.RootUncovered -> "UNKNOWN unsupported-root-fragment"
  | Z3SortedRootDocument.RootRejected -> "REJECT"

let replay_diagnostic schema doc verdict =
  (* Certification has no pending obligations; every other verdict is the base verdict. *)
  match verdict with
  | Z3SortedRootDocument.RootCertified -> Z3DocumentSyntax.DocumentChecked (Z.zero, [])
  | _ -> Z3IndependentChecker.diagnose schema doc

let whitespace = function ' ' | '\t' | '\r' | '\n' -> true | _ -> false

let read_command channel =
  let buffer = Buffer.create 256 in
  let rec start comment =
    match input_char channel with
    | '\n' when comment -> start false
    | _ when comment -> start true
    | ';' -> start true
    | c when whitespace c -> start false
    | '(' -> Buffer.add_char buffer '('; command 1 `Normal
    | _ -> Z3Native.fail "expected an SMT-LIB command beginning with '('"
    | exception End_of_file -> None
  and command depth mode =
    match input_char channel with
    | '\000' -> Z3Native.fail "null character in SMT-LIB input"
    | c -> Buffer.add_char buffer c; advance depth mode c
    | exception End_of_file -> Z3Native.fail "incomplete SMT-LIB command at end of input"
  and advance depth mode c =
    match mode, c with
    | `Comment, '\n' -> command depth `Normal
    | `Comment, _ -> command depth `Comment
    | `Quoted, '|' -> command depth `Normal
    | `Quoted, _ -> command depth `Quoted
    | `String, '"' -> command depth `AfterQuote
    | `String, _ -> command depth `String
    | `AfterQuote, '"' -> command depth `String
    | `AfterQuote, _ -> advance depth `Normal c
    | `Normal, ';' -> command depth `Comment
    | `Normal, '|' -> command depth `Quoted
    | `Normal, '"' -> command depth `String
    | `Normal, '(' -> command (depth + 1) `Normal
    | `Normal, ')' when depth = 1 -> Some (Buffer.contents buffer)
    | `Normal, ')' -> command (depth - 1) `Normal
    | `Normal, _ -> command depth `Normal
  in
  start false

let command_name text =
  let length = String.length text in
  let rec skip i comment =
    if i = length then i
    else if comment then skip (i + 1) (text.[i] <> '\n')
    else if text.[i] = ';' then skip (i + 1) true
    else if whitespace text.[i] then skip (i + 1) false
    else i
  in
  let first = skip 1 false in
  let quoted = first < length && text.[first] = '|' in
  let first = if quoted then first + 1 else first in
  let rec finish i =
    if i = length then i
    else if quoted then if text.[i] = '|' then i else finish (i + 1)
    else if whitespace text.[i] || text.[i] = ')' || text.[i] = '(' || text.[i] = ';'
    then i else finish (i + 1)
  in
  String.sub text first (finish first - first)

let parse_prime_evidence text =
  let bad () = raise (Arg.Bad "invalid --prime-evidence (expected BASE:FACTOR,...)") in
  let decimal limit text =
    if String.length text = 0 || String.length text > limit ||
       not (String.for_all (fun c -> c >= '0' && c <= '9') text)
    then bad ();
    Z.of_string text in
  if String.length text > 2640 then bad ();
  match String.split_on_char ':' text with
  | [base; factors] ->
      let a = decimal 78 base in
      let xs = if factors = "" then [] else String.split_on_char ',' factors in
      if Z.gt a (Z.shift_left Z.one 256) || List.length xs > 256 then bad ();
      let xs = List.map (decimal 9) xs in
      if List.exists (fun n -> Z.gt n (Z.shift_left Z.one 28)) xs then bad ();
      a, xs
  | _ -> bad ()

let interactive
    statistics diagnostics distinct_replay skolem_replay field_replay prime_evidence
    array_replay definition_replay definition_array_replay clause_proofs timeout =
  let context = Z3Native.create_context timeout in
  let error = ref false and rejected = ref false and pending = ref false
  and uncovered = ref false and queries = ref 0 in
  let start = ref (Unix.gettimeofday ()) in
  let registration = Z3native.set_proof_check_callback context (fun proof vector ->
    incr queries;
    let solved = Unix.gettimeofday () in
    let assertions = List.init (Z3native.ast_vector_size context vector)
        (Z3native.ast_vector_get context vector) in
    let doc, schema = Z3NativeProof.marshal_with_datatypes assertions proof in
    let marshaled = Unix.gettimeofday () in
    let verdict, cached_diagnostic =
      if diagnostics && definition_array_replay then
        let verdict, diagnostic = Z3IndependentChecker.check_definition_array_fast_diagnosed schema doc in
        verdict, Some diagnostic
      else if diagnostics && array_replay then
        let verdict, diagnostic = Z3IndependentChecker.check_array_diagnosed schema doc in
        verdict, Some diagnostic
      else if diagnostics && definition_replay then
        let verdict, diagnostic = Z3IndependentChecker.check_definition_diagnosed schema doc in
        verdict, Some diagnostic
      else if diagnostics &&
              not (distinct_replay || skolem_replay || field_replay ||
                   definition_replay || definition_array_replay) then
        let verdict, diagnostic = Z3IndependentChecker.check_diagnosed schema doc in
        verdict, Some diagnostic
      else
        (if distinct_replay then Z3IndependentChecker.check_distinct schema doc
         else if skolem_replay then Z3IndependentChecker.check_skolem schema doc
         else if field_replay then
           (match prime_evidence with
            | None -> Z3IndependentChecker.check_field schema doc
            | Some _ -> Z3IndependentChecker.check_field_with_evidence schema doc prime_evidence)
         else if definition_array_replay then Z3IndependentChecker.check_definition_array_fast schema doc
         else if array_replay then Z3IndependentChecker.check_array schema doc
         else if definition_replay then Z3IndependentChecker.check_definition schema doc
         else Z3IndependentChecker.check schema doc), None in
    let checked = Unix.gettimeofday () in
    (match verdict with
     | Z3SortedRootDocument.RootRejected -> rejected := true
     | Z3SortedRootDocument.RootPending _ -> pending := true
     | Z3SortedRootDocument.RootUncovered -> uncovered := true
     | Z3SortedRootDocument.RootCertified -> ());
    let nnf_summary = if diagnostics then (
      let diagnostic = match cached_diagnostic with
        | Some diagnostic -> diagnostic
        | None ->
            if distinct_replay then Z3IndependentChecker.diagnose_distinct schema doc
            else if skolem_replay || field_replay || array_replay || definition_replay ||
                    definition_array_replay then replay_diagnostic schema doc verdict
            else Z3IndependentChecker.diagnose schema doc in
      report_diagnostics verdict diagnostic;
      match diagnostic with
      | Z3DocumentSyntax.DocumentRejected _ -> ""
      | Z3DocumentSyntax.DocumentChecked (_, obligations) ->
          let counts rule entries =
            List.fold_left (fun n entry ->
              if diagnostic_rule entry.Z3DocumentSyntax.rule = rule then n + 1 else n) 0 entries in
          let pending rule =
            List.fold_left (fun n obligation ->
              if diagnostic_rule obligation.Z3DocumentSyntax.obligation_rule = rule
              then Z.add n obligation.Z3DocumentSyntax.obligation_count else n)
              Z.zero obligations in
          Printf.sprintf "\n; proof-nnf nnf-pos-roots=%d nnf-pos-pending=%s nnf-neg-roots=%d nnf-neg-pending=%s"
            (counts "nnf-pos" doc.Z3DocumentSyntax.entries) (Z.to_string (pending "nnf-pos"))
            (counts "nnf-neg" doc.Z3DocumentSyntax.entries) (Z.to_string (pending "nnf-neg")))
      else "" in
    let summary = Printf.sprintf
        "solve_ms=%.3f marshal_ms=%.3f check_ms=%.3f expressions=%d declarations=%d proof_nodes=%d semantics=%s"
        ((solved -. !start) *. 1000.) ((marshaled -. solved) *. 1000.)
        ((checked -. marshaled) *. 1000.)
        (List.length doc.Z3DocumentSyntax.expressions)
        (List.length doc.Z3DocumentSyntax.declarations)
        (List.length doc.Z3DocumentSyntax.entries)
        (if distinct_replay then "sorted-distinct" else if skolem_replay then "sorted-skolem"
         else if field_replay then "sorted-field"
         else if definition_array_replay then "sorted-definition-array"
         else if array_replay then "sorted-array"
         else if definition_replay then "sorted-definition"
         else "sorted-core") in
    if statistics then Printf.eprintf "%s\n%!" summary;
    "; proof-check " ^ result_text verdict ^ "\n; proof-stats " ^ summary ^ nnf_summary)
  in
  let initialize () =
    ignore (Z3native.eval_smtlib2_string context
      ("(set-option :produce-proofs true)(set-option :timeout " ^ Z.to_string timeout ^ ")" ^
       (if clause_proofs then "(set-option :smt.clause_proof true)" else "")))
  in
  Fun.protect ~finally:(fun () ->
    Z3native.clear_proof_check_callback context;
    ignore (Sys.opaque_identity registration))
    (fun () ->
      initialize ();
      let rec commands () =
        match read_command stdin with
        | None -> ()
        | Some command ->
            let name = command_name command in
            let successful =
              try
                start := Unix.gettimeofday ();
                let output = Z3native.eval_smtlib2_string context command in
                if name = "reset" then initialize ();
                if name = "set-option" &&
                   String.trim (Z3native.eval_smtlib2_string context
                     "(get-option :produce-proofs)") = "false" then (
                  ignore (Z3native.eval_smtlib2_string context "(set-option :produce-proofs true)");
                  Z3Native.fail "interactive mode requires :produce-proofs true");
                print_string output;
                flush stdout;
                true
              with Z3Native.Error message | Z3.Error message | Sys_error message ->
                error := true;
                let escaped = String.concat "\"\"" (String.split_on_char '"' message) in
                Printf.printf "(error \"%s\")\n%!" escaped;
                false
            in
            if not (successful && name = "exit") then commands ()
      in
      commands ());
  if !error then 2 else if !rejected then 1 else if !pending then 3
  else if !uncovered then 5 else 0

let run args =
  let statistics = ref false and diagnostics = ref false and timeout = ref Z.zero in
  let distinct_replay = ref false and skolem_replay = ref false and field_replay = ref false
  and array_replay = ref false
  and definition_replay = ref false
  and definition_array_replay = ref false in
  let interactive_mode = ref false in
  let prime_evidence = ref None in
  let clause_proofs = ref false and path = ref None in
  let options = [
    "--stats", Arg.Set statistics, " Report phase timings and proof sizes";
    "--diagnostics", Arg.Set diagnostics, " Report unmet-obligation families";
    "--distinct-replay", Arg.Set distinct_replay, " Enable distinct-model replay";
    "--skolem-replay", Arg.Set skolem_replay, " Enable larger-budget Skolem replay";
    "--field-replay", Arg.Set field_replay, " Enable finite-field replay";
    "--prime-evidence", Arg.String (fun value ->
      if !prime_evidence <> None then raise (Arg.Bad "--prime-evidence supplied more than once");
      prime_evidence := Some (parse_prime_evidence value)),
      "BASE:FACTOR,... Supply bounded Lucas evidence for --field-replay";
    "--array-replay", Arg.Set array_replay, " Enable array replay";
    "--definition-replay", Arg.Set definition_replay, " Enable definition, NNF and Skolem replay";
    "--definition-array-replay", Arg.Set definition_array_replay,
      " Enable combined definition, NNF, Skolem and array replay";
    "--interactive", Arg.Set interactive_mode, " Check an incremental SMT-LIB session from stdin";
    "--clause-proofs", Arg.Set clause_proofs, " Enable clausal proof production";
    "--timeout-ms", Arg.String (fun value ->
      try
        let n = Z.of_string value in
        if Z.sign n < 0 || Z.gt n (Z.of_string "4294967295")
        then raise (Arg.Bad "invalid --timeout-ms");
        timeout := n
      with Invalid_argument _ -> raise (Arg.Bad "invalid --timeout-ms")),
      "N Set solver timeout in milliseconds";
  ] in
  let input_path value =
    match !path with
    | None -> path := Some value
    | Some _ -> raise (Arg.Bad "expected at most one SMT-LIB input file")
  in
  try
    Arg.parse_argv ~current:(ref 0) (Array.of_list ("checker" :: args)) options
      input_path "usage: checker [--interactive] [--distinct-replay | --skolem-replay | --field-replay | --array-replay | --definition-replay | --definition-array-replay] [--stats] [--diagnostics] [--clause-proofs] [--timeout-ms N] [input.smt2]";
    if !distinct_replay && !skolem_replay then
      raise (Arg.Bad "--distinct-replay and --skolem-replay cannot be combined");
    if !field_replay && (!distinct_replay || !skolem_replay) then
      raise (Arg.Bad "--field-replay cannot be combined with other replay options");
    if !prime_evidence <> None && not !field_replay then
      raise (Arg.Bad "--prime-evidence requires --field-replay");
    if !array_replay && (!distinct_replay || !skolem_replay || !field_replay) then
      raise (Arg.Bad "--array-replay cannot be combined with other replay options");
    if !definition_replay && (!distinct_replay || !skolem_replay || !field_replay || !array_replay) then
      raise (Arg.Bad "--definition-replay cannot be combined with other replay options");
    if !definition_array_replay &&
       (!distinct_replay || !skolem_replay || !field_replay ||
        !array_replay || !definition_replay) then
      raise (Arg.Bad "--definition-array-replay cannot be combined with other replay options");
    if !interactive_mode then (
      if !path <> None then raise (Arg.Bad "--interactive reads commands from stdin");
      exit (interactive !statistics !diagnostics !distinct_replay !skolem_replay
        !field_replay !prime_evidence !array_replay !definition_replay
        !definition_array_replay !clause_proofs !timeout));
    let input = match !path with
      | None | Some "-" -> read_all stdin
      | Some name ->
          let channel = open_in_bin name in
          Fun.protect ~finally:(fun () -> close_in_noerr channel)
            (fun () -> read_all channel)
    in
    let started = Unix.gettimeofday () in
    match Z3Native.solve_with_clause_proofs input !timeout !clause_proofs with
    | Z3Native.Sat -> print_endline "SAT"; exit 4
    | Z3Native.Unknown reason -> Printf.printf "UNKNOWN %s\n" reason; exit 5
    | Z3Native.Unsat (assertions, proof) ->
        let solved = Unix.gettimeofday () in
        let doc, schema = Z3NativeProof.marshal_with_datatypes assertions proof in
        let marshaled = Unix.gettimeofday () in
        let verdict, cached_diagnostic =
          if !diagnostics && !definition_array_replay then
            let verdict, diagnostic = Z3IndependentChecker.check_definition_array_fast_diagnosed schema doc in
            verdict, Some diagnostic
          else if !diagnostics && !array_replay then
            let verdict, diagnostic = Z3IndependentChecker.check_array_diagnosed schema doc in
            verdict, Some diagnostic
          else if !diagnostics && !definition_replay then
            let verdict, diagnostic = Z3IndependentChecker.check_definition_diagnosed schema doc in
            verdict, Some diagnostic
          else if !diagnostics &&
                  not (!distinct_replay || !skolem_replay || !field_replay ||
                       !definition_replay || !definition_array_replay) then
            let verdict, diagnostic = Z3IndependentChecker.check_diagnosed schema doc in
            verdict, Some diagnostic
          else
            (if !distinct_replay then Z3IndependentChecker.check_distinct schema doc
             else if !skolem_replay then Z3IndependentChecker.check_skolem schema doc
             else if !field_replay then
               (match !prime_evidence with
                | None -> Z3IndependentChecker.check_field schema doc
                | Some _ -> Z3IndependentChecker.check_field_with_evidence schema doc !prime_evidence)
             else if !definition_array_replay then
               Z3IndependentChecker.check_definition_array_fast schema doc
             else if !array_replay then Z3IndependentChecker.check_array schema doc
             else if !definition_replay then Z3IndependentChecker.check_definition schema doc
             else Z3IndependentChecker.check schema doc), None in
        let checked = Unix.gettimeofday () in
        if !diagnostics then
          report_diagnostics verdict
            (match cached_diagnostic with
             | Some diagnostic -> diagnostic
             | None ->
                 if !distinct_replay then Z3IndependentChecker.diagnose_distinct schema doc
                 else if !skolem_replay || !field_replay || !array_replay ||
                         !definition_replay || !definition_array_replay then replay_diagnostic schema doc verdict
                 else Z3IndependentChecker.diagnose schema doc);
        if !statistics then
          Printf.eprintf
            "solve_ms=%.3f marshal_ms=%.3f check_ms=%.3f expressions=%d declarations=%d proof_nodes=%d semantics=%s\n%!"
            ((solved -. started) *. 1000.) ((marshaled -. solved) *. 1000.)
            ((checked -. marshaled) *. 1000.)
            (List.length doc.Z3DocumentSyntax.expressions)
            (List.length doc.Z3DocumentSyntax.declarations)
            (List.length doc.Z3DocumentSyntax.entries)
            (if !distinct_replay then "sorted-distinct" else if !skolem_replay then "sorted-skolem"
             else if !field_replay then "sorted-field"
             else if !definition_array_replay then "sorted-definition-array"
             else if !array_replay then "sorted-array"
             else if !definition_replay then "sorted-definition"
             else "sorted-core");
        match verdict with
        | Z3SortedRootDocument.RootCertified -> print_endline "ACCEPT"; exit 0
        | Z3SortedRootDocument.RootPending n ->
            Printf.printf "PARTIAL %s\n" (Z.to_string n); exit 3
        | Z3SortedRootDocument.RootUncovered ->
            print_endline "UNKNOWN unsupported-root-fragment"; exit 5
        | Z3SortedRootDocument.RootRejected -> print_endline "REJECT"; exit 1
  with
  | Arg.Help message -> print_string message; exit 0
  | Arg.Bad message -> prerr_string message; exit 2
  | Z3Native.Error message | Z3.Error message | Sys_error message ->
      prerr_endline ("ERROR " ^ message); exit 2
  | Stack_overflow -> prerr_endline "ERROR native checker stack limit exceeded"; exit 2
  | Out_of_memory -> prerr_endline "ERROR native checker ran out of memory"; exit 2

let () =
  match Array.to_list Sys.argv with
  | [_; "--version"] -> print_endline (Z3Native.version ())
  | _ :: args -> run args
  | [] -> run []
