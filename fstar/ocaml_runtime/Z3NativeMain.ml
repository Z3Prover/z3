let read_all channel =
  let buffer = Buffer.create 4096 in
  (try while true do Buffer.add_channel buffer channel 4096 done
   with End_of_file -> ());
  Buffer.contents buffer

let diagnostic_rule = function
  | Z3UnifiedProof.Unverified name -> name
  | Z3UnifiedProof.ArithmeticFarkas _ -> "arith/farkas"
  | Z3UnifiedProof.ArithmeticGomory _ -> "arith/lp-gomory"
  | Z3UnifiedProof.FiniteFieldPac _ -> "th-lemma"
  | Z3UnifiedProof.RewriteRule -> "rewrite"
  | Z3UnifiedProof.PullQuantifier -> "pull-quant"
  | Z3UnifiedProof.DestructiveEqualityResolution -> "der"
  | Z3UnifiedProof.Skolemization -> "sk"
  | Z3UnifiedProof.ElimUnused -> "elim-unused"
  | Z3UnifiedProof.PushQuantifier -> "push-quant"
  | Z3UnifiedProof.DestructiveEquality -> "der"
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
  | Z3UnifiedProof.QuantifierIntroduction certificate ->
      let root = certificate.Z3UnifiedProof.binder_root in
      if Z.sign root < 0 || not (Z.fits_int root) then "binder"
      else (match List.nth_opt certificate.Z3UnifiedProof.binder_entries (Z.to_int root) with
        | Some entry -> entry.Z3UnifiedProof.binder_name
        | None -> "binder")
  | Z3UnifiedProof.QuantifierInstantiation _ -> "quant-inst"

let diagnostic_stage = function
  | Z3ProofDocument.LogicalDeclarations -> "logical-declarations"
  | Z3ProofDocument.ExpressionWellFormedness -> "expression-well-formedness"
  | Z3ProofDocument.OriginalAssertions -> "original-assertions"
  | Z3ProofDocument.AssertionScope -> "assertion-scope"
  | Z3ProofDocument.DefinitionCollection -> "definition-collection"
  | Z3ProofDocument.DefinitionCycle -> "definition-cycle"
  | Z3ProofDocument.DefinitionExpansion -> "definition-expansion"
  | Z3ProofDocument.SkolemCollection -> "skolem-collection"
  | Z3ProofDocument.SkolemCycle -> "skolem-cycle"
  | Z3ProofDocument.SkolemFreshness -> "skolem-freshness"
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

let pretty_judgment judgment =
  let module A = Z3AstTheory in
  let module V = Z3ValueTheory in
  let budget = ref 512 and next_bound = ref 0 in
  let original_name prefix name =
    let prefix = prefix ^ "!" in
    let start = String.length prefix in
    if String.starts_with ~prefix name then
      match String.index_from_opt name start ':' with
      | Some stop when stop > start &&
          String.for_all (function '0' .. '9' -> true | _ -> false)
            (String.sub name start (stop - start)) ->
          String.sub name (stop + 1) (String.length name - stop - 1)
      | _ -> name
    else name
  in
  let symbol name =
    let safe = function
      | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '.' | '$' | '!' -> true
      | _ -> false in
    if name <> "" && String.length name <= 256 && String.for_all safe name &&
       (match name.[0] with '0' .. '9' -> false | _ -> true) &&
       not (List.mem name ["and"; "or"; "not"; "forall"; "exists"; "lambda"])
    then name
    else
      let name = if String.length name > 256 then String.sub name 0 256 ^ "..." else name in
      "|" ^ String.escaped name ^ "|"
  in
  let rec sort depth = function
    | A.BaseSort name -> symbol (original_name "sort" name)
    | A.ArraySort (domains, range) ->
        if depth = 0 || List.length domains > 32 then "Array"
        else "Array[" ^ String.concat ", " (List.map (sort (depth - 1)) domains) ^
             "; " ^ sort (depth - 1) range ^ "]"
  in
  let rec expression depth environment minimum e =
    if depth = 0 || !budget = 0 then "...:" ^ sort 2 (A.get_sort e)
    else (
      decr budget;
      let render minimum = expression (depth - 1) environment minimum in
      let precedence, text =
        match e with
        | A.Var (index, _) ->
            let name =
              if Z.sign index >= 0 && Z.fits_int index then
                List.nth_opt environment (Z.to_int index)
              else None in
            100, (match name with Some name -> name | None -> "#" ^ Z.to_string index)
        | A.Quantifier (kind, bindings, _, body) ->
            if List.length bindings > 32 then 100, "...:" ^ sort 2 (A.get_sort e)
            else
              let names = List.map (fun _ ->
                let name = "#b" ^ string_of_int !next_bound in
                incr next_bound;
                name) bindings in
              let declarations = List.map2 (fun name s -> name ^ ":" ^ sort 3 s) names bindings in
              let kind = match kind with A.Forall_k -> "forall"
                  | A.Exists_k -> "exists" | A.Lambda_k -> "lambda" in
              0, kind ^ " (" ^ String.concat ", " declarations ^ "). " ^
                 expression (depth - 1) (List.rev names @ environment) 0 body
        | A.App (decl, args) ->
            let is kind = decl.A.interp = Some kind in
            let name = if decl.A.interp = None
                then original_name "decl" decl.A.decl_name else decl.A.decl_name in
            let infix precedence token strict =
              precedence, String.concat (" " ^ token ^ " ")
                (List.mapi (fun i arg -> render
                  (if strict || i > 0 then precedence + 1 else precedence) arg) args) in
            if List.length args > 32 then 100, "...:" ^ sort 2 decl.A.range
            else if is V.op_num_rational && args = [] then
              (match decl.A.int_params with
               | [n; d] when Z.sign d > 0 ->
                   let text = Z.to_string n ^ (if Z.equal d Z.one then "" else "/" ^ Z.to_string d) in
                   if String.length text > 64 then 100, "...:" ^ sort 2 decl.A.range
                   else (if not (Z.equal d Z.one) then 50 else if Z.sign n < 0 then 60 else 100), text
               | _ -> 100, symbol name)
            else if is V.op_not && List.length args = 1 then
              60, "not " ^ render 61 (List.hd args)
            else if is V.op_arith_sub && List.length args = 1 then
              60, "-" ^ render 61 (List.hd args)
            else if List.length args >= 2 && is V.op_or then infix 10 "or" false
            else if List.length args >= 2 && is V.op_and then infix 20 "and" false
            else if List.length args = 2 && is V.op_eq then infix 30 "=" true
            else if List.length args = 2 && is V.op_arith_le then infix 30 "<=" true
            else if List.length args = 2 && is V.op_arith_lt then infix 30 "<" true
            else if List.length args = 2 && is V.op_arith_ge then infix 30 ">=" true
            else if List.length args = 2 && is V.op_arith_gt then infix 30 ">" true
            else if List.length args >= 2 && (is V.op_arith_add || is V.op_plus) then
              infix 40 "+" false
            else if List.length args >= 2 && is V.op_arith_sub then infix 40 "-" false
            else if List.length args >= 2 && (is V.op_arith_mul || is V.op_mul) then
              infix 50 "*" false
            else if List.length args = 2 && is V.op_arith_div then infix 50 "/" false
            else
              100, symbol name ^
                (if args = [] then "" else "(" ^ String.concat ", " (List.map (render 0) args) ^ ")")
      in
      if precedence < minimum then "(" ^ text ^ ")" else text)
  in
  match judgment with
  | Z3UnifiedProof.Holds e -> expression 12 [] 0 e
  | Z3UnifiedProof.Equal (left, right) ->
      let left = expression 12 [] 31 left in
      left ^ " = " ^ expression 12 [] 31 right
  | Z3UnifiedProof.Observational (left, right) ->
      let left = expression 12 [] 31 left in
      left ^ " ~ " ^ expression 12 [] 31 right

let pretty_expr e = pretty_judgment (Z3UnifiedProof.Holds e)

(* Inspect argument structure, not just the shared connective declaration. *)
let assertion_hash value = Z.of_int (Hashtbl.hash_param 64 256 value)

let report_diagnostics diagnostic expected =
  match diagnostic, expected with
  | Z3ProofDocument.DocumentChecked (pending, obligations), Some actual
      when Z.equal pending actual ->
      let families = Hashtbl.create 32 and total = ref Z.zero in
      List.iter (fun obligation ->
        let key = diagnostic_rule obligation.Z3ProofDocument.obligation_rule,
                  fingerprint obligation.Z3ProofDocument.obligation_conclusion in
        let count, first, conclusion =
          match Hashtbl.find_opt families key with
          | Some value -> value
          | None -> Z.zero, obligation.Z3ProofDocument.obligation_index,
                    obligation.Z3ProofDocument.obligation_conclusion in
        let local = obligation.Z3ProofDocument.obligation_count in
        total := Z.add !total local;
        Hashtbl.replace families key (Z.add count local, first, conclusion)) obligations;
      if not (Z.equal !total pending) then Z3Native.fail "Diagnostic obligation count mismatch";
      Printf.eprintf "diagnostic\tchecked\tpending=%s\tfamilies=%d\n"
        (Z.to_string pending) (Hashtbl.length families);
      Hashtbl.to_seq families |> List.of_seq |>
        List.sort (fun (key1, (n1, _, _)) (key2, (n2, _, _)) ->
          let order = Z.compare n2 n1 in if order = 0 then compare key1 key2 else order) |>
        List.iter (fun ((rule, shape), (count, first, conclusion)) ->
          Printf.eprintf "obligation\t%s\t%s\t%s\t%s\n"
            rule (Z.to_string count) (Z.to_string first) shape;
          Printf.eprintf "expression\t%s\t%s\t%s\t%s\n"
            rule (Z.to_string count) (Z.to_string first) (pretty_judgment conclusion))
  | Z3ProofDocument.DocumentRejected (stage, index, source), None ->
      Printf.eprintf "diagnostic\trejected\tstage=%s\tindex=%s%s\n"
        (diagnostic_stage stage) (match index with None -> "-" | Some n -> Z.to_string n)
        (match source with None -> "" | Some e -> "\t" ^ fingerprint (Z3UnifiedProof.Holds e))
  | _ -> Z3Native.fail "Diagnostic result disagrees with document checker"

let result_text = function
  | None -> "REJECT"
  | Some n when Z.equal n Z.zero -> "ACCEPT"
  | Some n -> "PARTIAL " ^ Z.to_string n

(* [fingerprint] groups obligations and is deliberately lossy. --readable also renders what the
   checker saw for one representative of each group: numeral values, bit-vector widths, declaration
   parameters, array and binder sorts, and declaration identity. Every limit below is explicit and
   leaves a "<...>" marker; nothing here feeds back into checking. *)
module Readable = struct
  module A = Z3AstTheory
  module P = Z3ProofDocument
  module U = Z3UnifiedProof

  let max_depth = 48 and max_nodes = 1000 and max_chars = 4096 and max_name_bytes = 96
  and max_digits = 100 and max_params = 16 and max_families = 20 and max_premises = 8
  and max_report_chars = 131072

  exception Limit of string

  type state = { text : Buffer.t; mutable nodes : int; mutable cut : bool }

  let add state piece =
    if Buffer.length state.text + String.length piece > max_chars then raise (Limit "chars");
    Buffer.add_string state.text piece

  let digit_limit = Z.pow (Z.of_int 10) max_digits

  (* Size is checked before conversion: a huge numeral never becomes a huge string. *)
  let integer n =
    if Z.numbits n <= 333 && Z.lt (Z.abs n) digit_limit then Z.to_string n
    else Printf.sprintf "<%shuge integer: more than %d digits omitted>"
        (if Z.sign n < 0 then "-" else "+") max_digits

  let simple_character = function
    | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '~' | '!' | '@' | '$' | '%' | '^' | '&' | '*'
    | '_' | '-' | '+' | '=' | '<' | '>' | '.' | '?' | '/' -> true
    | _ -> false

  (* SMT-LIB symbol for [name] from byte [first]: simple when possible, otherwise |quoted| with
     \xNN for control, invalid-UTF-8, '|' and '\' bytes. Long names are cut at [max_name_bytes]. *)
  let symbol ?(first = 0) name =
    let length = String.length name - first in
    let shown = min length max_name_bytes in
    let simple = ref (shown > 0 && (name.[first] < '0' || name.[first] > '9')) in
    for i = first to first + shown - 1 do
      if not (simple_character name.[i]) then simple := false
    done;
    if !simple && shown = length then String.sub name first length
    else (
      let quoted = Buffer.create (shown + 8) in
      Buffer.add_char quoted '|';
      let position = ref first in
      while !position < first + shown do
        let decoded = String.get_utf_8_uchar name !position in
        let width = Uchar.utf_decode_length decoded in
        let scalar = if Uchar.utf_decode_is_valid decoded
          then Uchar.to_int (Uchar.utf_decode_uchar decoded) else -1 in
        if scalar >= 0x20 && scalar <> 0x7f && (scalar < 0x80 || scalar >= 0xa0)
           && scalar <> 0x7c && scalar <> 0x5c
        then Buffer.add_string quoted (String.sub name !position width)
        else
          for j = !position to !position + width - 1 do
            Buffer.add_string quoted (Printf.sprintf "\\x%02x" (Char.code name.[j]))
          done;
        position := !position + width
      done;
      if !position < String.length name then
        Buffer.add_string quoted
          (Printf.sprintf "...<%d more bytes>" (String.length name - !position));
      Buffer.add_char quoted '|';
      Buffer.contents quoted)

  (* The native bridge names an opaque declaration "decl!ID:NAME" and a non-builtin sort
     "sort!ID:NAME"; they are shown as NAME#ID, which keeps same-named symbols apart. *)
  let identified prefix name =
    let start = String.length prefix + 1 in
    if String.length name > start && String.starts_with ~prefix:(prefix ^ "!") name then (
      let stop = min (String.length name) (start + 21) in
      let colon = ref start in
      while !colon < stop && name.[!colon] <> ':' do incr colon done;
      if !colon > start && !colon < stop then (
        let digits = ref true in
        for i = start to !colon - 1 do
          if name.[i] < '0' || name.[i] > '9' then digits := false
        done;
        if !digits then Some (!colon + 1, String.sub name start (!colon - start)) else None)
      else None)
    else None

  let rec sort state depth = function
    | A.BaseSort name ->
        add state (match identified "sort" name with
                   | Some (first, id) -> symbol ~first name ^ "#" ^ id
                   | None -> symbol name)
    | A.ArraySort (domains, range) ->
        if depth = 0 then (state.cut <- true; add state "<...depth>")
        else (
          add state "(Array";
          List.iter (fun domain -> add state " "; sort state (depth - 1) domain) domains;
          add state " ";
          sort state (depth - 1) range;
          add state ")")

  let kind_name = function
    | A.Forall_k -> "forall" | A.Exists_k -> "exists" | A.Lambda_k -> "lambda"

  let parameters state = function
    | [] -> ()
    | values ->
        add state "[";
        List.iteri (fun i value ->
          if i < max_params then (if i > 0 then add state ","; add state (integer value))) values;
        let extra = List.length values - max_params in
        if extra > 0 then add state (Printf.sprintf ",<%d more>" extra);
        add state "]"

  let datatype_marker k =
    if Z.equal k Z3DatatypeLemma.op_constructor then "@constructor"
    else if Z.equal k Z3DatatypeLemma.op_recognizer then "@recognizer"
    else if Z.equal k Z3DatatypeLemma.op_accessor then "@accessor"
    else ""

  (* Sorts are equal if they are the same name or the same array of equal sorts. The comparison is bounded like the rendering (depth,
     nodes, name bytes): when it cannot be completed the sorts count as different, which only prints more. *)
  let max_compared_name_bytes = 4096

  let same_sort a b =
    let budget = ref max_nodes in
    let rec go depth a b =
      decr budget;
      depth > 0 && !budget >= 0 &&
      (match a, b with
       | A.BaseSort x, A.BaseSort y ->
           String.length x <= max_compared_name_bytes && String.equal x y
       | A.ArraySort (d1, r1), A.ArraySort (d2, r2) ->
           List.compare_lengths d1 d2 = 0 && List.for_all2 (go (depth - 1)) d1 d2 && go (depth - 1) r1 r2
       | _ -> false)
    in
    go max_depth a b

  (* A rational numeral shows its value (and its sort unless Int), a bit-vector numeral
     (_ bvVALUE WIDTH). Every other head is NAME, followed by [reflected integer parameters]; an
     uninterpreted head is NAME#ID (or NAME#- without a native id) and a datatype operation carries
     @constructor, @recognizer or @accessor, each with its range sort after ':', so neither can
     be mistaken for a builtin connective that shares its name. Every other interpreted head also
     shows its range after ':', for example (const:(Array Int Int) 0), (select:Int a i) or
     (extract[32,15,8]:BV8 x), because the arguments do not always carry it (the domain sorts of a
     constant array occur nowhere in its arguments), except where the range is printed anyway or
     needs no printing: Bool (connectives and predicates: an interpreted head without a range is
     Bool) and the sort of the first argument, which that argument prints (+ * bvadd store, as in
     SMT-LIB). [implied] says whether the range is the first argument's sort and that argument
     prints its own: it is false when the argument would be cut by the depth or the node limit,
     is a quantifier (a lambda prints its binder sorts, not its own sort), or the comparison was
     not completed. *)
  let head state ~implied decl =
    match decl.A.interp, decl.A.int_params with
    | Some k, [n; d] when Z.equal k Z3ValueTheory.op_num_rational ->
        add state (integer n);
        if not (Z.equal d Z.one) then add state ("/" ^ integer d);
        (match decl.A.range with
         | A.BaseSort "Int" -> ()
         | range -> add state ":"; sort state max_depth range)
    | Some k, [width; value] when Z.equal k Z3BvLemma.op_numeral ->
        add state ("(_ bv" ^ integer value ^ " " ^ integer width ^ ")")
    | interp, values ->
        let name = decl.A.decl_name in
        add state (match interp with
                   | None ->
                       (match identified "decl" name with
                        | Some (first, id) -> symbol ~first name ^ "#" ^ id
                        | None -> symbol name ^ "#-")
                   | Some k -> symbol name ^ datatype_marker k);
        parameters state values;
        (match interp, decl.A.range with
         | Some k, A.BaseSort "Bool" when datatype_marker k = "" -> ()
         | Some k, _ when datatype_marker k = "" && Lazy.force implied -> ()
         | _ -> add state ":"; sort state max_depth decl.A.range)

  let rec expression state depth e =
    if depth = 0 then (state.cut <- true; add state "<...depth>")
    else (
      if state.nodes >= max_nodes then raise (Limit "nodes");
      state.nodes <- state.nodes + 1;
      match e with
      | A.Var (index, s) -> add state ("#" ^ integer index ^ ":"); sort state max_depth s
      | A.Quantifier (kind, sorts, _, body) ->
          add state ("(" ^ kind_name kind ^ " [");
          List.iteri (fun i s -> if i > 0 then add state " "; sort state max_depth s) sorts;
          add state "] ";
          expression state (depth - 1) body;
          add state ")"
      | A.App (decl, []) -> head state ~implied:(lazy false) decl
      | A.App (decl, arguments) ->
          add state "(";
          let first = List.hd arguments in
          let implied = lazy (depth >= 2 && state.nodes < max_nodes &&
                              (match first with
                               | A.Quantifier _ -> false
                               | _ -> same_sort decl.A.range (A.get_sort first))) in
          head state ~implied decl;
          List.iter (fun argument -> add state " "; expression state (depth - 1) argument) arguments;
          add state ")")

  let judgment state = function
    | U.Holds e -> add state "holds("; expression state max_depth e; add state ")"
    | U.Equal (left, right) ->
        add state "equal("; expression state max_depth left; add state ", ";
        expression state max_depth right; add state ")"
    | U.Observational (left, right) ->
        add state "observational("; expression state max_depth left; add state ", ";
        expression state max_depth right; add state ")"

  (* The bounded text of [write], and whether any limit cut it short. *)
  let render write =
    let state = { text = Buffer.create 256; nodes = 0; cut = false } in
    (try write state with Limit reason ->
       state.cut <- true;
       Buffer.add_string state.text ("<..." ^ reason ^ ">"));
    Buffer.contents state.text, state.cut

  let judgment_text value = render (fun state -> judgment state value)

  (* One readable block per query: the representative of each of the first [max_families]
     obligation families, in the order of the machine rows. The node index is the position of the
     obligation in the document's proof entries, which is where its premise ids are read from. *)
  let report_text query verdict (doc : P.document) diagnostic =
    let out = Buffer.create 1024 and full = ref false in
    let emit block =
      if not !full then
        if Buffer.length out + String.length block > max_report_chars then full := true
        else Buffer.add_string out block
    in
    let entry_at index =
      if Z.sign index >= 0 && Z.fits_int index then List.nth_opt doc.P.entries (Z.to_int index)
      else None
    in
    let premise_list = function
      | [] -> "none"
      | ids ->
          let extra = List.length ids - max_premises in
          String.concat " " (List.filteri (fun i _ -> i < max_premises) ids
                             |> List.map (fun id -> "#" ^ integer id)) ^
          (if extra > 0 then Printf.sprintf " ...<%d more>" extra else "")
    in
    let family_block position total rule count members (first : P.unmet_obligation) =
      let b = Buffer.create 512 in
      let index = first.P.obligation_index in
      Printf.bprintf b "readable\tfamily=%d/%d\trule=%s\tcount=%s\tmembers=%d\tnode=%s\tnode-pending=%s\n"
        position total rule (integer count) members (integer index)
        (integer first.P.obligation_count);
      let premises = first.P.obligation_premises in
      let ids = match entry_at index with
        | None -> Error "no document entry at this index"
        | Some e when diagnostic_rule e.P.rule <> diagnostic_rule first.P.obligation_rule
                      || List.length e.P.premise_ids <> List.length premises ->
            Error "the document entry at this index has another rule or premise count"
        | Some e -> Ok e.P.premise_ids in
      (match ids with
       | Ok ids -> Printf.bprintf b "  node %s: premises: %s\n" (integer index) (premise_list ids)
       | Error reason ->
           Printf.bprintf b "  node %s: no source-node mapping (%s): premise ids unavailable\n"
             (integer index) reason);
      List.iteri (fun k premise ->
        if k < max_premises then (
          let label = match ids with
            | Ok ids -> "#" ^ integer (List.nth ids k)
            | Error _ -> "[" ^ string_of_int k ^ "]" in
          Printf.bprintf b "  premise %s: %s\n" label (fst (judgment_text premise)))) premises;
      let extra = List.length premises - max_premises in
      if extra > 0 then Printf.bprintf b "  ...<%d more premises omitted>\n" extra;
      let conclusion, conclusion_cut = judgment_text first.P.obligation_conclusion in
      Printf.bprintf b "  conclusion: %s\n" conclusion;
      let source, source_cut = judgment_text (U.Holds first.P.obligation_source) in
      if source = conclusion && not conclusion_cut && not source_cut
      then Buffer.add_string b "  source formula: same as conclusion\n"
      else Printf.bprintf b "  source formula: %s\n" source;
      Buffer.contents b
    in
    (match diagnostic with
     | P.DocumentChecked (pending, obligations) ->
         let families = Hashtbl.create 32 in
         List.iter (fun obligation ->
           let key = diagnostic_rule obligation.P.obligation_rule,
                     fingerprint obligation.P.obligation_conclusion in
           let count, members, first =
             match Hashtbl.find_opt families key with
             | Some value -> value
             | None -> Z.zero, 0, obligation in
           Hashtbl.replace families key
             (Z.add count obligation.P.obligation_count, members + 1, first)) obligations;
         let ordered =
           Hashtbl.to_seq families |> List.of_seq |>
           List.sort (fun (key1, (n1, _, _)) (key2, (n2, _, _)) ->
             let order = Z.compare n2 n1 in if order = 0 then compare key1 key2 else order) in
         let total = List.length ordered in
         let shown = min total max_families in
         emit (Printf.sprintf "readable\tquery=%d\tverdict=%s\tpending=%s\tfamilies=%d\tshown=%d\n"
                 query verdict (integer pending) total shown);
         List.iteri (fun i ((rule, _), (count, members, first)) ->
           if i < max_families then emit (family_block (i + 1) total rule count members first))
           ordered;
         if total > shown then
           emit (Printf.sprintf "readable\tomitted\tfamilies=%d\treason=family-limit\n" (total - shown));
         if !full then Buffer.add_string out "readable\tomitted\treason=report-size\n"
     | P.DocumentRejected (stage, index, source) ->
         let b = Buffer.create 256 in
         Printf.bprintf b "readable\tquery=%d\tverdict=%s\tstage=%s\tindex=%s\n" query verdict
           (diagnostic_stage stage) (match index with None -> "-" | Some n -> integer n);
         (match stage, index with
          | (P.ProofEntry | P.MissingPremise), Some i ->
              (match entry_at i with
               | Some e ->
                   Printf.bprintf b "  node %s: rule=%s premises: %s\n" (integer i)
                     (diagnostic_rule e.P.rule) (premise_list e.P.premise_ids)
               | None ->
                   Printf.bprintf b "  node %s: no source-node mapping (no document entry at this index)\n"
                     (integer i))
          | _ -> ());
         (match source with
          | Some e ->
              Printf.bprintf b "  source formula: %s\n" (fst (judgment_text (U.Holds e)))
          | None -> Buffer.add_string b "  source formula: none reported\n");
         emit (Buffer.contents b));
    Buffer.add_string out (Printf.sprintf "readable\tend\tquery=%d\n" query);
    Buffer.contents out

  let report query verdict doc diagnostic =
    prerr_string (report_text query verdict doc diagnostic);
    flush stderr
end

let check_proof statistics diagnostics readable query sorted_core start solved assertions proof =
  let doc, schema = Z3NativeProof.marshal_with_datatypes assertions proof in
  let marshaled = Unix.gettimeofday () in
  let datatype = schema.Z3DatatypeSignature.cases <> [] in
  let sorted = datatype || sorted_core in
  let result, diagnostic =
    if diagnostics then (
      let result, diagnostic =
        if sorted then Z3SortedProof.check_document_epsilon_diagnosed schema doc
        else Z3ProofDocument.check_document_diagnosed_indexed assertion_hash doc in
      result, Some diagnostic)
    else (
      let result =
        if sorted then Z3SortedProof.check_document_epsilon schema doc
        else Z3ProofDocument.check_document_indexed assertion_hash doc in
      result, None) in
  let checked = Unix.gettimeofday () in
  let summary = Printf.sprintf
      "solve_ms=%.3f marshal_ms=%.3f check_ms=%.3f expressions=%d declarations=%d proof_nodes=%d semantics=%s"
      ((solved -. start) *. 1000.) ((marshaled -. solved) *. 1000.)
      ((checked -. marshaled) *. 1000.) (List.length doc.expressions)
      (List.length doc.declarations) (List.length doc.entries)
      (if datatype then "sorted-datatype" else if sorted then "sorted-core" else "legacy") in
  if statistics then Printf.eprintf "%s\n%!" summary;
  (match diagnostic with
   | None -> ()
   | Some diagnostic ->
       report_diagnostics diagnostic result;
       if readable then Readable.report query (result_text result) doc diagnostic;
       if statistics then
         Printf.eprintf "diagnose_ms=%.3f\n%!" ((Unix.gettimeofday () -. checked) *. 1000.));
  let edges = List.fold_left (fun count entry ->
    count + List.length entry.Z3ProofDocument.premise_ids) 0 doc.entries in
  let binder_nodes, binder_edges = List.fold_left (fun (nodes, edges) entry ->
    match entry.Z3ProofDocument.rule with
    | Z3UnifiedProof.QuantifierIntroduction certificate ->
        nodes + List.length certificate.Z3UnifiedProof.binder_entries,
        List.fold_left (fun count entry ->
            count + List.length entry.Z3UnifiedProof.binder_premises)
          edges certificate.Z3UnifiedProof.binder_entries
    | _ -> nodes, edges) (0, 0) doc.entries in
  result, Printf.sprintf
    "%s assertions=%d proof_edges=%d binder_nodes=%d binder_edges=%d pending=%s"
    summary (List.length assertions) edges binder_nodes binder_edges
    (match result with None -> "unknown" | Some n -> Z.to_string n)

let whitespace = function ' ' | '\t' | '\r' | '\n' -> true | _ -> false

(* Frame complete commands without interpreting SMT-LIB expressions. *)
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
    | c ->
        Buffer.add_char buffer c;
        advance depth mode c
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

let interactive statistics diagnostics readable sorted_core clause_proofs timeout =
  let context = Z3Native.create_context timeout in
  let error = ref false and rejected = ref false and partial = ref false and queries = ref 0 in
  let start = ref (Unix.gettimeofday ()) in
  let registration = Z3native.set_proof_check_callback context (fun proof vector ->
    incr queries;
    let solved = Unix.gettimeofday () in
    let assertions = List.init (Z3native.ast_vector_size context vector)
        (Z3native.ast_vector_get context vector) in
    let result, summary = check_proof statistics diagnostics readable !queries sorted_core !start solved assertions proof in
    (match result with
     | None -> rejected := true
     | Some n -> if not (Z.equal n Z.zero) then partial := true);
    "; proof-check " ^ result_text result ^ "\n; proof-stats " ^ summary)
  in
  let initialize () =
    ignore (Z3native.eval_smtlib2_string context
      ("(set-option :produce-proofs true)(set-option :timeout " ^ Z.to_string timeout ^ ")" ^
       (if clause_proofs then "(set-option :smt.clause_proof true)" else "")))
  in
  let report_error message =
    error := true;
    let escaped = String.concat "\"\"" (String.split_on_char '"' message) in
    Printf.printf "(error \"%s\")\n%!" escaped
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
                report_error message;
                false
            in
            if not (successful && name = "exit") then commands ()
      in
      commands ());
  if !error then 2 else if !rejected then 1 else if !partial then 3 else 0

let run args =
  let statistics = ref false and diagnostics = ref false and sorted_core = ref false
  and timeout = ref Z.zero and path = ref None and interactive_mode = ref false
  and clause_proofs = ref false and readable = ref false in
  let options = [
    "--interactive", Arg.Set interactive_mode,
      " Evaluate stdin commands incrementally and certify each UNSAT proof";
    "--clause-proofs", Arg.Set clause_proofs,
      " Produce and certify clausal SMT search proofs using reverse unit propagation";
    "--stats", Arg.Set statistics, " Report phase timings and unique marshaled node counts";
    "--diagnostics", Arg.Set diagnostics, " Report typed unmet-obligation fingerprints on stderr";
    "--readable", Arg.Set readable,
      " Also print bounded readable pending/rejected conditions on stderr (implies --diagnostics)";
    "--sorted-core", Arg.Set sorted_core,
      " Use the sort-indexed kernel without legacy fallback, including for non-datatype proofs";
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
      options anonymous "usage: checker [--interactive] [--clause-proofs] [--stats] [--diagnostics] [--readable] [--sorted-core] [--timeout-ms N] [input.smt2]";
    if !readable then diagnostics := true;
    if !interactive_mode then (
      if !path <> None && !path <> Some "-" then
        raise (Arg.Bad "--interactive reads commands from stdin, not an input file");
      exit (interactive !statistics !diagnostics !readable !sorted_core !clause_proofs !timeout));
    let input =
      match !path with
      | None | Some "-" -> read_all stdin
      | Some name ->
          let channel = open_in_bin name in
          Fun.protect ~finally:(fun () -> close_in_noerr channel)
            (fun () -> read_all channel)
    in
    let start = Unix.gettimeofday () in
    match Z3Native.solve_with_clause_proofs input !timeout !clause_proofs with
    | Z3Native.Sat -> print_endline "SAT"; exit 4
    | Z3Native.Unknown reason ->
        Printf.printf "UNKNOWN %s\n" reason; exit 5
    | Z3Native.Unsat (assertions, proof) ->
        let solved = Unix.gettimeofday () in
        let result, _ = check_proof !statistics !diagnostics !readable 1 !sorted_core start solved assertions proof in
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
