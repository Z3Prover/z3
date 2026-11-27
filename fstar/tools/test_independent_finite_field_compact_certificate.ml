module A = Z3AstTheory
module T = Z3OperatorTags
module Canonical = Z3CanonicalOps
module F = Z3SortedFiniteField
module C = Z3FiniteFieldCertificate
module W = Z3IndependentFiniteFieldWitness
module K = Z3IndependentFiniteFieldCompactCertificate
module I = Z3ProofIndex
module P = Z3IndependentFiniteFieldCompactPac
module M = Z3IndependentFiniteFieldCompactPacMetered

let zi = Z.of_int
let require value message = if not value then failwith message
let decl name domain range interp int_params =
  { A.decl_name = name; domain; range; interp; int_params }

let fixture p =
  let field = A.SortApp (A.FiniteFieldSymbol p, []) in
  let num n = A.App (decl "ff" [] field (Some F.op_ff_num) [p; n], []) in
  let x = A.App (decl "x" [] field None [], []) in
  let sum = A.App (decl "ff.add" [field; field] field (Some (zi 301)) [p], [x; num Z.zero]) in
  let eq = A.App (decl "=" [field; field] A.bool_sort (Some T.op_eq) [], [sum; x]) in
  let neq = A.App (decl "not" [A.bool_sort] A.bool_sort (Some T.op_not) [], [eq]) in
  let neg_one = num (Z.pred p) in
  let cert = { C.pac_premises = [neq];
               pac_nodes = [C.PacInput (zi 1); C.PacInput Z.zero;
                 C.PacMul (zi 1, neg_one, [zi 2]); C.PacAdd (Z.zero, zi 2);
                 C.PacMul (zi 3, neg_one, [])];
               pac_root = zi 4; pac_support = [Z.zero] } in
  eq, cert

let check_budget name expected run =
  let fuel = zi 1000000 in
  require (run Z.zero = None && run (zi (-1)) = None) (name ^ ": nonpositive fuel");
  match run fuel with
  | None -> failwith (name ^ ": exhausted test fuel")
  | Some (result, work) ->
    require (result = expected) (name ^ ": reference mismatch");
    require (Z.gt work Z.zero && Z.leq work fuel) (name ^ ": work outside budget");
    require (run work = Some (result, work)) (name ^ ": exact fuel");
    require (run (Z.pred work) = None) (name ^ ": one-less fuel");
    result, work

let check_metered p cert e =
  check_budget "already-prime certificate" (K.check_for_prime p cert e)
    (fun fuel -> K.check_for_prime_metered fuel p cert e)

let check_evidence_metered cert e evidence =
  check_budget "evidence-checked certificate" (K.check_with_evidence cert e evidence)
    (fun fuel -> K.check_with_evidence_metered fuel cert e evidence)

let check_count limit xs =
  let length = zi (List.length xs) in
  let expected = if Z.leq length limit then Some length else None in
  let result, work = check_budget "capped count" expected
    (fun fuel -> K.count_at_most_metered fuel limit xs) in
  let expected_work = if Z.sign limit < 0 then Z.one else Z.succ (Z.min length limit) in
  require (work = expected_work) "capped count scanned beyond the required prefix";
  result, work

let check_exact_length xs =
  let expected = zi (List.length xs) in
  let result, work = check_budget "fuel-limited exact length" expected
    (fun fuel ->
      match K.count_at_most_metered fuel fuel xs with
      | None -> None
      | Some (Some count, spent) -> Some (count, spent)
      | Some (None, _) -> failwith "fuel-limit counter completed an overflow rejection") in
  require (work = Z.succ expected) "exact length skipped a list guard";
  result, work

let check_header cert =
  let premises = List.length cert.C.pac_premises in
  let nodes = List.length cert.C.pac_nodes in
  let support = List.length cert.C.pac_support in
  let valid_premises = premises > 0 && premises <= 4096 in
  let valid_nodes = nodes <= 100000 in
  let expected =
    if valid_premises && valid_nodes && support <= premises
    then Some (zi premises, zi nodes) else None in
  let result, work = check_budget "certificate header" expected
    (fun fuel -> K.admit_header_metered fuel cert) in
  let expected_work = min premises 4096 + 1 +
    (if valid_premises then min nodes 100000 + 1 +
      (if valid_nodes then min support premises + 1 else 0) else 0) in
  require (work = zi expected_work) "header did not cap or share scan work";
  result, work

let rec sort_visit_work left right =
  match left, right with
  | A.SortApp (symbol, args), A.SortApp (other, rest) ->
    if symbol = other then Z.succ (sort_list_visit_work args rest) else Z.one
  | A.ArraySort (domain, range), A.ArraySort (other, result) ->
    let domain_work = sort_list_visit_work domain other in
    if A.sort_list_eq domain other then
      Z.add (Z.succ domain_work)
        (Z.add (sort_visit_work range result) (if A.sort_eq range result then Z.one else Z.zero))
    else Z.succ domain_work
  | _ -> Z.one
and sort_list_visit_work left right =
  match left, right with
  | a :: rest, b :: tail ->
    let head_work = sort_visit_work a b in
    if A.sort_eq a b then Z.add head_work (sort_list_visit_work rest tail) else head_work
  | _ -> Z.one

let check_sort_pair left right =
  let expected = A.sort_eq left right in
  require (expected = (left = right)) "sort reference differs from structural equality";
  let result, work = check_budget "structural sort comparison" expected
    (fun fuel -> K.sort_eq_metered fuel left right) in
  require (work = sort_list_visit_work [left] [right])
    "sort comparison changed reached domain/range work";
  result, work

let check_sort_lists left right =
  let expected = A.sort_list_eq left right in
  require (expected = (left = right)) "sort-list reference differs from structural equality";
  let result, work = check_budget "structural sort-list comparison" expected
    (fun fuel -> K.sort_list_eq_metered fuel left right) in
  require (work = sort_list_visit_work left right)
    "sort-list comparison changed reached prefix work";
  result, work

let int_list_visit_work left right =
  let rec prefix visited xs ys =
    match xs, ys with
    | a :: rest, b :: tail when a = b -> prefix (Z.succ visited) rest tail
    | _ -> Z.succ visited in
  prefix Z.zero left right

let check_int_lists left right =
  let result, work = check_budget "integer-list comparison" (left = right)
    (fun fuel -> K.int_list_eq_metered fuel left right) in
  require (work = int_list_visit_work left right)
    "integer-list comparison inspected beyond its reached prefix";
  result, work

let declaration_visit_work left right =
  if left.A.decl_name <> right.A.decl_name then Z.one
  else
    let domain = Z.succ (sort_list_visit_work left.A.domain right.A.domain) in
    if left.A.domain <> right.A.domain then domain
    else
      let ranged = Z.add domain (sort_list_visit_work [left.A.range] [right.A.range]) in
      if left.A.range <> right.A.range then ranged
      else
        let metadata = Z.succ ranged in
        if left.A.interp <> right.A.interp then metadata
        else Z.add metadata (int_list_visit_work left.A.int_params right.A.int_params)

let check_declarations left right =
  let result, work = check_budget "declaration comparison" (left = right)
    (fun fuel -> K.decl_eq_metered fuel left right) in
  require (work = declaration_visit_work left right)
    "declaration comparison skipped or reset a reached field";
  result, work

let check_allocation state term =
  let result, work = check_budget "encoding allocation" (F.allocate state term)
    (fun fuel -> K.allocate_metered fuel state term) in
  let length = List.length state.F.terms in
  let cap = Z.to_int F.max_variables in
  let counting = zi (2 + min length (cap - 1)) in
  let copying = if length < cap then zi (length + 1) else Z.zero in
  require (work = Z.add counting copying)
    "encoding allocation did not share capped-count and append work";
  require (K.allocate_metered (Z.pred counting) state term = None)
    "encoding allocation reset count fuel after its gate";
  if length < cap then
    require (K.allocate_metered counting state term = None)
      "encoding allocation copied without remaining fuel";
  result, work

let prime_header_work cert =
  let premises, premise_work = check_count (zi 4096) cert.C.pac_premises in
  let node_work =
    match premises with
    | Some n when Z.sign n > 0 -> snd (check_count (zi 100000) cert.C.pac_nodes)
    | _ -> Z.zero in
  Z.succ (Z.add premise_work node_work)

let check_support_tree n previous tree support =
  let result, work = check_budget "support tree" (F.support_tree n previous tree support)
    (fun fuel -> K.support_tree_metered fuel n previous tree support) in
  let rec prefix_work previous spent = function
    | [] -> Z.succ spent
    | k :: rest ->
      if Z.sign k >= 0 && Z.lt previous k && Z.lt k n then
        prefix_work k (Z.add spent (zi (1 + Z.numbits (Z.succ k)))) rest
      else Z.succ spent in
  require (work = prefix_work previous Z.zero support)
    "support tree did not charge guards and insertion depth";
  result, work

let check_equation_index tree k equations =
  let result, work = check_budget "equation index" (F.index_equations tree k equations)
    (fun fuel -> K.index_equations_metered fuel tree k equations) in
  let rec prefix_work k spent = function
    | [] -> Z.succ spent
    | _ :: rest ->
      if Z.sign k < 0 then Z.succ spent
      else prefix_work (Z.pred k)
        (Z.add spent (zi (1 + Z.numbits (Z.succ k)))) rest in
  require (work = prefix_work k Z.zero equations)
    "equation index did not charge reached guards and insertion depth";
  result, work

let boolean_sorts_visit_work domain =
  let rec prefix spent = function
    | [] -> Z.succ spent
    | s :: rest ->
      if s = A.bool_sort then prefix (Z.succ spent) rest else Z.succ spent in
  prefix Z.zero domain

let canonical_or_visit_work declaration =
  if declaration.A.decl_name = "or" && declaration.A.interp = Some T.op_or
  then Z.succ (boolean_sorts_visit_work declaration.A.domain)
  else Z.one

let check_boolean_sorts domain =
  let result, work = check_budget "Boolean domain" (Canonical.boolean_sorts domain)
    (fun fuel -> K.boolean_sorts_metered fuel domain) in
  require (work = boolean_sorts_visit_work domain)
    "Boolean domain scanned beyond its reached prefix";
  result, work

let check_canonical_or declaration =
  let result, work = check_budget "canonical or" (Canonical.canonical_or declaration)
    (fun fuel -> K.canonical_or_metered fuel declaration) in
  require (work = canonical_or_visit_work declaration)
    "canonical or reset or skipped Boolean-domain fuel";
  result, work

let check_clause_literals expression =
  let result, work = check_budget "clause literals" (F.clause_literals expression)
    (fun fuel -> K.clause_literals_metered fuel expression) in
  let expected =
    match expression with
    | A.App (declaration, _) -> canonical_or_visit_work declaration
    | _ -> Z.one in
  require (work = expected) "clause extraction reset recognition fuel";
  result, work

let domain_visit_work p domain =
  let rec prefix spent = function
    | [] -> Z.succ spent
    | sort :: rest ->
      if A.sort_eq sort (F.ff_sort p) then prefix (Z.succ spent) rest
      else Z.succ spent in
  prefix Z.zero domain

let check_domain_arity p domain =
  let expected =
    if List.for_all (fun sort -> A.sort_eq sort (F.ff_sort p)) domain
    then Some (zi (List.length domain)) else None in
  let result, work = check_budget "field domain arity" expected
    (fun fuel -> K.domain_arity_metered fuel p domain) in
  require (work = domain_visit_work p domain)
    "domain arity did not stop at the charged prefix";
  result, work

let operation_visit_work declaration =
  match declaration.A.int_params, declaration.A.interp with
  | [p], Some tag when Z.geq p (zi 2) &&
      A.sort_eq declaration.A.range (F.ff_sort p) &&
      List.mem tag [zi 301; zi 302; zi 304] ->
    Z.succ (domain_visit_work p declaration.A.domain)
  | _ -> Z.one

let check_operation declaration =
  let result, work = check_budget "field operation declaration" (F.operation_of declaration)
    (fun fuel -> K.operation_of_metered fuel declaration) in
  require (work = operation_visit_work declaration)
    "operation declaration reset or skipped domain fuel";
  result, work

let arguments_visit_work p domain args =
  let rec prefix spent domain args =
    match domain, args with
    | _ :: ds, arg :: rest when A.sort_eq (A.get_sort arg) (F.ff_sort p) ->
      prefix (Z.succ spent) ds rest
    | _ -> Z.succ spent in
  prefix Z.zero domain args

let check_arguments p domain args =
  let expected = F.args_have_sort p args && List.length args = List.length domain in
  let result, work = check_budget "field argument sort/arity" expected
    (fun fuel -> K.arguments_match_metered fuel p domain args) in
  require (work = arguments_visit_work p domain args)
    "argument matching did not stop at the charged prefix";
  result, work

let check_operation_at declaration args =
  let recognized, declaration_work = check_operation declaration in
  let result, work = check_budget "field operation arguments" (F.operation_at declaration args)
    (fun fuel -> K.operation_at_metered fuel declaration args) in
  let extra =
    match recognized with
    | None -> Z.zero
    | Some (p, _) ->
      require (K.operation_at_metered declaration_work declaration args = None)
        "operation_at skipped the remaining argument budget";
      arguments_visit_work p declaration.A.domain args in
  require (work = Z.add declaration_work extra)
    "operation_at reset or skipped shared declaration/argument fuel";
  result, work

let modulus_recognition_work e =
  match F.numeral e with
  | Some _ -> Z.one
  | None ->
    match e with
    | A.App (declaration, args) ->
      let extra =
        match F.operation_of declaration with
        | None -> Z.zero
        | Some (p, _) -> arguments_visit_work p declaration.A.domain args in
      Z.succ (Z.add (operation_visit_work declaration) extra)
    | _ -> Z.one

let check_modulus_of e =
  let result, work = check_budget "modulus recognition" (F.modulus_of e)
    (fun fuel -> K.modulus_of_metered fuel e) in
  require (work = modulus_recognition_work e)
    "modulus recognition reset or skipped operation fuel";
  result, work

let rec modulus_visit_work e =
  let visit = modulus_recognition_work e in
  match F.modulus_of e with
  | Some p -> Some p, visit
  | None ->
    match e with
    | A.App (_, args) ->
      let result, work = modulus_args_work args in result, Z.add visit work
    | _ -> None, visit

and modulus_args_work args =
  let rec siblings spent = function
    | [] -> None, Z.succ spent
    | a :: rest ->
      let result, work = modulus_visit_work a in
      let spent = Z.add spent work in
      match result with
      | Some _ -> result, spent
      | None -> siblings spent rest in
  siblings Z.zero args

let check_modulus_args args =
  let result, work = check_budget "modulus argument search" (F.find_modulus_args args)
    (fun fuel -> K.find_modulus_args_metered fuel args) in
  require ((result, work) = modulus_args_work args)
    "modulus search changed recognition/traversal work or first-result order";
  result, work

let check_modulus e =
  let result, work = check_budget "modulus expression search" (F.find_modulus e)
    (fun fuel -> K.find_modulus_metered fuel e) in
  require ((result, work) = modulus_args_work [e])
    "modulus expression search changed recognition/traversal work";
  result, work

let evidence_admission_work cert =
  let header, header_work = check_header cert in
  let discovery_work =
    match header with
    | None -> Z.zero
    | Some _ -> snd (check_modulus_args cert.C.pac_premises) in
  Z.succ (Z.add header_work discovery_work)

let check_shared_fuel p cert e =
  let fuel = zi 1000000 in
  let modulus, discovery_work = check_modulus_args cert.C.pac_premises in
  require (modulus = Some p) "shared-fuel fixture did not discover its modulus";
  let header = prime_header_work cert in
  let admission = Z.add header discovery_work in
  require (K.check_for_prime_metered Z.one p cert e = None)
    "certificate skipped premise-count fuel";
  require (K.check_for_prime_metered header p cert e = None)
    "certificate skipped modulus-discovery fuel";
  require (K.check_for_prime_metered admission p cert e = None)
    "certificate skipped support fuel after discovery";
  let support, support_work = check_support_tree (zi (List.length cert.C.pac_premises))
    (zi (-1)) I.Empty cert.C.pac_support in
  let spent = Z.add admission support_work in
  let rejected_setup () =
    require (K.check_for_prime_metered spent p cert e = Some (false, spent))
      "rejected support/binding reached replay" in
  match support with
  | None -> rejected_setup ()
  | Some sup ->
    match W.bind p Z.zero F.empty_encoding cert.C.pac_premises with
    | None -> rejected_setup ()
    | Some st ->
      let equations, count_work = check_exact_length st.F.equations in
      let counted = Z.add spent count_work in
      let eqs, index_work = check_equation_index I.Empty
        (Z.pred equations) st.F.equations in
      let indexed = Z.add counted index_work in
      let nvars, term_work = check_exact_length st.F.terms in
      let counted_terms = Z.add indexed term_work in
      let lits, clause_work = check_clause_literals e in
      let setup = Z.add counted_terms clause_work in
      require (K.check_for_prime_metered spent p cert e = None)
        "certificate skipped equation-count fuel";
      require (K.check_for_prime_metered (Z.pred counted) p cert e = None)
        "certificate reset equation-count fuel";
      require (K.check_for_prime_metered counted p cert e = None)
        "certificate skipped equation-index fuel";
      require (K.check_for_prime_metered (Z.pred indexed) p cert e = None)
        "certificate reset equation-index fuel";
      require (K.check_for_prime_metered indexed p cert e = None)
        "certificate skipped term-count fuel";
      require (K.check_for_prime_metered (Z.pred counted_terms) p cert e = None)
        "certificate reset term-count fuel";
      require (K.check_for_prime_metered counted_terms p cert e = None)
        "certificate skipped clause-recognition fuel";
      require (K.check_for_prime_metered (Z.pred setup) p cert e = None)
        "certificate reset clause-recognition fuel";
      require (K.check_for_prime_metered setup p cert e = None)
        "certificate skipped replay fuel after clause recognition";
      match M.replay_nodes_metered (Z.sub fuel setup) p nvars
        eqs sup lits P.initial cert.C.pac_nodes with
      | Some (Some state, replay_work) ->
        (match M.finalize_metered (Z.sub fuel (Z.add setup replay_work))
           state cert.C.pac_root cert.C.pac_support with
         | Some (result, final_work) ->
           let total = Z.add setup (Z.add replay_work final_work) in
           require (K.check_for_prime_metered total p cert e = Some (result, total))
             "certificate header/discovery/support/count/index/count/clause/replay/finality work decomposition";
           require (K.check_for_prime_metered (Z.add setup replay_work) p cert e = None)
             "certificate reset finality fuel"
         | None -> failwith "finality exhausted test fuel")
      | Some (None, replay_work) ->
        let total = Z.add setup replay_work in
        require (K.check_for_prime_metered total p cert e = Some (false, total))
          "rejected replay ran finality"
      | None -> failwith "replay exhausted test fuel"

let () =
  List.iter (fun p ->
    let eq, cert = fixture (zi p) in
    require (K.check cert eq && W.check cert eq) "valid witness certificate rejected";
    require (not (K.check { cert with C.pac_root = zi 3 } eq)) "invalid root accepted";
    require (not (K.check { cert with C.pac_root = zi 5 } eq)) "future root accepted";
    require (not (K.check { cert with C.pac_support = [] } eq)) "missing support accepted";
    require (not (K.check { cert with C.pac_support = [Z.zero; Z.zero] } eq))
      "duplicate support accepted";
    require (not (K.check { cert with C.pac_support = [zi 1] } eq)) "invalid support accepted";
    require (not (K.check cert (List.hd cert.C.pac_premises)))
      "unrelated conclusion accepted";
    require (not (K.check { cert with C.pac_nodes = [C.PacInput (zi (-1))] } eq))
      "negative input accepted") [5; 263];
  let eq, cert = fixture (zi 5) in
  let two = { cert with C.pac_premises = cert.C.pac_premises @ [eq] } in
  require (K.check two eq) "additional unused premise changed valid certificate";
  require (not (K.check { two with C.pac_support = [Z.zero; Z.one] } eq))
    "declared but unused support accepted";
  let eq, cert = fixture (zi 65537) in
  let evidence = Some (zi 3, List.init 16 (fun _ -> zi 2)) in
  require (K.check_with_evidence cert eq evidence && W.check_with_evidence cert eq evidence)
    "valid large-prime evidence rejected";
  require (not (K.check cert eq)) "missing large-prime evidence accepted";
  require (not (K.check_with_evidence cert eq (Some (zi 3, List.init 15 (fun _ -> zi 2)))))
    "incomplete prime evidence accepted";
  let composite_eq, composite = fixture (zi 4) in
  require (not (K.check_with_evidence composite composite_eq (Some (zi 1, [zi 3]))))
    "composite modulus accepted";
  List.iter (fun modulus ->
    let p = zi modulus in
    let e, cert = fixture p in
    List.iter (fun (c, conclusion) -> ignore (check_metered p c conclusion))
      [(cert, e);
       ({ cert with C.pac_root = zi (-1) }, e);
       ({ cert with C.pac_root = zi 3 }, e);
       ({ cert with C.pac_root = zi 5 }, e);
       ({ cert with C.pac_support = [] }, e);
       ({ cert with C.pac_support = [Z.zero; Z.zero] }, e);
       ({ cert with C.pac_support = [zi (-1)] }, e);
       ({ cert with C.pac_support = [Z.one] }, e);
       ({ cert with C.pac_nodes = [C.PacInput (zi (-1))] }, e);
       (cert, List.hd cert.C.pac_premises);
       ({ cert with C.pac_premises = [] }, e)];
    check_shared_fuel p cert e;
    let or_decl = decl "or" [A.bool_sort; A.bool_sort] A.bool_sort (Some T.op_or) [] in
    List.iter (fun conclusion ->
      ignore (check_metered p cert conclusion);
      ignore (check_evidence_metered cert conclusion
        (if modulus = 65537 then evidence else None));
      check_shared_fuel p cert conclusion)
      [A.App (or_decl, [e]);
       A.App ({ or_decl with A.domain = [] }, [e]);
       A.App ({ or_decl with A.domain = [A.bool_sort] }, [e]);
       A.App ({ or_decl with A.domain = List.init 12000 (fun _ -> A.bool_sort) }, [e]);
       A.App (or_decl, []);
       A.App ({ or_decl with A.interp = Some (zi 202) }, [e]);
       A.App ({ or_decl with A.domain = [A.bool_sort; F.ff_sort p; A.bool_sort] }, [e]);
       A.App ({ or_decl with A.range = F.ff_sort p }, [e]);
       A.App ({ or_decl with A.int_params = [Z.zero] }, [e]);
       A.Var (Z.zero, A.bool_sort);
       A.Quantifier (A.Forall_k, [A.bool_sort], A.bool_sort, A.Var (Z.zero, A.bool_sort))];
    check_shared_fuel p { cert with C.pac_root = zi 3 } e;
    check_shared_fuel p { cert with C.pac_nodes = [C.PacInput (zi (-1))] } e;
    List.iter (fun support ->
      check_shared_fuel p { cert with C.pac_support = support } e)
      [[zi (-1)]; [Z.zero; Z.zero]; [Z.one]];
    let empty = { cert with C.pac_nodes = [] } in
    let _, discovery_work = check_modulus_args empty.C.pac_premises in
    let header = prime_header_work empty in
    let admission = Z.add header discovery_work in
    let _, support_work = check_support_tree Z.one (zi (-1)) I.Empty empty.C.pac_support in
    let st = Option.get (W.bind p Z.zero F.empty_encoding empty.C.pac_premises) in
    let equations, count_work = check_exact_length st.F.equations in
    let _, index_work = check_equation_index I.Empty
      (Z.pred equations) st.F.equations in
    let _, term_work = check_exact_length st.F.terms in
    let counted = Z.add admission (Z.add support_work count_work) in
    let indexed = Z.add counted index_work in
    let counted_terms = Z.add indexed term_work in
    let _, clause_work = check_clause_literals e in
    let setup = Z.add counted_terms clause_work in
    require (check_metered p empty e = (false, Z.succ setup))
      "empty replay header/discovery/support/count/index/count/clause accounting";
    require (K.check_for_prime_metered Z.one p empty e = None)
      "empty replay skipped header fuel";
    require (K.check_for_prime_metered header p empty e = None)
      "empty replay skipped discovery fuel";
    require (K.check_for_prime_metered admission p empty e = None)
      "empty replay skipped support fuel after discovery";
    require (K.check_for_prime_metered (Z.add admission support_work) p empty e = None)
      "empty replay skipped equation-count fuel after support preparation";
    require (K.check_for_prime_metered counted p empty e = None)
      "empty replay skipped equation-index fuel after counting";
    require (K.check_for_prime_metered indexed p empty e = None)
      "empty replay skipped term-count fuel after indexing";
    require (K.check_for_prime_metered counted_terms p empty e = None)
      "empty replay skipped clause fuel after counting";
    require (K.check_for_prime_metered setup p empty e = None)
      "empty replay skipped replay/finality fuel after clause recognition";
    check_shared_fuel p empty e;
    let two = { cert with C.pac_premises = cert.C.pac_premises @ [e];
                         pac_support = [Z.zero; Z.one] } in
    ignore (check_metered p two e);
    check_shared_fuel p two e) [5; 263; 65537];
  let e, cert = fixture (zi 5) in
  let _, discovery_work = check_modulus_args cert.C.pac_premises in
  require (check_metered (zi 7) cert e =
    (false, Z.add (prime_header_work cert) discovery_work))
    "wrong modulus accounting";
  let oversized_premises = { cert with C.pac_premises = List.init 4097 (fun _ -> e) } in
  require (check_metered (zi 5) oversized_premises e =
    (false, prime_header_work oversized_premises))
    "premise limit accounting";
  let oversized_nodes = { cert with C.pac_nodes = List.init 100001 (fun _ -> C.PacInput Z.zero) } in
  require (check_metered (zi 5) oversized_nodes e =
    (false, prime_header_work oversized_nodes)) "node limit accounting";
  let large_evidence = Some (zi 3, List.init 16 (fun _ -> zi 2)) in
  List.iter (fun (modulus, evidence) ->
    let p = zi modulus in
    let e, cert = fixture p in
    let expected, prime_work = check_metered p cert e in
    let admission = evidence_admission_work cert in
    let result, work = check_evidence_metered cert e evidence in
    require (result && result = expected && work = Z.add admission prime_work)
      "evidence gate did not share header/discovery/certificate fuel";
    require (K.check_with_evidence_metered admission cert e evidence = None)
      "evidence entry reset the inner discovery budget";
    require (K.check_with_evidence_metered Z.one cert e evidence = None)
      "valid evidence skipped certificate fuel";
    List.iter (fun c -> ignore (check_evidence_metered c e evidence))
      [{ cert with C.pac_root = zi (-1) };
       { cert with C.pac_support = [] };
       { cert with C.pac_support = [Z.zero; Z.zero] };
       { cert with C.pac_support = [zi (-1)] };
       { cert with C.pac_support = [Z.one] };
       { cert with C.pac_support = [Z.shift_left Z.one 200] };
       { cert with C.pac_nodes = [] };
       { cert with C.pac_nodes = [C.PacInput (zi (-1))] }])
    [5, None; 263, None; 65537, large_evidence];
  let large_e, large_cert = fixture (zi 65537) in
  let large_admission = evidence_admission_work large_cert in
  List.iter (fun evidence ->
    require (check_evidence_metered large_cert large_e evidence =
      (false, large_admission))
      "invalid or absent evidence reached certificate replay")
    [None; Some (zi 3, List.init 15 (fun _ -> zi 2));
     Some (Z.zero, List.init 16 (fun _ -> zi 2)); Some (zi 3, [zi 65536])];
  List.iter (fun modulus ->
    let e, cert = fixture (zi modulus) in
    let admission = evidence_admission_work cert in
    List.iter (fun evidence ->
      require (check_evidence_metered cert e evidence = (false, admission))
        "invalid/composite modulus passed the evidence gate")
      [None; Some (Z.one, [zi (modulus - 1)])])
    [-1; 0; 1; 4; 9];
  require (fst (check_evidence_metered cert e (Some (Z.zero, []))))
    "irrelevant evidence changed small-prime acceptance";
  let atom = A.App (decl "p" [] A.bool_sort None [], []) in
  let binding_failure = { cert with C.pac_premises = cert.C.pac_premises @ [atom] } in
  require (F.find_modulus_args binding_failure.C.pac_premises = Some (zi 5) &&
    W.bind (zi 5) Z.zero F.empty_encoding binding_failure.C.pac_premises = None)
    "binding-rejection fixture did not reach binding";
  check_shared_fuel (zi 5) binding_failure e;
  let _, support_work = check_support_tree (zi 2) (zi (-1)) I.Empty
    binding_failure.C.pac_support in
  let _, discovery_work = check_modulus_args binding_failure.C.pac_premises in
  let helper_work = Z.add (prime_header_work binding_failure)
    (Z.add discovery_work support_work) in
  require (check_metered (zi 5) binding_failure e = (false, helper_work))
    "binding rejection did not pay discovery/support preparation";
  let admission = evidence_admission_work binding_failure in
  require (check_evidence_metered binding_failure e None =
    (false, Z.add admission helper_work))
    "evidence-checked binding rejection reset setup fuel";
  check_shared_fuel (zi 5) { binding_failure with C.pac_support = [zi (-1)] } e;
  List.iter (fun c ->
    let admission = evidence_admission_work c in
    require (check_evidence_metered c e None = (false, admission))
      "evidence header/discovery rejection accounting")
    [{ cert with C.pac_premises = [] };
     { cert with C.pac_premises = [atom] };
     { cert with C.pac_premises = List.init 4097 (fun _ -> e) };
     { cert with C.pac_nodes = List.init 100001 (fun _ -> C.PacInput Z.zero) }];
  List.iter (fun (limit, length) ->
    ignore (check_count (zi limit) (List.init length (fun _ -> ()))))
    [(-1, 0); (-1, 5); (0, 0); (0, 5); (1, 0); (1, 1); (1, 2);
     (3, 3); (3, 12000); (4096, 4096); (4096, 4097);
     (100000, 100000); (100000, 100001)];
  ignore (check_count (Z.shift_left Z.one 200) [()]);
  List.iter (fun xs -> ignore (check_exact_length xs))
    [[]; [Z.zero]; List.init 12000 zi];
  let long_nodes = List.init 200000 (fun _ -> C.PacInput Z.zero) in
  require (K.count_at_most_metered (zi 4) (zi 4) long_nodes = None)
    "fuel-limited exact counting completed a prefix rejection";
  let long_premises = List.init 200000 (fun _ -> e) in
  let no_premises = { cert with C.pac_premises = []; pac_nodes = long_nodes } in
  require (K.check_for_prime_metered (zi 2) (zi 5) no_premises e =
    Some (false, zi 2)) "empty prime header inspected the node tail";
  require (K.check_for_prime_metered Z.one (zi 5) no_premises e = None)
    "empty prime header skipped its count guard";
  let over_premises =
    { cert with C.pac_premises = long_premises; pac_nodes = long_nodes } in
  require (K.check_for_prime_metered (zi 4098) (zi 5) over_premises e =
    Some (false, zi 4098)) "prime premise cap scanned ignored tails";
  require (K.check_for_prime_metered (zi 4097) (zi 5) over_premises e = None)
    "prime premise cap skipped the final rejection guard";
  let over_nodes = { cert with C.pac_nodes = long_nodes } in
  require (K.check_for_prime_metered (zi 100004) (zi 5) over_nodes e =
    Some (false, zi 100004)) "prime node cap reset premise-count fuel";
  require (K.check_for_prime_metered (zi 100003) (zi 5) over_nodes e = None)
    "prime node cap skipped the final rejection guard";
  require (K.check_for_prime_metered (zi 4) (zi 5) over_nodes e = None)
    "prime node scan ignored its tiny remaining budget";
  require (K.check_for_prime_metered (zi 100004) (zi 5)
    { cert with C.pac_nodes = List.init 100000 (fun _ -> C.PacInput Z.zero) } e = None)
    "accepted node limit skipped discovery fuel";
  List.iter (fun c -> ignore (check_header c))
    [{ cert with C.pac_premises = []; pac_nodes = long_nodes };
     { cert with C.pac_premises = List.init 4096 (fun _ -> e); pac_nodes = [] };
     { cert with C.pac_premises = List.init 4097 (fun _ -> e); pac_nodes = long_nodes };
     { cert with C.pac_nodes = List.init 100000 (fun _ -> C.PacInput Z.zero) };
     { cert with C.pac_nodes = long_nodes }];
  require (K.admit_header_metered Z.one
    { cert with C.pac_premises = []; pac_nodes = long_nodes } = Some (None, Z.one))
    "empty premises inspected the node tail";
  require (K.admit_header_metered (zi 4097)
    { cert with C.pac_premises = List.init 4097 (fun _ -> e); pac_nodes = long_nodes }
    = Some (None, zi 4097)) "oversized premises inspected the node tail";
  require (K.count_at_most_metered (zi 4) (zi 3) long_nodes = Some (None, zi 4))
    "capped count did not stop at the prefix";
  require (K.admit_header_metered (zi 2) cert = None)
    "header reset node-count fuel";
  let long_support = List.init 200000 (fun _ -> Z.zero) in
  let capped = { cert with C.pac_support = long_support } in
  List.iter (fun c -> ignore (check_header c))
    [{ cert with C.pac_support = [] };
     cert;
     { cert with C.pac_support = [Z.zero; Z.one] };
     capped;
     { cert with C.pac_premises = List.init 4096 (fun _ -> e);
                 pac_nodes = []; pac_support = List.init 4096 zi };
     { cert with C.pac_premises = List.init 4096 (fun _ -> e);
                 pac_nodes = []; pac_support = List.init 4097 zi };
     { capped with C.pac_premises = []; pac_nodes = long_nodes };
     { capped with C.pac_nodes = long_nodes }];
  require (K.admit_header_metered (zi 10) capped = Some (None, zi 10))
    "support admission scanned beyond the premise cap";
  require (check_evidence_metered capped e None = (false, zi 11))
    "oversized support reached certificate setup";
  require (K.admit_header_metered Z.one
    { capped with C.pac_premises = []; pac_nodes = long_nodes } = Some (None, Z.one))
    "empty premises inspected support";
  require (K.admit_header_metered (zi 100003)
    { capped with C.pac_nodes = long_nodes } = Some (None, zi 100003))
    "oversized nodes inspected support";
  require (K.admit_header_metered (zi 8) cert = None)
    "header reset support-count fuel";
  List.iter (fun (n, previous, support) ->
    ignore (check_support_tree (zi n) (zi previous) I.Empty (List.map zi support)))
    [(0, -1, []); (-1, -1, []); (0, -1, [0]); (-1, -1, [0]);
     (5, -1, [0; 2; 4]); (5, 0, [1; 2]); (5, 2, [2]);
     (5, -1, [-1]); (5, -1, [0; 0]); (5, -1, [5]); (5, -1, [2; 1]);
     (5, 10, []); (5, 10, [0]); (5, -2, [0; 1])];
  let prepopulated = I.index_put (I.index_put I.Empty (zi 99) false) Z.zero false in
  let prepared, _ = check_support_tree (zi 5) (zi (-1)) prepopulated [Z.zero; zi 2] in
  let prepared = Option.get prepared in
  require (I.index_get prepared (zi 99) = Some false &&
           I.index_get prepared Z.zero = Some true &&
           I.index_get prepared (zi 2) = Some true)
    "support preparation lost existing entries or updates";
  ignore (check_support_tree Z.zero (zi 99) prepopulated []);
  let huge = Z.shift_left Z.one 200 in
  ignore (check_support_tree (Z.succ huge) (zi (-1)) I.Empty [huge]);
  List.iter (fun key ->
    require (check_support_tree (zi 5) (zi (-1)) prepopulated
      (key :: long_support) = (None, Z.one))
      "invalid support index inspected the rejected tail") [Z.neg huge; huge];
  require (K.support_tree_metered (zi 3) (zi 5) (zi (-1)) I.Empty [zi 2] = None)
    "support insertion skipped terminal or reset fuel";
  let ordered_support = List.init 12000 zi in
  ignore (check_support_tree (zi 12000) (zi (-1)) prepopulated ordered_support);
  require (check_support_tree (zi 12000) (zi (-1)) prepopulated
    (Z.zero :: Z.one :: Z.one :: ordered_support) = (None, zi 6))
    "support rejection did not stop after the charged prefix";
  let equation n = ([[], zi n], F.Definition) in
  let equations = List.map equation [11; 12; 13] in
  let indexed = I.index_put (I.index_put I.Empty (zi 99) (equation 44))
    Z.zero (equation 45) in
  List.iter (fun k ->
    List.iter (fun es -> ignore (check_equation_index indexed k es))
      [[]; equations])
    [zi (-1); Z.zero; Z.one; zi 2; zi 5; Z.neg huge; huge];
  let prepared, _ = check_equation_index indexed (zi 2) equations in
  require (I.index_get prepared (zi 99) = Some (equation 44) &&
           I.index_get prepared (zi 2) = Some (equation 11) &&
           I.index_get prepared Z.one = Some (equation 12) &&
           I.index_get prepared Z.zero = Some (equation 13))
    "equation indexing lost existing entries, updates or descending order";
  let long_equations = List.init 200000 (fun _ -> equation 11) in
  require (check_equation_index indexed (Z.neg huge) long_equations = (indexed, Z.one))
    "negative equation index inspected the ignored tail";
  let prefix = I.index_put indexed Z.zero (equation 11) in
  require (check_equation_index indexed Z.zero long_equations = (prefix, zi 3))
    "equation indexing continued after the index became negative";
  require (K.index_equations_metered (zi 2) indexed Z.zero long_equations = None)
    "equation indexing skipped terminal guard or reset insertion fuel";
  let many_equations = List.init 12000 equation in
  ignore (check_equation_index indexed (zi 11999) many_equations);
  let field p = A.SortApp (A.FiniteFieldSymbol (zi p), []) in
  let numeral p = A.App
    (decl "ff" [] (field p) (Some F.op_ff_num) [zi p; Z.zero], []) in
  let atom = A.Var (Z.zero, A.bool_sort) in
  let wrap args = A.App
    (decl "wrap" (List.map A.get_sort args) A.bool_sort None [], args) in
  let five = numeral 5 in
  let seven = numeral 7 in
  let quantifier = A.Quantifier
    (A.Forall_k, [A.bool_sort], A.bool_sort, wrap [five]) in
  let unrecognized_field = A.App (decl "u" [] (field 5) None [], []) in
  List.iter (fun expression -> ignore (check_modulus expression))
    [atom; wrap []; five; seven; numeral 4; numeral 1;
     unrecognized_field; quantifier; wrap [atom; wrap [five]; seven];
     wrap [wrap []; quantifier; seven]; wrap [wrap [atom]; wrap [atom]]];
  List.iter (fun args -> ignore (check_modulus_args args))
    [[]; [atom]; [five; seven]; [seven; five]; [wrap []; atom; wrap [five]];
     [quantifier; seven]; [wrap [atom]; atom]];
  require (check_modulus quantifier = (None, zi 2))
    "modulus search descended into a non-App body";
  require (fst (check_modulus unrecognized_field) = None)
    "modulus search treated a field sort alone as evidence";
  let hidden = A.App (decl "h" [field 5] (field 7) None [], [five]) in
  let operation = A.App
    (decl "ff.add" [field 7; field 7] (field 7) (Some (zi 301)) [zi 7],
     [hidden; seven]) in
  require (F.modulus_of operation = Some (zi 7) &&
           check_modulus operation = (Some (zi 7), zi 8))
    "modulus search did not prefer a recognized parent to its descendants";
  let long_tail = List.init 200000 (fun _ -> seven) in
  require (check_modulus_args (five :: long_tail) = (Some (zi 5), Z.one))
    "modulus search inspected siblings after its first result";
  ignore (check_modulus_args (List.init 12000 (fun _ -> atom)));
  let nested = List.fold_left (fun body _ -> wrap [body]) atom (List.init 12000 Fun.id) in
  ignore (check_modulus nested);
  ignore (check_modulus_args [nested; five; seven]);
  let very_deep = List.fold_left (fun body _ -> wrap [body]) atom
    (List.init 120000 Fun.id) in
  require (K.find_modulus_metered (zi 3) very_deep = None)
    "modulus search traversed beyond the exhausted prefix";
  require (K.find_modulus_args_metered (zi 3) [very_deep; five] = None)
    "modulus search reset fuel before siblings";
  List.iter (fun modulus ->
    let p = zi modulus in
    let fp = F.ff_sort p in
    let domains = [[]; [fp]; [fp; fp]; [fp; fp; fp]; [A.bool_sort];
      [A.bool_sort; fp]; [fp; A.bool_sort]; [fp; A.bool_sort; fp];
      [F.ff_sort (Z.succ p); fp];
      [A.SortApp (A.FiniteFieldSymbol p, [A.bool_sort]); fp];
      [A.ArraySort ([A.bool_sort], A.bool_sort); fp]] in
    List.iter (fun domain -> ignore (check_domain_arity p domain)) domains;
    List.iter (fun tag ->
      List.iter (fun domain ->
        let declaration = decl "ff.op" domain fp tag [p] in
        ignore (check_operation declaration);
        ignore (check_operation { declaration with A.range = A.bool_sort }))
        domains)
      [None; Some (zi (-1)); Some (zi 300); Some (zi 301); Some (zi 302);
       Some (zi 303); Some (zi 304); Some (zi 305)])
    [-1; 0; 1; 2; 4; 5; 263; 65537];
  let fp = field 5 in
  let add = decl "ff.add" [fp; fp] fp (Some (zi 301)) [zi 5] in
  List.iter (fun parameters ->
    ignore (check_operation { add with A.int_params = parameters }))
    [[]; [zi 5; zi 5]; [zi 5; Z.zero; zi 1]];
  let huge = Z.shift_left Z.one 200 in
  ignore (check_operation (decl "ff.add" [F.ff_sort huge; F.ff_sort huge]
    (F.ff_sort huge) (Some (zi 301)) [huge]));
  ignore (check_operation { add with A.interp = Some huge });
  let long_domain = List.init 200000 (fun _ -> fp) in
  ignore (check_domain_arity (zi 5) long_domain);
  require (check_domain_arity (zi 5) (A.bool_sort :: long_domain) = (None, Z.one))
    "bad domain sort inspected the ignored tail";
  require (K.operation_of_metered (zi 2)
    { add with A.domain = A.bool_sort :: long_domain } = Some (None, zi 2))
    "operation declaration scanned past a bad first domain sort";
  require (K.operation_of_metered (zi 3)
    { add with A.domain = fp :: A.bool_sort :: long_domain } = Some (None, zi 3))
    "operation declaration scanned past a bad domain prefix";
  require (K.operation_of_metered Z.one
    { add with A.domain = long_domain; interp = None } = Some (None, Z.one))
    "unsupported declaration inspected its domain";
  require (K.operation_of_metered Z.one
    { add with A.domain = long_domain; int_params = [Z.one] } = Some (None, Z.one))
    "invalid modulus inspected its domain";
  ignore (check_operation { add with A.domain = long_domain; interp = Some (zi 303) });
  List.iter (fun tag ->
    ignore (check_operation
      { add with A.domain = List.init 12000 (fun _ -> fp); interp = Some (zi tag) }))
    [301; 302; 304];
  require (K.operation_of_metered Z.one add = None)
    "operation declaration skipped its domain budget";
  require (K.operation_of_metered (zi 3) add = None)
    "operation declaration skipped its terminal domain guard";
  List.iter (fun modulus ->
    let p = zi modulus in
    let fp = F.ff_sort p in
    let good = A.Var (Z.zero, fp) in
    let bad = A.Var (Z.zero, A.bool_sort) in
    let domains = [[]; [fp]; [fp; fp]; [fp; fp; fp]; [A.bool_sort; fp]] in
    let arguments = [[]; [good]; [good; good]; [good; good; good];
      [bad]; [bad; good]; [good; bad]; [good; bad; good]; [quantifier]] in
    List.iter (fun domain ->
      List.iter (fun args ->
        ignore (check_arguments p domain args);
        List.iter (fun tag ->
          let declaration = decl "ff.op" domain fp (Some (zi tag)) [p] in
          ignore (check_operation_at declaration args))
          [300; 301; 302; 303; 304; 305])
        arguments)
      domains)
    [-1; 0; 1; 2; 4; 5; 263];
  let good = A.Var (Z.zero, fp) in
  let long_args = List.init 200000 (fun _ -> good) in
  ignore (check_arguments (zi 5) long_domain long_args);
  require (check_arguments (zi 5) [] long_args = (false, Z.one))
    "empty domain inspected extra arguments";
  require (check_arguments (zi 5) long_domain [] = (false, Z.one))
    "empty arguments inspected extra domain entries";
  require (check_arguments (zi 5) [fp] (good :: long_args) = (false, zi 2))
    "arity mismatch inspected the ignored argument tail";
  require (check_arguments (zi 5) long_domain [good] = (false, zi 2))
    "arity mismatch inspected the ignored domain tail";
  require (check_arguments (zi 5) long_domain (quantifier :: long_args) = (false, Z.one))
    "bad first argument inspected the ignored tail";
  let nested_field = A.App
    (decl "field.h" [A.bool_sort] fp None [], [very_deep]) in
  require (check_arguments (zi 5) [fp] [nested_field] = (true, zi 2))
    "argument matching traversed a nested body instead of its stored sort";
  let lambda = A.Quantifier
    (A.Lambda_k, [A.bool_sort], A.ArraySort ([A.bool_sort], A.bool_sort), very_deep) in
  require (check_arguments (zi 5) [fp] [lambda] = (false, Z.one))
    "argument matching ignored a lambda's stored array sort";
  ignore (check_operation_at add [good; good]);
  ignore (check_operation_at add long_args);
  ignore (check_operation_at add [nested_field; nested_field]);
  ignore (check_operation_at { add with A.interp = Some (zi 303); domain = [fp] } [good]);
  ignore (check_operation_at
    { add with A.domain = List.init 12000 (fun _ -> fp) }
    (List.init 12000 (fun _ -> good)));
  require (K.operation_at_metered Z.one { add with A.interp = None } long_args =
    Some (None, Z.one)) "rejected declaration inspected arguments";
  require (K.arguments_match_metered Z.one (zi 5) [fp] [good] = None)
    "argument matching skipped the terminal guard";
  List.iter (fun expression ->
    ignore (check_modulus_of expression);
    ignore (check_modulus expression))
    [five; numeral 1; numeral 4; atom; quantifier; lambda; unrecognized_field;
     operation; A.App (add, [good; good]); A.App (add, []);
     A.App (add, [good; atom]); A.App (add, long_args);
     A.App ({ add with A.interp = Some (zi 303); domain = [fp] }, [good]);
     A.App ({ add with A.domain = List.init 12000 (fun _ -> fp) },
       List.init 12000 (fun _ -> good))];
  let numeral_decl = decl "ff" [] fp (Some F.op_ff_num) [zi 5; Z.zero] in
  List.iter (fun declaration -> ignore (check_modulus_of (A.App (declaration, []))))
    [{ numeral_decl with A.int_params = [] };
     { numeral_decl with A.int_params = [zi 5] };
     { numeral_decl with A.int_params = [zi 5; zi (-1)] };
     { numeral_decl with A.int_params = [zi 5; zi 5] };
     { numeral_decl with A.int_params = [zi 5; Z.zero; Z.one] };
     { numeral_decl with A.range = A.bool_sort };
     { numeral_decl with A.domain = [fp] }];
  require (check_modulus_of five = (Some (zi 5), Z.one))
    "valid numeral reached operation recognition";
  let bad_domain = A.App ({ add with A.domain = A.bool_sort :: long_domain }, long_args) in
  require (K.modulus_of_metered (zi 3) bad_domain = Some (None, zi 3))
    "modulus recognition scanned beyond a rejected declaration prefix";
  require (K.modulus_of_metered (zi 2) bad_domain = None)
    "modulus recognition reset its declaration budget";
  require (K.modulus_of_metered (zi 6) (A.App (add, atom :: long_args)) =
    Some (None, zi 6)) "modulus recognition scanned beyond a bad argument";
  require (K.modulus_of_metered (zi 5) (A.App (add, atom :: long_args)) = None)
    "modulus recognition reset its argument budget";
  let fallback = A.App (add, [five; seven]) in
  ignore (check_modulus fallback);
  ignore (check_modulus_args [A.App ({ add with A.domain = [A.bool_sort; fp] },
    [five; seven]); five]);
  require (K.find_modulus_args_metered (zi 3) [bad_domain; five] = None)
    "modulus search reset fuel after declaration rejection";
  let missing = { cert with C.pac_premises = [atom] } in
  let _, missing_work = check_modulus_args missing.C.pac_premises in
  require (check_metered (zi 5) missing e =
    (false, Z.add (prime_header_work missing) missing_work))
    "missing modulus skipped discovery accounting";
  ignore (check_evidence_metered missing e None);
  let deep = { cert with C.pac_premises = [very_deep] } in
  let _, header_work = check_header deep in
  require (K.check_for_prime_metered (Z.add (prime_header_work deep) (zi 3))
    (zi 5) deep e = None)
    "already-prime certificate traversed past its discovery prefix";
  require (K.check_with_evidence_metered (Z.add header_work (zi 4)) deep e None = None)
    "evidence certificate reset discovery fuel after header admission";
  let or_decl = decl "or" [A.bool_sort; A.bool_sort] A.bool_sort (Some T.op_or) [] in
  let bool_domains =
    [[]; [A.bool_sort]; [A.bool_sort; A.bool_sort]; [fp];
     [A.bool_sort; fp; A.bool_sort]; List.init 12000 (fun _ -> A.bool_sort)] in
  List.iter (fun domain ->
    ignore (check_boolean_sorts domain);
    List.iter (fun declaration ->
      ignore (check_canonical_or declaration);
      List.iter (fun args -> ignore (check_clause_literals (A.App (declaration, args))))
        [[]; [atom]; [five; lambda]; [very_deep]])
      [{ or_decl with A.domain = domain };
       { or_decl with A.domain = domain; decl_name = "OR" };
       { or_decl with A.domain = domain; interp = None };
       { or_decl with A.domain = domain; interp = Some T.op_and };
       { or_decl with A.domain = domain; interp = Some (zi 202) };
       { or_decl with A.domain = domain; range = fp };
       { or_decl with A.domain = domain; int_params = [Z.zero] }])
    bool_domains;
  List.iter (fun expression -> ignore (check_clause_literals expression))
    [atom; quantifier; lambda; very_deep];
  let bool_tail = List.init 200000 (fun _ -> A.bool_sort) in
  require (K.boolean_sorts_metered Z.one (fp :: bool_tail) = Some (false, Z.one))
    "Boolean domain inspected a rejected tail";
  require (K.boolean_sorts_metered (zi 3) bool_tail = None)
    "Boolean domain ignored its tiny remaining budget";
  let bad_domain = { or_decl with A.domain = fp :: bool_tail } in
  require (K.canonical_or_metered (zi 2) bad_domain = Some (false, zi 2))
    "canonical or inspected a rejected domain tail";
  require (K.canonical_or_metered Z.one bad_domain = None)
    "canonical or reset its domain budget";
  require (K.canonical_or_metered Z.one
    { or_decl with A.decl_name = "user.or"; domain = bool_tail } =
    Some (false, Z.one)) "wrong Boolean name inspected the domain";
  require (K.canonical_or_metered Z.one
    { or_decl with A.interp = Some (zi 202); domain = bool_tail } =
    Some (false, Z.one)) "non-Boolean tag inspected the domain";
  require (K.canonical_or_metered (zi 3)
    { or_decl with A.domain = bool_tail; range = fp } = None)
    "canonical or skipped domain work before range rejection";
  ignore (check_canonical_or
    { or_decl with A.int_params = List.init 200000 (fun _ -> Z.zero) });
  let literals = List.init 200000 (fun _ -> very_deep) in
  (match K.clause_literals_metered (zi 4) (A.App (or_decl, literals)) with
   | Some (result, work) ->
     require (result == literals && work = zi 4)
       "clause extraction copied or inspected arguments"
   | None -> failwith "fixed declaration exhausted on ignored arguments");
  require (K.clause_literals_metered (zi 3) (A.App (or_decl, literals)) = None)
    "clause extraction reset its recognizer budget";
  require (check_clause_literals (A.App ({ or_decl with A.domain = [] }, [five])) =
    ([five], zi 2)) "clause extraction added an arity/domain argument check";
  let clause_e, clause_cert = fixture (zi 5) in
  let _, discovery_work = check_modulus_args clause_cert.C.pac_premises in
  let _, support_work = check_support_tree Z.one (zi (-1)) I.Empty clause_cert.C.pac_support in
  let st = Option.get (W.bind (zi 5) Z.zero F.empty_encoding clause_cert.C.pac_premises) in
  let equations, count_work = check_exact_length st.F.equations in
  let _, index_work = check_equation_index I.Empty (Z.pred equations) st.F.equations in
  let _, term_work = check_exact_length st.F.terms in
  let before_clause = List.fold_left Z.add (prime_header_work clause_cert)
    [discovery_work; support_work; count_work; index_work; term_work] in
  let long_clause = A.App ({ or_decl with A.domain = bool_tail }, [clause_e]) in
  require (K.check_for_prime_metered (Z.add before_clause (zi 3))
    (zi 5) clause_cert long_clause = None)
    "certificate ignored its tiny clause-domain budget";
  require (K.check_for_prime_metered (Z.add before_clause (zi 3)) (zi 5) clause_cert
    (A.App ({ or_decl with A.domain = bool_tail; range = fp }, [clause_e])) = None)
    "certificate skipped earlier domain work before range rejection";
  List.iter (fun (conclusion, clause_work) ->
    require (K.check_for_prime_metered (Z.add before_clause clause_work)
      (zi 5) clause_cert conclusion = None)
      "certificate reset fuel after clause extraction")
    [A.App ({ or_decl with A.domain = fp :: bool_tail }, [clause_e]), zi 2;
     A.App ({ or_decl with A.domain = bool_tail; interp = None }, [clause_e]), Z.one;
     A.App (or_decl, literals), zi 4];
  check_shared_fuel (zi 5) { clause_cert with C.pac_support = [zi (-1)] } long_clause;
  check_shared_fuel (zi 5)
    { clause_cert with C.pac_premises = clause_cert.C.pac_premises @ [atom] } long_clause;
  let allocation_cap = Z.to_int F.max_variables in
  let allocation_state terms =
    { F.terms = terms; equations = [([([], zi 7)], F.Definition)];
      count = Z.shift_left Z.one 200 } in
  List.iter (fun length ->
    ignore (check_allocation
      (allocation_state (List.init length (fun k -> if k mod 2 = 0 then atom else five)))
      atom))
    [0; 1; 7; allocation_cap - 2; allocation_cap - 1; allocation_cap; allocation_cap + 1];
  ignore (check_allocation (allocation_state [very_deep; lambda; very_deep]) quantifier);
  let oversized = allocation_state (List.init 200000 (fun _ -> very_deep)) in
  let rejected_work = Z.succ F.max_variables in
  require (K.allocate_metered rejected_work oversized very_deep =
    Some (None, rejected_work)) "encoding allocation scanned an oversized ignored tail";
  require (K.allocate_metered (Z.pred rejected_work) oversized very_deep = None)
    "encoding allocation skipped its capped rejection guard";
  require (K.allocate_metered (zi 3) oversized very_deep = None)
    "encoding allocation ignored its tiny count budget";
  require (K.allocate_metered Z.zero oversized very_deep = None &&
    K.allocate_metered (zi (-1)) oversized very_deep = None)
    "encoding allocation inspected oversized terms with nonpositive fuel";
  let sort_symbols =
    [A.BoolSymbol; A.IntSymbol; A.RealSymbol; A.CharSymbol; A.BvSymbol (zi (-1));
     A.BvSymbol Z.zero; A.BvSymbol (zi 32); A.SeqSymbol; A.ReSymbol;
     A.FiniteFieldSymbol (zi 4); A.FiniteFieldSymbol (zi 5); A.FiniteSetSymbol;
     A.FloatSymbol (zi 8, zi 24); A.FloatSymbol (zi 8, zi 53);
     A.RoundingModeSymbol; A.DatatypeSymbol Z.zero; A.DatatypeSymbol Z.one;
     A.ExtensionSymbol (Z.zero, zi (-1)); A.ExtensionSymbol (Z.one, zi (-1))] in
  let sorts = List.map (fun symbol -> A.SortApp (symbol, [])) sort_symbols @
    [A.BaseSort ""; A.BaseSort "u"; A.BaseSort "v";
     A.ArraySort ([], A.bool_sort); A.ArraySort ([A.bool_sort], fp);
     A.SortApp (A.BoolSymbol, [fp]); A.SortApp (A.SeqSymbol, [A.bool_sort])] in
  List.iter (fun left ->
    List.iter (fun right -> ignore (check_sort_pair left right)) sorts)
    sorts;
  List.iter (fun (left, right) -> ignore (check_sort_lists left right))
    [[], []; [], sorts; sorts, []; sorts, sorts;
     [A.bool_sort; fp], [fp; A.bool_sort];
     [A.bool_sort; fp], [A.bool_sort; A.bool_sort];
     List.init 12000 (fun _ -> A.bool_sort), List.init 12000 (fun _ -> A.bool_sort)];
  let deep_left = ref A.bool_sort and deep_right = ref A.bool_sort in
  let bad_left = ref (A.BaseSort "left") and bad_right = ref (A.BaseSort "right") in
  let sort_depth = 120000 in
  for _ = 1 to sort_depth do
    deep_left := A.ArraySort ([!deep_left], A.bool_sort);
    deep_right := A.ArraySort ([!deep_right], A.bool_sort);
    bad_left := A.ArraySort ([!bad_left], A.bool_sort);
    bad_right := A.ArraySort ([!bad_right], A.bool_sort)
  done;
  require (K.sort_eq_metered (zi 3) !deep_left !deep_right = None &&
    K.sort_eq_metered Z.zero !deep_left !deep_right = None &&
    K.sort_eq_metered (zi (-1)) !deep_left !deep_right = None)
    "sort comparison inspected deep sorts beyond its prefix budget";
  let deep_work = zi (5 * sort_depth + 3) in
  require (K.sort_eq_metered deep_work !deep_left !deep_right = Some (true, deep_work))
    "stack-safe deep comparison disagreed with its closed-form work";
  require (K.sort_eq_metered (Z.pred deep_work) !deep_left !deep_right = None)
    "deep comparison reset pending-list fuel";
  let mismatch_work = zi (sort_depth + 1) in
  require (K.sort_eq_metered mismatch_work !bad_left !bad_right =
    Some (false, mismatch_work)) "deep mismatch inspected deferred ranges";
  require (K.sort_eq_metered (Z.pred mismatch_work) !bad_left !bad_right = None)
    "deep mismatch skipped a reached comparison";
  require (K.sort_eq_metered (zi 2)
    (A.ArraySort ([A.bool_sort], !deep_left))
    (A.ArraySort ([fp], !deep_right)) = Some (false, zi 2))
    "domain mismatch inspected ignored deep ranges";
  require (K.sort_eq_metered (zi 2)
    (A.ArraySort ([], !deep_left)) (A.ArraySort ([], !deep_right)) = None)
    "array comparison reset fuel before its range";
  require (K.sort_eq_metered Z.one
    (A.SortApp (A.BoolSymbol, bool_tail))
    (A.SortApp (A.IntSymbol, bool_tail)) = Some (false, Z.one))
    "sort-symbol mismatch inspected ignored argument tails";
  require (K.sort_list_eq_metered Z.one [] bool_tail = Some (false, Z.one) &&
    K.sort_list_eq_metered (zi 3) bool_tail bool_tail = None)
    "sort-list comparison ignored its shape or tiny remaining budget";
  List.iter (fun (left, right) -> ignore (check_int_lists left right))
    [[], []; [], [Z.zero]; [Z.zero], []; [Z.zero], [Z.zero]; [Z.zero], [Z.one];
     [Z.zero; Z.one], [Z.zero]; [Z.zero], [Z.zero; Z.one];
     [Z.zero; zi (-1)], [Z.zero; Z.one];
     [Z.shift_left Z.one 200], [Z.shift_left Z.one 201];
     List.init 12000 zi, List.init 12000 zi];
  let declaration = decl "f" [] A.bool_sort None [] in
  let declarations =
    [declaration; { declaration with A.decl_name = "g" };
     { declaration with A.domain = [A.bool_sort] };
     { declaration with A.domain = [A.bool_sort; fp] };
     { declaration with A.range = fp };
     { declaration with A.range = A.ArraySort ([], A.bool_sort) };
     { declaration with A.interp = Some Z.zero };
     { declaration with A.interp = Some (zi (-1)) };
     { declaration with A.int_params = [Z.zero] };
     { declaration with A.int_params = [Z.zero; Z.one] }] in
  List.iter (fun left ->
    List.iter (fun right -> ignore (check_declarations left right)) declarations)
    declarations;
  List.iter (fun (fuel, field) ->
    require (K.decl_eq_metered (zi fuel) declaration declaration = None)
      ("declaration comparison reset fuel before " ^ field))
    [1, "domain"; 2, "range"; 5, "interp"; 6, "parameters"];
  require (K.decl_eq_metered (zi 7) declaration declaration = Some (true, zi 7))
    "declaration field work did not compose exactly";
  let parameter_tail = List.init 200000 (fun _ -> Z.zero) in
  require (K.int_list_eq_metered Z.one (Z.one :: parameter_tail)
    (zi 2 :: parameter_tail) = Some (false, Z.one))
    "integer mismatch inspected an ignored parameter tail";
  require (K.int_list_eq_metered (zi 3) parameter_tail parameter_tail = None)
    "integer-list comparison ignored its tiny budget";
  let wide = { declaration with A.domain = bool_tail; range = !deep_left;
                                int_params = parameter_tail } in
  require (K.decl_eq_metered Z.one { wide with A.decl_name = "other" } wide =
    Some (false, Z.one)) "name mismatch inspected ignored metadata";
  require (K.decl_eq_metered (zi 2) { wide with A.domain = [] } wide =
    Some (false, zi 2)) "domain mismatch inspected ignored range/parameters";
  require (K.decl_eq_metered (zi 3) wide wide = None)
    "declaration domain ignored its tiny remaining budget";
  let ranged = { declaration with A.range = !deep_left; int_params = parameter_tail } in
  require (K.decl_eq_metered (zi 5) ranged
    { ranged with A.range = !deep_right; interp = Some Z.zero } = None)
    "declaration skipped earlier deep range work before interp rejection";
  require (K.decl_eq_metered (zi 3)
    { declaration with A.int_params = parameter_tail }
    { declaration with A.range = fp; int_params = parameter_tail } =
    Some (false, zi 3)) "range mismatch inspected ignored metadata";
  let parameterized = { declaration with A.int_params = parameter_tail } in
  require (K.decl_eq_metered (zi 6) parameterized
    { parameterized with A.interp = Some Z.zero } = Some (false, zi 6))
    "interp mismatch inspected ignored parameters";
  require (K.decl_eq_metered (zi 7)
    { declaration with A.int_params = Z.one :: parameter_tail }
    { declaration with A.int_params = zi 2 :: parameter_tail } =
    Some (false, zi 7)) "declaration parameter rejection reset earlier fuel";
  require (K.decl_eq_metered (zi 9) parameterized parameterized = None)
    "declaration parameter scan ignored shared remaining fuel";
  let parameter_work = zi 200007 in
  require (K.decl_eq_metered parameter_work parameterized parameterized =
    Some (true, parameter_work)) "long parameter equality work did not compose";
  require (K.decl_eq_metered (Z.pred parameter_work) parameterized parameterized = None)
    "long parameter equality skipped its terminal guard";
  print_endline "compact finite-field certificate tests passed"
