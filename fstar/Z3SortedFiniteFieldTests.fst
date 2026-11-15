(* Focused regressions for the sort-indexed PAC replay checker.  These use
   the producer's unit-ideal certificate at large and composite moduli, plus
   representative mutations of the existing replay gates. *)
module Z3SortedFiniteFieldTests

open Z3AstTheory
open Z3OperatorTags
open Z3ClauseSyntax
module FF = Z3SortedFiniteField
module Legacy = Z3FiniteFieldPac
module LegacyFF = Z3FiniteFieldLemma
module V = Z3DatatypeValue
module IX = Z3ProofIndex
module A = Z3ArraySyntax
module C = Z3CanonicalOps
module D = Z3ExprScope
module FE = FStar.FunctionalExtensionality
module L = FStar.List.Tot
module M = FStar.Math.Lemmas

let num (p n:int) : expr =
  App { decl_name = "ff"; domain = []; range = FF.ff_sort p;
        interp = Some FF.op_ff_num; int_params = [p; n] } []

let const (p:int) (name:string) : expr =
  App { decl_name = name; domain = []; range = FF.ff_sort p;
        interp = None; int_params = [] } []

let field (p:int) (name:string) (tag:decl_kind) (args:list expr) : expr =
  App { decl_name = name; domain = FF.repeat_sort p (L.length args);
        range = FF.ff_sort p; interp = Some tag; int_params = [p] } args

let add (p:int) (args:list expr) : expr = field p "ff.add" FF.op_ff_add args
let mul (p:int) (args:list expr) : expr = field p "ff.mul" FF.op_ff_mul args
let eq (a b:expr) : expr = mk_eq_expr a b

let disj (args:list expr) : expr =
  App { decl_name = "or"; domain = L.map (fun _ -> bool_sort) args;
        range = bool_sort; interp = Some op_or; int_params = [] } args

let premise0 (p:int) : expr =
  eq (mul p [const p "x"; const p "y"]) (num p 1)

let premise1 (p:int) : expr =
  eq (mul p [const p "x"; add p [num p 1; const p "y"]])
     (add p [num p 2; const p "x"])

let clause (p:int) : expr =
  disj [mk_not_expr (premise0 p); mk_not_expr (premise1 p)]

let later_nodes (m:expr) : list FF.pac_node = [
  FF.PacInput 5; FF.PacInput 3; FF.PacMul 2 m [];
  FF.PacAdd 1 3; FF.PacAdd 0 4; FF.PacInput 2; FF.PacMul 6 m [1];
  FF.PacAdd 5 7; FF.PacInput 1; FF.PacInput 0; FF.PacMul 10 m [];
  FF.PacAdd 9 11; FF.PacMul 12 m []; FF.PacAdd 8 13; FF.PacMul 14 m []
]

let nodes (p:int) (m:expr) : list FF.pac_node =
  FF.PacInput 4 :: later_nodes m

let certificate (p:int) : FF.certificate = {
  pac_premises = [premise0 p; premise1 p];
  pac_nodes = nodes p (num p (p - 1));
  pac_root = 15;
  pac_support = [0; 1];
}

let p31 : int = 2147483647
let p127 : int = 170141183460469231731687303715884105727

let test_accepted_unit_ideal_certificates () : Lemma (
  FF.check (certificate p31) (clause p31) /\
  FF.check (certificate p127) (clause p127) /\
  FF.check (certificate 4) (clause 4)) =
  assert_norm (
    FF.check (certificate p31) (clause p31) /\
    FF.check (certificate p127) (clause p127) /\
    FF.check (certificate 4) (clause 4))

let with_nodes (c:FF.certificate) (ns:list FF.pac_node) : FF.certificate =
  { c with pac_nodes = ns }

let with_support (c:FF.certificate) (support:list int) : FF.certificate =
  { c with pac_support = support }

let with_root (c:FF.certificate) (root:int) : FF.certificate =
  { c with pac_root = root }

let test_replay_gate_mutations () : Lemma (
  not (FF.check (with_nodes (certificate p31)
            (nodes p31 (num p31 2))) (clause p31)) /\
  not (FF.check (with_support (certificate p31) [0]) (clause p31)) /\
  not (FF.check (with_support (certificate p31) [1; 0]) (clause p31)) /\
  not (FF.check (with_root (certificate p31) 14) (clause p31)) /\
  not (FF.check (with_root (certificate p31) 16) (clause p31)) /\
  not (FF.check (with_nodes (certificate p31)
            [FF.PacInput 4; FF.PacAdd 0 2]) (clause p31))) =
  assert_norm (
    not (FF.check (with_nodes (certificate p31)
              (nodes p31 (num p31 2))) (clause p31)) /\
    not (FF.check (with_support (certificate p31) [0]) (clause p31)) /\
    not (FF.check (with_support (certificate p31) [1; 0]) (clause p31)) /\
    not (FF.check (with_root (certificate p31) 14) (clause p31)) /\
    not (FF.check (with_root (certificate p31) 16) (clause p31)) /\
    not (FF.check (with_nodes (certificate p31)
              [FF.PacInput 4; FF.PacAdd 0 2]) (clause p31)))

let square (p:int) : expr =
  eq (num p 0) (mul p [const p "x"; const p "x"])

let nonzero (p:int) : expr =
  mk_not_expr (eq (const p "x") (num p 0))

let inverse_witness_certificate (p:int) : FF.certificate = {
  pac_premises = [square p; nonzero p];
  pac_nodes = [
    FF.PacInput 0; FF.PacInput 1; FF.PacAdd 0 1; FF.PacMul 2 (num p (p - 1)) [];
    FF.PacMul 3 (num p 1) [2]; FF.PacInput 2; FF.PacMul 5 (num p 1) [0];
    FF.PacMul 6 (num p (p - 1)) []; FF.PacAdd 4 7; FF.PacMul 8 (num p 1) [2];
    FF.PacInput 2; FF.PacMul 10 (num p (p - 1)) []; FF.PacAdd 9 11
  ];
  pac_root = 12;
  pac_support = [0; 1];
}

let inverse_witness_clause (p:int) : expr =
  disj [mk_not_expr (square p); eq (const p "x") (num p 0)]

let test_negative_premise_witness_remains_unsupported () : Lemma (
  not (FF.check (inverse_witness_certificate p31) (inverse_witness_clause p31)) /\
  not (FF.check (inverse_witness_certificate 4) (inverse_witness_clause 4))) =
  assert_norm (
    not (FF.check (inverse_witness_certificate p31) (inverse_witness_clause p31)) /\
    not (FF.check (inverse_witness_certificate 4) (inverse_witness_clause 4)))

let test_original_limits () : Lemma (
  FF.max_premises == 4096 /\ FF.max_variables == 4096 /\
  FF.max_equations == 8192 /\ FF.max_nodes == 100000 /\
  FF.max_poly_size == 16384 /\ FF.max_work == 4000000) =
  assert_norm (
    FF.max_premises == 4096 /\ FF.max_variables == 4096 /\
    FF.max_equations == 8192 /\ FF.max_nodes == 100000 /\
    FF.max_poly_size == 16384 /\ FF.max_work == 4000000)

let malformed_add_decl (p:int) : func_decl =
  { decl_name = "ff.add"; domain = [FF.ff_sort p; FF.ff_sort p];
    range = FF.ff_sort p; interp = Some FF.op_ff_add; int_params = [p] }

let malformed_add_arity (p:int) (x:expr) : expr =
  App (malformed_add_decl p) [x]

let ite (c t u:expr) : expr =
  App (A.term_ite_decl (get_sort t)) [c; t; u]

let and2 (x y:expr) : expr =
  App (and_decl [x; y]) [x; y]

let test_rewrite_acceptance_composite_modulus () : Lemma (
  FF.term_equivalent
    (add 4 [const 4 "x"; num 4 0]) (const 4 "x") /\
  FF.eq_truth_equivalent
    (eq (add 4 [const 4 "x"; num 4 1]) (const 4 "x")) false_expr /\
  FF.eq_eq_equivalent
    (eq (const 4 "x") (num 4 0))
    (eq (mul 4 [num 4 3; const 4 "x"]) (num 4 0))) =
  assert_norm (
    FF.term_equivalent
      (add 4 [const 4 "x"; num 4 0]) (const 4 "x") /\
    FF.eq_truth_equivalent
      (eq (add 4 [const 4 "x"; num 4 1]) (const 4 "x")) false_expr /\
    FF.eq_eq_equivalent
      (eq (const 4 "x") (num 4 0))
      (eq (mul 4 [num 4 3; const 4 "x"]) (num 4 0)))

let test_conditional_rewrite_gate () : Lemma (
  FF.ite_eq_equivalent
    (eq (ite (eq (const 4 "x") (num 4 0)) (num 4 1) (num 4 0))
        (num 4 0))
    (and2 (eq (num 4 0) (num 4 0))
          (mk_not_expr (eq (const 4 "x") (num 4 0))))) =
  assert_norm (
    FF.ite_eq_equivalent
      (eq (ite (eq (const 4 "x") (num 4 0)) (num 4 1) (num 4 0))
          (num 4 0))
      (and2 (eq (num 4 0) (num 4 0))
            (mk_not_expr (eq (const 4 "x") (num 4 0)))))

let test_exhaustive_clause_regressions () : Lemma (
  FF.exhaustive_clause
    (disj [eq (add 4 [const 4 "x"; num 4 0]) (const 4 "x");
           mk_not_expr (eq (add 4 [const 4 "x"; num 4 0]) (const 4 "x"))]) /\
  not (FF.exhaustive_clause
         (eq (num 1 0) (num 1 0))) /\
  not (FF.exhaustive_clause (Var 0 bool_sort)) /\
  FF.max_assignments == 4096 /\
  FF.within_budget 2 12 1 /\ not (FF.within_budget 2 13 1)) =
  assert_norm (FF.exhaustive_clause
    (disj [eq (add 4 [const 4 "x"; num 4 0]) (const 4 "x");
           mk_not_expr (eq (add 4 [const 4 "x"; num 4 0]) (const 4 "x"))]));
  assert_norm (not (FF.exhaustive_clause (eq (num 1 0) (num 1 0))));
  assert_norm (not (FF.exhaustive_clause (Var 0 bool_sort)));
  assert_norm (FF.max_assignments == 4096);
  assert_norm (FF.within_budget 2 12 1);
  assert_norm (not (FF.within_budget 2 13 1))

let test_operation_gate_rejects_malformed_arity () : Lemma (
  FF.operation_at (malformed_add_decl 4) [const 4 "x"] == None /\
  LegacyFF.operation (malformed_add_decl 4) [const 4 "x"] == None) =
  assert_norm (
    FF.operation_at (malformed_add_decl 4) [const 4 "x"] == None /\
    LegacyFF.operation (malformed_add_decl 4) [const 4 "x"] == None)

let test_visit_rejects_non_application () : Lemma (
  FF.visit p31 FF.empty_encoding (Var 0 (FF.ff_sort p31)) == None) =
  assert_norm (FF.visit p31 FF.empty_encoding (Var 0 (FF.ff_sort p31)) == None)

let to_legacy_node (n:FF.pac_node) : Legacy.pac_node =
  match n with
  | FF.PacInput i -> Legacy.PacInput i
  | FF.PacAdd i j -> Legacy.PacAdd i j
  | FF.PacMul i c fs -> Legacy.PacMul i c fs

let rec to_legacy_nodes (ns:list FF.pac_node) : list Legacy.pac_node =
  match ns with
  | [] -> []
  | n :: rest -> to_legacy_node n :: to_legacy_nodes rest

let rec lemma_to_legacy_nodes_length (ns:list FF.pac_node)
  : Lemma (L.length (to_legacy_nodes ns) == L.length ns)
          (decreases ns) =
  match ns with
  | [] -> ()
  | _ :: rest -> lemma_to_legacy_nodes_length rest

let to_legacy_certificate (c:FF.certificate) : Legacy.certificate = {
  pac_premises = c.pac_premises;
  pac_nodes = to_legacy_nodes c.pac_nodes;
  pac_root = c.pac_root;
  pac_support = c.pac_support
}

let to_legacy_origin (o:FF.origin) : Legacy.origin =
  match o with
  | FF.Definition -> Legacy.Definition
  | FF.Premise k l -> Legacy.Premise k l
  | FF.Witness -> Legacy.Witness

let to_legacy_equation (e:FF.equation) : LegacyFF.poly & Legacy.origin =
  let (q, o) = e in (q, to_legacy_origin o)

let rec to_legacy_equations (es:list FF.equation) : list (LegacyFF.poly & Legacy.origin) =
  match es with
  | [] -> []
  | e :: rest -> to_legacy_equation e :: to_legacy_equations rest

let to_legacy_encoding (st:FF.encoding) : Legacy.encoding = {
  terms = st.terms;
  equations = to_legacy_equations st.equations;
  count = st.count
}

#push-options "--fuel 12 --ifuel 8"
let lemma_numeral_matches_legacy (e:expr)
  : Lemma (FF.numeral e == LegacyFF.numeral e) = ()

let rec lemma_index_of_matches_legacy (e:expr) (tbl:list expr)
  : Lemma (FF.index_of e tbl == LegacyFF.index_of e tbl) =
  match tbl with
  | [] -> ()
  | _ :: rest -> lemma_index_of_matches_legacy e rest

let lemma_term_poly_matches_legacy (p:int) (tbl:list expr) (t:expr)
  : Lemma (FF.term_poly p tbl t == Legacy.term_poly p tbl t) =
  lemma_numeral_matches_legacy t;
  lemma_index_of_matches_legacy t tbl

let rec lemma_term_polys_matches_legacy (p:int) (tbl ts:list expr)
  : Lemma (FF.term_polys p tbl ts == Legacy.term_polys p tbl ts)
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: rest ->
    lemma_term_poly_matches_legacy p tbl t;
    lemma_term_polys_matches_legacy p tbl rest

let rec lemma_mono_mul_matches_legacy (a b:FF.mono)
  : Lemma (FF.mono_mul a b == LegacyFF.mono_mul a b)
          (decreases (L.length a + L.length b)) =
  match a, b with
  | [], _ -> ()
  | _, [] -> ()
  | _ :: a', _ :: b' ->
    if L.hd a <= L.hd b then lemma_mono_mul_matches_legacy a' b
    else lemma_mono_mul_matches_legacy a b'

let rec lemma_mono_lt_matches_legacy (a b:FF.mono)
  : Lemma (FF.mono_lt a b == LegacyFF.mono_lt a b) (decreases a) =
  match a, b with
  | [], [] | [], _ | _, [] -> ()
  | _ :: a', _ :: b' ->
    if L.hd a < L.hd b then ()
    else if L.hd a > L.hd b then ()
    else lemma_mono_lt_matches_legacy a' b'

let rec lemma_padd_matches_legacy (a b:FF.poly)
  : Lemma (FF.padd a b == LegacyFF.padd a b)
          (decreases (L.length a + L.length b)) =
  match a, b with
  | [], _ | _, [] -> ()
  | (m1, _) :: a', (m2, _) :: b' ->
    lemma_mono_lt_matches_legacy m1 m2;
    if m1 == m2 then lemma_padd_matches_legacy a' b'
    else if FF.mono_lt m1 m2 then lemma_padd_matches_legacy a' b
    else lemma_padd_matches_legacy a b'

let rec lemma_pscale_matches_legacy (k:int) (q:FF.poly)
  : Lemma (FF.pscale k q == LegacyFF.pscale k q) (decreases q) =
  match q with
  | [] -> ()
  | _ :: rest -> lemma_pscale_matches_legacy k rest

let rec lemma_pmul_term_matches_legacy (m:FF.mono) (c:int) (q:FF.poly)
  : Lemma (FF.pmul_term m c q == LegacyFF.pmul_term m c q)
          (decreases q) =
  match q with
  | [] -> ()
  | _ :: rest ->
    lemma_mono_mul_matches_legacy m (fst (L.hd q));
    lemma_padd_matches_legacy [(FF.mono_mul m (fst (L.hd q)), c * snd (L.hd q))]
                              (FF.pmul_term m c rest);
    lemma_pmul_term_matches_legacy m c rest

let rec lemma_pmul_matches_legacy (a b:FF.poly)
  : Lemma (FF.pmul a b == LegacyFF.pmul a b) (decreases a) =
  match a with
  | [] -> ()
  | _ :: rest ->
    lemma_pmul_term_matches_legacy (fst (L.hd a)) (snd (L.hd a)) b;
    lemma_pmul_matches_legacy rest b;
    lemma_padd_matches_legacy (FF.pmul_term (fst (L.hd a)) (snd (L.hd a)) b)
                              (FF.pmul rest b)

let rec lemma_psum_matches_legacy (qs:list FF.poly)
  : Lemma (FF.psum qs == LegacyFF.psum qs) (decreases qs) =
  match qs with
  | [] -> ()
  | q :: rest ->
    lemma_psum_matches_legacy rest;
    lemma_padd_matches_legacy q (FF.psum rest)

let rec lemma_pbitsum_matches_legacy (weight:int) (qs:list FF.poly)
  : Lemma (FF.pbitsum weight qs == LegacyFF.pbitsum weight qs)
          (decreases qs) =
  match qs with
  | [] -> ()
  | q :: rest ->
    lemma_pscale_matches_legacy weight q;
    lemma_pbitsum_matches_legacy (2 * weight) rest;
    lemma_padd_matches_legacy (FF.pscale weight q) (FF.pbitsum (2 * weight) rest)

let rec lemma_pprod_matches_legacy (qs:list FF.poly)
  : Lemma (FF.pprod qs == LegacyFF.pprod qs) (decreases qs) =
  match qs with
  | [] -> ()
  | q :: rest ->
    lemma_pprod_matches_legacy rest;
    match FF.pprod rest with
    | None -> ()
    | Some r ->
      lemma_pmul_matches_legacy q r

let lemma_combine_matches_legacy (op:decl_kind) (qs:list FF.poly)
  : Lemma (FF.combine op qs == LegacyFF.combine op qs) =
  if op == FF.op_ff_add then lemma_psum_matches_legacy qs
  else if op == FF.op_ff_mul then lemma_pprod_matches_legacy qs
  else if op == FF.op_ff_bitsum then lemma_pbitsum_matches_legacy 1 qs
  else
    match qs with
    | [q] -> lemma_pscale_matches_legacy (-1) q
    | _ -> ()

let rec lemma_size_matches_legacy (q:FF.poly)
  : Lemma (FF.poly_size q == Legacy.size q) (decreases q) =
  match q with
  | [] -> ()
  | _ :: rest -> lemma_size_matches_legacy rest

let rec lemma_scale_mono_matches_legacy (m:FF.mono) (c:int) (q:FF.poly)
  : Lemma (FF.scale_mono m c q == Legacy.scale_mono m c q)
          (decreases q) =
  match q with
  | [] -> ()
  | (m2, _) :: rest ->
    lemma_mono_mul_matches_legacy m m2;
    lemma_scale_mono_matches_legacy m c rest

let rec lemma_split_matches_legacy (q:FF.poly)
  : Lemma (FF.split q == Legacy.split q) (decreases q) =
  match q with
  | _ :: _ :: rest -> lemma_split_matches_legacy rest
  | _ -> ()

let rec lemma_canon_matches_legacy (q:FF.poly)
  : Lemma (FF.canon q == Legacy.canon q)
          (decreases (L.length q)) =
  if L.length q < 2 then ()
  else
    let (a, b) = FF.split q in
    lemma_split_matches_legacy q;
    lemma_canon_matches_legacy a;
    lemma_canon_matches_legacy b;
    lemma_padd_matches_legacy (FF.canon a) (FF.canon b)

let rec lemma_reduce_matches_legacy (p:pos) (q:FF.poly)
  : Lemma (FF.reduce p q == Legacy.reduce p q) (decreases q) =
  match q with
  | [] -> ()
  | _ :: rest -> lemma_reduce_matches_legacy p rest

let lemma_normalize_matches_legacy (p:pos) (q:FF.poly)
  : Lemma (FF.normalize p q == Legacy.normalize p q) =
  lemma_canon_matches_legacy q;
  lemma_reduce_matches_legacy p (FF.canon q)

let rec lemma_support_tree_matches_legacy
    (n previous:int) (tree:IX.index_tree bool) (s:list int)
  : Lemma (FF.support_tree n previous tree s ==
           Legacy.support_tree n previous tree s)
          (decreases s) =
  match s with
  | [] -> ()
  | k :: rest ->
    if 0 <= k && previous < k && k < n then
      lemma_support_tree_matches_legacy n k (IX.index_put tree k true) rest

let rec lemma_all_used_matches_legacy (used:IX.index_tree bool) (s:list int)
  : Lemma (FF.all_used used s == Legacy.all_used used s)
          (decreases s) =
  match s with
  | [] -> ()
  | _ :: rest -> lemma_all_used_matches_legacy used rest

let rec lemma_variables_matches_legacy (n:nat) (previous:int) (fs:list int)
  : Lemma (FF.variables n previous fs == Legacy.variables n previous fs)
          (decreases fs) =
  match fs with
  | [] -> ()
  | f :: rest ->
    if 0 <= f && previous <= f && f < n then
      lemma_variables_matches_legacy n f rest

let lemma_clause_literals_matches_legacy (e:expr)
  : Lemma (FF.clause_literals e == Legacy.clause_literals e) = ()

let rec lemma_negated_in_matches_legacy (l:expr) (lits:list expr)
  : Lemma (FF.negated_in l lits == Legacy.negated_in l lits)
          (decreases lits) =
  match lits with
  | [] -> ()
  | _ :: rest -> lemma_negated_in_matches_legacy l rest

let rec lemma_repeat_sort_matches_domain (p:int) (args:list expr)
  : Lemma (FF.repeat_sort p (L.length args) == LegacyFF.ff_domain p args)
          (decreases args) =
  match args with
  | [] -> ()
  | _ :: rest -> lemma_repeat_sort_matches_domain p rest

let rec lemma_args_have_sort_matches_legacy (p:int) (args:list expr)
  : Lemma (FF.args_have_sort p args == sorts_match args (LegacyFF.ff_domain p args))
          (decreases args) =
  match args with
  | [] -> ()
  | _ :: rest -> lemma_args_have_sort_matches_legacy p rest

let rec lemma_repeat_sort_length (p:int) (n:nat)
  : Lemma (L.length (FF.repeat_sort p n) == n) (decreases n) =
  match n with
  | 0 -> ()
  | _ -> lemma_repeat_sort_length p (n - 1)

let lemma_operation_domain_gate (p:int) (f:func_decl) (args:list expr)
  : Lemma (
      (f.domain == LegacyFF.ff_domain p args &&
       sorts_match args (LegacyFF.ff_domain p args))
      <==>
      (sort_list_eq f.domain (FF.repeat_sort p (L.length f.domain)) &&
       FF.args_have_sort p args && L.length args == L.length f.domain)) =
  lemma_repeat_sort_matches_domain p args;
  lemma_args_have_sort_matches_legacy p args;
  lemma_repeat_sort_length p (L.length args);
  V.lemma_sort_list_eq f.domain (FF.repeat_sort p (L.length f.domain));
  if f.domain == LegacyFF.ff_domain p args then
    assert (L.length f.domain == L.length args)

let lemma_operation_matches_legacy (f:func_decl) (args:list expr)
  : Lemma (FF.operation_at f args == LegacyFF.operation f args) =
  match f.int_params, f.interp with
  | [p], Some op ->
    lemma_operation_domain_gate p f args;
    V.lemma_sort_eq f.range (FF.ff_sort p)
  | _, _ -> ()

let lemma_modulus_of_matches_legacy (e:expr)
  : Lemma (FF.modulus_of e == LegacyFF.modulus_of e) =
  lemma_numeral_matches_legacy e;
  match e with
  | App f args -> lemma_operation_matches_legacy f args
  | _ -> ()

let rec lemma_find_modulus_matches_legacy (e:expr)
  : Lemma (FF.find_modulus e == LegacyFF.find_modulus e)
          (decreases e) =
  lemma_modulus_of_matches_legacy e;
  match FF.modulus_of e with
  | Some _ -> ()
  | None ->
    match e with
    | App _ args -> lemma_find_modulus_args_matches_legacy args
    | _ -> ()

and lemma_find_modulus_args_matches_legacy (args:list expr)
  : Lemma (FF.find_modulus_args args == LegacyFF.find_modulus_args args)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_find_modulus_matches_legacy a;
    match FF.find_modulus a with
    | Some _ -> ()
    | None -> lemma_find_modulus_args_matches_legacy rest

let map_option (#a #b:Type) (f:a -> b) (x:option a) : option b =
  match x with
  | None -> None
  | Some y -> Some (f y)

let rec equations_tree_related
    (new_tree:IX.index_tree FF.equation)
    (old_tree:IX.index_tree (LegacyFF.poly & Legacy.origin))
  : Tot prop (decreases new_tree) =
  match new_tree, old_tree with
  | IX.Empty, IX.Empty -> True
  | IX.Branch nv nl nr, IX.Branch ov ol or ->
    map_option to_legacy_equation nv == ov /\
    equations_tree_related nl ol /\ equations_tree_related nr or
  | _, _ -> False

let rec lemma_equation_tree_get_related
    (new_tree:IX.index_tree FF.equation)
    (old_tree:IX.index_tree (LegacyFF.poly & Legacy.origin))
    (k:nat)
  : Lemma (requires equations_tree_related new_tree old_tree)
          (ensures map_option to_legacy_equation (IX.index_get new_tree k) ==
                  IX.index_get old_tree k)
          (decreases k) =
  match new_tree, old_tree with
  | IX.Empty, IX.Empty -> ()
  | IX.Branch _ nl nr, IX.Branch _ ol or ->
    if k == 0 then ()
    else if k % 2 == 1 then lemma_equation_tree_get_related nl ol ((k - 1) / 2)
    else lemma_equation_tree_get_related nr or ((k - 1) / 2)
  | _, _ -> assert_norm False

let rec lemma_put_equation_tree_related
    (new_tree:IX.index_tree FF.equation)
    (old_tree:IX.index_tree (LegacyFF.poly & Legacy.origin))
    (k:nat) (new_eq:FF.equation) (old_eq:LegacyFF.poly & Legacy.origin)
  : Lemma (requires equations_tree_related new_tree old_tree /\
                    to_legacy_equation new_eq == old_eq)
          (ensures equations_tree_related
                     (IX.index_put new_tree k new_eq)
                     (IX.index_put old_tree k old_eq))
          (decreases k) =
  match new_tree, old_tree with
  | IX.Empty, IX.Empty ->
    if k == 0 then ()
    else if k % 2 == 1 then
      lemma_put_equation_tree_related IX.Empty IX.Empty ((k - 1) / 2) new_eq old_eq
    else
      lemma_put_equation_tree_related IX.Empty IX.Empty ((k - 1) / 2) new_eq old_eq
  | IX.Branch _ nl nr, IX.Branch _ ol or ->
    if k == 0 then ()
    else if k % 2 == 1 then
      lemma_put_equation_tree_related nl ol ((k - 1) / 2) new_eq old_eq
    else
      lemma_put_equation_tree_related nr or ((k - 1) / 2) new_eq old_eq
  | _, _ -> assert_norm False

let rec lemma_index_equations_related
    (new_tree:IX.index_tree FF.equation)
    (old_tree:IX.index_tree (LegacyFF.poly & Legacy.origin))
    (k:int) (es:list FF.equation)
  : Lemma (requires equations_tree_related new_tree old_tree)
          (ensures equations_tree_related
                    (FF.index_equations new_tree k es)
                    (Legacy.index_equations old_tree k (to_legacy_equations es)))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: rest ->
    if k < 0 then ()
    else (
      lemma_put_equation_tree_related new_tree old_tree k e (to_legacy_equation e);
      lemma_index_equations_related
        (IX.index_put new_tree k e)
        (IX.index_put old_tree k (to_legacy_equation e))
        (k - 1) rest)

let rec lemma_to_legacy_equations_length (es:list FF.equation)
  : Lemma (L.length (to_legacy_equations es) == L.length es)
          (decreases es) =
  match es with
  | [] -> ()
  | _ :: rest -> lemma_to_legacy_equations_length rest

let rec poly_tree_related
    (new_tree:IX.index_tree FF.poly)
    (old_tree:IX.index_tree LegacyFF.poly) : Tot prop (decreases new_tree) =
  match new_tree, old_tree with
  | IX.Empty, IX.Empty -> True
  | IX.Branch nv nl nr, IX.Branch ov ol or ->
    nv == ov /\ poly_tree_related nl ol /\ poly_tree_related nr or
  | _, _ -> False

let rec bool_tree_related
    (new_tree:IX.index_tree bool)
    (old_tree:IX.index_tree bool) : Tot prop (decreases new_tree) =
  match new_tree, old_tree with
  | IX.Empty, IX.Empty -> True
  | IX.Branch nv nl nr, IX.Branch ov ol or ->
    nv == ov /\ bool_tree_related nl ol /\ bool_tree_related nr or
  | _, _ -> False

let rec lemma_poly_tree_get_related
    (new_tree:IX.index_tree FF.poly) (old_tree:IX.index_tree LegacyFF.poly)
    (k:nat)
  : Lemma (requires poly_tree_related new_tree old_tree)
          (ensures IX.index_get new_tree k == IX.index_get old_tree k)
          (decreases k) =
  match new_tree, old_tree with
  | IX.Empty, IX.Empty -> ()
  | IX.Branch _ nl nr, IX.Branch _ ol or ->
    if k == 0 then ()
    else if k % 2 == 1 then lemma_poly_tree_get_related nl ol ((k - 1) / 2)
    else lemma_poly_tree_get_related nr or ((k - 1) / 2)
  | _, _ -> assert_norm False

let rec lemma_bool_tree_get_related
    (new_tree:IX.index_tree bool) (old_tree:IX.index_tree bool) (k:nat)
  : Lemma (requires bool_tree_related new_tree old_tree)
          (ensures IX.index_get new_tree k == IX.index_get old_tree k)
          (decreases k) =
  match new_tree, old_tree with
  | IX.Empty, IX.Empty -> ()
  | IX.Branch _ nl nr, IX.Branch _ ol or ->
    if k == 0 then ()
    else if k % 2 == 1 then lemma_bool_tree_get_related nl ol ((k - 1) / 2)
    else lemma_bool_tree_get_related nr or ((k - 1) / 2)
  | _, _ -> assert_norm False

let rec lemma_poly_tree_put_related
    (new_tree:IX.index_tree FF.poly) (old_tree:IX.index_tree LegacyFF.poly)
    (k:nat) (new_v:FF.poly) (old_v:LegacyFF.poly)
  : Lemma (requires poly_tree_related new_tree old_tree /\ new_v == old_v)
          (ensures poly_tree_related
                     (IX.index_put new_tree k new_v)
                     (IX.index_put old_tree k old_v))
          (decreases k) =
  match new_tree, old_tree with
  | IX.Empty, IX.Empty ->
    if k == 0 then ()
    else if k % 2 == 1 then
      lemma_poly_tree_put_related IX.Empty IX.Empty ((k - 1) / 2) new_v old_v
    else
      lemma_poly_tree_put_related IX.Empty IX.Empty ((k - 1) / 2) new_v old_v
  | IX.Branch _ nl nr, IX.Branch _ ol or ->
    if k == 0 then ()
    else if k % 2 == 1 then
      lemma_poly_tree_put_related nl ol ((k - 1) / 2) new_v old_v
    else
      lemma_poly_tree_put_related nr or ((k - 1) / 2) new_v old_v
  | _, _ -> assert_norm False

let rec lemma_bool_tree_put_related
    (new_tree:IX.index_tree bool) (old_tree:IX.index_tree bool)
    (k:nat) (new_v old_v:bool)
  : Lemma (requires bool_tree_related new_tree old_tree /\ new_v == old_v)
          (ensures bool_tree_related
                     (IX.index_put new_tree k new_v)
                     (IX.index_put old_tree k old_v))
          (decreases k) =
  match new_tree, old_tree with
  | IX.Empty, IX.Empty ->
    if k == 0 then ()
    else if k % 2 == 1 then
      lemma_bool_tree_put_related IX.Empty IX.Empty ((k - 1) / 2) new_v old_v
    else
      lemma_bool_tree_put_related IX.Empty IX.Empty ((k - 1) / 2) new_v old_v
  | IX.Branch _ nl nr, IX.Branch _ ol or ->
    if k == 0 then ()
    else if k % 2 == 1 then
      lemma_bool_tree_put_related nl ol ((k - 1) / 2) new_v old_v
    else
      lemma_bool_tree_put_related nr or ((k - 1) / 2) new_v old_v
  | _, _ -> assert_norm False

let support_options_related
    (new_tree:option (IX.index_tree bool))
    (old_tree:option (IX.index_tree bool)) : prop =
  match new_tree, old_tree with
  | None, None -> True
  | Some a, Some b -> bool_tree_related a b
  | _, _ -> False

let rec lemma_support_tree_related
    (n previous:int) (new_tree old_tree:IX.index_tree bool) (s:list int)
  : Lemma (requires bool_tree_related new_tree old_tree)
          (ensures support_options_related
                    (FF.support_tree n previous new_tree s)
                    (Legacy.support_tree n previous old_tree s))
          (decreases s) =
  match s with
  | [] -> ()
  | k :: rest ->
    if 0 <= k && previous < k && k < n then (
      lemma_bool_tree_put_related new_tree old_tree k true true;
      lemma_support_tree_related n k (IX.index_put new_tree k true)
        (IX.index_put old_tree k true) rest)

let replay_related (new_r:FF.replay) (old_r:Legacy.replay) : prop =
  new_r.next == old_r.next /\ new_r.work == old_r.work /\
  poly_tree_related new_r.values old_r.values /\
  bool_tree_related new_r.used old_r.used

let replay_options_related
    (new_r:option FF.replay) (old_r:option Legacy.replay) : prop =
  match new_r, old_r with
  | None, None -> True
  | Some a, Some b -> replay_related a b
  | _, _ -> False

let to_legacy_replay (r:FF.replay) : Legacy.replay = {
  values = r.values;
  next = r.next;
  work = r.work;
  used = r.used
}

let lemma_initial_replay_matches_legacy ()
  : Lemma (replay_related FF.initial_replay Legacy.initial_replay) = ()

let lemma_record_matches_legacy
    (p:pos) (r:FF.replay) (old_r:Legacy.replay) (cost:nat)
    (q:FF.poly) (old_q:LegacyFF.poly)
    (used:IX.index_tree bool) (old_used:IX.index_tree bool)
  : Lemma (requires replay_related r old_r /\ q == old_q /\
                    bool_tree_related used old_used)
          (ensures replay_options_related
                     (FF.record p r cost q used)
                     (Legacy.record p old_r cost old_q old_used)) =
  lemma_normalize_matches_legacy p q;
  lemma_poly_tree_put_related r.values old_r.values r.next
    (FF.normalize p q) (Legacy.normalize p old_q);
  assert (r.next == old_r.next /\ r.work == old_r.work)

let lemma_earlier_matches_legacy
    (r:FF.replay) (old_r:Legacy.replay) (j:int)
  : Lemma (requires replay_related r old_r)
          (ensures FF.earlier r j == Legacy.earlier old_r j) =
  if 0 <= j && j < r.next then
    lemma_poly_tree_get_related r.values old_r.values j

let lemma_unit_root_matches_legacy
    (r:FF.replay) (old_r:Legacy.replay) (root:int)
  : Lemma (requires replay_related r old_r)
          (ensures FF.unit_root r root == Legacy.unit_root old_r root) =
  if 0 <= root && root < r.next then
    lemma_poly_tree_get_related r.values old_r.values root

let lemma_empty_encoding_matches_legacy ()
  : Lemma (to_legacy_encoding FF.empty_encoding == Legacy.empty_encoding) = ()

let lemma_allocate_matches_legacy (st:FF.encoding) (t:expr)
  : Lemma (map_option to_legacy_encoding (FF.allocate st t) ==
           Legacy.allocate (to_legacy_encoding st) t) =
  if L.length st.terms + 1 > FF.max_variables then ()
  else assert (to_legacy_encoding
                 { st with terms = L.append st.terms [t] } ==
               { (to_legacy_encoding st) with terms = L.append st.terms [t] })

let lemma_push_matches_legacy (st:FF.encoding) (e:FF.equation)
  : Lemma (map_option to_legacy_encoding (FF.push st e) ==
           Legacy.push (to_legacy_encoding st) (to_legacy_equation e)) =
  if st.count + 1 > FF.max_equations then ()
  else
    assert (to_legacy_equations (e :: st.equations) ==
            to_legacy_equation e :: to_legacy_equations st.equations)

let lemma_definition_matches_legacy (k:nat) (q:FF.poly)
  : Lemma (FF.definition k q == Legacy.definition k q) =
  lemma_pscale_matches_legacy (-1) q;
  lemma_padd_matches_legacy [([k], 1)] (FF.pscale (-1) q)

let lemma_define_matches_legacy (st:FF.encoding) (t:expr) (q:FF.poly)
  : Lemma (map_option to_legacy_encoding (FF.define st t q) ==
           Legacy.define (to_legacy_encoding st) t q) =
  lemma_definition_matches_legacy (L.length st.terms) q;
  lemma_allocate_matches_legacy st t

let lemma_eq_parts_matches_legacy (e:expr)
  : Lemma (FF.eq_parts e == LegacyFF.eq_parts e) = ()

let lemma_closed_ff_matches_legacy (p:int) (e:expr)
  : Lemma (FF.closed_ff p e == LegacyFF.closed_ff p e) = ()

let rec lemma_collect_matches_legacy (p:int) (tbl:list expr) (e:expr)
  : Lemma (FF.collect p tbl e == LegacyFF.collect p tbl e)
          (decreases e) =
  match FF.numeral e with
  | Some _ -> lemma_numeral_matches_legacy e
  | None ->
    match e with
    | App f args ->
      lemma_operation_matches_legacy f args;
      if Some? (FF.operation_at f args) then
        let (q, _) = Some?.v (FF.operation_at f args) in
        if q == p then lemma_collect_args_matches_legacy p tbl args
        else ()
      else ()
    | _ -> ()

and lemma_collect_args_matches_legacy (p:int) (tbl args:list expr)
  : Lemma (FF.collect_args p tbl args == LegacyFF.collect_args p tbl args)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_collect_matches_legacy p tbl a;
    lemma_collect_args_matches_legacy p (FF.collect p tbl a) rest

let lemma_atom_poly_matches_legacy (tbl:list expr) (e:expr)
  : Lemma (FF.atom_poly tbl e == LegacyFF.atom_poly tbl e) =
  lemma_index_of_matches_legacy e tbl

let rec lemma_to_poly_matches_legacy (p:int) (tbl:list expr) (e:expr)
  : Lemma (FF.to_poly p tbl e == LegacyFF.to_poly p tbl e)
          (decreases e) =
  match FF.numeral e with
  | Some _ -> lemma_numeral_matches_legacy e
  | None ->
    match e with
    | App f args ->
      lemma_operation_matches_legacy f args;
      if Some? (FF.operation_at f args) then
        let (q, op) = Some?.v (FF.operation_at f args) in
        if q == p then (
          lemma_to_polys_matches_legacy p tbl args;
          match FF.to_polys p tbl args with
          | Some qs -> lemma_combine_matches_legacy op qs
          | None -> ())
        else ()
      else lemma_atom_poly_matches_legacy tbl e
    | _ -> lemma_atom_poly_matches_legacy tbl e

and lemma_to_polys_matches_legacy (p:int) (tbl args:list expr)
  : Lemma (FF.to_polys p tbl args == LegacyFF.to_polys p tbl args)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_to_poly_matches_legacy p tbl a;
    lemma_to_polys_matches_legacy p tbl rest

let lemma_difference_matches_legacy (p:int) (tbl:list expr) (a b:expr)
  : Lemma (FF.difference p tbl a b == LegacyFF.difference p tbl a b) =
  lemma_to_poly_matches_legacy p tbl a;
  lemma_to_poly_matches_legacy p tbl b;
  match FF.to_poly p tbl a, FF.to_poly p tbl b with
  | Some qa, Some qb ->
    lemma_pscale_matches_legacy (-1) qb;
    lemma_padd_matches_legacy qa (FF.pscale (-1) qb)
  | _, _ -> ()

let lemma_shared_modulus_matches_legacy (a b:expr)
  : Lemma (FF.shared_modulus a b == LegacyFF.shared_modulus a b) =
  lemma_modulus_of_matches_legacy a;
  lemma_modulus_of_matches_legacy b

let rec lemma_zero_mod_matches_legacy (p:pos) (q:FF.poly)
  : Lemma (FF.zero_mod p q == LegacyFF.zero_mod p q) (decreases q) =
  match q with
  | [] -> ()
  | _ :: rest -> lemma_zero_mod_matches_legacy p rest

let rec lemma_prune_matches_legacy (p:pos) (q:FF.poly)
  : Lemma (FF.prune p q == LegacyFF.prune p q) (decreases q) =
  match q with
  | [] -> ()
  | _ :: rest -> lemma_prune_matches_legacy p rest

let lemma_nonzero_constant_matches_legacy (p:pos) (q:FF.poly)
  : Lemma (FF.nonzero_constant p q == LegacyFF.nonzero_constant p q) =
  lemma_prune_matches_legacy p q

let rec lemma_egcd_matches_legacy (a b:nat)
  : Lemma (FF.egcd a b == LegacyFF.egcd a b) (decreases b) =
  if b == 0 then ()
  else lemma_egcd_matches_legacy b (a % b)

let lemma_inverse_mod_matches_legacy (p:pos) (c:int)
  : Lemma (FF.inverse_mod p c == LegacyFF.inverse_mod p c) =
  lemma_egcd_matches_legacy (c % p) p

let rec lemma_coeff_of_matches_legacy (m:FF.mono) (q:FF.poly)
  : Lemma (FF.coeff_of m q == LegacyFF.coeff_of m q) (decreases q) =
  match q with
  | [] -> ()
  | _ :: rest -> lemma_coeff_of_matches_legacy m rest

let rec lemma_first_nonzero_matches_legacy (p:pos) (q:FF.poly)
  : Lemma (FF.first_nonzero p q == LegacyFF.first_nonzero p q)
          (decreases q) =
  match q with
  | [] -> ()
  | _ :: rest -> lemma_first_nonzero_matches_legacy p rest

let lemma_scale_witness_matches_legacy (p:pos) (d1 d2:FF.poly)
  : Lemma (FF.scale_witness p d1 d2 == LegacyFF.scale_witness p d1 d2) =
  lemma_first_nonzero_matches_legacy p d2;
  match FF.first_nonzero p d2 with
  | None -> ()
  | Some m ->
    lemma_coeff_of_matches_legacy m d1;
    lemma_coeff_of_matches_legacy m d2;
    lemma_inverse_mod_matches_legacy p (FF.coeff_of m d1);
    lemma_inverse_mod_matches_legacy p (FF.coeff_of m d2)

let lemma_same_zero_set_matches_legacy (p:pos) (d1 d2:FF.poly)
  : Lemma (FF.same_zero_set p d1 d2 == LegacyFF.same_zero_set p d1 d2) =
  lemma_zero_mod_matches_legacy p d1;
  lemma_zero_mod_matches_legacy p d2;
  lemma_scale_witness_matches_legacy p d1 d2;
  match FF.scale_witness p d1 d2 with
  | None -> ()
  | Some (k, w) ->
    lemma_pscale_matches_legacy (-k) d2;
    lemma_pscale_matches_legacy (-w) d1;
    lemma_padd_matches_legacy d1 (FF.pscale (-k) d2);
    lemma_padd_matches_legacy d2 (FF.pscale (-w) d1);
    lemma_zero_mod_matches_legacy p (FF.padd d1 (FF.pscale (-k) d2));
    lemma_zero_mod_matches_legacy p (FF.padd d2 (FF.pscale (-w) d1))

let lemma_term_equivalent_matches_legacy (a b:expr)
  : Lemma (FF.term_equivalent a b == LegacyFF.term_equivalent a b) =
  lemma_shared_modulus_matches_legacy a b;
  match FF.shared_modulus a b with
  | None -> ()
  | Some p ->
    lemma_closed_ff_matches_legacy p a;
    lemma_closed_ff_matches_legacy p b;
    if p >= 2 && FF.closed_ff p a && FF.closed_ff p b then (
      let tbl = FF.collect p (FF.collect p [] a) b in
      lemma_collect_matches_legacy p [] a;
      lemma_collect_matches_legacy p (FF.collect p [] a) b;
      assert (tbl == LegacyFF.collect p (LegacyFF.collect p [] a) b);
      lemma_difference_matches_legacy p tbl a b;
      match FF.difference p tbl a b with
      | Some d -> lemma_zero_mod_matches_legacy p d
      | None -> ())

let lemma_atom_modulus_matches_legacy (e:expr)
  : Lemma (FF.atom_modulus e == LegacyFF.atom_modulus e) =
  lemma_eq_parts_matches_legacy e;
  match FF.eq_parts e with
  | Some (s, t) -> lemma_shared_modulus_matches_legacy s t
  | None -> ()

let lemma_eq_collect_matches_legacy (p:int) (tbl:list expr) (e:expr)
  : Lemma (FF.eq_collect p tbl e == LegacyFF.eq_collect p tbl e) =
  lemma_eq_parts_matches_legacy e;
  match FF.eq_parts e with
  | Some (s, t) ->
    lemma_collect_matches_legacy p tbl s;
    lemma_collect_matches_legacy p (FF.collect p tbl s) t
  | None -> ()

let lemma_eq_diff_matches_legacy (p:int) (tbl:list expr) (e:expr)
  : Lemma (FF.eq_diff p tbl e == LegacyFF.eq_diff p tbl e) =
  lemma_eq_parts_matches_legacy e;
  match FF.eq_parts e with
  | Some (s, t) ->
    lemma_closed_ff_matches_legacy p s;
    lemma_closed_ff_matches_legacy p t;
    if FF.closed_ff p s && FF.closed_ff p t then
      lemma_difference_matches_legacy p tbl s t
  | None -> ()

let lemma_eq_truth_equivalent_matches_legacy (a b:expr)
  : Lemma (FF.eq_truth_equivalent a b == LegacyFF.eq_truth_equivalent a b) =
  lemma_atom_modulus_matches_legacy a;
  match FF.atom_modulus a with
  | None -> ()
  | Some p ->
    if p >= 2 then (
      let tbl = FF.eq_collect p [] a in
      lemma_eq_collect_matches_legacy p [] a;
      lemma_eq_diff_matches_legacy p tbl a;
      match FF.eq_diff p tbl a with
      | Some d ->
        lemma_zero_mod_matches_legacy p d;
        lemma_nonzero_constant_matches_legacy p d
      | None -> ())

let lemma_eq_eq_equivalent_matches_legacy (a b:expr)
  : Lemma (FF.eq_eq_equivalent a b == LegacyFF.eq_eq_equivalent a b) =
  lemma_atom_modulus_matches_legacy a;
  lemma_atom_modulus_matches_legacy b;
  let modulus =
    match FF.atom_modulus a with
    | Some p -> Some p
    | None -> FF.atom_modulus b in
  match modulus with
  | None -> ()
  | Some p ->
    if p >= 2 then (
      let tbl = FF.eq_collect p (FF.eq_collect p [] a) b in
      lemma_eq_collect_matches_legacy p [] a;
      lemma_eq_collect_matches_legacy p (FF.eq_collect p [] a) b;
      lemma_eq_diff_matches_legacy p tbl a;
      lemma_eq_diff_matches_legacy p tbl b;
      match FF.eq_diff p tbl a, FF.eq_diff p tbl b with
      | Some d1, Some d2 -> lemma_same_zero_set_matches_legacy p d1 d2
      | _, _ -> ())

let lemma_atom_equivalent_matches_legacy (atom x:expr)
  : Lemma (FF.atom_equivalent atom x == LegacyFF.atom_equivalent atom x) =
  lemma_eq_truth_equivalent_matches_legacy atom x;
  lemma_eq_eq_equivalent_matches_legacy atom x

let lemma_ite_eq_parts_matches_legacy (e:expr)
  : Lemma (FF.ite_eq_parts e == LegacyFF.ite_eq_parts e) = ()

let lemma_conjunction_parts_matches_legacy (e:expr)
  : Lemma (FF.conjunction_parts e == LegacyFF.conjunction_parts e) =
  match e with
  | App _ [_; _] -> assert_norm (FF.conjunction_parts e == LegacyFF.conjunction_parts e)
  | _ -> ()

let lemma_ite_eq_equivalent_matches_legacy (a b:expr)
  : Lemma (FF.ite_eq_equivalent a b == LegacyFF.ite_eq_equivalent a b) =
  lemma_ite_eq_parts_matches_legacy a;
  lemma_conjunction_parts_matches_legacy b;
  match FF.ite_eq_parts a, FF.conjunction_parts b with
  | Some (c, t, u, k), Some (x, y) ->
    let at = mk_eq_expr t k in
    let au = mk_eq_expr u k in
    lemma_eq_truth_equivalent_matches_legacy at false_expr;
    lemma_eq_truth_equivalent_matches_legacy au false_expr;
    lemma_atom_equivalent_matches_legacy au x;
    lemma_atom_equivalent_matches_legacy at x
  | _, _ -> ()

let lemma_equivalent_matches_legacy (a b:expr)
  : Lemma (FF.equivalent a b == LegacyFF.equivalent a b) =
  lemma_term_equivalent_matches_legacy a b;
  lemma_eq_eq_equivalent_matches_legacy a b;
  lemma_eq_truth_equivalent_matches_legacy a b;
  lemma_eq_truth_equivalent_matches_legacy b a;
  lemma_ite_eq_equivalent_matches_legacy a b

let lemma_leaf_matches_legacy (p:pos) (tbl:list expr) (v:nat -> int) (e:expr)
  : Lemma (FF.leaf p tbl v e == LegacyFF.leaf p tbl v e) =
  lemma_index_of_matches_legacy e tbl

let rec lemma_sum_mod_matches_legacy (p:pos) (xs:list int)
  : Lemma (FF.sum_mod p xs == LegacyFF.sum_mod p xs) (decreases xs) =
  match xs with
  | [] -> ()
  | _ :: rest -> lemma_sum_mod_matches_legacy p rest

let rec lemma_product_mod_matches_legacy (p:pos) (xs:list int)
  : Lemma (FF.product_mod p xs == LegacyFF.prod_mod p xs) (decreases xs) =
  match xs with
  | [] -> ()
  | _ :: rest -> lemma_product_mod_matches_legacy p rest

let rec lemma_bitsum_mod_matches_legacy (p:pos) (w:int) (xs:list int)
  : Lemma (FF.bitsum_mod p w xs == LegacyFF.bitsum_mod p w xs)
          (decreases xs) =
  match xs with
  | [] -> ()
  | _ :: rest -> lemma_bitsum_mod_matches_legacy p (2 * w) rest

let lemma_calculate_matches_legacy (p:pos) (op:decl_kind) (xs:list int)
  : Lemma (FF.calculate p op xs == LegacyFF.calculate p op xs) =
  if op == FF.op_ff_add then lemma_sum_mod_matches_legacy p xs
  else if op == FF.op_ff_mul then lemma_product_mod_matches_legacy p xs
  else if op == FF.op_ff_bitsum then lemma_bitsum_mod_matches_legacy p 1 xs
  else match xs with
       | [x] -> ()
       | _ -> ()

let rec lemma_eval_ff_matches_legacy (p:pos) (tbl:list expr) (v:nat -> int) (e:expr)
  : Lemma (FF.eval_ff p tbl v e == LegacyFF.eval_ff p tbl v e)
          (decreases e) =
  match FF.numeral e with
  | Some _ -> lemma_numeral_matches_legacy e
  | None ->
    (match e with
    | App f args ->
      lemma_operation_matches_legacy f args;
      if Some? (FF.operation_at f args) then
        let (q, op) = Some?.v (FF.operation_at f args) in
        if q == p then (
          lemma_eval_ffs_matches_legacy p tbl v args;
          (match FF.eval_ffs p tbl v args with
           | Some xs -> lemma_calculate_matches_legacy p op xs
           | None -> ());
          assert (FF.eval_ff p tbl v e == LegacyFF.eval_ff p tbl v e))
        else assert (FF.eval_ff p tbl v e == LegacyFF.eval_ff p tbl v e)
      else
        (match args with
        | [c; t; u] ->
          if f == A.term_ite_decl (FF.ff_sort p) &&
             get_sort c == bool_sort && get_sort t == FF.ff_sort p &&
             get_sort u == FF.ff_sort p then (
            (lemma_eval_bool_matches_legacy p tbl v c;
             match FF.eval_bool p tbl v c with
             | Some true -> lemma_eval_ff_matches_legacy p tbl v t
             | Some false -> lemma_eval_ff_matches_legacy p tbl v u
             | None -> ());
            assert (FF.eval_ff p tbl v e == LegacyFF.eval_ff p tbl v e))
          else (
            lemma_leaf_matches_legacy p tbl v e;
            assert (FF.eval_ff p tbl v e == LegacyFF.eval_ff p tbl v e))
        | _ ->
          lemma_leaf_matches_legacy p tbl v e;
          assert (FF.eval_ff p tbl v e == LegacyFF.eval_ff p tbl v e))
    | _ ->
      lemma_leaf_matches_legacy p tbl v e;
      assert (FF.eval_ff p tbl v e == LegacyFF.eval_ff p tbl v e))

and lemma_eval_ffs_matches_legacy (p:pos) (tbl:list expr) (v:nat -> int)
                                  (args:list expr)
  : Lemma (FF.eval_ffs p tbl v args == LegacyFF.eval_ffs p tbl v args)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_eval_ff_matches_legacy p tbl v a;
    lemma_eval_ffs_matches_legacy p tbl v rest

and lemma_eval_bool_matches_legacy (p:pos) (tbl:list expr) (v:nat -> int) (e:expr)
  : Lemma (FF.eval_bool p tbl v e == LegacyFF.eval_bool p tbl v e)
          (decreases e) =
  match e with
  | App f args ->
    if get_sort e <> bool_sort then ()
    else if C.canonical_true f && args == [] then ()
    else if C.canonical_false f && args == [] then ()
    else if C.canonical_not f then
      (match args with
       | [a] -> lemma_eval_bool_matches_legacy p tbl v a
       | _ -> ())
    else if C.canonical_or f then lemma_eval_or_matches_legacy p tbl v args
    else if C.canonical_and f then lemma_eval_and_matches_legacy p tbl v args
    else if C.canonical_eq f then
      (match args with
       | [a; b] ->
         if get_sort a == FF.ff_sort p && get_sort b == FF.ff_sort p then (
           lemma_eval_ff_matches_legacy p tbl v a;
           lemma_eval_ff_matches_legacy p tbl v b)
         else if get_sort a == bool_sort && get_sort b == bool_sort then (
           lemma_eval_bool_matches_legacy p tbl v a;
           lemma_eval_bool_matches_legacy p tbl v b)
         else ()
       | _ -> ())
    else ()
  | _ -> ()

and lemma_eval_or_matches_legacy (p:pos) (tbl:list expr) (v:nat -> int)
                                 (args:list expr)
  : Lemma (FF.eval_or p tbl v args == LegacyFF.eval_or p tbl v args)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_eval_bool_matches_legacy p tbl v a;
    lemma_eval_or_matches_legacy p tbl v rest

and lemma_eval_and_matches_legacy (p:pos) (tbl:list expr) (v:nat -> int)
                                  (args:list expr)
  : Lemma (FF.eval_and p tbl v args == LegacyFF.eval_and p tbl v args)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_eval_bool_matches_legacy p tbl v a;
    lemma_eval_and_matches_legacy p tbl v rest

let lemma_leaf_congruent (p:pos) (tbl:list expr) (v1 v2:nat -> int) (e:expr)
  : Lemma (requires (forall (k:nat). v1 k == v2 k))
          (ensures FF.leaf p tbl v1 e == FF.leaf p tbl v2 e) =
  match FF.index_of e tbl with
  | Some k -> assert (v1 k == v2 k)
  | None -> ()

let rec lemma_eval_ff_congruent (p:pos) (tbl:list expr) (v1 v2:nat -> int) (e:expr)
  : Lemma (requires (forall (k:nat). v1 k == v2 k))
          (ensures FF.eval_ff p tbl v1 e == FF.eval_ff p tbl v2 e)
          (decreases e) =
  match FF.numeral e with
  | Some _ -> ()
  | None ->
    (match e with
     | App f args ->
       if Some? (FF.operation_at f args) then
         let (q, _) = Some?.v (FF.operation_at f args) in
         if q == p then (
           lemma_eval_ffs_congruent p tbl v1 v2 args;
           assert (FF.eval_ff p tbl v1 e == FF.eval_ff p tbl v2 e))
         else assert (FF.eval_ff p tbl v1 e == FF.eval_ff p tbl v2 e)
       else
         (match args with
          | [c; t; u] ->
            if f == A.term_ite_decl (FF.ff_sort p) &&
               get_sort c == bool_sort && get_sort t == FF.ff_sort p &&
               get_sort u == FF.ff_sort p then (
              lemma_eval_bool_congruent p tbl v1 v2 c;
              match FF.eval_bool p tbl v1 c with
              | Some true -> lemma_eval_ff_congruent p tbl v1 v2 t
              | Some false -> lemma_eval_ff_congruent p tbl v1 v2 u
              | None -> ();
              assert (FF.eval_ff p tbl v1 e == FF.eval_ff p tbl v2 e))
            else (
              lemma_leaf_congruent p tbl v1 v2 e;
              assert (FF.eval_ff p tbl v1 e == FF.eval_ff p tbl v2 e))
          | _ ->
            lemma_leaf_congruent p tbl v1 v2 e;
            assert (FF.eval_ff p tbl v1 e == FF.eval_ff p tbl v2 e))
     | _ ->
       lemma_leaf_congruent p tbl v1 v2 e;
       assert (FF.eval_ff p tbl v1 e == FF.eval_ff p tbl v2 e))

and lemma_eval_ffs_congruent (p:pos) (tbl:list expr) (v1 v2:nat -> int)
                             (args:list expr)
  : Lemma (requires (forall (k:nat). v1 k == v2 k))
          (ensures FF.eval_ffs p tbl v1 args == FF.eval_ffs p tbl v2 args)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_eval_ff_congruent p tbl v1 v2 a;
    lemma_eval_ffs_congruent p tbl v1 v2 rest

and lemma_eval_bool_congruent (p:pos) (tbl:list expr) (v1 v2:nat -> int) (e:expr)
  : Lemma (requires (forall (k:nat). v1 k == v2 k))
          (ensures FF.eval_bool p tbl v1 e == FF.eval_bool p tbl v2 e)
          (decreases e) =
  match e with
  | App f args ->
    if get_sort e <> bool_sort then ()
    else if C.canonical_true f && args == [] then ()
    else if C.canonical_false f && args == [] then ()
    else if C.canonical_not f then
      (match args with
       | [a] -> lemma_eval_bool_congruent p tbl v1 v2 a
       | _ -> ())
    else if C.canonical_or f then lemma_eval_or_congruent p tbl v1 v2 args
    else if C.canonical_and f then lemma_eval_and_congruent p tbl v1 v2 args
    else if C.canonical_eq f then
      (match args with
       | [a; b] ->
         if get_sort a == FF.ff_sort p && get_sort b == FF.ff_sort p then (
           lemma_eval_ff_congruent p tbl v1 v2 a;
           lemma_eval_ff_congruent p tbl v1 v2 b)
         else if get_sort a == bool_sort && get_sort b == bool_sort then (
           lemma_eval_bool_congruent p tbl v1 v2 a;
           lemma_eval_bool_congruent p tbl v1 v2 b)
         else ()
       | _ -> ())
    else ()
  | _ -> ()

and lemma_eval_or_congruent (p:pos) (tbl:list expr) (v1 v2:nat -> int)
                            (args:list expr)
  : Lemma (requires (forall (k:nat). v1 k == v2 k))
          (ensures FF.eval_or p tbl v1 args == FF.eval_or p tbl v2 args)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_eval_bool_congruent p tbl v1 v2 a;
    lemma_eval_or_congruent p tbl v1 v2 rest

and lemma_eval_and_congruent (p:pos) (tbl:list expr) (v1 v2:nat -> int)
                             (args:list expr)
  : Lemma (requires (forall (k:nat). v1 k == v2 k))
          (ensures FF.eval_and p tbl v1 args == FF.eval_and p tbl v2 args)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_eval_bool_congruent p tbl v1 v2 a;
    lemma_eval_and_congruent p tbl v1 v2 rest

let lemma_add_leaf_matches_legacy (tbl:list expr) (e:expr)
  : Lemma (FF.add_leaf tbl e == LegacyFF.add_leaf tbl e) = ()

let rec lemma_leaves_matches_legacy (p:int) (tbl:list expr) (e:expr)
  : Lemma (FF.leaves p tbl e == LegacyFF.leaves p tbl e)
          (decreases e) =
  match FF.numeral e with
  | Some _ -> lemma_numeral_matches_legacy e
  | None ->
    match e with
    | App f args ->
      lemma_operation_matches_legacy f args;
      if Some? (FF.operation_at f args) ||
         get_sort e <> FF.ff_sort p || Some? (A.ite_parts e)
      then lemma_leaves_args_matches_legacy p tbl args
      else lemma_add_leaf_matches_legacy tbl e
    | _ -> lemma_add_leaf_matches_legacy tbl e

and lemma_leaves_args_matches_legacy (p:int) (tbl args:list expr)
  : Lemma (FF.leaves_args p tbl args == LegacyFF.leaves_args p tbl args)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_leaves_matches_legacy p tbl a;
    lemma_leaves_args_matches_legacy p (FF.leaves p tbl a) rest

let rec lemma_within_budget_matches_legacy (p:int) (n:nat) (acc:int)
  : Lemma (FF.within_budget p n acc == LegacyFF.within_budget p n acc)
          (decreases n) =
  assert (FF.max_assignments == LegacyFF.max_assignments);
  if acc > FF.max_assignments then ()
  else if n == 0 then ()
  else lemma_within_budget_matches_legacy p (n - 1) (acc * p)

let lemma_vector_value_pointwise_matches_legacy (r:list int)
  : Lemma (forall (k:nat).
             FF.vector_value r k == LegacyFF.vector_value r k) =
  let aux (k:nat)
    : Lemma (FF.vector_value r k == LegacyFF.vector_value r k) = ()
  in FStar.Classical.forall_intro aux

let lemma_clause_true_matches_legacy (p:pos) (tbl:list expr) (e:expr) (r:list int)
  : Lemma (FF.clause_true p tbl e r == LegacyFF.clause_true p tbl e r) =
  let v1 = FF.vector_value r in
  let v2 = LegacyFF.vector_value r in
  lemma_vector_value_pointwise_matches_legacy r;
  lemma_eval_bool_congruent p tbl v1 v2 e;
  lemma_eval_bool_matches_legacy p tbl v2 e

let rec lemma_closed_ff_for_all_matches_legacy (p:int) (tbl:list expr)
  : Lemma (L.for_all (FF.closed_ff p) tbl ==
           L.for_all (LegacyFF.closed_ff p) tbl)
          (decreases tbl) =
  match tbl with
  | [] -> ()
  | e :: rest ->
    lemma_closed_ff_matches_legacy p e;
    lemma_closed_ff_for_all_matches_legacy p rest

let rec lemma_for_all_vectors_related (p:nat) (n:nat)
                                      (f g:list int -> bool)
  : Lemma (requires (forall (r:list int). f r == g r))
          (ensures FF.for_all_vectors p n f ==
                   LegacyFF.for_all_vectors p n g)
          (decreases %[n; 0; 0]) =
  if n == 0 then
    assert (f [] == g [])
  else
    lemma_for_all_heads_related p p (n - 1) f g

and lemma_for_all_heads_related (p:nat) (k:nat) (n:nat)
                                (f g:list int -> bool)
  : Lemma (requires (forall (r:list int). f r == g r))
          (ensures FF.for_all_heads p k n f ==
                   LegacyFF.for_all_heads p k n g)
          (decreases %[n; 1; k]) =
  if k == 0 then ()
  else (
    let h = k - 1 in
    let f' = FF.with_head f h in
    let g' = LegacyFF.with_head g h in
    let aux (r:list int) : Lemma (f' r == g' r) =
      assert (f (h :: r) == g (h :: r))
    in
    FStar.Classical.forall_intro aux;
    lemma_for_all_vectors_related p n f' g';
    lemma_for_all_heads_related p (k - 1) n f g)

unfold let exhaustive_from_modulus_sorted (m:option int) (e:expr) : GTot bool =
  match m with
  | None -> false
  | Some p ->
    if p >= 2 && D.scoped [] e && get_sort e == bool_sort then
      let tbl = FF.leaves p [] e in
      if FF.within_budget p (L.length tbl) 1 &&
         L.for_all (FF.closed_ff p) tbl
      then FF.for_all_vectors p (L.length tbl) (FF.clause_true p tbl e)
      else false
    else false

unfold let exhaustive_from_modulus_legacy (m:option int) (e:expr) : GTot bool =
  match m with
  | None -> false
  | Some p ->
    if p >= 2 && D.scoped [] e && get_sort e == bool_sort then
      let tbl = LegacyFF.leaves p [] e in
      if LegacyFF.within_budget p (L.length tbl) 1 &&
         L.for_all (LegacyFF.closed_ff p) tbl
      then LegacyFF.for_all_vectors p (L.length tbl)
             (LegacyFF.clause_true p tbl e)
      else false
    else false

let lemma_exhaustive_from_modulus_matches_legacy (m:option int) (e:expr)
  : Lemma (exhaustive_from_modulus_sorted m e ==
           exhaustive_from_modulus_legacy m e) =
  match m with
  | None -> assert (exhaustive_from_modulus_sorted m e ==
                    exhaustive_from_modulus_legacy m e)
  | Some p ->
    if p >= 2 && D.scoped [] e && get_sort e == bool_sort then (
      let tbl = FF.leaves p [] e in
      lemma_leaves_matches_legacy p [] e;
      assert (LegacyFF.leaves p [] e == tbl);
      lemma_within_budget_matches_legacy p (L.length tbl) 1;
      lemma_closed_ff_for_all_matches_legacy p tbl;
      let gate = FF.within_budget p (L.length tbl) 1 &&
                 L.for_all (FF.closed_ff p) tbl in
      assert (gate ==
              (LegacyFF.within_budget p (L.length tbl) 1 &&
               L.for_all (LegacyFF.closed_ff p) tbl));
      match gate with
      | true ->
        let aux (r:list int)
          : Lemma (FF.clause_true p tbl e r ==
                   LegacyFF.clause_true p tbl e r) =
          lemma_clause_true_matches_legacy p tbl e r
        in
        FStar.Classical.forall_intro aux;
        lemma_for_all_vectors_related p (L.length tbl)
          (FF.clause_true p tbl e) (LegacyFF.clause_true p tbl e);
        assert (FF.for_all_vectors p (L.length tbl)
                  (FF.clause_true p tbl e) ==
                LegacyFF.for_all_vectors p (L.length tbl)
                  (LegacyFF.clause_true p tbl e));
        assert (exhaustive_from_modulus_sorted m e ==
                (if gate then
                   FF.for_all_vectors p (L.length tbl)
                     (FF.clause_true p tbl e)
                 else false));
        assert (exhaustive_from_modulus_legacy m e ==
                (if gate then
                   LegacyFF.for_all_vectors p (L.length tbl)
                     (LegacyFF.clause_true p tbl e)
                 else false));
        assert (exhaustive_from_modulus_sorted m e ==
                exhaustive_from_modulus_legacy m e)
      | false ->
        assert (exhaustive_from_modulus_sorted m e ==
                exhaustive_from_modulus_legacy m e))
    else
      assert (exhaustive_from_modulus_sorted m e ==
              exhaustive_from_modulus_legacy m e)

let lemma_exhaustive_clause_decompose_sorted (e:expr)
  : Lemma (FF.exhaustive_clause e ==
           exhaustive_from_modulus_sorted (FF.find_modulus e) e) =
  reveal_opaque (`%FF.exhaustive_clause) (FF.exhaustive_clause e)

let lemma_exhaustive_clause_decompose_legacy (e:expr)
  : Lemma (LegacyFF.exhaustive_clause e ==
           exhaustive_from_modulus_legacy (LegacyFF.find_modulus e) e) =
  reveal_opaque (`%LegacyFF.exhaustive_clause)
    (LegacyFF.exhaustive_clause e)

let lemma_exhaustive_clause_matches_legacy (e:expr)
  : Lemma (FF.exhaustive_clause e == LegacyFF.exhaustive_clause e) =
  lemma_exhaustive_clause_decompose_sorted e;
  lemma_exhaustive_clause_decompose_legacy e;
  lemma_find_modulus_matches_legacy e;
  lemma_exhaustive_from_modulus_matches_legacy (FF.find_modulus e) e

let lemma_premise_parts_matches_legacy (p:int) (l:expr)
  : Lemma (FF.premise_parts p l == Legacy.premise_parts p l) =
  lemma_eq_parts_matches_legacy l;
  lemma_closed_ff_matches_legacy p l

let lemma_premise_equation_matches_legacy
    (p:int) (k:nat) (l a b:expr) (st:FF.encoding) (positive:bool)
  : Lemma (
      map_option to_legacy_encoding (FF.premise_equation p k l a b st positive) ==
      Legacy.premise_equation p k l a b (to_legacy_encoding st) positive) =
  if positive then (
    lemma_term_poly_matches_legacy p st.terms a;
    lemma_term_poly_matches_legacy p st.terms b;
    match FF.term_poly p st.terms a, FF.term_poly p st.terms b with
    | Some qa, Some qb ->
      lemma_pscale_matches_legacy (-1) qb;
      lemma_padd_matches_legacy qa (FF.pscale (-1) qb);
      lemma_push_matches_legacy st (FF.padd qa (FF.pscale (-1) qb), FF.Premise k l)
    | _, _ -> ())
  else (
    lemma_allocate_matches_legacy st l;
    if Some? (FF.allocate st l) then
      lemma_push_matches_legacy (Some?.v (FF.allocate st l)) ([], FF.Witness))

let rec lemma_visit_matches_legacy (p:int) (st:FF.encoding) (t:expr)
  : Lemma (map_option to_legacy_encoding (FF.visit p st t) ==
           Legacy.visit p (to_legacy_encoding st) t)
          (decreases t) =
  match FF.numeral t with
  | Some _ -> lemma_numeral_matches_legacy t
  | None ->
    lemma_index_of_matches_legacy t st.terms;
    if Some? (FF.index_of t st.terms) then ()
    else if get_sort t <> FF.ff_sort p then ()
    else
      match t with
      | App f args ->
        lemma_operation_matches_legacy f args;
        let op_result = FF.operation_at f args in
        if Some? op_result then
          let (q, op) = Some?.v op_result in
          assert (LegacyFF.operation f args == Some (q, op));
          if q <> p then assert_norm (
            map_option to_legacy_encoding (FF.visit p st t) ==
            Legacy.visit p (to_legacy_encoding st) t)
          else
            let visit_result = FF.visit_args p st args in
            lemma_visit_args_matches_legacy p st args;
            if Some? visit_result then
              let st1 = Some?.v visit_result in
              let old_st1 = Some?.v (Legacy.visit_args p (to_legacy_encoding st) args) in
              assert (to_legacy_encoding st1 == old_st1);
              lemma_term_polys_matches_legacy p st1.terms args;
              let polys_result = FF.term_polys p st1.terms args in
              if Some? polys_result then
                let qs = Some?.v polys_result in
                lemma_combine_matches_legacy op qs;
                let combined = FF.combine op qs in
                if Some? combined then
                  lemma_define_matches_legacy st1 t (Some?.v combined)
                else ()
              else ()
            else
              assert (Legacy.visit_args p (to_legacy_encoding st) args == None)
        else
          assert (LegacyFF.operation f args == None);
          lemma_allocate_matches_legacy st t
      | _ -> ()

and lemma_visit_args_matches_legacy (p:int) (st:FF.encoding) (args:list expr)
  : Lemma (map_option to_legacy_encoding (FF.visit_args p st args) ==
           Legacy.visit_args p (to_legacy_encoding st) args)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_visit_args_matches_legacy p st rest;
    match FF.visit_args p st rest with
    | None -> ()
    | Some st1 -> lemma_visit_matches_legacy p st1 a

let rec lemma_bind_matches_legacy (p:int) (k:nat) (st:FF.encoding) (ps:list expr)
  : Lemma (map_option to_legacy_encoding (FF.bind p k st ps) ==
           Legacy.bind p k (to_legacy_encoding st) ps)
          (decreases ps) =
  match ps with
  | [] -> ()
  | l :: rest ->
    lemma_premise_parts_matches_legacy p l;
    let parts = FF.premise_parts p l in
    if Some? parts then
      let (positive, a, b) = Some?.v parts in
      assert (Legacy.premise_parts p l == Some (positive, a, b));
      let first = FF.visit p st a in
      lemma_visit_matches_legacy p st a;
      if Some? first then
        let st1 = Some?.v first in
        let old_st1 = Some?.v (Legacy.visit p (to_legacy_encoding st) a) in
        assert (to_legacy_encoding st1 == old_st1);
        let second = FF.visit p st1 b in
        lemma_visit_matches_legacy p st1 b;
        if Some? second then
          let st2 = Some?.v second in
          let old_st2 = Some?.v (Legacy.visit p (to_legacy_encoding st1) b) in
          assert (to_legacy_encoding st2 == old_st2);
          let added = FF.premise_equation p k l a b st2 positive in
          lemma_premise_equation_matches_legacy p k l a b st2 positive;
          if Some? added then
            let st3 = Some?.v added in
            let old_st3 =
              Some?.v (Legacy.premise_equation p k l a b (to_legacy_encoding st2) positive) in
            assert (to_legacy_encoding st3 == old_st3);
            lemma_bind_matches_legacy p (k + 1) st3 rest
          else
            assert (Legacy.premise_equation p k l a b
                      (to_legacy_encoding st2) positive == None)
        else
          assert (Legacy.visit p (to_legacy_encoding st1) b == None)
      else
        assert (Legacy.visit p (to_legacy_encoding st) a == None)
    else
      assert (Legacy.premise_parts p l == None)

let lemma_step_matches_legacy
    (p:pos) (nvars:nat)
    (eqs:IX.index_tree FF.equation)
    (old_eqs:IX.index_tree (LegacyFF.poly & Legacy.origin))
    (sup:IX.index_tree bool) (old_sup:IX.index_tree bool)
    (lits:list expr) (r:FF.replay) (old_r:Legacy.replay)
    (n:FF.pac_node)
  : Lemma (requires equations_tree_related eqs old_eqs /\
                    bool_tree_related sup old_sup /\ replay_related r old_r)
          (ensures replay_options_related
                     (FF.step p nvars eqs sup lits r n)
                     (Legacy.step p nvars old_eqs old_sup lits old_r (to_legacy_node n))) =
  match n with
  | FF.PacInput j ->
    if j < 0 then ()
    else (
      lemma_equation_tree_get_related eqs old_eqs j;
      let found = IX.index_get eqs j in
      if Some? found then
        let (q, o) = Some?.v found in
        let old_found = IX.index_get old_eqs j in
        assert (Some? old_found);
        let (old_q, old_o) = Some?.v old_found in
        assert (to_legacy_equation (q, o) == (old_q, old_o));
        assert (q == old_q /\ to_legacy_origin o == old_o);
        match o with
        | FF.Definition ->
          assert (old_o == Legacy.Definition);
          lemma_size_matches_legacy q;
          if r.work + FF.poly_size q > FF.max_work then ()
          else lemma_record_matches_legacy p r old_r (FF.poly_size q) q old_q
                 r.used old_r.used
        | FF.Premise k lit ->
          assert (old_o == Legacy.Premise k lit);
          lemma_bool_tree_get_related sup old_sup k;
          lemma_negated_in_matches_legacy lit lits;
          lemma_size_matches_legacy q;
          if IX.index_get sup k == Some true && FF.negated_in lit lits &&
             r.work + FF.poly_size q <= FF.max_work then (
            lemma_bool_tree_put_related r.used old_r.used k true true;
            lemma_record_matches_legacy p r old_r (FF.poly_size q) q old_q
              (IX.index_put r.used k true) (IX.index_put old_r.used k true))
        | FF.Witness -> ()
      else ())
  | FF.PacAdd a b ->
    lemma_earlier_matches_legacy r old_r a;
    lemma_earlier_matches_legacy r old_r b;
    let qa = FF.earlier r a in
    let qb = FF.earlier r b in
    if Some? qa && Some? qb then
      let pa = Some?.v qa in
      let pb = Some?.v qb in
      let cost = FF.poly_size pa + FF.poly_size pb in
      lemma_size_matches_legacy pa;
      lemma_size_matches_legacy pb;
      if cost <= FF.max_poly_size && r.work + cost <= FF.max_work then (
        lemma_padd_matches_legacy pa pb;
        lemma_record_matches_legacy p r old_r cost (FF.padd pa pb)
          (LegacyFF.padd pa pb) r.used old_r.used)
  | FF.PacMul source c fs ->
    lemma_earlier_matches_legacy r old_r source;
    lemma_numeral_matches_legacy c;
    lemma_variables_matches_legacy nvars 0 fs;
    let source_poly = FF.earlier r source in
    let coefficient = FF.numeral c in
    let factors = FF.variables nvars 0 fs in
    if Some? source_poly && Some? coefficient && Some? factors then
      let q = Some?.v source_poly in
      let (pc, k) = Some?.v coefficient in
      let vs = Some?.v factors in
      if L.length q > 0 && L.length vs > 0 then
        M.lemma_mul_pos_pos_is_pos (L.length q) (L.length vs);
      let cost:nat = FF.poly_size q + L.length q * L.length vs in
      lemma_size_matches_legacy q;
      if pc == p && cost <= FF.max_poly_size && r.work + cost <= FF.max_work then (
        lemma_scale_mono_matches_legacy vs k q;
        lemma_record_matches_legacy p r old_r cost (FF.scale_mono vs k q)
          (Legacy.scale_mono vs k q) r.used old_r.used)

let rec lemma_replay_nodes_matches_legacy
    (p:pos) (nvars:nat)
    (eqs:IX.index_tree FF.equation)
    (old_eqs:IX.index_tree (LegacyFF.poly & Legacy.origin))
    (sup:IX.index_tree bool) (old_sup:IX.index_tree bool)
    (lits:list expr) (r:FF.replay) (old_r:Legacy.replay)
    (ns:list FF.pac_node)
  : Lemma (requires equations_tree_related eqs old_eqs /\
                    bool_tree_related sup old_sup /\ replay_related r old_r)
          (ensures replay_options_related
                     (FF.replay_nodes p nvars eqs sup lits r ns)
                     (Legacy.replay_nodes p nvars old_eqs old_sup lits old_r
                       (to_legacy_nodes ns)))
          (decreases ns) =
  match ns with
  | [] -> ()
  | n :: rest ->
    lemma_step_matches_legacy p nvars eqs old_eqs sup old_sup lits r old_r n;
    let next = FF.step p nvars eqs sup lits r n in
    if Some? next then
      let r' = Some?.v next in
      let old_r' =
        Some?.v (Legacy.step p nvars old_eqs old_sup lits old_r (to_legacy_node n)) in
      assert (replay_related r' old_r');
      lemma_replay_nodes_matches_legacy p nvars eqs old_eqs sup old_sup
        lits r' old_r' rest
    else
      assert (Legacy.step p nvars old_eqs old_sup lits old_r (to_legacy_node n) == None)

let rec lemma_all_used_related
    (new_used:IX.index_tree bool) (old_used:IX.index_tree bool) (s:list int)
  : Lemma (requires bool_tree_related new_used old_used)
          (ensures FF.all_used new_used s == Legacy.all_used old_used s)
          (decreases s) =
  match s with
  | [] -> ()
  | k :: rest ->
    if k >= 0 then (
      lemma_bool_tree_get_related new_used old_used k;
      lemma_all_used_related new_used old_used rest)

let lemma_checker_acceptance_matches_legacy (c:FF.certificate) (e:expr)
  : Lemma (FF.check c e == Legacy.check (to_legacy_certificate c) e) =
  let n = L.length c.pac_premises in
  lemma_to_legacy_nodes_length c.pac_nodes;
  assert (FF.max_premises == Legacy.max_premises /\
          FF.max_nodes == Legacy.max_nodes /\
          FF.max_variables == Legacy.max_variables /\
          FF.max_equations == Legacy.max_equations /\
          FF.max_poly_size == Legacy.max_poly_size /\
          FF.max_work == Legacy.max_work);
  if n == 0 || n > FF.max_premises || L.length c.pac_nodes > FF.max_nodes then ()
  else (
    lemma_find_modulus_args_matches_legacy c.pac_premises;
    let modulus = FF.find_modulus_args c.pac_premises in
    if Some? modulus then
      let p = Some?.v modulus in
      if p < 2 then ()
      else (
        let binding = FF.bind p 0 FF.empty_encoding c.pac_premises in
        let old_binding =
          Legacy.bind p 0 Legacy.empty_encoding c.pac_premises in
        lemma_bind_matches_legacy p 0 FF.empty_encoding c.pac_premises;
        if Some? binding then (
          let st = Some?.v binding in
          let old_st = Some?.v old_binding in
          assert (to_legacy_encoding st == old_st);
          let support = FF.support_tree n (-1) IX.Empty c.pac_support in
          let old_support =
            Legacy.support_tree n (-1) IX.Empty c.pac_support in
          lemma_support_tree_related n (-1) IX.Empty IX.Empty c.pac_support;
          if Some? support then (
            let sup = Some?.v support in
            let old_sup = Some?.v old_support in
            assert (bool_tree_related sup old_sup);
            assert (to_legacy_equations st.equations == old_st.equations);
            lemma_to_legacy_equations_length st.equations;
            assert (L.length st.equations == L.length old_st.equations);
            let eqs = FF.index_equations IX.Empty
                        (L.length st.equations - 1) st.equations in
            let old_eqs = Legacy.index_equations IX.Empty
                            (L.length old_st.equations - 1) old_st.equations in
            lemma_index_equations_related IX.Empty IX.Empty
              (L.length st.equations - 1) st.equations;
            assert (equations_tree_related eqs old_eqs);
            let lits = FF.clause_literals e in
            lemma_clause_literals_matches_legacy e;
            lemma_initial_replay_matches_legacy ();
            let result = FF.replay_nodes p (L.length st.terms) eqs sup lits
                           FF.initial_replay c.pac_nodes in
            let old_result =
              Legacy.replay_nodes p (L.length old_st.terms) old_eqs old_sup
                lits Legacy.initial_replay (to_legacy_nodes c.pac_nodes) in
            lemma_replay_nodes_matches_legacy p (L.length st.terms)
              eqs old_eqs sup old_sup lits FF.initial_replay Legacy.initial_replay
              c.pac_nodes;
            if Some? result then (
              let r = Some?.v result in
              let old_r = Some?.v old_result in
              assert (replay_related r old_r);
              lemma_unit_root_matches_legacy r old_r c.pac_root;
              lemma_all_used_related r.used old_r.used c.pac_support)
            else
              assert (old_result == None))
          else
            assert (old_support == None))
        else
          assert (old_binding == None))
    else
      assert (LegacyFF.find_modulus_args c.pac_premises == None))
#pop-options

let rec lemma_shared_nodes (ns:list FF.pac_node)
  : Lemma (ensures to_legacy_nodes ns == ns) (decreases ns) =
  match ns with
  | [] -> ()
  | n :: rest ->
    (match n with
     | FF.PacInput _ -> ()
     | FF.PacAdd _ _ -> ()
     | FF.PacMul _ _ _ -> ());
    lemma_shared_nodes rest

let lemma_shared_certificate_acceptance (c:FF.certificate) (e:expr)
  : Lemma (FF.check c e == Legacy.check c e) =
  lemma_shared_nodes c.pac_nodes;
  lemma_checker_acceptance_matches_legacy c e
