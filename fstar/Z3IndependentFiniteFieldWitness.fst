module Z3IndependentFiniteFieldWitness

open Z3AstTheory
module E = FStar.Math.Euclid
module M = FStar.Math.Lemmas
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module D = Z3ExprScope
module C = Z3CanonicalOps
module R = Z3ClauseSyntax
module PT = Z3ProofTheory
module FF = Z3SortedFiniteField
module SS = Z3SortedSemantics
module Prime = Z3IndependentFiniteFieldPrime
module L = FStar.List.Tot
module IX = Z3ProofIndex

#push-options "--fuel 8 --ifuel 4"
let rec lemma_complementary_in (#base:sort -> Type0) (schema:S.checked_schema)
  (p:pos) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (l:expr) (lits:list expr)
  : Lemma (requires D.scoped_args [] lits /\
                    FF.none_true schema p m rho lits /\ complementary_in l lits)
          (ensures SS.truth_at schema m.FF.booleans m.FF.scalar_model
                    (FF.override schema p m) [] rho l)
          (decreases lits) =
  match lits with
  | [] -> ()
  | x :: rest ->
    if PT.is_not x == Some l then
      FF.lemma_negated_in schema p m rho l lits
    else if PT.is_not l == Some x && get_sort x == bool_sort then
      (match l with
       | App f [a] ->
         assert (a == x);
         assert (C.canonical_not f);
         assert (SS.classify f == SS.Negation);
         FF.lemma_negation_at schema p m rho f a
       | _ -> ())
    else lemma_complementary_in schema p m rho l rest
#pop-options

let slot (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (e:expr{D.scoped [] e}) : GTot int =
  match FF.premise_parts p e with
  | Some (false, a, b) ->
    FF.lemma_premise_parts_wf p e false a b;
    Prime.witness p (FF.residue schema p m rho a) (FF.residue schema p m rho b)
  | _ -> FF.residue schema p m rho e

let lemma_field_slot (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (e:expr{D.scoped [] e /\ get_sort e == FF.ff_sort p})
  : Lemma (slot schema p m rho e == FF.residue schema p m rho e) =
  match FF.premise_parts p e with
  | Some (false, a, b) -> FF.lemma_premise_parts_wf p e false a b
  | _ -> ()

#push-options "--fuel 8 --ifuel 4"
let lemma_witness_slot (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (l:expr{D.scoped [] l}) (a:expr{D.scoped [] a}) (b:expr{D.scoped [] b})
  : Lemma (requires FF.premise_parts p l == Some (false, a, b) /\
                    FF.truth_at schema p m [] rho l)
          (ensures (slot schema p m rho l *
                    (FF.residue schema p m rho a - FF.residue schema p m rho b) - 1) % p == 0) =
  FF.lemma_premise_parts_wf p l false a b;
  match l with
  | App f [atom] ->
    assert (PT.is_not l == Some atom);
    assert (FF.eq_parts atom == Some (a, b));
    FF.lemma_eq_parts_normalized atom a b;
    assert (C.canonical_not f);
    assert (SS.classify f == SS.Negation);
    FF.lemma_negation_at schema p m rho f atom;
    FF.lemma_truth_field_eq schema p m rho a b;
    let av = FF.residue schema p m rho a in
    let bv = FF.residue schema p m rho b in
    m.FF.project_range (FF.evaluate_at schema p m [] rho a);
    m.FF.project_range (FF.evaluate_at schema p m [] rho b);
    M.small_mod av p;
    M.small_mod bv p;
    if (av - bv) % p == 0 then FF.lemma_diff_mod p av bv
  | _ -> ()
#pop-options

let rec values (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (tbl:list expr{D.scoped_args [] tbl}) : GTot (list int) (decreases tbl) =
  match tbl with
  | [] -> []
  | e :: rest -> slot schema p m rho e :: values schema p m rho rest

let rec lemma_values_length (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (tbl:list expr{D.scoped_args [] tbl})
  : Lemma (ensures L.length (values schema p m rho tbl) == L.length tbl)
          (decreases tbl) =
  match tbl with
  | [] -> ()
  | _ :: rest -> lemma_values_length schema p m rho rest

let rec lemma_values_index (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (tbl:list expr{D.scoped_args [] tbl}) (k:nat)
  : Lemma (requires k < L.length tbl /\
                    k < L.length (values schema p m rho tbl) /\
                    D.scoped [] (L.index tbl k))
          (ensures L.index (values schema p m rho tbl) k ==
                   slot schema p m rho (L.index tbl k))
          (decreases tbl) =
  lemma_values_length schema p m rho tbl;
  FF.lemma_scoped_args_index tbl k;
  match tbl with
  | [] -> ()
  | _ :: rest ->
    if k > 0 then (
      FF.lemma_scoped_args_index rest (k - 1);
      lemma_values_length schema p m rho rest;
      lemma_values_index schema p m rho rest (k - 1))

let valuation (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (tbl:list expr{D.scoped_args [] tbl}) : GTot (nat -> int) =
  let vs = values schema p m rho tbl in
  fun k -> if k < L.length vs then L.index vs k else 0

let lemma_valuation_field (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (tbl:list expr{D.scoped_args [] tbl}) (k:nat)
  : Lemma (requires k < L.length tbl /\ get_sort (L.index tbl k) == FF.ff_sort p)
          (ensures valuation schema p m rho tbl k == FF.valuation schema p m rho tbl k) =
  FF.lemma_scoped_args_index tbl k;
  lemma_values_length schema p m rho tbl;
  lemma_values_index schema p m rho tbl k;
  lemma_field_slot schema p m rho (L.index tbl k);
  FF.lemma_valuation_index schema p m rho tbl k

let lemma_valuation_witness (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (tbl:list expr{D.scoped_args [] tbl}) (k:nat)
  (a:expr{D.scoped [] a}) (b:expr{D.scoped [] b})
  : Lemma (requires k < L.length tbl /\
                    FF.premise_parts p (L.index tbl k) == Some (false, a, b) /\
                    FF.truth_at schema p m [] rho (L.index tbl k))
          (ensures (valuation schema p m rho tbl k *
                    (FF.residue schema p m rho a - FF.residue schema p m rho b) - 1) % p == 0) =
  FF.lemma_scoped_args_index tbl k;
  lemma_values_length schema p m rho tbl;
  lemma_values_index schema p m rho tbl k;
  lemma_witness_slot schema p m rho (L.index tbl k) a b

let lemma_term_poly (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (tbl final:list expr) (t:expr) (q:FF.poly)
  : Lemma (requires D.scoped [] t /\ get_sort t == FF.ff_sort p /\
                    D.scoped_args [] final /\ FF.prefix tbl final /\
                    FF.term_poly p tbl t == Some q)
          (ensures FF.peval (valuation schema p m rho final) q % p ==
                   FF.residue schema p m rho t) =
  let v = valuation schema p m rho final in
  let old = FF.valuation schema p m rho final in
  FF.lemma_term_poly schema p m rho tbl final t q;
  match FF.numeral t with
  | Some (_, n) ->
    FF.lemma_peval_constant v n;
    FF.lemma_peval_constant old n
  | None ->
    let k = Some?.v (FF.index_of t tbl) in
    FF.lemma_index_of t tbl k;
    FF.lemma_prefix_index tbl final k;
    lemma_valuation_field schema p m rho final k;
    FF.lemma_peval_variable v k;
    FF.lemma_peval_variable old k

let rec lemma_term_polys (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (tbl final:list expr) (args:list expr) (qs:list FF.poly)
  : Lemma (requires D.scoped_args [] args /\ FF.args_have_sort p args /\
                    D.scoped_args [] final /\ FF.prefix tbl final /\
                    FF.term_polys p tbl args == Some qs)
          (ensures FF.match_list (valuation schema p m rho final) p qs
                   (FF.expressions_residues schema p m rho args))
          (decreases args) =
  match args, qs with
  | a :: rest, q :: qs' ->
    V.lemma_sort_eq (get_sort a) (FF.ff_sort p);
    lemma_term_poly schema p m rho tbl final a q;
    lemma_term_polys schema p m rho tbl final rest qs'
  | _, _ -> ()

let lemma_definition_eval (v:nat -> int) (k:nat) (q:FF.poly)
  : Lemma (FF.peval v (FF.definition k q) == v k - FF.peval v q) =
  FF.lemma_peval_variable v k;
  FF.lemma_pscale v (-1) q;
  FF.lemma_padd v [([k], 1)] (FF.pscale (-1) q)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"
let lemma_definition (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (tbl final:list expr) (f:func_decl) (args:list expr)
  (op:decl_kind) (qs:list FF.poly) (fq:FF.poly)
  : Lemma (requires D.scoped [] (App f args) /\
                    FF.operation_at f args == Some (p, op) /\
                    D.scoped_args [] final /\ FF.prefix tbl final /\
                    L.length tbl < L.length final /\
                    L.index final (L.length tbl) == App f args /\
                    FF.term_polys p tbl args == Some qs /\ FF.combine op qs == Some fq)
          (ensures FF.peval (valuation schema p m rho final)
                    (FF.definition (L.length tbl) fq) % p == 0) =
  let v = valuation schema p m rho final in
  let k = L.length tbl in
  lemma_term_polys schema p m rho tbl final args qs;
  FF.lemma_residues_args schema p m rho args f.domain;
  FF.lemma_evaluate_operation_at schema p m [] rho f args op;
  FF.lemma_combine v p op qs (FF.expressions_residues schema p m rho args) fq;
  assert (FF.residue schema p m rho (App f args) ==
          FF.calculate p op (FF.expressions_residues schema p m rho args));
  assert (FF.peval v fq % p == FF.residue schema p m rho (App f args));
  lemma_valuation_field schema p m rho final k;
  FF.lemma_scoped_args_index final k;
  FF.lemma_valuation_index schema p m rho final k;
  assert (v k == FF.residue schema p m rho (App f args));
  lemma_definition_eval v k fq;
  assert (FF.peval v (FF.definition k fq) ==
          FF.residue schema p m rho (App f args) - FF.peval v fq);
  m.FF.project_range (FF.evaluate_at schema p m [] rho (App f args));
  M.small_mod (FF.residue schema p m rho (App f args)) p;
  FF.lemma_same_mod_diff p
    (FF.residue schema p m rho (App f args)) (FF.peval v fq)
#pop-options

let rec lemma_visit (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (st:FF.encoding) (t:expr) (st':FF.encoding) (final:list expr)
  : Lemma (requires D.scoped_args [] st.FF.terms /\ D.scoped [] t /\
                    D.scoped_args [] final /\ FF.visit p st t == Some st' /\
                    FF.prefix st'.FF.terms final)
          (ensures FF.prefix st.FF.terms st'.FF.terms /\
                   (FF.eqs_ok schema p m rho (valuation schema p m rho final) st.FF.equations ==>
                    FF.eqs_ok schema p m rho (valuation schema p m rho final) st'.FF.equations))
          (decreases t) =
  match FF.numeral t with
  | Some (_, _) -> FF.lemma_prefix_refl st.FF.terms
  | None ->
    if Some? (FF.index_of t st.FF.terms) then FF.lemma_prefix_refl st.FF.terms
    else
      match t with
      | App f args ->
        (match FF.operation_at f args with
         | Some (q, op) ->
           let st1 = Some?.v (FF.visit_args p st args) in
           let qs = Some?.v (FF.term_polys p st1.FF.terms args) in
           let fq = Some?.v (FF.combine op qs) in
           let st2 = Some?.v (FF.define st1 t fq) in
           let k = L.length st1.FF.terms in
           assert (q == p);
           FF.lemma_visit_args_scoped p st args st1;
           FF.lemma_prefix_append st1.FF.terms t;
           FF.lemma_append_last st1.FF.terms t;
           assert (st2.FF.terms == L.append st1.FF.terms [t]);
           assert (st2.FF.equations == (FF.definition k fq, FF.Definition) :: st1.FF.equations);
           assert (st' == st2);
           FF.lemma_prefix_trans st1.FF.terms st2.FF.terms final;
           FF.lemma_prefix_index st2.FF.terms final k;
           lemma_visit_args schema p m rho st args st1 final;
           FF.lemma_prefix_trans st.FF.terms st1.FF.terms st2.FF.terms;
           lemma_definition schema p m rho st1.FF.terms final f args op qs fq;
           FF.lemma_eqs_prepend schema p m rho
             (valuation schema p m rho final) (FF.definition k fq, FF.Definition) st1.FF.equations
         | None ->
           FF.lemma_prefix_append st.FF.terms t;
           assert (st'.FF.terms == L.append st.FF.terms [t]);
           assert (st'.FF.equations == st.FF.equations))
      | _ ->
        FF.lemma_prefix_append st.FF.terms t;
        assert (st'.FF.terms == L.append st.FF.terms [t]);
        assert (st'.FF.equations == st.FF.equations)

and lemma_visit_args (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (st:FF.encoding) (args:list expr) (st':FF.encoding) (final:list expr)
  : Lemma (requires D.scoped_args [] st.FF.terms /\ D.scoped_args [] args /\
                    D.scoped_args [] final /\ FF.visit_args p st args == Some st' /\
                    FF.prefix st'.FF.terms final)
          (ensures FF.prefix st.FF.terms st'.FF.terms /\
                   (FF.eqs_ok schema p m rho (valuation schema p m rho final) st.FF.equations ==>
                    FF.eqs_ok schema p m rho (valuation schema p m rho final) st'.FF.equations))
          (decreases args) =
  match args with
  | [] -> FF.lemma_prefix_refl st.FF.terms
  | a :: rest ->
    let st1 = Some?.v (FF.visit_args p st rest) in
    FF.lemma_visit_args_scoped p st rest st1;
    lemma_visit schema p m rho st1 a st' final;
    FF.lemma_prefix_trans st1.FF.terms st'.FF.terms final;
    lemma_visit_args schema p m rho st rest st1 final;
    FF.lemma_prefix_trans st.FF.terms st1.FF.terms st'.FF.terms

let lemma_witness_polynomial_eval (v:nat -> int) (k:nat) (qa qb:FF.poly)
  : Lemma (FF.peval v (witness_polynomial k qa qb) ==
           v k * (FF.peval v qa - FF.peval v qb) - 1) =
  let d = FF.padd qa (FF.pscale (-1) qb) in
  let w = [([k], 1)] in
  FF.lemma_peval_variable v k;
  FF.lemma_pscale v (-1) qb;
  FF.lemma_padd v qa (FF.pscale (-1) qb);
  FF.lemma_pmul v w d;
  FF.lemma_peval_constant v (-1);
  FF.lemma_padd v (FF.pmul w d) [([], -1)]

#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"
let lemma_witness_polynomial (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (tbl:list expr) (final:list expr{D.scoped_args [] final}) (k:nat)
  (a b:expr) (qa qb:FF.poly)
  : Lemma (requires FF.prefix tbl final /\ k < L.length final /\
                    FF.premise_parts p (L.index final k) == Some (false, a, b) /\
                    FF.truth_at schema p m [] rho (L.index final k) /\
                    FF.term_poly p tbl a == Some qa /\ FF.term_poly p tbl b == Some qb)
          (ensures FF.peval (valuation schema p m rho final) (witness_polynomial k qa qb) % p == 0) =
  let v = valuation schema p m rho final in
  FF.lemma_scoped_args_index final k;
  FF.lemma_premise_parts_wf p (L.index final k) false a b;
  lemma_term_poly schema p m rho tbl final a qa;
  lemma_term_poly schema p m rho tbl final b qb;
  lemma_valuation_witness schema p m rho final k a b;
  lemma_witness_polynomial_eval v k qa qb;
  let av = FF.residue schema p m rho a in
  let bv = FF.residue schema p m rho b in
  m.FF.project_range (FF.evaluate_at schema p m [] rho a);
  m.FF.project_range (FF.evaluate_at schema p m [] rho b);
  M.small_mod av p;
  M.small_mod bv p;
  M.lemma_mod_sub_distr 0 (FF.peval v qb) p;
  M.lemma_mod_sub_distr 0 bv p;
  FF.lemma_add_cong p (FF.peval v qa) (0 - FF.peval v qb) av (0 - bv);
  FF.lemma_mul_cong p (v k) (FF.peval v qa - FF.peval v qb) (v k) (av - bv);
  FF.lemma_add_cong p (v k * (FF.peval v qa - FF.peval v qb)) (-1)
                       (v k * (av - bv)) (-1)
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"
let lemma_premise_equation (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (k:nat) (l a b:expr) (st st':FF.encoding) (positive:bool) (final:list expr)
  : Lemma (requires D.scoped_args [] st.FF.terms /\ D.scoped_args [] final /\
                    D.scoped [] l /\ FF.premise_parts p l == Some (positive, a, b) /\
                    premise_equation p k l a b st positive == Some st' /\
                    FF.prefix st'.FF.terms final)
          (ensures FF.prefix st.FF.terms st'.FF.terms /\
                   (FF.eqs_ok schema p m rho (valuation schema p m rho final) st.FF.equations ==>
                    FF.eqs_ok schema p m rho (valuation schema p m rho final) st'.FF.equations)) =
  FF.lemma_premise_parts_wf p l positive a b;
  let qa = Some?.v (FF.term_poly p st.FF.terms a) in
  let qb = Some?.v (FF.term_poly p st.FF.terms b) in
  let v = valuation schema p m rho final in
  if positive then (
    let q = FF.padd qa (FF.pscale (-1) qb) in
    assert (st'.FF.terms == st.FF.terms);
    assert (st'.FF.equations == (q, FF.Premise k l) :: st.FF.equations);
    FF.lemma_prefix_refl st.FF.terms;
    let aux () : Lemma
        (requires FF.truth_at schema p m [] rho l)
        (ensures FF.peval v q % p == 0) =
      lemma_term_poly schema p m rho st.FF.terms final a qa;
      lemma_term_poly schema p m rho st.FF.terms final b qb;
      FF.lemma_truth_positive_premise schema p m rho l a b;
      FF.lemma_pscale v (-1) qb;
      FF.lemma_padd v qa (FF.pscale (-1) qb);
      FF.lemma_same_mod_diff p (FF.peval v qa) (FF.peval v qb) in
    FStar.Classical.move_requires aux ();
    FF.lemma_eqs_prepend schema p m rho v (q, FF.Premise k l) st.FF.equations)
  else (
    let j = L.length st.FF.terms in
    let q = witness_polynomial j qa qb in
    assert (st'.FF.terms == L.append st.FF.terms [l]);
    assert (st'.FF.equations == (q, FF.Premise k l) :: st.FF.equations);
    FF.lemma_prefix_append st.FF.terms l;
    FF.lemma_append_last st.FF.terms l;
    FF.lemma_prefix_index st'.FF.terms final j;
    FF.lemma_prefix_trans st.FF.terms st'.FF.terms final;
    let aux () : Lemma
        (requires FF.truth_at schema p m [] rho l)
        (ensures FF.peval v q % p == 0) =
      lemma_witness_polynomial schema p m rho st.FF.terms final j a b qa qb in
    FStar.Classical.move_requires aux ();
    FF.lemma_eqs_prepend schema p m rho v (q, FF.Premise k l) st.FF.equations)
#pop-options

let rec lemma_bind_scoped (p:int) (k:nat) (st:FF.encoding) (ps:list expr) (st':FF.encoding)
  : Lemma (requires D.scoped_args [] st.FF.terms /\ D.scoped_args [] ps /\
                    bind p k st ps == Some st')
          (ensures D.scoped_args [] st'.FF.terms)
          (decreases ps) =
  match ps with
  | [] -> ()
  | l :: rest ->
    let (positive, a, b) = Some?.v (FF.premise_parts p l) in
    FF.lemma_premise_parts_wf p l positive a b;
    let st1 = Some?.v (FF.visit p st a) in
    let st2 = Some?.v (FF.visit p st1 b) in
    let st3 = Some?.v (premise_equation p k l a b st2 positive) in
    FF.lemma_visit_scoped p st a st1;
    FF.lemma_visit_scoped p st1 b st2;
    if positive then assert (st3.FF.terms == st2.FF.terms)
    else (
      assert (st3.FF.terms == L.append st2.FF.terms [l]);
      FF.lemma_scoped_append_single st2.FF.terms l);
    lemma_bind_scoped p (k + 1) st3 rest st'

let rec lemma_bind (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (k:nat) (st:FF.encoding) (ps:list expr) (st':FF.encoding) (final:list expr)
  : Lemma (requires D.scoped_args [] st.FF.terms /\ D.scoped_args [] ps /\
                    D.scoped_args [] final /\ bind p k st ps == Some st' /\
                    FF.prefix st'.FF.terms final)
          (ensures FF.prefix st.FF.terms st'.FF.terms /\
                   (FF.eqs_ok schema p m rho (valuation schema p m rho final) st.FF.equations ==>
                    FF.eqs_ok schema p m rho (valuation schema p m rho final) st'.FF.equations))
          (decreases ps) =
  match ps with
  | [] -> FF.lemma_prefix_refl st.FF.terms
  | l :: rest ->
    let (positive, a, b) = Some?.v (FF.premise_parts p l) in
    let st1 = Some?.v (FF.visit p st a) in
    let st2 = Some?.v (FF.visit p st1 b) in
    let st3 = Some?.v (premise_equation p k l a b st2 positive) in
    lemma_bind_scoped p k st (l :: rest) st';
    FF.lemma_premise_parts_wf p l positive a b;
    FF.lemma_visit_scoped p st a st1;
    FF.lemma_visit_scoped p st1 b st2;
    if positive then assert (st3.FF.terms == st2.FF.terms)
    else (
      assert (st3.FF.terms == L.append st2.FF.terms [l]);
      FF.lemma_scoped_append_single st2.FF.terms l);
    lemma_bind schema p m rho (k + 1) st3 rest st' final;
    FF.lemma_prefix_trans st3.FF.terms st'.FF.terms final;
    lemma_premise_equation schema p m rho k l a b st2 st3 positive final;
    FF.lemma_prefix_trans st2.FF.terms st3.FF.terms final;
    lemma_visit schema p m rho st1 b st2 final;
    FF.lemma_prefix_trans st1.FF.terms st2.FF.terms final;
    lemma_visit schema p m rho st a st1 final;
    FF.lemma_prefix_trans st.FF.terms st1.FF.terms st2.FF.terms;
    FF.lemma_prefix_trans st.FF.terms st2.FF.terms st3.FF.terms;
    FF.lemma_prefix_trans st.FF.terms st3.FF.terms st'.FF.terms

let lemma_step (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
  (m:FF.model base schema p) (rho:V.environment base (S.signature schema) [])
  (v:nat -> int) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:FF.replay) (n:FF.pac_node) (r':FF.replay)
  : Lemma (requires D.scoped_args [] lits /\ FF.tree_ok schema p m rho v eqs /\
                    FF.values_ok schema p m rho v lits r.FF.values /\
                    step p nvars eqs sup lits r n == Some r')
          (ensures FF.values_ok schema p m rho v lits r'.FF.values) =
  match n with
  | FF.PacInput j ->
    (match IX.index_get eqs j with
     | Some (q, FF.Premise k l) ->
       FF.lemma_tree_get schema p m rho v eqs j (q, FF.Premise k l);
       let aux () : Lemma
         (requires FF.none_true schema p m rho lits /\ complementary_in l lits)
         (ensures FF.peval v q % p == 0) =
         lemma_complementary_in schema p m rho l lits;
         assert (FF.eq_ok schema p m rho v (q, FF.Premise k l)) in
       FStar.Classical.move_requires aux ();
       FF.lemma_record schema p m rho v lits r (FF.poly_size q) q
         (IX.index_put r.FF.used k true)
     | _ -> FF.lemma_step schema p m rho v nvars eqs sup lits r n r')
  | _ -> FF.lemma_step schema p m rho v nvars eqs sup lits r n r'

let rec lemma_replay_nodes (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
  (m:FF.model base schema p) (rho:V.environment base (S.signature schema) [])
  (v:nat -> int) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:FF.replay) (ns:list FF.pac_node) (r':FF.replay)
  : Lemma (requires D.scoped_args [] lits /\ FF.tree_ok schema p m rho v eqs /\
                    FF.values_ok schema p m rho v lits r.FF.values /\
                    replay_nodes p nvars eqs sup lits r ns == Some r')
          (ensures FF.values_ok schema p m rho v lits r'.FF.values)
          (decreases ns) =
  match ns with
  | [] -> ()
  | n :: rest ->
    let r1 = Some?.v (step p nvars eqs sup lits r n) in
    lemma_step schema p m rho v nvars eqs sup lits r n r1;
    lemma_replay_nodes schema p m rho v nvars eqs sup lits r1 rest r'

let lemma_check_for_prime_sound (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p) (c:FF.certificate) (e:expr)
  : Lemma (requires D.scoped_args [] c.FF.pac_premises /\ D.scoped [] e /\
                    get_sort e == bool_sort /\ check_for_prime p c e)
          (ensures SS.truth_at schema m.FF.booleans m.FF.scalar_model
                    (FF.override schema p m) [] (SS.empty_environment (S.signature schema)) e) =
  let rho = SS.empty_environment (S.signature schema) in
  let st = Some?.v (bind p 0 FF.empty_encoding c.FF.pac_premises) in
  lemma_bind_scoped p 0 FF.empty_encoding c.FF.pac_premises st;
  let sup = Some?.v
    (FF.support_tree (L.length c.FF.pac_premises) (-1) IX.Empty c.FF.pac_support) in
  let v = valuation schema p m rho st.FF.terms in
  let eqs = FF.index_equations IX.Empty (L.length st.FF.equations - 1) st.FF.equations in
  let lits = FF.clause_literals e in
  let r = Some?.v
    (replay_nodes p (L.length st.FF.terms) eqs sup lits FF.initial_replay c.FF.pac_nodes) in
  FF.lemma_prefix_refl st.FF.terms;
  lemma_bind schema p m rho 0 FF.empty_encoding c.FF.pac_premises st st.FF.terms;
  FF.lemma_index_equations schema p m rho v IX.Empty (L.length st.FF.equations - 1) st.FF.equations;
  FF.lemma_clause_literals_scoped e;
  lemma_replay_nodes schema p m rho v (L.length st.FF.terms) eqs sup lits
    FF.initial_replay c.FF.pac_nodes r;
  assert (IX.index_get r.FF.values c.FF.pac_root == Some [([], 1)]);
  FF.lemma_values_get schema p m rho v lits r.FF.values c.FF.pac_root [([], 1)];
  FF.lemma_peval_constant v 1;
  M.small_mod 1 p;
  let aux () : Lemma
    (requires not (SS.truth_at schema m.FF.booleans m.FF.scalar_model
                    (FF.override schema p m) [] rho e))
    (ensures False) =
    FF.lemma_clause_false_literals schema p m rho e;
    assert (FF.none_true schema p m rho lits);
    assert (FF.node_ok schema p m rho v lits [([], 1)]);
    assert (FF.peval v [([], 1)] % p == 0);
    assert False in
  FStar.Classical.move_requires aux ()

let lemma_check_with_evidence_sound (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
  (m:FF.model base schema p) (c:FF.certificate) (e:expr)
  (evidence:option (int & list int))
  : Lemma (requires FF.find_modulus_args c.FF.pac_premises == Some p /\
                    D.scoped_args [] c.FF.pac_premises /\ D.scoped [] e /\
                    get_sort e == bool_sort /\ check_with_evidence c e evidence)
          (ensures SS.truth_at schema m.FF.booleans m.FF.scalar_model
                    (FF.override schema p m) [] (SS.empty_environment (S.signature schema)) e) =
  assert (prime_with_evidence p evidence);
  lemma_check_for_prime_sound schema p m c e

let lemma_check_sound (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
  (m:FF.model base schema p) (c:FF.certificate) (e:expr)
  : Lemma (requires FF.find_modulus_args c.FF.pac_premises == Some p /\
                    D.scoped_args [] c.FF.pac_premises /\ D.scoped [] e /\
                    get_sort e == bool_sort /\ check c e)
          (ensures SS.truth_at schema m.FF.booleans m.FF.scalar_model
                    (FF.override schema p m) [] (SS.empty_environment (S.signature schema)) e) =
  lemma_check_with_evidence_sound schema p m c e None
