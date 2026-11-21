module Z3IndependentRealDivisionClause

open Z3AstTheory
open FStar.Real
module A = Z3LinearArithmeticAst
module D = Z3ExprScope
module DT = Z3SortedDatatype
module L = FStar.List.Tot
module R = Z3ClauseSyntax
module RL = Z3SortedReal
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module V = Z3DatatypeValue

let guarded (guard body:expr) : bool =
  match guard, body with
  | App eg [App z []; d], App eb [x; App mul [d'; App div [x'; d'']]] ->
    eg = R.eq_decl A.real_s && eb = R.eq_decl A.real_s &&
    RL.classify z = RL.Numeral 0 1 &&
    RL.classify mul = RL.Calculate A.Mul && RL.classify div = RL.Divide &&
    d = d' && d = d'' && x = x'
  | _, _ -> false

let check (conclusion:expr) : bool =
  match DT.literals conclusion with
  | [guard; body] -> guarded guard body || guarded body guard
  | _ -> false

let rec lemma_literals_scoped (es:list expr) (e:expr)
  : Lemma (requires D.scoped_args [] es /\ L.mem e es)
          (ensures D.scoped [] e) (decreases es) =
  match es with [] -> () | a :: rest -> if a <> e then lemma_literals_scoped rest e

#push-options "--using_facts_from 'Prims FStar.Real' --fuel 0 --ifuel 0"
let lemma_zero_quotient ()
  : Lemma (0.0R /. 1.0R == 0.0R) = ()

let lemma_division_identity (x d q p:real)
  : Lemma (requires q *. d == x /\ p == d *. q)
          (ensures x == p) = ()
#pop-options

let lemma_guarded (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                  (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                  (reals:RL.carrier base) (conclusion guard body:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\
                    D.scoped [] conclusion /\ get_sort conclusion == bool_sort /\
                    L.mem guard (DT.literals conclusion) /\ L.mem body (DT.literals conclusion) /\
                    guarded guard body)
          (ensures T.truth s bc model other conclusion) =
  (match conclusion with App _ _ -> () | _ -> ());
  lemma_literals_scoped (DT.literals conclusion) guard;
  lemma_literals_scoped (DT.literals conclusion) body;
  match guard, body with
  | App _ [App z []; d], App _ [x; App mul [d'; App div [x'; d'']]] ->
    let rho = T.empty_environment (S.signature s) in
    let q = App div [x'; d''] in
    let p = App mul [d'; q] in
    RL.lemma_real_divide_at s bc model other reals [] rho div x' d'';
    RL.lemma_real_binary_at s bc model other reals [] rho mul d' q A.Mul;
    RL.lemma_real_numeral_at s bc model other reals [] rho z 0 1;
    lemma_zero_quotient ();
    assert (RL.real_at s bc model other reals [] rho (App z []) == 0.0R);
    RL.lemma_real_equality_at s bc model other reals [] rho (App z []) d;
    RL.lemma_real_equality_at s bc model other reals [] rho x p;
    assert (guard == R.mk_eq_expr (App z []) d);
    assert (body == R.mk_eq_expr x p);
    if T.truth s bc model other guard then
      DT.lemma_literal_member (T.truth s bc model other) (DT.literals conclusion) guard
    else (
      assert (~(RL.real_at s bc model other reals [] rho d == 0.0R));
      lemma_division_identity (RL.real_at s bc model other reals [] rho x)
        (RL.real_at s bc model other reals [] rho d)
        (RL.real_at s bc model other reals [] rho q)
        (RL.real_at s bc model other reals [] rho p);
      assert (T.truth s bc model other body);
      DT.lemma_literal_member (T.truth s bc model other) (DT.literals conclusion) body);
    DT.lemma_literals s bc model other conclusion
  | _, _ -> ()

let lemma_check (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                (reals:RL.carrier base) (conclusion:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped [] conclusion /\
                    get_sort conclusion == bool_sort /\ check conclusion)
          (ensures T.truth s bc model other conclusion) =
  match DT.literals conclusion with
  | [a; b] ->
    if guarded a b then lemma_guarded s bc model other reals conclusion a b
    else lemma_guarded s bc model other reals conclusion b a
  | _ -> ()
