module Z3IndependentIntQuotientClause

open Z3AstTheory
module A = Z3LinearArithmeticAst
module AR = Z3SortedArithmetic
module D = Z3ExprScope
module DT = Z3SortedDatatype
module DV = Z3SortedIntDivision
module B = Z3BoundedBoolEquiv
module L = FStar.List.Tot
module Q = Z3IndependentIntSmallQuotient
module R = Z3ClauseSyntax
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module V = Z3DatatypeValue

let guarded (high low result:expr) : bool =
  match high, low, result with
  | App _ [x; d], App n [App g [x'; z]], App eq [z'; App div [x''; d']] ->
    A.comparison high = Some (A.Ge, x, d) && get_sort x = A.int_s &&
    T.classify n = T.Negation &&
    A.comparison (App g [x'; z]) = Some (A.Ge, x', z) &&
    AR.int_numeral 0 z && AR.int_numeral 0 z' &&
    eq = R.eq_decl A.int_s && DV.classify div = DV.Quotient &&
    x = x' && x = x'' && d = d'
  | _, _, _ -> false

let check (conclusion:expr) : bool =
  match conclusion with
  | App f [high; low; result] ->
    T.classify f = T.Nary B.Or && guarded high low result
  | _ -> false

let rec lemma_literals_scoped (es:list expr) (e:expr)
  : Lemma (requires D.scoped_args [] es /\ L.mem e es)
          (ensures D.scoped [] e) (decreases es) =
  match es with [] -> () | a :: rest -> if a <> e then lemma_literals_scoped rest e

let lemma_guarded (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (model:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (conclusion high low result:expr)
  : Lemma (requires DV.division_laws s bc model other /\
                    D.scoped [] conclusion /\ get_sort conclusion == bool_sort /\
                    L.mem high (DT.literals conclusion) /\
                    L.mem low (DT.literals conclusion) /\
                    L.mem result (DT.literals conclusion) /\ guarded high low result)
          (ensures T.truth s bc model other conclusion) =
  (match conclusion with App _ _ -> () | _ -> ());
  lemma_literals_scoped (DT.literals conclusion) high;
  lemma_literals_scoped (DT.literals conclusion) low;
  lemma_literals_scoped (DT.literals conclusion) result;
  match high, low, result with
  | App _ [x; d], App n [App g [x'; z]], App _ [z'; App div [x''; d']] ->
    let rho = T.empty_environment (S.signature s) in
    let bottom = App g [x'; z] in
    let quotient = App div [x''; d'] in
    AR.lemma_int_comparison s bc model other [] rho high A.Ge x d;
    AR.lemma_int_comparison s bc model other [] rho bottom A.Ge x' z;
    T.lemma_negation s bc model other n bottom;
    AR.lemma_int_numeral s bc model other [] rho 0 z;
    AR.lemma_int_numeral s bc model other [] rho 0 z';
    DV.lemma_quotient_at s bc model other [] rho div x'' d';
    T.lemma_equality s bc model other z' quotient;
    AR.lemma_integer_equality s bc model other [] rho z' quotient;
    if T.truth s bc model other high then
      DT.lemma_literal_member (T.truth s bc model other) (DT.literals conclusion) high
    else if T.truth s bc model other low then
      DT.lemma_literal_member (T.truth s bc model other) (DT.literals conclusion) low
    else (
      Q.lemma_small_quotient (AR.integer s bc model other [] rho x)
        (AR.integer s bc model other [] rho d);
      assert (T.truth s bc model other result);
      DT.lemma_literal_member (T.truth s bc model other) (DT.literals conclusion) result);
    DT.lemma_literals s bc model other conclusion
  | _, _, _ -> ()

let lemma_check (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (model:T.scalar_model base)
  (other:V.interpretation base (S.signature s)) (conclusion:expr)
  : Lemma (requires DV.division_laws s bc model other /\
                    D.scoped [] conclusion /\ get_sort conclusion == bool_sort /\
                    check conclusion)
          (ensures T.truth s bc model other conclusion) =
  match DT.literals conclusion with
  | [high; low; result] -> lemma_guarded s bc model other conclusion high low result
  | _ -> ()
