module Z3IndependentFiniteFieldWitnessTests

open Z3AstTheory
module E = FStar.Math.Euclid
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module D = Z3ExprScope
module R = Z3ClauseSyntax
module FF = Z3SortedFiniteField
module W = Z3IndependentFiniteFieldWitness

let a = R.true_expr
let b = R.false_expr
let na = R.mk_not_expr a
let fake_not =
  App { decl_name = "not"; domain = [bool_sort]; range = bool_sort;
        interp = None; int_params = [] } [a]
let field_sort = FF.ff_sort 5
let x = App { decl_name = "x"; domain = []; range = field_sort;
              interp = None; int_params = [] } []
let y = App { decl_name = "y"; domain = []; range = field_sort;
              interp = None; int_params = [] } []
let eq = R.mk_eq_expr x y
let neq = R.mk_not_expr eq

let witness_bind_control () : bool =
  match W.bind 5 0 FF.empty_encoding [neq] with
  | Some st ->
    st.FF.terms = [x; y; neq] &&
    st.FF.equations = [(W.witness_polynomial 2 [([0], 1)] [([1], 1)], FF.Premise 0 neq)]
  | None -> false

let lemma_bind_controls ()
  : Lemma (witness_bind_control () /\
           W.bind 5 0 FF.empty_encoding [eq] == FF.bind 5 0 FF.empty_encoding [eq] /\
           W.bind 7 0 FF.empty_encoding [neq] == None /\
           W.bind 5 0 FF.empty_encoding [a] == None) =
  assert_norm (witness_bind_control ());
  assert_norm (W.bind 5 0 FF.empty_encoding [eq] == FF.bind 5 0 FF.empty_encoding [eq]);
  assert_norm (W.bind 7 0 FF.empty_encoding [neq] == None);
  assert_norm (W.bind 5 0 FF.empty_encoding [a] == None)

let lemma_complement_controls ()
  : Lemma (W.complementary_in a [na] /\
           W.complementary_in na [a] /\
           W.complementary_in a [b; na] /\
           not (W.complementary_in a []) /\
           not (W.complementary_in a [a; b]) /\
           not (W.complementary_in na [na]) /\
           not (W.complementary_in a [fake_not]) /\
           not (W.complementary_in (R.mk_not_expr x) [x])) =
  assert_norm (W.complementary_in a [na]);
  assert_norm (W.complementary_in na [a]);
  assert_norm (W.complementary_in a [b; na]);
  assert_norm (not (W.complementary_in a []));
  assert_norm (not (W.complementary_in a [a; b]));
  assert_norm (not (W.complementary_in na [na]));
  assert_norm (not (W.complementary_in a [fake_not]));
  assert_norm (not (W.complementary_in (R.mk_not_expr x) [x]))

let lemma_indexed_slots (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (x:expr{D.scoped [] x /\ get_sort x == FF.ff_sort p})
  (y:expr{D.scoped [] y /\ get_sort y == FF.ff_sort p})
  (l:expr{D.scoped [] l})
  : Lemma (requires FF.premise_parts p l == Some (false, x, y) /\
                    FF.truth_at schema p m [] rho l)
          (ensures W.valuation schema p m rho [l; x] 1 ==
                     FF.valuation schema p m rho [l; x] 1 /\
                   (W.valuation schema p m rho [l; x] 0 *
                     (FF.residue schema p m rho x - FF.residue schema p m rho y) - 1) % p == 0) =
  W.lemma_valuation_field schema p m rho [l; x] 1;
  W.lemma_valuation_witness schema p m rho [l; x] 0 x y
