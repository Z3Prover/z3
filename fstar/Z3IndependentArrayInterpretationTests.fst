module Z3IndependentArrayInterpretationTests

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module TR = Z3TypedRoot
module A = Z3SortedArray
module AR = Z3IndependentArrayRoot
module AF = Z3IndependentArrayFamily
module AI = Z3IndependentArrayInterpretation
module SR = Z3SortedRoot

let int_s = TR.int_s
let data_s = BaseSort "data"
let ctor : func_decl =
  { decl_name = "ctor"; domain = []; range = data_s; interp = None; int_params = [] }
let canonical = A.ext_decl int_s int_s
let wrong_name = { canonical with decl_name = "not-array-ext" }
let wrong_tag = { canonical with interp = None }
let wrong_params = { canonical with int_params = [1] }
let wrong_range = { canonical with range = bool_sort }
let wrong_arity = { canonical with domain = [ArraySort [int_s] int_s] }
let nested_element = A.ext_decl int_s (ArraySort [int_s] int_s)
let multi_domain =
  { canonical with domain = [ArraySort [int_s; int_s] int_s; ArraySort [int_s; int_s] int_s] }
let unsupported = A.ext_decl data_s int_s

let target_controls ()
  : Lemma (AI.target [] canonical == Some (int_s, int_s) /\
           AI.target [] nested_element == Some (int_s, ArraySort [int_s] int_s) /\
           None? (AI.target [] wrong_name) /\
           None? (AI.target [] wrong_tag) /\
           None? (AI.target [] wrong_params) /\
           None? (AI.target [] wrong_range) /\
           None? (AI.target [] wrong_arity) /\
           None? (AI.target [] multi_domain) /\
           None? (AI.target [ctor] unsupported)) = ()

let preserves_malformed (u:TR.uninterpreted) (sch:S.checked_schema)
                        (uf:TR.symbols u sch)
                        (xs:TR.targuments u sch wrong_params.domain)
  : Lemma ((AI.symbols u sch uf).TR.apply wrong_params xs == uf.TR.apply wrong_params xs) =
  AI.lemma_preserves_other u sch uf wrong_params xs

let witness_in_root (u:TR.uninterpreted) (sch:S.checked_schema) (uf:TR.symbols u sch)
                    (index:sort) (element:sort{AR.supports (S.signature sch) index element})
                    (a b:A.array_value (TR.carrier u) (S.signature sch) index element)
  : Lemma (
    let root = TR.standard u sch (AI.symbols u sch uf) in
    let k = root.V.application (A.ext_decl index element) [a; b] in
    TR.root_model u sch root /\
    A.model sch (TR.booleans u) (SR.root_scalars u) root (AF.family u (S.signature sch)) /\
    (a == b \/ ~(AR.read u (S.signature sch) index element a k ==
                 AR.read u (S.signature sch) index element b k))) =
  AI.lemma_root_inhabited u sch uf;
  AI.lemma_model u sch uf;
  AI.lemma_ext_application u sch uf index element a b;
  AR.lemma_difference u (S.signature sch) index element a b

let distinct_arrays (u:TR.uninterpreted)
                    (sch:S.checked_schema{AR.supports (S.signature sch) int_s int_s})
                    (uf:TR.symbols u sch)
  : Lemma (
    let sigma = S.signature sch in
    let zero = TR.make #u #sigma int_s 0 in
    let one = TR.make #u #sigma int_s 1 in
    let a = AR.constant u sigma int_s int_s zero in
    let b = AR.write u sigma int_s int_s a zero one in
    let root = TR.standard u sch (AI.symbols u sch uf) in
    let k = root.V.application (A.ext_decl int_s int_s) [a; b] in
    ~(AR.read u sigma int_s int_s a k == AR.read u sigma int_s int_s b k)) =
  let sigma = S.signature sch in
  let zero = TR.make #u #sigma int_s 0 in
  let one = TR.make #u #sigma int_s 1 in
  let a = AR.constant u sigma int_s int_s zero in
  let b = AR.write u sigma int_s int_s a zero one in
  AR.lemma_read_constant u sigma int_s int_s zero zero;
  AR.lemma_read_write u sigma int_s int_s a zero zero one;
  AI.lemma_ext_application u sch uf int_s int_s a b;
  AR.lemma_difference u sigma int_s int_s a b
