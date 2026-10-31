(* G1 typed-root PROTOTYPE witnesses for the CORRECTED root contract (not
   production, not in the manifest).

   Almost every witness is proved for EVERY model `i` of the corrected
   contract Z3TypedRoot.root_model (R1-R6), using only the named laws of
   Z3TypedRoot (never unfolding `interpreted` or `standard`), on production
   AST terms (Z3AstTheory Var/App/Quantifier) evaluated with the production
   evaluator Z3DatatypeValue.evaluate. The positive joint witness then
   instantiates them at ONE standard interpretation, TR.standard u sch uf,
   for EVERY choice of uninterpreted carriers u and free symbols uf
   (`standard_joint_empty`, `standard_joint_list`), using L1. There is no
   legacy model_sound / numeric_model / array_model hypothesis.

   Only the free-choice controls (x/0 and head(nil) disagree across two
   standard models) are standard-specific, by design. *)
module Z3TypedRootTests

open Z3AstTheory
open Z3ValueTheory
open FStar.List.Tot
open FStar.Real
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module TR = Z3TypedRoot
module R = Z3ResolutionProofTheory
module D = Z3Definitions
module L = FStar.List.Tot
module B = Z3BoundedBoolEquiv
module DL = Z3DatatypeLemma

let empty_schema : S.schema = { S.sorts = []; S.cases = [] }

let sch : TR.supported_schema = assert_norm (TR.supported empty_schema); empty_schema

let sigma : V.signature = S.signature sch

let int_s : sort = TR.int_s
let real_s : sort = TR.real_s

type env (u:TR.uninterpreted) (scope:list sort) = V.environment (TR.carrier u) sigma scope

(* EVERY model of the corrected root contract over the empty schema. *)
type model (u:TR.uninterpreted) = i:TR.interp u sch{TR.root_model u sch i}

let ev (u:TR.uninterpreted) (i:TR.interp u sch) (scope:list sort) (rho:env u scope)
       (e:expr{D.scoped scope e})
  : GTot (TR.tvalue u sch (get_sort e)) =
  V.evaluate sigma i scope rho e

let int_v (#u:TR.uninterpreted) (v:TR.tvalue u sch int_s) : int = TR.int_of sch v
let real_v (#u:TR.uninterpreted) (v:TR.tvalue u sch real_s) : real = TR.real_of sch v
let bool_v (#u:TR.uninterpreted) (v:TR.tvalue u sch bool_sort) : bool = TR.truth sch v

let int_ext (#u:TR.uninterpreted) (v w:TR.tvalue u sch int_s)
  : Lemma (requires int_v v == int_v w) (ensures v == w) =
  TR.lemma_make_scalar #u #sigma int_s v;
  TR.lemma_make_scalar #u #sigma int_s w

let real_ext (#u:TR.uninterpreted) (v w:TR.tvalue u sch real_s)
  : Lemma (requires real_v v == real_v w) (ensures v == w) =
  TR.lemma_make_scalar #u #sigma real_s v;
  TR.lemma_make_scalar #u #sigma real_s w

(* --- Production terms ---------------------------------------------------- *)

let inum (n:int) : expr = App (TR.int_numeral n) []
let rnum (n:int) (d:pos) : expr = App (TR.real_numeral n d) []
let bin (f:func_decl) (a b:expr) : expr = App f [a; b]
let eq (a b:expr) : expr = R.mk_eq_expr a b
let true_e : expr = App TR.true_decl []
let false_e : expr = App TR.false_decl []
let not_ (a:expr) : expr = App TR.not_decl [a]
let implies_ (a b:expr) : expr = bin TR.implies_decl a b
let and_ (a b:expr) : expr = bin (TR.bool2_decl "and" op_and) a b
let or_ (a b:expr) : expr = bin (TR.bool2_decl "or" op_or) a b
let xor_ (a b:expr) : expr = bin (TR.bool2_decl "xor" op_xor) a b
let ite (s:sort) (c a b:expr) : expr = App (TR.ite_decl s) [c; a; b]
let iadd (a b:expr) : expr = bin (TR.plus_decl int_s) a b
let imul (a b:expr) : expr = bin (TR.times_decl int_s) a b
let isub (a b:expr) : expr = bin (TR.minus_decl int_s) a b
let ineg (a:expr) : expr = App (TR.negate_decl int_s) [a]
let radd (a b:expr) : expr = bin (TR.plus_decl real_s) a b
let rmul (a b:expr) : expr = bin (TR.times_decl real_s) a b
let rsub (a b:expr) : expr = bin (TR.minus_decl real_s) a b
let rneg (a:expr) : expr = App (TR.negate_decl real_s) [a]
let rdiv (a b:expr) : expr = bin TR.divide_decl a b
let to_real (a:expr) : expr = App TR.to_real_decl [a]
let ile (a b:expr) : expr = bin (TR.le_decl int_s) a b
let ilt (a b:expr) : expr = bin (TR.lt_decl int_s) a b
let ige (a b:expr) : expr = bin (TR.ge_decl int_s) a b
let igt (a b:expr) : expr = bin (TR.gt_decl int_s) a b
let rle (a b:expr) : expr = bin (TR.le_decl real_s) a b
let rlt (a b:expr) : expr = bin (TR.lt_decl real_s) a b
let rge (a b:expr) : expr = bin (TR.ge_decl real_s) a b
let rgt (a b:expr) : expr = bin (TR.gt_decl real_s) a b

let zero : expr = inum 0
let one : expr = inum 1
let two : expr = inum 2
let three : expr = inum 3
let four : expr = inum 4
let five : expr = inum 5
let six : expr = inum 6

(* --- Evaluator steps (any interpretation; the schema has no constructor) -- *)

let ev_app0 (u:TR.uninterpreted) (i:TR.interp u sch) (scope:list sort) (rho:env u scope) (f:func_decl)
  : Lemma (requires f.domain == [])
          (ensures D.scoped scope (App f []) /\ ev u i scope rho (App f []) == i.V.application f []) = ()

let ev_app1 (u:TR.uninterpreted) (i:TR.interp u sch) (scope:list sort) (rho:env u scope) (f:func_decl)
            (a:expr)
  : Lemma (requires D.scoped scope a /\ f.domain == [get_sort a])
          (ensures D.scoped scope (App f [a]) /\
                   ev u i scope rho (App f [a]) == i.V.application f [ev u i scope rho a]) =
  V.lemma_sort_eq (get_sort a) (get_sort a)

let ev_app2 (u:TR.uninterpreted) (i:TR.interp u sch) (scope:list sort) (rho:env u scope) (f:func_decl)
            (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ f.domain == [get_sort a; get_sort b])
          (ensures D.scoped scope (App f [a; b]) /\
                   ev u i scope rho (App f [a; b]) == i.V.application f [ev u i scope rho a; ev u i scope rho b]) =
  V.lemma_sort_eq (get_sort a) (get_sort a);
  V.lemma_sort_eq (get_sort b) (get_sort b)

(* One evaluate_args step, so that 3- and 4-argument applications are
   assembled from small queries. *)
let ev_args_cons (u:TR.uninterpreted) (i:TR.interp u sch) (scope:list sort) (rho:env u scope)
                 (e:expr) (es:list expr) (ss:list sort)
  : Lemma (requires D.scoped scope e /\ D.scoped_args scope es /\ sorts_match es ss)
          (ensures sorts_match (e :: es) (get_sort e :: ss) /\ D.scoped_args scope (e :: es) /\
                   V.evaluate_args sigma i scope rho (e :: es) (get_sort e :: ss) ==
                   ev u i scope rho e :: V.evaluate_args sigma i scope rho es ss) =
  V.lemma_sort_eq (get_sort e) (get_sort e)

let ev_app3 (u:TR.uninterpreted) (i:TR.interp u sch) (scope:list sort) (rho:env u scope) (f:func_decl)
            (a b c:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ D.scoped scope c /\
                    f.domain == [get_sort a; get_sort b; get_sort c])
          (ensures D.scoped scope (App f [a; b; c]) /\
                   ev u i scope rho (App f [a; b; c]) ==
                   i.V.application f [ev u i scope rho a; ev u i scope rho b; ev u i scope rho c]) =
  ev_args_cons u i scope rho c [] [];
  ev_args_cons u i scope rho b [c] [get_sort c];
  ev_args_cons u i scope rho a [b; c] [get_sort b; get_sort c]

let ev_app4 (u:TR.uninterpreted) (i:TR.interp u sch) (scope:list sort) (rho:env u scope) (f:func_decl)
            (a b c d:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ D.scoped scope c /\ D.scoped scope d /\
                    f.domain == [get_sort a; get_sort b; get_sort c; get_sort d])
          (ensures D.scoped scope (App f [a; b; c; d]) /\
                   ev u i scope rho (App f [a; b; c; d]) ==
                   i.V.application f [ev u i scope rho a; ev u i scope rho b; ev u i scope rho c;
                                      ev u i scope rho d]) =
  ev_args_cons u i scope rho d [] [];
  ev_args_cons u i scope rho c [d] [get_sort d];
  ev_args_cons u i scope rho b [c; d] [get_sort c; get_sort d];
  ev_args_cons u i scope rho a [b; c; d] [get_sort b; get_sort c; get_sort d]

(* --- Expression steps from the NAMED laws (every root model) -------------- *)

let ev_inum (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope) (n:int)
  : Lemma (D.scoped scope (inum n) /\ int_v (ev u i scope rho (inum n)) == n) =
  ev_app0 u i scope rho (TR.int_numeral n);
  TR.lemma_classify_numerals sch n 1;
  TR.law_int_numeral i (TR.int_numeral n) n 1 []

let ev_rnum (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope) (n:int) (d:pos)
  : Lemma (D.scoped scope (rnum n d) /\ real_v (ev u i scope rho (rnum n d)) == of_int n /. of_int d) =
  ev_app0 u i scope rho (TR.real_numeral n d);
  TR.lemma_classify_numerals sch n d;
  TR.law_real_numeral i (TR.real_numeral n d) n d []

let ev_constants (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope true_e /\ D.scoped scope false_e /\
           bool_v (ev u i scope rho true_e) == true /\ bool_v (ev u i scope rho false_e) == false) =
  ev_app0 u i scope rho TR.true_decl;
  ev_app0 u i scope rho TR.false_decl;
  TR.lemma_classify_booleans sigma bool_sort;
  TR.law_constant i TR.true_decl true [];
  TR.law_constant i TR.false_decl false []

let ev_not (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope) (a:expr)
  : Lemma (requires D.scoped scope a /\ get_sort a == bool_sort)
          (ensures D.scoped scope (not_ a) /\
                   bool_v (ev u i scope rho (not_ a)) == not (bool_v (ev u i scope rho a))) =
  ev_app1 u i scope rho TR.not_decl a;
  TR.lemma_classify_booleans sigma bool_sort;
  TR.law_not i TR.not_decl (ev u i scope rho a)

let ev_implies (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope) (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ get_sort a == bool_sort /\ get_sort b == bool_sort)
          (ensures D.scoped scope (implies_ a b) /\
                   bool_v (ev u i scope rho (implies_ a b)) ==
                   (not (bool_v (ev u i scope rho a)) || bool_v (ev u i scope rho b))) =
  ev_app2 u i scope rho TR.implies_decl a b;
  TR.lemma_classify_booleans sigma bool_sort;
  TR.law_implies i TR.implies_decl (ev u i scope rho a) (ev u i scope rho b)

let ev_and_or_xor (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope) (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ get_sort a == bool_sort /\ get_sort b == bool_sort)
          (ensures D.scoped scope (and_ a b) /\ D.scoped scope (or_ a b) /\ D.scoped scope (xor_ a b) /\
                   bool_v (ev u i scope rho (and_ a b)) == (bool_v (ev u i scope rho a) && bool_v (ev u i scope rho b)) /\
                   bool_v (ev u i scope rho (or_ a b)) == (bool_v (ev u i scope rho a) || bool_v (ev u i scope rho b)) /\
                   bool_v (ev u i scope rho (xor_ a b)) == (bool_v (ev u i scope rho a) <> bool_v (ev u i scope rho b))) =
  ev_app2 u i scope rho (TR.bool2_decl "and" op_and) a b;
  ev_app2 u i scope rho (TR.bool2_decl "or" op_or) a b;
  ev_app2 u i scope rho (TR.bool2_decl "xor" op_xor) a b;
  TR.lemma_classify_booleans sigma bool_sort;
  TR.law_and i (TR.bool2_decl "and" op_and) (ev u i scope rho a) (ev u i scope rho b);
  TR.law_or i (TR.bool2_decl "or" op_or) (ev u i scope rho a) (ev u i scope rho b);
  TR.law_xor i (TR.bool2_decl "xor" op_xor) (ev u i scope rho a) (ev u i scope rho b)

let ev_eq (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope) (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ get_sort b == get_sort a)
          (ensures D.scoped scope (eq a b) /\
                   (bool_v (ev u i scope rho (eq a b)) == true <==> ev u i scope rho a == ev u i scope rho b)) =
  ev_app2 u i scope rho (R.eq_decl (get_sort a)) a b;
  TR.lemma_classify_booleans sigma (get_sort a);
  TR.law_equality i (R.eq_decl (get_sort a)) (get_sort a) (ev u i scope rho a) (ev u i scope rho b)

let ev_ite (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope) (s:sort) (c a b:expr)
  : Lemma (requires D.scoped scope c /\ D.scoped scope a /\ D.scoped scope b /\
                    get_sort c == bool_sort /\ get_sort a == s /\ get_sort b == s)
          (ensures D.scoped scope (ite s c a b) /\
                   ev u i scope rho (ite s c a b) ==
                   (if bool_v (ev u i scope rho c) then ev u i scope rho a else ev u i scope rho b)) =
  ev_app3 u i scope rho (TR.ite_decl s) c a b;
  TR.lemma_classify_booleans sigma s;
  TR.law_ite i (TR.ite_decl s) s (ev u i scope rho c) (ev u i scope rho a) (ev u i scope rho b)

let ev_iadd (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope) (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ get_sort a == int_s /\ get_sort b == int_s)
          (ensures D.scoped scope (iadd a b) /\
                   int_v (ev u i scope rho (iadd a b)) == int_v (ev u i scope rho a) + int_v (ev u i scope rho b)) =
  ev_app2 u i scope rho (TR.plus_decl int_s) a b;
  TR.lemma_classify_plus sch int_s;
  TR.law_int_add i (TR.plus_decl int_s) (ev u i scope rho a) (ev u i scope rho b)

let ev_imul (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope) (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ get_sort a == int_s /\ get_sort b == int_s)
          (ensures D.scoped scope (imul a b) /\
                   int_v (ev u i scope rho (imul a b)) == int_v (ev u i scope rho a) * int_v (ev u i scope rho b)) =
  ev_app2 u i scope rho (TR.times_decl int_s) a b;
  TR.lemma_classify_times sch int_s;
  TR.law_int_mul i (TR.times_decl int_s) (ev u i scope rho a) (ev u i scope rho b)

let ev_isub (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope) (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ get_sort a == int_s /\ get_sort b == int_s)
          (ensures D.scoped scope (isub a b) /\
                   int_v (ev u i scope rho (isub a b)) == int_v (ev u i scope rho a) - int_v (ev u i scope rho b)) =
  ev_app2 u i scope rho (TR.minus_decl int_s) a b;
  TR.lemma_classify_minus sch int_s;
  TR.law_int_sub i (TR.minus_decl int_s) (ev u i scope rho a) (ev u i scope rho b)

let ev_ineg (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope) (a:expr)
  : Lemma (requires D.scoped scope a /\ get_sort a == int_s)
          (ensures D.scoped scope (ineg a) /\ int_v (ev u i scope rho (ineg a)) == - (int_v (ev u i scope rho a))) =
  ev_app1 u i scope rho (TR.negate_decl int_s) a;
  TR.lemma_classify_negate sch int_s;
  TR.law_int_negate i (TR.negate_decl int_s) (ev u i scope rho a)

let ev_radd (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope) (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ get_sort a == real_s /\ get_sort b == real_s)
          (ensures D.scoped scope (radd a b) /\
                   real_v (ev u i scope rho (radd a b)) == real_v (ev u i scope rho a) +. real_v (ev u i scope rho b)) =
  ev_app2 u i scope rho (TR.plus_decl real_s) a b;
  TR.lemma_classify_plus sch real_s;
  TR.law_real_add i (TR.plus_decl real_s) (ev u i scope rho a) (ev u i scope rho b)

let ev_rmul (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope) (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ get_sort a == real_s /\ get_sort b == real_s)
          (ensures D.scoped scope (rmul a b) /\
                   real_v (ev u i scope rho (rmul a b)) == real_v (ev u i scope rho a) *. real_v (ev u i scope rho b)) =
  ev_app2 u i scope rho (TR.times_decl real_s) a b;
  TR.lemma_classify_times sch real_s;
  TR.law_real_mul i (TR.times_decl real_s) (ev u i scope rho a) (ev u i scope rho b)

let ev_rsub (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope) (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ get_sort a == real_s /\ get_sort b == real_s)
          (ensures D.scoped scope (rsub a b) /\
                   real_v (ev u i scope rho (rsub a b)) == real_v (ev u i scope rho a) -. real_v (ev u i scope rho b)) =
  ev_app2 u i scope rho (TR.minus_decl real_s) a b;
  TR.lemma_classify_minus sch real_s;
  TR.law_real_sub i (TR.minus_decl real_s) (ev u i scope rho a) (ev u i scope rho b)

let ev_rneg (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope) (a:expr)
  : Lemma (requires D.scoped scope a /\ get_sort a == real_s)
          (ensures D.scoped scope (rneg a) /\ real_v (ev u i scope rho (rneg a)) == 0.0R -. real_v (ev u i scope rho a)) =
  ev_app1 u i scope rho (TR.negate_decl real_s) a;
  TR.lemma_classify_negate sch real_s;
  TR.law_real_negate i (TR.negate_decl real_s) (ev u i scope rho a)

let ev_rdiv (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope) (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ get_sort a == real_s /\ get_sort b == real_s /\
                    ~(real_v (ev u i scope rho b) == 0.0R))
          (ensures D.scoped scope (rdiv a b) /\
                   real_v (ev u i scope rho (rdiv a b)) == real_v (ev u i scope rho a) /. real_v (ev u i scope rho b)) =
  ev_app2 u i scope rho TR.divide_decl a b;
  TR.lemma_classify_divide sch;
  TR.law_real_divide i TR.divide_decl (ev u i scope rho a) (ev u i scope rho b)

let ev_to_real (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope) (a:expr)
  : Lemma (requires D.scoped scope a /\ get_sort a == int_s)
          (ensures D.scoped scope (to_real a) /\ real_v (ev u i scope rho (to_real a)) == of_int (int_v (ev u i scope rho a))) =
  ev_app1 u i scope rho TR.to_real_decl a;
  TR.lemma_classify_to_real sch;
  TR.law_to_real i TR.to_real_decl (ev u i scope rho a)

let ev_icompare (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope) (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ get_sort a == int_s /\ get_sort b == int_s)
          (ensures D.scoped scope (ile a b) /\ D.scoped scope (ilt a b) /\ D.scoped scope (ige a b) /\
                   D.scoped scope (igt a b) /\
                   bool_v (ev u i scope rho (ile a b)) == (int_v (ev u i scope rho a) <= int_v (ev u i scope rho b)) /\
                   bool_v (ev u i scope rho (ilt a b)) == (int_v (ev u i scope rho a) < int_v (ev u i scope rho b)) /\
                   bool_v (ev u i scope rho (ige a b)) == (int_v (ev u i scope rho a) >= int_v (ev u i scope rho b)) /\
                   bool_v (ev u i scope rho (igt a b)) == (int_v (ev u i scope rho a) > int_v (ev u i scope rho b))) =
  let x = ev u i scope rho a in
  let y = ev u i scope rho b in
  ev_app2 u i scope rho (TR.le_decl int_s) a b;
  ev_app2 u i scope rho (TR.lt_decl int_s) a b;
  ev_app2 u i scope rho (TR.ge_decl int_s) a b;
  ev_app2 u i scope rho (TR.gt_decl int_s) a b;
  TR.lemma_classify_le sch int_s; TR.lemma_classify_lt sch int_s;
  TR.lemma_classify_ge sch int_s; TR.lemma_classify_gt sch int_s;
  TR.law_int_le i (TR.le_decl int_s) x y; TR.law_int_lt i (TR.lt_decl int_s) x y;
  TR.law_int_ge i (TR.ge_decl int_s) x y; TR.law_int_gt i (TR.gt_decl int_s) x y

let ev_rcompare (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope) (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ get_sort a == real_s /\ get_sort b == real_s)
          (ensures D.scoped scope (rle a b) /\ D.scoped scope (rlt a b) /\ D.scoped scope (rge a b) /\
                   D.scoped scope (rgt a b) /\
                   (bool_v (ev u i scope rho (rle a b)) == true <==> real_v (ev u i scope rho a) <=. real_v (ev u i scope rho b)) /\
                   (bool_v (ev u i scope rho (rlt a b)) == true <==> real_v (ev u i scope rho a) <. real_v (ev u i scope rho b)) /\
                   (bool_v (ev u i scope rho (rge a b)) == true <==> real_v (ev u i scope rho a) >=. real_v (ev u i scope rho b)) /\
                   (bool_v (ev u i scope rho (rgt a b)) == true <==> real_v (ev u i scope rho a) >. real_v (ev u i scope rho b))) =
  let x = ev u i scope rho a in
  let y = ev u i scope rho b in
  ev_app2 u i scope rho (TR.le_decl real_s) a b;
  ev_app2 u i scope rho (TR.lt_decl real_s) a b;
  ev_app2 u i scope rho (TR.ge_decl real_s) a b;
  ev_app2 u i scope rho (TR.gt_decl real_s) a b;
  TR.lemma_classify_le sch real_s; TR.lemma_classify_lt sch real_s;
  TR.lemma_classify_ge sch real_s; TR.lemma_classify_gt sch real_s;
  TR.law_real_le i (TR.le_decl real_s) x y; TR.law_real_lt i (TR.lt_decl real_s) x y;
  TR.law_real_ge i (TR.ge_decl real_s) x y; TR.law_real_gt i (TR.gt_decl real_s) x y

(* ========================================================================== *)
(* A. Numerals, arithmetic, comparisons, conversion and connectives          *)
(*    (the cases the first witness missed), every root model                 *)
(* ========================================================================== *)

let arith_i : expr = isub (imul two three) one

let arith_int_value (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope arith_i /\ int_v (ev u i scope rho arith_i) == 5) =
  ev_inum u i scope rho 2; ev_inum u i scope rho 3; ev_inum u i scope rho 1;
  ev_imul u i scope rho two three;
  ev_isub u i scope rho (imul two three) one

(* (2 * 3) - 1 = 5 is true; = 6 is false *)
let arith_int (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (eq arith_i five) /\ D.scoped scope (eq arith_i six) /\
           bool_v (ev u i scope rho (eq arith_i five)) == true /\
           bool_v (ev u i scope rho (eq arith_i six)) == false) =
  arith_int_value u i scope rho;
  ev_inum u i scope rho 5; ev_inum u i scope rho 6;
  int_ext (ev u i scope rho arith_i) (ev u i scope rho five);
  ev_eq u i scope rho arith_i five;
  ev_eq u i scope rho arith_i six

(* (-(3)) + 3 = 0 *)
let negate_int (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (iadd (ineg three) three) /\ int_v (ev u i scope rho (iadd (ineg three) three)) == 0) =
  ev_inum u i scope rho 3;
  ev_ineg u i scope rho three;
  ev_iadd u i scope rho (ineg three) three

let half : expr = rnum 1 2
let third : expr = rnum 1 3
let sixth : expr = rnum 1 6
let fifth : expr = rnum 1 5
let two_thirds : expr = rnum 2 3

(* Pure real facts, in their own small contexts. *)
let real_product () : Lemma ((of_int 1 /. of_int 2) *. (of_int 2 /. of_int 3) == of_int 1 /. of_int 3) = ()

let real_difference () : Lemma ((of_int 1 /. of_int 2) -. (of_int 1 /. of_int 3) == of_int 1 /. of_int 6 /\
                                 ~((of_int 1 /. of_int 2) -. (of_int 1 /. of_int 3) == of_int 1 /. of_int 5)) = ()

(* (1/2) * (2/3) = 1/3 *)
let product_real (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (rmul half two_thirds) /\
           real_v (ev u i scope rho (rmul half two_thirds)) == real_v (ev u i scope rho third)) =
  ev_rnum u i scope rho 1 2; ev_rnum u i scope rho 2 3; ev_rnum u i scope rho 1 3;
  ev_rmul u i scope rho half two_thirds;
  real_product ()

(* (1/2) - (1/3) = 1/6 and not 1/5 *)
let difference_real (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (rsub half third) /\
           real_v (ev u i scope rho (rsub half third)) == real_v (ev u i scope rho sixth) /\
           ~(real_v (ev u i scope rho (rsub half third)) == real_v (ev u i scope rho fifth))) =
  ev_rnum u i scope rho 1 2; ev_rnum u i scope rho 1 3;
  ev_rnum u i scope rho 1 6; ev_rnum u i scope rho 1 5;
  ev_rsub u i scope rho half third;
  real_difference ()

(* (-(1/2)) + 1/2 = 0 *)
let negation_real (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (radd (rneg half) half) /\ real_v (ev u i scope rho (radd (rneg half) half)) == 0.0R) =
  ev_rnum u i scope rho 1 2;
  ev_rneg u i scope rho half;
  ev_radd u i scope rho (rneg half) half

let three_halves : expr = rdiv (to_real three) (rnum 2 1)

let real_conversion () : Lemma (of_int 2 /. of_int 1 == of_int 2 /\ of_int 1 /. of_int 1 == of_int 1 /\
                                ~(of_int 3 /. of_int 2 == of_int 1)) = ()

(* to_real(3) / 2 = 3/2 and not 1 (no integer division) *)
let conversion (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope three_halves /\ real_v (ev u i scope rho three_halves) == of_int 3 /. of_int 2 /\
           ~(real_v (ev u i scope rho three_halves) == real_v (ev u i scope rho (rnum 1 1)))) =
  ev_inum u i scope rho 3;
  ev_to_real u i scope rho three;
  ev_rnum u i scope rho 2 1;
  ev_rnum u i scope rho 1 1;
  real_conversion ();
  ev_rdiv u i scope rho (to_real three) (rnum 2 1)

(* 2 <= 3, not 3 < 3, 3 >= 3, not 2 > 3 *)
let compare_int (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (ile two three) /\ D.scoped scope (ilt three three) /\
           D.scoped scope (ige three three) /\ D.scoped scope (igt two three) /\
           bool_v (ev u i scope rho (ile two three)) == true /\ bool_v (ev u i scope rho (ilt three three)) == false /\
           bool_v (ev u i scope rho (ige three three)) == true /\ bool_v (ev u i scope rho (igt two three)) == false) =
  ev_inum u i scope rho 2; ev_inum u i scope rho 3;
  ev_icompare u i scope rho two three;
  ev_icompare u i scope rho three three

let real_order () : Lemma (of_int 1 /. of_int 3 <. of_int 1 /. of_int 2 /\
                           ~(of_int 1 /. of_int 2 <=. of_int 1 /. of_int 3) /\
                           of_int 1 /. of_int 2 >=. of_int 1 /. of_int 2 /\
                           ~(of_int 1 /. of_int 3 >. of_int 1 /. of_int 2)) = ()

(* 1/3 < 1/2 and not 1/3 > 1/2 *)
let compare_real_third_half (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (rlt third half) /\ D.scoped scope (rgt third half) /\
           bool_v (ev u i scope rho (rlt third half)) == true /\ bool_v (ev u i scope rho (rgt third half)) == false) =
  ev_rnum u i scope rho 1 2; ev_rnum u i scope rho 1 3;
  real_order ();
  ev_rcompare u i scope rho third half

(* not 1/2 <= 1/3, 1/2 >= 1/2 *)
let compare_real_half (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (rle half third) /\ D.scoped scope (rge half half) /\
           bool_v (ev u i scope rho (rle half third)) == false /\ bool_v (ev u i scope rho (rge half half)) == true) =
  ev_rnum u i scope rho 1 2; ev_rnum u i scope rho 1 3;
  real_order ();
  ev_rcompare u i scope rho half third;
  ev_rcompare u i scope rho half half

(* not, =>, and, or, xor truth-table rows *)
let connectives (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (not_ true_e) /\ D.scoped scope (implies_ true_e false_e) /\
           D.scoped scope (implies_ false_e false_e) /\ D.scoped scope (and_ true_e false_e) /\
           D.scoped scope (or_ false_e true_e) /\ D.scoped scope (xor_ true_e true_e) /\
           D.scoped scope (xor_ true_e false_e) /\
           bool_v (ev u i scope rho (not_ true_e)) == false /\
           bool_v (ev u i scope rho (implies_ true_e false_e)) == false /\
           bool_v (ev u i scope rho (implies_ false_e false_e)) == true /\
           bool_v (ev u i scope rho (and_ true_e false_e)) == false /\
           bool_v (ev u i scope rho (or_ false_e true_e)) == true /\
           bool_v (ev u i scope rho (xor_ true_e true_e)) == false /\
           bool_v (ev u i scope rho (xor_ true_e false_e)) == true) =
  ev_constants u i scope rho;
  ev_not u i scope rho true_e;
  ev_implies u i scope rho true_e false_e;
  ev_implies u i scope rho false_e false_e;
  ev_and_or_xor u i scope rho true_e false_e;
  ev_and_or_xor u i scope rho false_e true_e;
  ev_and_or_xor u i scope rho true_e true_e

let real_numeral_facts () : Lemma (of_int 2 /. of_int 4 == of_int 1 /. of_int 2 /\
                                   of_int 4 /. of_int 2 == of_int 2 /. of_int 1 /\
                                   ~(of_int 1 /. of_int 2 == of_int 1 /. of_int 3)) = ()

(* Numeral meaning: 2/4 and 1/2 denote the same real; 4/2 is the real 2; 1/2 is not 1/3. *)
let numerals (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (eq (rnum 2 4) half) /\ D.scoped scope (eq (rnum 4 2) (rnum 2 1)) /\
           D.scoped scope (eq half third) /\
           bool_v (ev u i scope rho (eq (rnum 2 4) half)) == true /\
           bool_v (ev u i scope rho (eq (rnum 4 2) (rnum 2 1))) == true /\
           bool_v (ev u i scope rho (eq half third)) == false) =
  ev_rnum u i scope rho 2 4; ev_rnum u i scope rho 1 2; ev_rnum u i scope rho 4 2;
  ev_rnum u i scope rho 2 1; ev_rnum u i scope rho 1 3;
  real_numeral_facts ();
  real_ext (ev u i scope rho (rnum 2 4)) (ev u i scope rho half);
  real_ext (ev u i scope rho (rnum 4 2)) (ev u i scope rho (rnum 2 1));
  ev_eq u i scope rho (rnum 2 4) half;
  ev_eq u i scope rho (rnum 4 2) (rnum 2 1);
  ev_eq u i scope rho half third

(* ========================================================================== *)
(* B. O1: (Array Int Real), store 1/2 at index 0, read back                  *)
(* ========================================================================== *)

let arr_s : sort = ArraySort [int_s] real_s
let scope1 : list sort = [arr_s]
let a0 : expr = Var 0 arr_s
let store_ir : func_decl = TR.store_decl [int_s] real_s
let select_ir : func_decl = TR.select_decl [int_s] real_s
let stored : expr = App store_ir [a0; zero; half]
let read_back : expr = App select_ir [stored; zero]

let o1_half_e : e:expr{D.scoped scope1 e} = assert_norm (D.scoped scope1 (eq read_back half)); eq read_back half
let o1_third_e : e:expr{D.scoped scope1 e} = assert_norm (D.scoped scope1 (eq read_back third)); eq read_back third

let ev_stored (u:TR.uninterpreted) (i:model u) (rho:env u scope1)
  : Lemma (D.scoped scope1 stored /\
           ev u i scope1 rho stored ==
           i.V.application store_ir
             (TR.store_arguments #u #sch [int_s] real_s (rho 0) [ev u i scope1 rho zero] (ev u i scope1 rho half))) =
  ev_inum u i scope1 rho 0;
  ev_rnum u i scope1 rho 1 2;
  ev_app3 u i scope1 rho store_ir a0 zero half;
  assert_norm (TR.store_arguments #u #sch [int_s] real_s (rho 0) [ev u i scope1 rho zero] (ev u i scope1 rho half) ==
               [rho 0; ev u i scope1 rho zero; ev u i scope1 rho half])

(* read-over-write: the stored value is read back as the genuine real 1/2 *)
let ev_read_back (u:TR.uninterpreted) (i:model u) (rho:env u scope1)
  : Lemma (D.scoped scope1 read_back /\ ev u i scope1 rho read_back == ev u i scope1 rho half) =
  ev_stored u i rho;
  ev_app2 u i scope1 rho select_ir stored zero;
  assert_norm (TR.free sigma arr_s);
  TR.law_select_store_same i [int_s] real_s (rho 0) [ev u i scope1 rho zero] (ev u i scope1 rho half)

let o1_half (u:TR.uninterpreted) (i:model u) (rho:env u scope1)
  : Lemma (bool_v (ev u i scope1 rho o1_half_e) == true) =
  ev_read_back u i rho;
  ev_eq u i scope1 rho read_back half

(* mutation: reading back 1/3 is false (a genuine false claim) *)
let o1_third (u:TR.uninterpreted) (i:model u) (rho:env u scope1)
  : Lemma (bool_v (ev u i scope1 rho o1_third_e) == false) =
  ev_read_back u i rho;
  ev_rnum u i scope1 rho 1 2;
  ev_rnum u i scope1 rho 1 3;
  real_numeral_facts ();
  ev_eq u i scope1 rho read_back third

[@@expect_failure [19]]
let o1_third_is_true (u:TR.uninterpreted) (i:model u) (rho:env u scope1)
  : Lemma (bool_v (ev u i scope1 rho o1_third_e) == true) =
  ev_read_back u i rho;
  ev_rnum u i scope1 rho 1 2;
  ev_rnum u i scope1 rho 1 3;
  real_numeral_facts ();
  ev_eq u i scope1 rho read_back third

(* ========================================================================== *)
(* C. Typed open environments                                                *)
(* ========================================================================== *)

let scope_b : list sort = [bool_sort]
let p0 : expr = Var 0 bool_sort

let typed_bool_variable (u:TR.uninterpreted) (i:TR.interp u sch) (rho:env u scope_b)
  : Lemma (ev u i scope_b rho p0 == TR.boolean #u sch (TR.truth sch (rho 0))) = ()

let env_true (u:TR.uninterpreted) : env u scope_b = fun _ -> TR.boolean #u sch true

let bool_variable_true (u:TR.uninterpreted) (i:TR.interp u sch)
  : Lemma (bool_v (ev u i scope_b (env_true u) p0) == true) = ()

(* The legacy counterexample shape (an Int value for a Bool variable) is not
   an environment of this scope: the typed condition is checkable and rejects it. *)
[@@expect_failure [19]]
let int_in_bool_environment (u:TR.uninterpreted) : env u scope_b =
  fun _ -> V.Scalar int_s (0 <: TR.carrier u int_s)

(* ========================================================================== *)
(* D. Ghost lambdas (production Lambda_k nodes), every root model            *)
(* ========================================================================== *)

let ii_s : sort = ArraySort [int_s] int_s
let x0 : expr = Var 0 int_s
let lam (body:expr) : expr = Quantifier Lambda_k [int_s] ii_s body
let succ : expr = lam (iadd x0 one)
let ident : expr = lam x0
let plus_zero : expr = lam (iadd x0 zero)
let sel_ii : func_decl = TR.select_decl [int_s] int_s
let at (f e:expr) : expr = App sel_ii [f; e]

let ev_at (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope) (body e:expr)
  : Lemma (requires D.scoped (int_s :: scope) body /\ get_sort body == int_s /\ D.scoped scope e /\ get_sort e == int_s)
          (ensures D.scoped scope (at (lam body) e) /\
                   ev u i scope rho (at (lam body) e) ==
                   ev u i (int_s :: scope) (V.extend sigma scope [int_s] [ev u i scope rho e] rho) body) =
  assert_norm (L.rev [int_s] == [int_s]);
  assert_norm (TR.free sigma ii_s);
  ev_app2 u i scope rho sel_ii (lam body) e;
  let v = ev u i scope rho e in
  assert_norm (TR.reverse_arguments sigma [int_s] [v] == [v]);
  TR.lemma_eval_select_lambda i scope rho [int_s] int_s body [v]

let succ_at (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope) (e:expr)
  : Lemma (requires D.scoped scope e /\ get_sort e == int_s)
          (ensures D.scoped scope (at succ e) /\ int_v (ev u i scope rho (at succ e)) == int_v (ev u i scope rho e) + 1) =
  ev_at u i scope rho (iadd x0 one) e;
  let rho' = V.extend sigma scope [int_s] [ev u i scope rho e] rho in
  ev_inum u i (int_s :: scope) rho' 1;
  ev_iadd u i (int_s :: scope) rho' x0 one

let ident_at (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope) (e:expr)
  : Lemma (requires D.scoped scope e /\ get_sort e == int_s)
          (ensures D.scoped scope (at ident e) /\ ev u i scope rho (at ident e) == ev u i scope rho e) =
  ev_at u i scope rho x0 e

(* select (lambda x:Int. x + 1) 2 = 3 is true; = 4 is false *)
let beta (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (eq (at succ two) three) /\ D.scoped scope (eq (at succ two) four) /\
           bool_v (ev u i scope rho (eq (at succ two) three)) == true /\
           bool_v (ev u i scope rho (eq (at succ two) four)) == false) =
  ev_inum u i scope rho 2; ev_inum u i scope rho 3; ev_inum u i scope rho 4;
  succ_at u i scope rho two;
  int_ext (ev u i scope rho (at succ two)) (ev u i scope rho three);
  ev_eq u i scope rho (at succ two) three;
  ev_eq u i scope rho (at succ two) four

(* identity and successor lambdas are different array values *)
let identity_not_successor (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (eq ident succ) /\ bool_v (ev u i scope rho (eq ident succ)) == false) =
  ev_inum u i scope rho 0;
  ident_at u i scope rho zero;
  succ_at u i scope rho zero;
  ev_app2 u i scope rho sel_ii ident zero;
  ev_app2 u i scope rho sel_ii succ zero;
  ev_eq u i scope rho ident succ

(* x + 0 and x are extensionally equal lambdas (law_array_extensionality) *)
let plus_zero_is_identity (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (eq plus_zero ident) /\ bool_v (ev u i scope rho (eq plus_zero ident)) == true) =
  assert_norm (TR.free sigma ii_s);
  assert_norm (D.scoped scope plus_zero /\ D.scoped scope ident);
  let pointwise (jx:TR.targuments u sch [int_s])
    : Lemma (i.V.application sel_ii (ev u i scope rho plus_zero :: jx) ==
             i.V.application sel_ii (ev u i scope rho ident :: jx)) =
    match jx with
    | [v] ->
      assert_norm (L.rev [int_s] == [int_s]);
      assert_norm (TR.reverse_arguments sigma [int_s] [v] == [v]);
      TR.lemma_eval_select_lambda i scope rho [int_s] int_s (iadd x0 zero) [v];
      TR.lemma_eval_select_lambda i scope rho [int_s] int_s x0 [v];
      let rho' = V.extend sigma scope [int_s] [v] rho in
      ev_inum u i (int_s :: scope) rho' 0;
      ev_iadd u i (int_s :: scope) rho' x0 zero;
      int_ext (ev u i (int_s :: scope) rho' (iadd x0 zero)) v
    | _ -> () in
  FStar.Classical.forall_intro pointwise;
  TR.law_array_extensionality i [int_s] int_s (ev u i scope rho plus_zero) (ev u i scope rho ident);
  ev_eq u i scope rho plus_zero ident

(* ========================================================================== *)
(* E. Typed quantifiers over infinite Int and Real and finite Bool           *)
(* ========================================================================== *)

let pz_body : expr = eq (iadd x0 zero) x0
let p1_body : expr = eq (iadd x0 one) x0
let forall_int (body:expr) : expr = Quantifier Forall_k [int_s] bool_sort body

(* forall x:Int. x + 0 = x  is true *)
let forall_plus_zero (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (forall_int pz_body) /\ bool_v (ev u i scope rho (forall_int pz_body)) == true) =
  assert_norm (L.rev [int_s] == [int_s]);
  TR.lemma_eval_forall i scope rho [int_s] pz_body;
  let inst (vs:TR.targuments u sch (L.rev [int_s]))
    : Lemma (TR.truth sch (V.evaluate sigma i (L.rev [int_s] @ scope)
               (V.extend sigma scope (L.rev [int_s]) vs rho) pz_body) == true) =
    assert_norm (L.rev [int_s] == [int_s]);
    match vs with
    | [v] ->
      let rho' = V.extend sigma scope [int_s] [v] rho in
      ev_inum u i (int_s :: scope) rho' 0;
      ev_iadd u i (int_s :: scope) rho' x0 zero;
      int_ext (ev u i (int_s :: scope) rho' (iadd x0 zero)) v;
      ev_eq u i (int_s :: scope) rho' (iadd x0 zero) x0
    | _ -> () in
  FStar.Classical.forall_intro inst

(* mutation: forall x:Int. x + 1 = x  is false (instance x = 0) *)
let forall_plus_one_false (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (forall_int p1_body) /\ bool_v (ev u i scope rho (forall_int p1_body)) == false) =
  assert_norm (L.rev [int_s] == [int_s]);
  TR.lemma_eval_forall i scope rho [int_s] p1_body;
  let v0 = TR.make #u #sigma int_s 0 in
  let rho' = V.extend sigma scope [int_s] [v0] rho in
  ev_inum u i (int_s :: scope) rho' 1;
  ev_iadd u i (int_s :: scope) rho' x0 one;
  ev_eq u i (int_s :: scope) rho' (iadd x0 one) x0;
  assert (TR.truth sch (V.evaluate sigma i (L.rev [int_s] @ scope)
            (V.extend sigma scope (L.rev [int_s]) [v0] rho) p1_body) == false)

let y0r : expr = Var 0 real_s
let x1r : expr = Var 1 real_s
let halves_r : expr = eq (radd y0r y0r) x1r
let fa_halving_r : expr = Quantifier Forall_k [real_s] bool_sort (Quantifier Exists_k [real_s] bool_sort halves_r)
let y0i : expr = Var 0 int_s
let x1i : expr = Var 1 int_s
let halves_i : expr = eq (iadd y0i y0i) x1i
let fa_halving_i : expr = Quantifier Forall_k [int_s] bool_sort (Quantifier Exists_k [int_s] bool_sort halves_i)

(* The witness step at one value of x, in a small context: y = x / 2. *)
let halving_witness (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
                    (vx:TR.tvalue u sch real_s)
  : Lemma (let rho' = V.extend sigma scope [real_s] [vx] rho in
           let vy = TR.make #u #sigma real_s (real_v vx /. 2.0R) in
           TR.truth sch (ev u i (real_s :: real_s :: scope)
                          (V.extend sigma (real_s :: scope) [real_s] [vy] rho') halves_r) == true) =
  let x = real_v vx in
  let rho' = V.extend sigma scope [real_s] [vx] rho in
  let vy = TR.make #u #sigma real_s (x /. 2.0R) in
  let rho'' = V.extend sigma (real_s :: scope) [real_s] [vy] rho' in
  assert (ev u i (real_s :: real_s :: scope) rho'' y0r == vy);
  assert (ev u i (real_s :: real_s :: scope) rho'' x1r == vx);
  ev_radd u i (real_s :: real_s :: scope) rho'' y0r y0r;
  real_ext (ev u i (real_s :: real_s :: scope) rho'' (radd y0r y0r)) vx;
  ev_eq u i (real_s :: real_s :: scope) rho'' (radd y0r y0r) x1r

(* forall x:Real. exists y:Real. y + y = x  is true (Real is not integer-coded) *)
let forall_halving_real (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope fa_halving_r /\ bool_v (ev u i scope rho fa_halving_r) == true) =
  let inner = Quantifier Exists_k [real_s] bool_sort halves_r in
  assert_norm (L.rev [real_s] == [real_s]);
  TR.lemma_eval_forall i scope rho [real_s] inner;
  let inst (vs:TR.targuments u sch (L.rev [real_s]))
    : Lemma (TR.truth sch (V.evaluate sigma i (L.rev [real_s] @ scope)
               (V.extend sigma scope (L.rev [real_s]) vs rho) inner) == true) =
    assert_norm (L.rev [real_s] == [real_s]);
    match vs with
    | [vx] ->
      let rho' = V.extend sigma scope [real_s] [vx] rho in
      TR.lemma_eval_exists i (real_s :: scope) rho' [real_s] halves_r;
      let vy = TR.make #u #sigma real_s (real_v vx /. 2.0R) in
      halving_witness u i scope rho vx;
      FStar.Classical.exists_intro
        (fun (ws:TR.targuments u sch (L.rev [real_s])) ->
          TR.truth sch (V.evaluate sigma i (L.rev [real_s] @ (real_s :: scope))
            (V.extend sigma (real_s :: scope) (L.rev [real_s]) ws rho') halves_r) == true)
        [vy]
    | _ -> () in
  FStar.Classical.forall_intro inst

(* The Int body y + y = x at one pair of values, in a small context. *)
let halves_i_body (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
                  (vx vy:TR.tvalue u sch int_s)
  : Lemma (let rho'' = V.extend sigma (int_s :: scope) [int_s] [vy] (V.extend sigma scope [int_s] [vx] rho) in
           D.scoped (int_s :: int_s :: scope) halves_i /\
           (bool_v (ev u i (int_s :: int_s :: scope) rho'' halves_i) == true <==> int_v vy + int_v vy == int_v vx)) =
  let sc = int_s :: int_s :: scope in
  let rho'' = V.extend sigma (int_s :: scope) [int_s] [vy] (V.extend sigma scope [int_s] [vx] rho) in
  assert (ev u i sc rho'' y0i == vy);
  assert (ev u i sc rho'' x1i == vx);
  ev_iadd u i sc rho'' y0i y0i;
  ev_eq u i sc rho'' (iadd y0i y0i) x1i;
  if int_v (ev u i sc rho'' (iadd y0i y0i)) = int_v vx then int_ext (ev u i sc rho'' (iadd y0i y0i)) vx

(* mutation: over Int, forall x. exists y. y + y = x  is false (x = 1) *)
let forall_halving_int_false (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope fa_halving_i /\ bool_v (ev u i scope rho fa_halving_i) == false) =
  let inner = Quantifier Exists_k [int_s] bool_sort halves_i in
  assert_norm (L.rev [int_s] == [int_s]);
  TR.lemma_eval_forall i scope rho [int_s] inner;
  let vx = TR.make #u #sigma int_s 1 in
  let rho' = V.extend sigma scope [int_s] [vx] rho in
  TR.lemma_eval_exists i (int_s :: scope) rho' [int_s] halves_i;
  let none (ws:TR.targuments u sch (L.rev [int_s]))
    : Lemma (TR.truth sch (V.evaluate sigma i (L.rev [int_s] @ (int_s :: scope))
               (V.extend sigma (int_s :: scope) (L.rev [int_s]) ws rho') halves_i) == false) =
    assert_norm (L.rev [int_s] == [int_s]);
    match ws with
    | [vy] -> halves_i_body u i scope rho vx vy
    | _ -> () in
  FStar.Classical.forall_intro none;
  assert (TR.truth sch (V.evaluate sigma i (L.rev [int_s] @ scope)
            (V.extend sigma scope (L.rev [int_s]) [vx] rho) inner) == false)

(* Heterogeneous binders: forall (x:Int) (p:Bool). ite p x (x+1) >= x.
   In the body p is Var 0 (innermost) and x is Var 1; the typed argument
   list is L.rev [Int; Bool] = [Bool; Int]. *)
let hite : expr = ite int_s (Var 0 bool_sort) (Var 1 int_s) (iadd (Var 1 int_s) one)
let hb_body : expr = ige hite (Var 1 int_s)
let hb_mutant : expr = eq hite (Var 1 int_s)
let fa_hetero (body:expr) : expr = Quantifier Forall_k [int_s; bool_sort] bool_sort body

let hetero_body (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
                (vp:TR.tvalue u sch bool_sort) (vx:TR.tvalue u sch int_s)
  : Lemma (let rho' = V.extend sigma scope [bool_sort; int_s] [vp; vx] rho in
           D.scoped (bool_sort :: int_s :: scope) hb_body /\ D.scoped (bool_sort :: int_s :: scope) hb_mutant /\
           int_v (ev u i (bool_sort :: int_s :: scope) rho' hite) == (if bool_v vp then int_v vx else int_v vx + 1) /\
           bool_v (ev u i (bool_sort :: int_s :: scope) rho' hb_body) == true /\
           (bool_v (ev u i (bool_sort :: int_s :: scope) rho' hb_mutant) == true <==> bool_v vp == true)) =
  let sc = bool_sort :: int_s :: scope in
  let rho' = V.extend sigma scope [bool_sort; int_s] [vp; vx] rho in
  assert (ev u i sc rho' (Var 0 bool_sort) == vp);
  assert (ev u i sc rho' (Var 1 int_s) == vx);
  ev_inum u i sc rho' 1;
  ev_iadd u i sc rho' (Var 1 int_s) one;
  ev_ite u i sc rho' int_s (Var 0 bool_sort) (Var 1 int_s) (iadd (Var 1 int_s) one);
  ev_icompare u i sc rho' hite (Var 1 int_s);
  ev_eq u i sc rho' hite (Var 1 int_s);
  if bool_v vp then int_ext (ev u i sc rho' hite) vx

let hetero_scoped (scope:list sort)
  : Lemma (D.scoped scope (fa_hetero hb_body) /\ D.scoped scope (fa_hetero hb_mutant) /\
           L.rev [int_s; bool_sort] == [bool_sort; int_s]) =
  assert_norm (L.rev [int_s; bool_sort] == [bool_sort; int_s]);
  assert_norm (D.scoped scope (fa_hetero hb_body) /\ D.scoped scope (fa_hetero hb_mutant))

(* forall (x:Int) (p:Bool). ite p x (x+1) >= x  is true *)
let forall_hetero (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (fa_hetero hb_body) /\ bool_v (ev u i scope rho (fa_hetero hb_body)) == true) =
  hetero_scoped scope;
  TR.lemma_eval_forall i scope rho [int_s; bool_sort] hb_body;
  let inst (vs:TR.targuments u sch (L.rev [int_s; bool_sort]))
    : Lemma (TR.truth sch (V.evaluate sigma i (L.rev [int_s; bool_sort] @ scope)
               (V.extend sigma scope (L.rev [int_s; bool_sort]) vs rho) hb_body) == true) =
    hetero_scoped scope;
    match vs with
    | [vp; vx] -> hetero_body u i scope rho vp vx
    | _ -> () in
  FStar.Classical.forall_intro inst

(* mutation: forall (x:Int) (p:Bool). ite p x (x+1) = x  is false (instance p = false, x = 0) *)
let forall_hetero_mutant (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (fa_hetero hb_mutant) /\ bool_v (ev u i scope rho (fa_hetero hb_mutant)) == false) =
  hetero_scoped scope;
  TR.lemma_eval_forall i scope rho [int_s; bool_sort] hb_mutant;
  let vf = TR.boolean #u sch false in
  let v0 = TR.make #u #sigma int_s 0 in
  hetero_body u i scope rho vf v0;
  assert (TR.truth sch (V.evaluate sigma i (L.rev [int_s; bool_sort] @ scope)
            (V.extend sigma scope (L.rev [int_s; bool_sort]) [vf; v0] rho) hb_mutant) == false)

(* ========================================================================== *)
(* F. Multi-index arrays: lambdas (binder order), read-over-write, nesting   *)
(* ========================================================================== *)

let ev_at2 (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope) (s1 s2 t:sort)
           (body e1 e2:expr)
  : Lemma (requires TR.free sigma (ArraySort [s1; s2] t) /\ D.scoped (s2 :: s1 :: scope) body /\
                    get_sort body == t /\ D.scoped scope e1 /\ D.scoped scope e2 /\
                    get_sort e1 == s1 /\ get_sort e2 == s2)
          (ensures D.scoped scope (App (TR.select_decl [s1; s2] t)
                                     [Quantifier Lambda_k [s1; s2] (ArraySort [s1; s2] t) body; e1; e2]) /\
                   ev u i scope rho (App (TR.select_decl [s1; s2] t)
                                       [Quantifier Lambda_k [s1; s2] (ArraySort [s1; s2] t) body; e1; e2]) ==
                   ev u i (s2 :: s1 :: scope)
                     (V.extend sigma scope [s2; s1] [ev u i scope rho e2; ev u i scope rho e1] rho) body) =
  let lam2 = Quantifier Lambda_k [s1; s2] (ArraySort [s1; s2] t) body in
  assert_norm (L.rev [s1; s2] == [s2; s1]);
  ev_app3 u i scope rho (TR.select_decl [s1; s2] t) lam2 e1 e2;
  let v1 = ev u i scope rho e1 in
  let v2 = ev u i scope rho e2 in
  assert_norm (TR.reverse_arguments sigma [s1; s2] [v1; v2] == [v2; v1]);
  TR.lemma_eval_select_lambda i scope rho [s1; s2] t body [v1; v2]

(* lambda (x:Int) (y:Int). x - y   -- inside the body y is Var 0, x is Var 1 *)
let iii_s : sort = ArraySort [int_s; int_s] int_s
let minus_body : expr = isub (Var 1 int_s) (Var 0 int_s)
let minus_lam : expr = Quantifier Lambda_k [int_s; int_s] iii_s minus_body
let read_minus : expr = App (TR.select_decl [int_s; int_s] int_s) [minus_lam; five; two]

let read_minus_value (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope read_minus /\ int_v (ev u i scope rho read_minus) == 3) =
  ev_inum u i scope rho 5;
  ev_inum u i scope rho 2;
  assert_norm (TR.free sigma iii_s);
  ev_at2 u i scope rho int_s int_s int_s minus_body five two;
  let rho' = V.extend sigma scope [int_s; int_s] [ev u i scope rho two; ev u i scope rho five] rho in
  ev_isub u i (int_s :: int_s :: scope) rho' (Var 1 int_s) (Var 0 int_s)

(* select (lambda x y. x - y) 5 2 = 3; the swapped-order value -3 is false *)
let minus_reads (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (eq read_minus three) /\ D.scoped scope (eq read_minus (inum (-3))) /\
           bool_v (ev u i scope rho (eq read_minus three)) == true /\
           bool_v (ev u i scope rho (eq read_minus (inum (-3)))) == false) =
  read_minus_value u i scope rho;
  ev_inum u i scope rho 3;
  ev_inum u i scope rho (-3);
  int_ext (ev u i scope rho read_minus) (ev u i scope rho three);
  ev_eq u i scope rho read_minus three;
  ev_eq u i scope rho read_minus (inum (-3))

(* Heterogeneous lambda (x:Int) (p:Bool). ite p x (x + 1) at (Array Int Bool Int) *)
let ibi_s : sort = ArraySort [int_s; bool_sort] int_s
let choose_lam : expr = Quantifier Lambda_k [int_s; bool_sort] ibi_s hite
let read_choose (p:expr) : expr = App (TR.select_decl [int_s; bool_sort] int_s) [choose_lam; five; p]

let choose_value (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope) (p:expr)
  : Lemma (requires D.scoped scope p /\ get_sort p == bool_sort)
          (ensures D.scoped scope (read_choose p) /\
                   int_v (ev u i scope rho (read_choose p)) == (if bool_v (ev u i scope rho p) then 5 else 6)) =
  ev_inum u i scope rho 5;
  assert_norm (TR.free sigma ibi_s);
  ev_at2 u i scope rho int_s bool_sort int_s hite five p;
  hetero_body u i scope rho (ev u i scope rho p) (ev u i scope rho five)

(* select (lambda (x:Int) (p:Bool). ite p x (x+1)) 5 true = 5, 5 false = 6; mutant (5, true) = 6 false *)
let choose_reads (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (read_choose true_e) /\ D.scoped scope (read_choose false_e) /\
           D.scoped scope (eq (read_choose true_e) six) /\
           int_v (ev u i scope rho (read_choose true_e)) == 5 /\
           int_v (ev u i scope rho (read_choose false_e)) == 6 /\
           bool_v (ev u i scope rho (eq (read_choose true_e) six)) == false) =
  ev_constants u i scope rho;
  choose_value u i scope rho true_e;
  choose_value u i scope rho false_e;
  ev_inum u i scope rho 6;
  ev_eq u i scope rho (read_choose true_e) six

(* Multi-index read-over-write at (Array Int Bool Real), heterogeneous index tuple *)
let ibr_s : sort = ArraySort [int_s; bool_sort] real_s
let scope3 : list sort = [ibr_s]
let c0 : expr = Var 0 ibr_s
let q34 : expr = rnum 3 4
let store2_d : func_decl = TR.store_decl [int_s; bool_sort] real_s
let select2_d : func_decl = TR.select_decl [int_s; bool_sort] real_s
let store2 : expr = App store2_d [c0; one; true_e; q34]
let read2 (p:expr) : expr = App select2_d [store2; one; p]
let orig2 (p:expr) : expr = App select2_d [c0; one; p]

let ev_store2 (u:TR.uninterpreted) (i:model u) (rho:env u scope3)
  : Lemma (D.scoped scope3 store2 /\
           ev u i scope3 rho store2 ==
           i.V.application store2_d
             (TR.store_arguments #u #sch [int_s; bool_sort] real_s (rho 0)
               [ev u i scope3 rho one; ev u i scope3 rho true_e] (ev u i scope3 rho q34))) =
  ev_inum u i scope3 rho 1;
  ev_constants u i scope3 rho;
  ev_rnum u i scope3 rho 3 4;
  ev_app4 u i scope3 rho store2_d c0 one true_e q34;
  assert_norm (TR.store_arguments #u #sch [int_s; bool_sort] real_s (rho 0)
                 [ev u i scope3 rho one; ev u i scope3 rho true_e] (ev u i scope3 rho q34) ==
               [rho 0; ev u i scope3 rho one; ev u i scope3 rho true_e; ev u i scope3 rho q34])

(* select(store(c, 1, true, 3/4), 1, true) = 3/4 *)
let multi_store_same (u:TR.uninterpreted) (i:model u) (rho:env u scope3)
  : Lemma (D.scoped scope3 (read2 true_e) /\ ev u i scope3 rho (read2 true_e) == ev u i scope3 rho q34) =
  ev_store2 u i rho;
  ev_app3 u i scope3 rho select2_d store2 one true_e;
  assert_norm (TR.free sigma ibr_s);
  TR.law_select_store_same i [int_s; bool_sort] real_s (rho 0)
    [ev u i scope3 rho one; ev u i scope3 rho true_e] (ev u i scope3 rho q34)

(* select(store(c, 1, true, 3/4), 1, false) = select(c, 1, false): the tuples differ only in the Bool index *)
let multi_store_other (u:TR.uninterpreted) (i:model u) (rho:env u scope3)
  : Lemma (D.scoped scope3 (read2 false_e) /\ D.scoped scope3 (orig2 false_e) /\
           ev u i scope3 rho (read2 false_e) == ev u i scope3 rho (orig2 false_e)) =
  ev_store2 u i rho;
  ev_constants u i scope3 rho;
  ev_app3 u i scope3 rho select2_d store2 one false_e;
  ev_app3 u i scope3 rho select2_d c0 one false_e;
  assert_norm (TR.free sigma ibr_s);
  TR.law_select_store_other i [int_s; bool_sort] real_s (rho 0)
    [ev u i scope3 rho one; ev u i scope3 rho true_e] [ev u i scope3 rho one; ev u i scope3 rho false_e]
    (ev u i scope3 rho q34)

let real_quarters () : Lemma (~(of_int 3 /. of_int 4 == of_int 1 /. of_int 4)) = ()

(* 3/4 read back is true; 1/4 is false *)
let multi_store_reads (u:TR.uninterpreted) (i:model u) (rho:env u scope3)
  : Lemma (D.scoped scope3 (eq (read2 true_e) q34) /\ D.scoped scope3 (eq (read2 true_e) (rnum 1 4)) /\
           bool_v (ev u i scope3 rho (eq (read2 true_e) q34)) == true /\
           bool_v (ev u i scope3 rho (eq (read2 true_e) (rnum 1 4))) == false) =
  multi_store_same u i rho;
  ev_rnum u i scope3 rho 3 4;
  ev_rnum u i scope3 rho 1 4;
  real_quarters ();
  ev_eq u i scope3 rho (read2 true_e) q34;
  ev_eq u i scope3 rho (read2 true_e) (rnum 1 4)

(* Nested arrays (Array Int (Array Int Real)):
   select (select (store b 0 (store a 0 1/2)) 0) 0 = 1/2 *)
let nested_s : sort = ArraySort [int_s] arr_s
let scope2 : list sort = [arr_s; nested_s]
let a_2 : expr = Var 0 arr_s
let b_2 : expr = Var 1 nested_s
let select_n : func_decl = TR.select_decl [int_s] arr_s
let store_n : func_decl = TR.store_decl [int_s] arr_s
let inner_store : expr = App store_ir [a_2; zero; half]
let outer_store : expr = App store_n [b_2; zero; inner_store]
let outer_read : expr = App select_n [outer_store; zero]
let nested_read : expr = App select_ir [outer_read; zero]

let nested_carrier (u:TR.uninterpreted)
  : Lemma (TR.carrier u nested_s == TR.func_space (int & unit) (TR.func_space (int & unit) real)) =
  assert_norm (TR.carrier u nested_s == TR.func_space (int & unit) (TR.func_space (int & unit) real))

let nested_outer (u:TR.uninterpreted) (i:model u) (rho:env u scope2)
  : Lemma (D.scoped scope2 outer_read /\ ev u i scope2 rho outer_read == ev u i scope2 rho inner_store) =
  let z = ev u i scope2 rho zero in
  ev_inum u i scope2 rho 0;
  ev_rnum u i scope2 rho 1 2;
  ev_app3 u i scope2 rho store_ir a_2 zero half;
  ev_app3 u i scope2 rho store_n b_2 zero inner_store;
  ev_app2 u i scope2 rho select_n outer_store zero;
  assert_norm (TR.store_arguments #u #sch [int_s] arr_s (rho 1) [z] (ev u i scope2 rho inner_store) ==
               [rho 1; z; ev u i scope2 rho inner_store]);
  assert_norm (TR.free sigma nested_s);
  TR.law_select_store_same i [int_s] arr_s (rho 1) [z] (ev u i scope2 rho inner_store)

let nested_read_back (u:TR.uninterpreted) (i:model u) (rho:env u scope2)
  : Lemma (D.scoped scope2 (eq nested_read half) /\ bool_v (ev u i scope2 rho (eq nested_read half)) == true) =
  let z = ev u i scope2 rho zero in
  nested_outer u i rho;
  ev_app2 u i scope2 rho select_ir outer_read zero;
  ev_app3 u i scope2 rho store_ir a_2 zero half;
  assert_norm (TR.store_arguments #u #sch [int_s] real_s (rho 0) [z] (ev u i scope2 rho half) ==
               [rho 0; z; ev u i scope2 rho half]);
  assert_norm (TR.free sigma arr_s);
  TR.law_select_store_same i [int_s] real_s (rho 0) [z] (ev u i scope2 rho half);
  ev_eq u i scope2 rho nested_read half

(* ========================================================================== *)
(* G. Real division: law at a nonzero divisor, FREE at zero                  *)
(* ========================================================================== *)

let one_r : expr = rnum 1 1
let zero_r : expr = rnum 0 1
let two_r : expr = rnum 2 1
let div_by_two : expr = rdiv one_r two_r
let div_by_zero : expr = rdiv one_r zero_r

(* 1/2 computed by division equals the numeral 1/2, in every root model *)
let division_by_two (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (eq div_by_two half) /\ bool_v (ev u i scope rho (eq div_by_two half)) == true) =
  ev_rnum u i scope rho 1 1;
  ev_rnum u i scope rho 2 1;
  ev_rnum u i scope rho 1 2;
  ev_rdiv u i scope rho one_r two_r;
  real_ext (ev u i scope rho div_by_two) (ev u i scope rho half);
  ev_eq u i scope rho div_by_two half

(* The contract does not force 1/0 = 0 (semantic control: not derivable). *)
[@@expect_failure [19]]
let division_by_zero_forced (u:TR.uninterpreted) (i:model u) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (eq div_by_zero zero_r) /\ bool_v (ev u i scope rho (eq div_by_zero zero_r)) == true) =
  ev_rnum u i scope rho 1 1;
  ev_rnum u i scope rho 0 1;
  ev_eq u i scope rho div_by_zero zero_r
let real_zero () : Lemma (of_int 0 /. of_int 1 == 0.0R) = ()

(* In the standard family 1/0 is exactly the free choice uf.apply. *)
let division_by_zero_is_free (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope div_by_zero /\
           ev u (TR.standard u sch uf) scope rho div_by_zero ==
           uf.TR.apply TR.divide_decl [ev u (TR.standard u sch uf) scope rho one_r;
                                       ev u (TR.standard u sch uf) scope rho zero_r]) =
  TR.lemma_standard_root u sch uf;
  let i : model u = TR.standard u sch uf in
  ev_rnum u i scope rho 1 1;
  ev_rnum u i scope rho 0 1;
  real_zero ();
  ev_app2 u i scope rho TR.divide_decl one_r zero_r;
  TR.lemma_classify_divide sch;
  TR.lemma_standard_divide_by_zero u sch uf TR.divide_decl (ev u i scope rho one_r) (ev u i scope rho zero_r)

(* Two free-symbol choices that differ only in the value of x/0 for reals. *)
let uf_const (u:TR.uninterpreted) (k:real) : TR.symbols u sch = {
  TR.apply = (fun f _ ->
    if f.range = real_s then TR.make #u #sigma real_s k
    else S.value_inhabitant sch (TR.default_value u) f.range);
  TR.lambda = (fun bound t _ -> S.value_inhabitant sch (TR.default_value u) (ArraySort bound t));
}

(* Coverage control: both are root models (L1) of the corrected contract,
   yet they disagree on 1/0 = 0. Division by zero is not forced. *)
let division_by_zero_not_forced (u:TR.uninterpreted) (scope:list sort) (rho:env u scope)
  : Lemma (TR.root_model u sch (TR.standard u sch (uf_const u 0.0R)) /\
           TR.root_model u sch (TR.standard u sch (uf_const u 1.0R)) /\
           D.scoped scope (eq div_by_zero zero_r) /\
           bool_v (ev u (TR.standard u sch (uf_const u 0.0R)) scope rho (eq div_by_zero zero_r)) == true /\
           bool_v (ev u (TR.standard u sch (uf_const u 1.0R)) scope rho (eq div_by_zero zero_r)) == false) =
  TR.lemma_standard_root u sch (uf_const u 0.0R);
  TR.lemma_standard_root u sch (uf_const u 1.0R);
  let i0 : model u = TR.standard u sch (uf_const u 0.0R) in
  let i1 : model u = TR.standard u sch (uf_const u 1.0R) in
  division_by_zero_is_free u (uf_const u 0.0R) scope rho;
  division_by_zero_is_free u (uf_const u 1.0R) scope rho;
  ev_rnum u i0 scope rho 0 1;
  ev_rnum u i1 scope rho 0 1;
  real_ext (ev u i0 scope rho div_by_zero) (ev u i0 scope rho zero_r);
  ev_eq u i0 scope rho div_by_zero zero_r;
  ev_eq u i1 scope rho div_by_zero zero_r

(* ========================================================================== *)
(* H. Uninterpreted carriers stay model-chosen (size 1 versus 2)             *)
(* ========================================================================== *)

let us : sort = BaseSort "U"
let u_two : TR.uninterpreted = { TR.sort_carrier = (fun _ -> bool); TR.inhabitant = (fun _ -> false) }
let u_one : TR.uninterpreted = { TR.sort_carrier = (fun _ -> unit); TR.inhabitant = (fun _ -> ()) }

let lemma_u_carrier (u:TR.uninterpreted) : Lemma (TR.carrier u us == u.TR.sort_carrier us) =
  assert_norm (TR.carrier u us == u.TR.sort_carrier us)

let ne_body : expr = not_ (eq (Var 1 us) (Var 0 us))
let ex_ne : expr = Quantifier Exists_k [us; us] bool_sort ne_body

let ne_value (u:TR.uninterpreted) (i:model u) (rho:env u []) (vx vy:TR.tvalue u sch us)
  : Lemma (D.scoped [us; us] ne_body /\
           (bool_v (ev u i [us; us] (V.extend sigma [] [us; us] [vy; vx] rho) ne_body) == true <==> ~(vy == vx))) =
  let rho' = V.extend sigma [] [us; us] [vy; vx] rho in
  assert (ev u i [us; us] rho' (Var 0 us) == vy);
  assert (ev u i [us; us] rho' (Var 1 us) == vx);
  ev_eq u i [us; us] rho' (Var 1 us) (Var 0 us);
  ev_not u i [us; us] rho' (eq (Var 1 us) (Var 0 us))

(* exists x y:U. x <> y : true when u gives U two elements, in every root model *)
let two_elements (i:model u_two) (rho:env u_two [])
  : Lemma (D.scoped [] ex_ne /\ bool_v (ev u_two i [] rho ex_ne) == true) =
  assert_norm (L.rev [us; us] == [us; us]);
  TR.lemma_eval_exists i [] rho [us; us] ne_body;
  lemma_u_carrier u_two;
  let vt : TR.tvalue u_two sch us = V.Scalar us (true <: TR.carrier u_two us) in
  let vf : TR.tvalue u_two sch us = V.Scalar us (false <: TR.carrier u_two us) in
  ne_value u_two i rho vf vt;
  assert (TR.truth sch (V.evaluate sigma i (L.rev [us; us] @ [])
            (V.extend sigma [] (L.rev [us; us]) [vt; vf] rho) ne_body) == true)

let one_element_equal (x y:TR.tvalue u_one sch us) : Lemma (x == y) =
  lemma_u_carrier u_one;
  match x, y with
  | V.Scalar _ a, V.Scalar _ b -> let _ : unit = a in let _ : unit = b in ()
  | _ -> ()

(* ... and false when U is a singleton, in every root model *)
let one_element (i:model u_one) (rho:env u_one [])
  : Lemma (D.scoped [] ex_ne /\ bool_v (ev u_one i [] rho ex_ne) == false) =
  assert_norm (L.rev [us; us] == [us; us]);
  TR.lemma_eval_exists i [] rho [us; us] ne_body;
  let none (ws:TR.targuments u_one sch (L.rev [us; us]))
    : Lemma (TR.truth sch (V.evaluate sigma i (L.rev [us; us] @ [])
               (V.extend sigma [] (L.rev [us; us]) ws rho) ne_body) == false) =
    assert_norm (L.rev [us; us] == [us; us]);
    match ws with
    | [vy; vx] -> one_element_equal vy vx; ne_value u_one i rho vx vy
    | _ -> () in
  FStar.Classical.forall_intro none

(* ========================================================================== *)
(* I. Datatypes: R5/R6 for EVERY root model, the always-false recognizer     *)
(*    countermodel is excluded, unmatched selectors stay free               *)
(* ========================================================================== *)

let l_s : sort = BaseSort "IntList"
let nil_decl : func_decl =
  { decl_name = "nil"; domain = []; range = l_s; interp = Some DL.op_constructor; int_params = [0; 0; 0] }
let cons_decl : func_decl =
  { decl_name = "cons"; domain = [int_s; l_s]; range = l_s; interp = Some DL.op_constructor; int_params = [0; 1; 2] }
let is_nil_decl : func_decl =
  { decl_name = "is-nil"; domain = [l_s]; range = bool_sort; interp = Some DL.op_recognizer; int_params = [0; 0] }
let is_cons_decl : func_decl =
  { decl_name = "is-cons"; domain = [l_s]; range = bool_sort; interp = Some DL.op_recognizer; int_params = [0; 1] }
let head_decl : func_decl =
  { decl_name = "head"; domain = [l_s]; range = int_s; interp = Some DL.op_accessor; int_params = [0; 1; 0] }
let tail_decl : func_decl =
  { decl_name = "tail"; domain = [l_s]; range = l_s; interp = Some DL.op_accessor; int_params = [0; 1; 1] }

let nil_case : S.constructor_case = { S.constructor = nil_decl; S.recognizer = is_nil_decl; S.accessors = [] }
let cons_case : S.constructor_case =
  { S.constructor = cons_decl; S.recognizer = is_cons_decl; S.accessors = [head_decl; tail_decl] }
let list_schema : S.schema = { S.sorts = [l_s]; S.cases = [nil_case; cons_case] }

let lsch : TR.supported_schema = assert_norm (TR.supported list_schema); list_schema
let lsigma : V.signature = S.signature lsch

type lenv (u:TR.uninterpreted) = V.environment (TR.carrier u) lsigma []
type lmodel (u:TR.uninterpreted) = i:TR.interp u lsch{TR.root_model u lsch i}

let evl (u:TR.uninterpreted) (i:TR.interp u lsch) (rho:lenv u) (e:expr{D.scoped [] e})
  : GTot (TR.tvalue u lsch (get_sort e)) =
  V.evaluate lsigma i [] rho e

let nil_e : expr = App nil_decl []
let cons_one_nil : expr = App cons_decl [one; nil_e]
let is_nil_of (l:expr) : expr = App is_nil_decl [l]
let is_cons_of (l:expr) : expr = App is_cons_decl [l]
let head_of (l:expr) : expr = App head_decl [l]
let tail_of (l:expr) : expr = App tail_decl [l]

let member_facts ()
  : Lemma (L.mem nil_decl lsigma /\ L.mem cons_decl lsigma /\
           L.mem nil_case lsch.S.cases /\ L.mem cons_case lsch.S.cases /\
           not (L.mem (TR.int_numeral 1) lsigma) /\ not (L.mem head_decl lsigma)) =
  assert_norm (L.mem nil_decl lsigma /\ L.mem cons_decl lsigma);
  assert_norm (L.mem nil_case lsch.S.cases /\ L.mem cons_case lsch.S.cases);
  assert_norm (not (L.mem (TR.int_numeral 1) lsigma) /\ not (L.mem head_decl lsigma))

(* The executable metadata search finds the recognizers and accessors. *)
let recognizer_facts ()
  : Lemma (S.find_recognizer is_nil_decl lsch.S.cases == Some nil_case /\
           S.find_recognizer is_cons_decl lsch.S.cases == Some cons_case /\
           None? (S.find_recognizer head_decl lsch.S.cases)) =
  assert_norm (S.find_recognizer is_nil_decl lsch.S.cases == Some nil_case);
  assert_norm (S.find_recognizer is_cons_decl lsch.S.cases == Some cons_case);
  assert_norm (None? (S.find_recognizer head_decl lsch.S.cases))

let accessor_facts ()
  : Lemma (Some? (S.find_accessor head_decl lsch.S.cases) /\
           (Some?.v (S.find_accessor head_decl lsch.S.cases)).S.matched_case == cons_case /\
           (Some?.v (S.find_accessor head_decl lsch.S.cases)).S.field == 0 /\
           Some? (S.find_accessor tail_decl lsch.S.cases) /\
           (Some?.v (S.find_accessor tail_decl lsch.S.cases)).S.matched_case == cons_case /\
           (Some?.v (S.find_accessor tail_decl lsch.S.cases)).S.field == 1) =
  assert_norm (Some? (S.find_accessor head_decl lsch.S.cases) /\
               (Some?.v (S.find_accessor head_decl lsch.S.cases)).S.matched_case == cons_case /\
               (Some?.v (S.find_accessor head_decl lsch.S.cases)).S.field == 0);
  assert_norm (Some? (S.find_accessor tail_decl lsch.S.cases) /\
               (Some?.v (S.find_accessor tail_decl lsch.S.cases)).S.matched_case == cons_case /\
               (Some?.v (S.find_accessor tail_decl lsch.S.cases)).S.field == 1)

let list_scoped ()
  : Lemma (D.scoped [] nil_e /\ D.scoped [] one /\ D.scoped [] cons_one_nil /\
           D.scoped [] (is_cons_of cons_one_nil) /\ D.scoped [] (is_cons_of nil_e) /\
           D.scoped [] (is_nil_of nil_e) /\ D.scoped [] (is_nil_of cons_one_nil) /\
           D.scoped [] (head_of cons_one_nil) /\ D.scoped [] (tail_of cons_one_nil) /\
           D.scoped [] (head_of nil_e)) =
  assert_norm (D.scoped [] nil_e /\ D.scoped [] one /\ D.scoped [] cons_one_nil /\
               D.scoped [] (is_cons_of cons_one_nil) /\ D.scoped [] (is_cons_of nil_e) /\
               D.scoped [] (is_nil_of nil_e) /\ D.scoped [] (is_nil_of cons_one_nil) /\
               D.scoped [] (head_of cons_one_nil) /\ D.scoped [] (tail_of cons_one_nil) /\
               D.scoped [] (head_of nil_e))

let nil_v (u:TR.uninterpreted) : TR.tvalue u lsch l_s =
  member_facts (); S.constructor_value lsch nil_case []

(* The numeral 1 by its law, in every root model of the list schema. *)
let ev_lone (u:TR.uninterpreted) (i:lmodel u) (rho:lenv u)
  : Lemma (D.scoped [] one /\ TR.int_of lsch (evl u i rho one) == 1) =
  member_facts ();
  TR.lemma_classify_numerals lsch 1 1;
  TR.law_int_numeral i (TR.int_numeral 1) 1 1 []

(* Constructors are built by the evaluator, under ANY interpretation. *)
let ev_lcons (u:TR.uninterpreted) (i:TR.interp u lsch) (rho:lenv u)
  : Lemma (D.scoped [] nil_e /\ D.scoped [] cons_one_nil /\
           evl u i rho nil_e == nil_v u /\
           evl u i rho cons_one_nil == S.constructor_value lsch cons_case [evl u i rho one; nil_v u]) =
  member_facts ();
  list_scoped ()

(* R5 for every root model: is-cons(cons 1 nil) true, is-cons(nil) false. *)
let recognizers_cons (u:TR.uninterpreted) (i:lmodel u) (rho:lenv u)
  : Lemma (D.scoped [] (is_cons_of cons_one_nil) /\ D.scoped [] (is_cons_of nil_e) /\
           TR.truth lsch (evl u i rho (is_cons_of cons_one_nil)) == true /\
           TR.truth lsch (evl u i rho (is_cons_of nil_e)) == false) =
  member_facts (); recognizer_facts (); list_scoped ();
  ev_lcons u i rho;
  TR.lemma_not_registered lsch is_cons_decl;
  let ys : TR.targuments u lsch cons_decl.domain = [evl u i rho one; nil_v u] in
  TR.law_recognizer i is_cons_decl cons_case ys;
  TR.law_recognizer i is_cons_decl nil_case []

(* R5 for every root model: is-nil(nil) true, is-nil(cons 1 nil) false. *)
let recognizers_nil (u:TR.uninterpreted) (i:lmodel u) (rho:lenv u)
  : Lemma (D.scoped [] (is_nil_of nil_e) /\ D.scoped [] (is_nil_of cons_one_nil) /\
           TR.truth lsch (evl u i rho (is_nil_of nil_e)) == true /\
           TR.truth lsch (evl u i rho (is_nil_of cons_one_nil)) == false) =
  member_facts (); recognizer_facts (); list_scoped ();
  ev_lcons u i rho;
  TR.lemma_not_registered lsch is_nil_decl;
  let ys : TR.targuments u lsch cons_decl.domain = [evl u i rho one; nil_v u] in
  TR.law_recognizer i is_nil_decl nil_case [];
  TR.law_recognizer i is_nil_decl cons_case ys

(* R6 for every root model: head(cons 1 nil) = 1, tail(cons 1 nil) = nil *)
let accessors (u:TR.uninterpreted) (i:lmodel u) (rho:lenv u)
  : Lemma (D.scoped [] (head_of cons_one_nil) /\ D.scoped [] (tail_of cons_one_nil) /\
           TR.int_of lsch (evl u i rho (head_of cons_one_nil)) == 1 /\
           evl u i rho (tail_of cons_one_nil) == nil_v u) =
  member_facts (); accessor_facts (); list_scoped ();
  ev_lone u i rho;
  ev_lcons u i rho;
  TR.lemma_not_registered lsch head_decl;
  TR.lemma_not_registered lsch tail_decl;
  let ys : TR.targuments u lsch cons_decl.domain = [evl u i rho one; nil_v u] in
  TR.law_accessor i head_decl ys;
  TR.law_accessor i tail_decl ys

(* The independent verifier's countermodel: standard with is-cons answered
   false everywhere. It satisfied the OLD contract; it is NOT a model of the
   corrected one. *)
let wrong_recognizer (u:TR.uninterpreted) (uf:TR.symbols u lsch) : TR.interp u lsch =
  let i = TR.standard u lsch uf in
  { V.application = (fun (f:func_decl) (xs:TR.targuments u lsch f.domain) ->
      if f = is_cons_decl then (TR.boolean #u lsch false <: TR.tvalue u lsch f.range)
      else i.V.application f xs);
    V.quantification = i.V.quantification }

let wrong_recognizer_not_root (u:TR.uninterpreted) (uf:TR.symbols u lsch)
  : Lemma (~(TR.root_model u lsch (wrong_recognizer u uf))) =
  member_facts (); recognizer_facts ();
  let ys : TR.targuments u lsch cons_decl.domain = [TR.make #u #lsigma int_s 1; nil_v u] in
  let aux () : Lemma (requires TR.root_model u lsch (wrong_recognizer u uf)) (ensures False) =
    TR.law_recognizer (wrong_recognizer u uf) is_cons_decl cons_case ys in
  FStar.Classical.move_requires aux ()

(* An unmatched selector is the standard model's free choice ... *)
let head_of_nil_is_free (u:TR.uninterpreted) (uf:TR.symbols u lsch) (rho:lenv u)
  : Lemma (D.scoped [] (head_of nil_e) /\
           evl u (TR.standard u lsch uf) rho (head_of nil_e) == uf.TR.apply head_decl [nil_v u]) =
  member_facts (); recognizer_facts (); accessor_facts (); list_scoped ();
  ev_lcons u (TR.standard u lsch uf) rho;
  assert_norm (TR.classify lsigma head_decl == TR.Other)

let uf_int (u:TR.uninterpreted) (k:int) : TR.symbols u lsch = {
  TR.apply = (fun f _ ->
    if f.range = int_s then TR.make #u #lsigma int_s k
    else S.value_inhabitant lsch (TR.default_value u) f.range);
  TR.lambda = (fun bound t _ -> S.value_inhabitant lsch (TR.default_value u) (ArraySort bound t));
}

(* ... so two models of the CORRECTED contract disagree on head(nil). *)
let head_of_nil_not_forced (u:TR.uninterpreted) (rho:lenv u)
  : Lemma (TR.root_model u lsch (TR.standard u lsch (uf_int u 0)) /\
           TR.root_model u lsch (TR.standard u lsch (uf_int u 1)) /\
           D.scoped [] (head_of nil_e) /\
           evl u (TR.standard u lsch (uf_int u 0)) rho (head_of nil_e) == TR.make #u #lsigma int_s 0 /\
           evl u (TR.standard u lsch (uf_int u 1)) rho (head_of nil_e) == TR.make #u #lsigma int_s 1) =
  TR.lemma_standard_root u lsch (uf_int u 0);
  TR.lemma_standard_root u lsch (uf_int u 1);
  head_of_nil_is_free u (uf_int u 0) rho;
  head_of_nil_is_free u (uf_int u 1) rho

(* ========================================================================== *)
(* J. The support predicates: positive and negative pins                     *)
(* ========================================================================== *)

let support_positive_schemas () : Lemma (TR.supported empty_schema /\ TR.supported list_schema) =
  assert_norm (TR.supported empty_schema /\ TR.supported list_schema)

let support_positive_reals () : Lemma (TR.supported_expression sigma o1_half_e /\
                                       TR.supported_expression sigma fa_halving_r /\
                                       TR.supported_expression sigma three_halves) =
  assert_norm (TR.supported_expression sigma o1_half_e /\ TR.supported_expression sigma fa_halving_r /\
               TR.supported_expression sigma three_halves)

let support_positive_arrays () : Lemma (TR.supported_expression sigma (eq nested_read half) /\
                                        TR.supported_expression sigma (eq read_minus three) /\
                                        TR.supported_expression sigma (read_choose true_e) /\
                                        TR.supported_expression sigma (read2 false_e) /\
                                        TR.supported_expression sigma (fa_hetero hb_body)) =
  assert_norm (TR.supported_expression sigma (eq nested_read half));
  assert_norm (TR.supported_expression sigma (eq read_minus three));
  assert_norm (TR.supported_expression sigma (read_choose true_e));
  assert_norm (TR.supported_expression sigma (read2 false_e));
  assert_norm (TR.supported_expression sigma (fa_hetero hb_body))

(* Datatype sorts used directly (trees, recognizers, selectors, binders) and
   datatype-free arrays next to them are supported. *)
let fa_list : expr =
  Quantifier Forall_k [l_s] bool_sort (or_ (is_nil_of (Var 0 l_s)) (is_cons_of (Var 0 l_s)))
let real_arr_in_list : expr = App (TR.select_decl [int_s] real_s) [Var 0 arr_s; head_of cons_one_nil]

let support_positive_datatypes ()
  : Lemma (TR.supported_document lsch [is_cons_of cons_one_nil; head_of cons_one_nil; fa_list] /\
           TR.supported_expression lsigma real_arr_in_list /\
           TR.supported_sort lsigma arr_s /\ TR.supported_sort lsigma l_s) =
  assert_norm (TR.supported_document lsch [is_cons_of cons_one_nil; head_of cons_one_nil; fa_list]);
  assert_norm (TR.supported_expression lsigma real_arr_in_list);
  assert_norm (TR.supported_sort lsigma arr_s /\ TR.supported_sort lsigma l_s)

(* The implication is usable (not vacuous) on the list schema. *)
let support_implies_array_laws ()
  : Lemma (TR.free lsigma arr_s /\ TR.classify lsigma (TR.select_decl [int_s] real_s) == TR.Select [int_s] real_s /\
           TR.classify lsigma (TR.store_decl [int_s] real_s) == TR.Store [int_s] real_s) =
  assert_norm (TR.supported_sort lsigma arr_s);
  TR.lemma_supported_array lsch [int_s] real_s

let arr_dt : sort = ArraySort [int_s] l_s
let dt_idx : sort = ArraySort [l_s] int_s
let nested_dt : sort = ArraySort [int_s] (ArraySort [int_s] l_s)
let hidden_select : expr = App (TR.select_decl [int_s] l_s) [Var 0 arr_dt; zero]
let hidden_binder : expr = Quantifier Forall_k [arr_dt] bool_sort true_e
let hidden_lambda : expr = Quantifier Lambda_k [int_s] arr_dt nil_e
let g_decl : func_decl = { decl_name = "g"; domain = [nested_dt]; range = int_s; interp = None; int_params = [] }
let hidden_uf : expr = App g_decl [Var 0 nested_dt]

(* Well-scoped terms rejected only by the support check: an array with a
   datatype result, index or nested result; a datatype array hidden in a
   declaration domain under a supported result, in a binder of a Bool
   quantifier, as a lambda sort, under an uninterpreted head. *)
let support_negative ()
  : Lemma (D.scoped [arr_dt] hidden_select /\ D.scoped [] hidden_binder /\ D.scoped [] hidden_lambda /\
           D.scoped [nested_dt] hidden_uf /\
           not (TR.supported_sort lsigma arr_dt) /\ not (TR.supported_sort lsigma dt_idx) /\
           not (TR.supported_sort lsigma nested_dt) /\
           TR.supported_sort lsigma (get_sort hidden_select) /\ not (TR.supported_expression lsigma hidden_select) /\
           not (TR.supported_expression lsigma hidden_binder) /\
           not (TR.supported_expression lsigma hidden_lambda) /\
           TR.supported_sort lsigma (get_sort hidden_uf) /\ not (TR.supported_expression lsigma hidden_uf) /\
           not (TR.supported_expression lsigma (Var 0 dt_idx))) =
  assert_norm (D.scoped [arr_dt] hidden_select /\ D.scoped [] hidden_binder /\ D.scoped [] hidden_lambda /\
               D.scoped [nested_dt] hidden_uf);
  assert_norm (not (TR.supported_sort lsigma arr_dt) /\ not (TR.supported_sort lsigma dt_idx) /\
               not (TR.supported_sort lsigma nested_dt));
  assert_norm (TR.supported_sort lsigma (get_sort hidden_select) /\
               not (TR.supported_expression lsigma hidden_select));
  assert_norm (not (TR.supported_expression lsigma hidden_binder) /\
               not (TR.supported_expression lsigma hidden_lambda));
  assert_norm (TR.supported_sort lsigma (get_sort hidden_uf) /\ not (TR.supported_expression lsigma hidden_uf));
  assert_norm (not (TR.supported_expression lsigma (Var 0 dt_idx)))

(* The schema gate is NOT implied by S.valid. *)
let r_s : sort = BaseSort "Real"
let mk_real_decl : func_decl =
  { decl_name = "mk"; domain = []; range = r_s; interp = Some DL.op_constructor; int_params = [0; 0; 0] }
let is_mk_decl : func_decl =
  { decl_name = "is-mk"; domain = [r_s]; range = bool_sort; interp = Some DL.op_recognizer; int_params = [0; 0] }
let real_named_datatype : S.schema =
  { S.sorts = [r_s]; S.cases = [{ S.constructor = mk_real_decl; S.recognizer = is_mk_decl; S.accessors = [] }] }

(* A datatype registered under the primitive name Real passes S.valid, is
   rejected by the support check, and there the Real heads are FREE symbols
   (so a root model over it is not an SMT semantics). *)
let real_datatype_valid_but_unsupported ()
  : Lemma (S.valid real_named_datatype /\ not (TR.supported real_named_datatype) /\
           TR.classify (S.signature real_named_datatype) (TR.real_numeral 1 2) == TR.Other /\
           TR.classify (S.signature real_named_datatype) (TR.plus_decl real_s) == TR.Other) =
  assert_norm (S.valid real_named_datatype /\ not (TR.supported real_named_datatype));
  assert_norm (TR.classify (S.signature real_named_datatype) (TR.real_numeral 1 2) == TR.Other);
  assert_norm (TR.classify (S.signature real_named_datatype) (TR.plus_decl real_s) == TR.Other)

let ai_s : sort = ArraySort [int_s] int_s
let mk_arr_decl : func_decl =
  { decl_name = "mka"; domain = []; range = ai_s; interp = Some DL.op_constructor; int_params = [1; 0; 0] }
let is_mka_decl : func_decl =
  { decl_name = "is-mka"; domain = [ai_s]; range = bool_sort; interp = Some DL.op_recognizer; int_params = [1; 0] }
let array_owned_datatype : S.schema =
  { S.sorts = [ai_s]; S.cases = [{ S.constructor = mk_arr_decl; S.recognizer = is_mka_decl; S.accessors = [] }] }

(* A constructor whose range is an array sort passes S.valid but is rejected. *)
let array_datatype_valid_but_unsupported ()
  : Lemma (S.valid array_owned_datatype /\ not (TR.supported array_owned_datatype)) =
  assert_norm (S.valid array_owned_datatype /\ not (TR.supported array_owned_datatype))

(* ========================================================================== *)
(* K. Operators explicitly left FREE in this correction (no law)             *)
(* ========================================================================== *)

let mk (name:string) (k:decl_kind) (dom:list sort) (rng:sort) (ps:list int) : func_decl =
  { decl_name = name; domain = dom; range = rng; interp = Some k; int_params = ps }
let bv8 : sort = BaseSort "BV8"

(* distinct, op_num_int numerals, Int div/mod (Z3IntegerDivision op_idiv = 33,
   op_mod = 34), const-array, array-ext, op_oeq, n-ary =, bvand and "/" at
   Int classify as Other: their meaning is a free model choice until a
   future family migration adds and proves a law. *)
let free_operators ()
  : Lemma (TR.classify sigma (mk "distinct" op_distinct [int_s; int_s] bool_sort []) == TR.Other /\
           TR.classify sigma (mk "num" op_num_int [] int_s [5]) == TR.Other /\
           TR.classify sigma (mk "div" 33 [int_s; int_s] int_s []) == TR.Other /\
           TR.classify sigma (mk "mod" 34 [int_s; int_s] int_s []) == TR.Other /\
           TR.classify sigma (mk "const" op_const_array [real_s] arr_s []) == TR.Other /\
           TR.classify sigma (mk "array-ext" op_array_ext [arr_s; arr_s] int_s []) == TR.Other /\
           TR.classify sigma (mk "~" op_oeq [int_s; int_s] bool_sort []) == TR.Other /\
           TR.classify sigma (mk "=" op_eq [int_s; int_s; int_s] bool_sort []) == TR.Other /\
           TR.classify sigma (mk "bvand" op_bvand [bv8; bv8] bv8 []) == TR.Other /\
           TR.classify sigma (mk "/" op_arith_div [int_s; int_s] int_s []) == TR.Other) =
  assert_norm (TR.classify sigma (mk "distinct" op_distinct [int_s; int_s] bool_sort []) == TR.Other);
  assert_norm (TR.classify sigma (mk "num" op_num_int [] int_s [5]) == TR.Other);
  assert_norm (TR.classify sigma (mk "div" 33 [int_s; int_s] int_s []) == TR.Other);
  assert_norm (TR.classify sigma (mk "mod" 34 [int_s; int_s] int_s []) == TR.Other);
  assert_norm (TR.classify sigma (mk "const" op_const_array [real_s] arr_s []) == TR.Other);
  assert_norm (TR.classify sigma (mk "array-ext" op_array_ext [arr_s; arr_s] int_s []) == TR.Other);
  assert_norm (TR.classify sigma (mk "~" op_oeq [int_s; int_s] bool_sort []) == TR.Other);
  assert_norm (TR.classify sigma (mk "=" op_eq [int_s; int_s; int_s] bool_sort []) == TR.Other);
  assert_norm (TR.classify sigma (mk "bvand" op_bvand [bv8; bv8] bv8 []) == TR.Other);
  assert_norm (TR.classify sigma (mk "/" op_arith_div [int_s; int_s] int_s []) == TR.Other)

(* Numeral limits: only op_num_rational [n; d] with d > 0 (and d = 1 at Int)
   is a numeral law. A zero or negative denominator, or an Int numeral with
   d <> 1, is NOT given a standard meaning: it is a free symbol. *)
let numeral_limits ()
  : Lemma (TR.classify sigma (mk "num" op_num_rational [] real_s [1; 0]) == TR.Other /\
           TR.classify sigma (mk "num" op_num_rational [] real_s [1; -2]) == TR.Other /\
           TR.classify sigma (mk "num" op_num_rational [] int_s [4; 2]) == TR.Other /\
           TR.classify sigma (mk "num" op_num_rational [] real_s [-3; 2]) == TR.Numeral real_s (-3) 2) =
  assert_norm (TR.classify sigma (mk "num" op_num_rational [] real_s [1; 0]) == TR.Other);
  assert_norm (TR.classify sigma (mk "num" op_num_rational [] real_s [1; -2]) == TR.Other);
  assert_norm (TR.classify sigma (mk "num" op_num_rational [] int_s [4; 2]) == TR.Other);
  assert_norm (TR.classify sigma (mk "num" op_num_rational [] real_s [-3; 2]) == TR.Numeral real_s (-3) 2)

(* ========================================================================== *)
(* L. THE joint positive witness: one standard model per (u, uf), no hypothesis *)
(* ========================================================================== *)

type closed (scope:list sort) = e:expr{D.scoped scope e}

let c_beta : closed [] = assert_norm (D.scoped [] (eq (at succ two) three)); eq (at succ two) three
let c_ident : closed [] = assert_norm (D.scoped [] (eq ident succ)); eq ident succ
let c_ext : closed [] = assert_norm (D.scoped [] (eq plus_zero ident)); eq plus_zero ident
let c_fa_pz : closed [] = assert_norm (D.scoped [] (forall_int pz_body)); forall_int pz_body
let c_half_r : closed [] = assert_norm (D.scoped [] fa_halving_r); fa_halving_r
let c_half_i : closed [] = assert_norm (D.scoped [] fa_halving_i); fa_halving_i
let c_hetero : closed [] = assert_norm (D.scoped [] (fa_hetero hb_body)); fa_hetero hb_body
let c_minus : closed [] = assert_norm (D.scoped [] (eq read_minus three)); eq read_minus three
let c_choose : closed [] = assert_norm (D.scoped [] (read_choose false_e)); read_choose false_e
let c_multi : closed scope3 = assert_norm (D.scoped scope3 (eq (read2 true_e) q34)); eq (read2 true_e) q34
let c_nested : closed scope2 = assert_norm (D.scoped scope2 (eq nested_read half)); eq nested_read half
let c_arith : closed [] = assert_norm (D.scoped [] (eq arith_i five)); eq arith_i five
let c_order : closed [] = assert_norm (D.scoped [] (rlt third half)); rlt third half
let c_div : closed [] = assert_norm (D.scoped [] (eq div_by_two half)); eq div_by_two half

(* Groups of facts about ONE interpretation i (named, to keep each VC small). *)
let array_facts (u:TR.uninterpreted) (i:TR.interp u sch) (rho1:env u scope1) (rho2:env u scope2)
                (rho3:env u scope3) (rho:env u []) : prop =
  bool_v (ev u i scope1 rho1 o1_half_e) == true /\ bool_v (ev u i scope1 rho1 o1_third_e) == false /\
  bool_v (ev u i scope3 rho3 c_multi) == true /\ bool_v (ev u i scope2 rho2 c_nested) == true /\
  bool_v (ev u i [] rho c_minus) == true /\ int_v (ev u i [] rho c_choose) == 6

let lambda_quantifier_facts (u:TR.uninterpreted) (i:TR.interp u sch) (rho:env u []) : prop =
  bool_v (ev u i [] rho c_beta) == true /\ bool_v (ev u i [] rho c_ident) == false /\
  bool_v (ev u i [] rho c_ext) == true /\ bool_v (ev u i [] rho c_fa_pz) == true /\
  bool_v (ev u i [] rho c_half_r) == true /\ bool_v (ev u i [] rho c_half_i) == false /\
  bool_v (ev u i [] rho c_hetero) == true

let arithmetic_facts (u:TR.uninterpreted) (i:TR.interp u sch) (rho:env u []) : prop =
  bool_v (ev u i [] rho c_arith) == true /\ bool_v (ev u i [] rho c_order) == true /\
  bool_v (ev u i [] rho c_div) == true

let array_facts_hold (u:TR.uninterpreted) (i:model u) (rho1:env u scope1) (rho2:env u scope2)
                     (rho3:env u scope3) (rho:env u [])
  : Lemma (array_facts u i rho1 rho2 rho3 rho) =
  o1_half u i rho1;
  o1_third u i rho1;
  multi_store_reads u i rho3;
  nested_read_back u i rho2;
  minus_reads u i [] rho;
  choose_reads u i [] rho

let lambda_quantifier_facts_hold (u:TR.uninterpreted) (i:model u) (rho:env u [])
  : Lemma (lambda_quantifier_facts u i rho) =
  beta u i [] rho;
  identity_not_successor u i [] rho;
  plus_zero_is_identity u i [] rho;
  forall_plus_zero u i [] rho;
  forall_halving_real u i [] rho;
  forall_halving_int_false u i [] rho;
  forall_hetero u i [] rho

let arithmetic_facts_hold (u:TR.uninterpreted) (i:model u) (rho:env u [])
  : Lemma (arithmetic_facts u i rho) =
  arith_int u i [] rho;
  compare_real_third_half u i [] rho;
  division_by_two u i [] rho

(* Over the empty schema: every listed fact holds simultaneously in the
   single interpretation TR.standard u sch uf, for every u and uf. *)
let standard_joint_empty (u:TR.uninterpreted) (uf:TR.symbols u sch)
                         (rho:env u []) (rho1:env u scope1) (rho2:env u scope2) (rho3:env u scope3)
  : Lemma (TR.root_model u sch (TR.standard u sch uf) /\
           array_facts u (TR.standard u sch uf) rho1 rho2 rho3 rho /\
           lambda_quantifier_facts u (TR.standard u sch uf) rho /\
           arithmetic_facts u (TR.standard u sch uf) rho) =
  TR.lemma_standard_root u sch uf;
  let i : model u = TR.standard u sch uf in
  array_facts_hold u i rho1 rho2 rho3 rho;
  lambda_quantifier_facts_hold u i rho;
  arithmetic_facts_hold u i rho

(* Over the list schema: R5/R6 facts in the single standard model. *)
let standard_joint_list (u:TR.uninterpreted) (uf:TR.symbols u lsch) (rho:lenv u)
  : Lemma (TR.root_model u lsch (TR.standard u lsch uf) /\
           D.scoped [] (is_cons_of cons_one_nil) /\ D.scoped [] (is_cons_of nil_e) /\
           D.scoped [] (head_of cons_one_nil) /\ D.scoped [] (tail_of cons_one_nil) /\
           D.scoped [] (head_of nil_e) /\
           TR.truth lsch (evl u (TR.standard u lsch uf) rho (is_cons_of cons_one_nil)) == true /\
           TR.truth lsch (evl u (TR.standard u lsch uf) rho (is_cons_of nil_e)) == false /\
           TR.int_of lsch (evl u (TR.standard u lsch uf) rho (head_of cons_one_nil)) == 1 /\
           evl u (TR.standard u lsch uf) rho (tail_of cons_one_nil) == nil_v u /\
           evl u (TR.standard u lsch uf) rho (head_of nil_e) == uf.TR.apply head_decl [nil_v u]) =
  TR.lemma_standard_root u lsch uf;
  let i : lmodel u = TR.standard u lsch uf in
  recognizers_cons u i rho;
  accessors u i rho;
  head_of_nil_is_free u uf rho
