(* G1 typed-root PROTOTYPE witnesses (not production, not in the manifest).

   Every lemma below is about ONE joint interpretation, Z3TypedRoot.standard,
   for EVERY choice of uninterpreted carriers u and free symbols uf, evaluated
   with the production evaluator Z3DatatypeValue.evaluate on production AST
   terms (Z3AstTheory Var/App/Quantifier). There is no model hypothesis and
   no legacy model_sound / numeric_model / array_model assumption.

   The schema here is the EMPTY checked schema: the first witness probe only,
   not datatype coverage. *)
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

let empty_schema : S.schema = { S.sorts = []; S.cases = [] }

let sch : TR.supported_schema = assert_norm (TR.supported empty_schema); empty_schema

let sigma : V.signature = S.signature sch

let int_s : sort = TR.int_s
let real_s : sort = TR.real_s
let arr_s : sort = ArraySort [int_s] real_s

type env (u:TR.uninterpreted) (scope:list sort) = V.environment (TR.carrier u) (S.signature sch) scope

let ev (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
       (e:expr{D.scoped scope e})
  : GTot (TR.tvalue u sch (get_sort e)) =
  V.evaluate (S.signature sch) (TR.standard u sch uf) scope rho e

(* --- Production terms -------------------------------------------------------- *)

let inum_decl (n:int) : func_decl =
  { decl_name = "num"; domain = []; range = int_s; interp = Some op_num_rational; int_params = [n; 1] }
let rnum_decl (n:int) (d:pos) : func_decl =
  { decl_name = "num"; domain = []; range = real_s; interp = Some op_num_rational; int_params = [n; d] }
let inum (n:int) : expr = App (inum_decl n) []
let rnum (n:int) (d:pos) : expr = App (rnum_decl n d) []

let select_ir : func_decl = TR.select_decl [int_s] real_s
let store_ir : func_decl = TR.store_decl [int_s] real_s

let eq (a b:expr) : expr = R.mk_eq_expr a b

(* --- O1: (Array Int Real), store 1/2 at index 0, read back --------------------- *)

let scope1 : list sort = [arr_s]
let a0 : expr = Var 0 arr_s
let zero : expr = inum 0
let half : expr = rnum 1 2
let third : expr = rnum 1 3
let stored : expr = App store_ir [a0; zero; half]
let read_back : expr = App select_ir [stored; zero]
let o1 (v:expr) : expr = eq read_back v

let o1_half_e : e:expr{D.scoped scope1 e} = assert_norm (D.scoped scope1 (o1 half)); o1 half
let o1_third_e : e:expr{D.scoped scope1 e} = assert_norm (D.scoped scope1 (o1 third)); o1 third

let lemma_zero (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
  : Lemma (ev u uf scope rho zero == TR.make #u #sigma int_s 0) =
  assert_norm (TR.classify sigma (inum_decl 0) == TR.Numeral int_s 0 1);
  TR.lemma_eval_interpreted u sch uf scope rho (inum_decl 0) []

let lemma_rational (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
                   (n:int) (d:pos)
  : Lemma (requires TR.classify sigma (rnum_decl n d) == TR.Numeral real_s n d)
          (ensures ev u uf scope rho (rnum n d) == TR.make #u #sigma real_s (TR.rational n d)) =
  TR.lemma_eval_interpreted u sch uf scope rho (rnum_decl n d) []

let lemma_stored (u:TR.uninterpreted) (uf:TR.symbols u sch) (rho:env u scope1)
  : Lemma (ev u uf scope1 rho stored ==
           TR.make #u #sigma arr_s
             (TR.write #(TR.indices u [int_s]) #(TR.carrier u real_s)
               (TR.scalar #u #sigma arr_s (rho 0)) (0, ()) (TR.rational 1 2))) =
  lemma_zero u uf scope1 rho;
  assert_norm (TR.classify sigma (rnum_decl 1 2) == TR.Numeral real_s 1 2);
  lemma_rational u uf scope1 rho 1 2;
  assert_norm (TR.classify sigma store_ir == TR.Store [int_s] real_s);
  TR.lemma_eval_interpreted u sch uf scope1 rho store_ir [a0; zero; half]

let lemma_read_back (u:TR.uninterpreted) (uf:TR.symbols u sch) (rho:env u scope1)
  : Lemma (ev u uf scope1 rho read_back == TR.make #u #sigma real_s (TR.rational 1 2)) =
  lemma_stored u uf rho;
  lemma_zero u uf scope1 rho;
  assert_norm (TR.classify sigma select_ir == TR.Select [int_s] real_s);
  TR.lemma_eval_interpreted u sch uf scope1 rho select_ir [stored; zero]

let lemma_real_equality (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
                        (a b:expr) (x y:real)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ get_sort a == real_s /\ get_sort b == real_s /\
                    ev u uf scope rho a == TR.make #u #sigma real_s x /\
                    ev u uf scope rho b == TR.make #u #sigma real_s y)
          (ensures TR.truth sch (ev u uf scope rho (eq a b)) == true <==> x == y) =
  assert_norm (TR.classify sigma (R.eq_decl real_s) == TR.Equality real_s);
  TR.lemma_eval_interpreted u sch uf scope rho (R.eq_decl real_s) [a; b]

(* O1, positive: the stored value is a genuine real 1/2, read back in the same
   joint model that interprets the numeral, the store and the select. *)
let o1_half (u:TR.uninterpreted) (uf:TR.symbols u sch) (rho:env u scope1)
  : Lemma (TR.truth sch (ev u uf scope1 rho o1_half_e) == true) =
  lemma_read_back u uf rho;
  lemma_rational u uf scope1 rho 1 2;
  lemma_real_equality u uf scope1 rho read_back half (TR.rational 1 2) (TR.rational 1 2)

(* O1, mutation: reading back 1/3 is false (a genuine false claim, not a typing failure). *)
let o1_third (u:TR.uninterpreted) (uf:TR.symbols u sch) (rho:env u scope1)
  : Lemma (TR.truth sch (ev u uf scope1 rho o1_third_e) == false) =
  lemma_read_back u uf rho;
  assert_norm (TR.classify sigma (rnum_decl 1 3) == TR.Numeral real_s 1 3);
  lemma_rational u uf scope1 rho 1 3;
  lemma_real_equality u uf scope1 rho read_back third (TR.rational 1 2) (TR.rational 1 3)

[@@expect_failure [19]]
let o1_third_is_true (u:TR.uninterpreted) (uf:TR.symbols u sch) (rho:env u scope1)
  : Lemma (TR.truth sch (ev u uf scope1 rho o1_third_e) == true) =
  lemma_read_back u uf rho;
  assert_norm (TR.classify sigma (rnum_decl 1 3) == TR.Numeral real_s 1 3);
  lemma_rational u uf scope1 rho 1 3;
  lemma_real_equality u uf scope1 rho read_back third (TR.rational 1 2) (TR.rational 1 3)

(* --- Typed open environments -------------------------------------------------- *)

let scope_b : list sort = [bool_sort]
let p0 : expr = Var 0 bool_sort

(* Any well-typed environment gives a Boolean SCALAR to a Bool variable. *)
let typed_bool_variable (u:TR.uninterpreted) (uf:TR.symbols u sch) (rho:env u scope_b)
  : Lemma (ev u uf scope_b rho p0 == TR.boolean #u sch (TR.truth sch (rho 0))) = ()

let env_true (u:TR.uninterpreted) : env u scope_b = fun _ -> TR.boolean #u sch true

let bool_variable_true (u:TR.uninterpreted) (uf:TR.symbols u sch)
  : Lemma (TR.truth sch (ev u uf scope_b (env_true u) p0) == true) = ()

(* The legacy counterexample shape (an Int value for a Bool variable) is not
   an environment of this scope: the typed condition is checkable and rejects it. *)
[@@expect_failure [19]]
let int_in_bool_environment (u:TR.uninterpreted) : env u scope_b =
  fun _ -> V.Scalar int_s (0 <: TR.carrier u int_s)

(* --- Integer and real arithmetic steps ---------------------------------------- *)

let add_decl (s:sort) : func_decl =
  { decl_name = "+"; domain = [s; s]; range = s; interp = Some op_arith_add; int_params = [] }
let add (s:sort) (a b:expr) : expr = App (add_decl s) [a; b]

let lemma_add_int (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
                  (a b:expr) (x y:int)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ get_sort a == int_s /\ get_sort b == int_s /\
                    ev u uf scope rho a == TR.make #u #sigma int_s x /\
                    ev u uf scope rho b == TR.make #u #sigma int_s y)
          (ensures ev u uf scope rho (add int_s a b) == TR.make #u #sigma int_s (x + y)) =
  assert_norm (TR.classify sigma (add_decl int_s) == TR.Arith int_s Z3LinearArithmeticAst.Add);
  TR.lemma_eval_interpreted u sch uf scope rho (add_decl int_s) [a; b]

let lemma_add_real (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
                   (a b:expr) (x y:real)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ get_sort a == real_s /\ get_sort b == real_s /\
                    ev u uf scope rho a == TR.make #u #sigma real_s x /\
                    ev u uf scope rho b == TR.make #u #sigma real_s y)
          (ensures ev u uf scope rho (add real_s a b) == TR.make #u #sigma real_s (x +. y)) =
  assert_norm (TR.classify sigma (add_decl real_s) == TR.Arith real_s Z3LinearArithmeticAst.Add);
  TR.lemma_eval_interpreted u sch uf scope rho (add_decl real_s) [a; b]

let lemma_int_num (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope) (n:int)
  : Lemma (requires TR.classify sigma (inum_decl n) == TR.Numeral int_s n 1)
          (ensures ev u uf scope rho (inum n) == TR.make #u #sigma int_s n) =
  TR.lemma_eval_interpreted u sch uf scope rho (inum_decl n) []

let lemma_equality_any (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
                       (t:sort) (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ get_sort a == t /\ get_sort b == t /\
                    D.scoped scope (eq a b) /\ TR.classify sigma (R.eq_decl t) == TR.Equality t)
          (ensures TR.truth sch (ev u uf scope rho (eq a b)) == true <==>
                   ev u uf scope rho a == ev u uf scope rho b) =
  TR.lemma_eval_interpreted u sch uf scope rho (R.eq_decl t) [a; b]

(* --- Ghost lambdas (actual production Lambda_k nodes) ------------------------- *)

let ii_s : sort = ArraySort [int_s] int_s
let x0 : expr = Var 0 int_s
let one : expr = inum 1
let two : expr = inum 2
let three : expr = inum 3
let four : expr = inum 4
let lam (body:expr) : expr = Quantifier Lambda_k [int_s] ii_s body
let succ : expr = lam (add int_s x0 one)
let ident : expr = lam x0
let plus_zero : expr = lam (add int_s x0 zero)
let select_ii : func_decl = TR.select_decl [int_s] int_s
let beta (v:expr) : expr = eq (App select_ii [succ; two]) v

let lemma_index_int (u:TR.uninterpreted) : Lemma (TR.indices u [int_s] == (int & unit)) =
  assert_norm (TR.indices u [int_s] == (int & unit))

let lemma_read_lambda_int (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
                          (body:expr) (n:int)
  : Lemma (requires D.scoped (int_s :: scope) body /\ get_sort body == int_s)
          (ensures TR.read #(TR.indices u [int_s]) #(TR.carrier u int_s)
                     (TR.scalar #u #sigma ii_s (ev u uf scope rho (lam body)))
                     (coerce_eq #(int & unit) #(TR.indices u [int_s]) (lemma_index_int u) (n, ())) ==
                   TR.scalar #u #sigma int_s
                     (ev u uf (int_s :: scope)
                        (V.extend sigma scope [int_s] [TR.make #u #sigma int_s n] rho) body)) =
  assert_norm (L.rev [int_s] == [int_s]);
  lemma_index_int u;
  TR.lemma_eval_lambda u sch uf scope rho [int_s] int_s body
    (coerce_eq #(int & unit) #(TR.indices u [int_s]) () (n, ()))

let lemma_var0 (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
               (s:sort) (v:TR.tvalue u sch s)
  : Lemma (ev u uf (s :: scope) (V.extend sigma scope [s] [v] rho) (Var 0 s) == v) = ()

let lemma_succ_at (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope) (n:int)
  : Lemma (TR.read #(TR.indices u [int_s]) #(TR.carrier u int_s)
             (TR.scalar #u #sigma ii_s (ev u uf scope rho succ))
             (coerce_eq #(int & unit) #(TR.indices u [int_s]) (lemma_index_int u) (n, ())) == n + 1) =
  let rho' = V.extend sigma scope [int_s] [TR.make #u #sigma int_s n] rho in
  lemma_read_lambda_int u uf scope rho (add int_s x0 one) n;
  lemma_var0 u uf scope rho int_s (TR.make #u #sigma int_s n);
  assert_norm (TR.classify sigma (inum_decl 1) == TR.Numeral int_s 1 1);
  lemma_int_num u uf (int_s :: scope) rho' 1;
  lemma_add_int u uf (int_s :: scope) rho' x0 one n 1

let lemma_ident_at (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope) (n:int)
  : Lemma (TR.read #(TR.indices u [int_s]) #(TR.carrier u int_s)
             (TR.scalar #u #sigma ii_s (ev u uf scope rho ident))
             (coerce_eq #(int & unit) #(TR.indices u [int_s]) (lemma_index_int u) (n, ())) == n) =
  lemma_read_lambda_int u uf scope rho x0 n;
  lemma_var0 u uf scope rho int_s (TR.make #u #sigma int_s n)

let lemma_plus_zero_at (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope) (n:int)
  : Lemma (TR.read #(TR.indices u [int_s]) #(TR.carrier u int_s)
             (TR.scalar #u #sigma ii_s (ev u uf scope rho plus_zero))
             (coerce_eq #(int & unit) #(TR.indices u [int_s]) (lemma_index_int u) (n, ())) == n) =
  let rho' = V.extend sigma scope [int_s] [TR.make #u #sigma int_s n] rho in
  lemma_read_lambda_int u uf scope rho (add int_s x0 zero) n;
  lemma_var0 u uf scope rho int_s (TR.make #u #sigma int_s n);
  lemma_zero u uf (int_s :: scope) rho';
  lemma_add_int u uf (int_s :: scope) rho' x0 zero n 0

let lemma_select_succ (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
  : Lemma (ev u uf scope rho (App select_ii [succ; two]) == TR.make #u #sigma int_s 3) =
  assert_norm (TR.classify sigma (inum_decl 2) == TR.Numeral int_s 2 1);
  lemma_int_num u uf scope rho 2;
  assert_norm (TR.classify sigma select_ii == TR.Select [int_s] int_s);
  TR.lemma_eval_interpreted u sch uf scope rho select_ii [succ; two];
  lemma_succ_at u uf scope rho 2

(* select (lambda x:Int. x + 1) 2 = 3 *)
let beta_three (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (beta three) /\ TR.truth sch (ev u uf scope rho (beta three)) == true) =
  lemma_select_succ u uf scope rho;
  assert_norm (TR.classify sigma (inum_decl 3) == TR.Numeral int_s 3 1);
  lemma_int_num u uf scope rho 3;
  assert_norm (TR.classify sigma (R.eq_decl int_s) == TR.Equality int_s);
  lemma_equality_any u uf scope rho int_s (App select_ii [succ; two]) three

(* mutation: = 4 is false *)
let beta_four (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (beta four) /\ TR.truth sch (ev u uf scope rho (beta four)) == false) =
  lemma_select_succ u uf scope rho;
  assert_norm (TR.classify sigma (inum_decl 4) == TR.Numeral int_s 4 1);
  lemma_int_num u uf scope rho 4;
  assert_norm (TR.classify sigma (R.eq_decl int_s) == TR.Equality int_s);
  lemma_equality_any u uf scope rho int_s (App select_ii [succ; two]) four

(* identity and successor lambdas are different array values *)
let identity_not_successor (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (eq ident succ) /\ TR.truth sch (ev u uf scope rho (eq ident succ)) == false) =
  lemma_ident_at u uf scope rho 0;
  lemma_succ_at u uf scope rho 0;
  assert_norm (TR.classify sigma (R.eq_decl ii_s) == TR.Equality ii_s);
  lemma_equality_any u uf scope rho ii_s ident succ

(* x + 0 and x are extensionally equal lambdas *)
let plus_zero_is_identity (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (eq plus_zero ident) /\ TR.truth sch (ev u uf scope rho (eq plus_zero ident)) == true) =
  let fa = TR.scalar #u #sigma ii_s (ev u uf scope rho plus_zero) in
  let fb = TR.scalar #u #sigma ii_s (ev u uf scope rho ident) in
  let pointwise (ix:TR.indices u [int_s])
    : Lemma (TR.read #(TR.indices u [int_s]) #(TR.carrier u int_s) fa ix ==
             TR.read #(TR.indices u [int_s]) #(TR.carrier u int_s) fb ix) =
    lemma_index_int u;
    let p = coerce_eq #(TR.indices u [int_s]) #(int & unit) () ix in
    lemma_plus_zero_at u uf scope rho (fst p);
    lemma_ident_at u uf scope rho (fst p) in
  FStar.Classical.forall_intro pointwise;
  TR.lemma_function_extensionality #(TR.indices u [int_s]) #(TR.carrier u int_s) fa fb;
  assert_norm (TR.classify sigma (R.eq_decl ii_s) == TR.Equality ii_s);
  lemma_equality_any u uf scope rho ii_s plus_zero ident

(* --- Typed quantifiers over infinite Int and Real carriers --------------------- *)

let pz_body : expr = eq (add int_s x0 zero) x0
let p1_body : expr = eq (add int_s x0 one) x0
let forall_int (body:expr) : expr = Quantifier Forall_k [int_s] bool_sort body
let y0r : expr = Var 0 real_s
let x1r : expr = Var 1 real_s
let halves_r : expr = eq (add real_s y0r y0r) x1r
let fa_halving_r : expr = Quantifier Forall_k [real_s] bool_sort (Quantifier Exists_k [real_s] bool_sort halves_r)
let y0i : expr = Var 0 int_s
let x1i : expr = Var 1 int_s
let halves_i : expr = eq (add int_s y0i y0i) x1i
let fa_halving_i : expr = Quantifier Forall_k [int_s] bool_sort (Quantifier Exists_k [int_s] bool_sort halves_i)

let lemma_int_body (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
                   (k:int) (n:int)
  : Lemma (requires TR.classify sigma (inum_decl k) == TR.Numeral int_s k 1)
          (ensures (let rho' = V.extend sigma scope [int_s] [TR.make #u #sigma int_s n] rho in
                    D.scoped (int_s :: scope) (eq (add int_s x0 (inum k)) x0) /\
                    (TR.truth sch (ev u uf (int_s :: scope) rho' (eq (add int_s x0 (inum k)) x0)) == true <==>
                     n + k == n))) =
  let rho' = V.extend sigma scope [int_s] [TR.make #u #sigma int_s n] rho in
  lemma_var0 u uf scope rho int_s (TR.make #u #sigma int_s n);
  lemma_int_num u uf (int_s :: scope) rho' k;
  lemma_add_int u uf (int_s :: scope) rho' x0 (inum k) n k;
  assert_norm (TR.classify sigma (R.eq_decl int_s) == TR.Equality int_s);
  lemma_equality_any u uf (int_s :: scope) rho' int_s (add int_s x0 (inum k)) x0

(* forall x:Int. x + 0 = x  is true *)
let forall_plus_zero (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (forall_int pz_body) /\
           TR.truth sch (ev u uf scope rho (forall_int pz_body)) == true) =
  assert_norm (L.rev [int_s] == [int_s]);
  TR.lemma_eval_forall u sch uf scope rho [int_s] pz_body;
  let inst (vs:TR.targuments u sch (L.rev [int_s]))
    : Lemma (TR.truth sch (V.evaluate sigma (TR.standard u sch uf) (L.rev [int_s] @ scope)
               (V.extend sigma scope (L.rev [int_s]) vs rho) pz_body) == true) =
    assert_norm (L.rev [int_s] == [int_s]);
    match vs with
    | [v] ->
      TR.lemma_make_scalar #u #sigma int_s v;
      assert_norm (TR.classify sigma (inum_decl 0) == TR.Numeral int_s 0 1);
      lemma_int_body u uf scope rho 0 (TR.scalar #u #sigma int_s v)
    | _ -> () in
  FStar.Classical.forall_intro inst

(* mutation: forall x:Int. x + 1 = x  is false (instance x = 0) *)
let forall_plus_one_false (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (forall_int p1_body) /\
           TR.truth sch (ev u uf scope rho (forall_int p1_body)) == false) =
  assert_norm (L.rev [int_s] == [int_s]);
  TR.lemma_eval_forall u sch uf scope rho [int_s] p1_body;
  assert_norm (TR.classify sigma (inum_decl 1) == TR.Numeral int_s 1 1);
  lemma_int_body u uf scope rho 1 0

let lemma_real_var (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
                   (vx vy:TR.tvalue u sch real_s)
  : Lemma (let rho' = V.extend sigma (real_s :: scope) [real_s] [vy]
                        (V.extend sigma scope [real_s] [vx] rho) in
           ev u uf (real_s :: real_s :: scope) rho' y0r == vy /\
           ev u uf (real_s :: real_s :: scope) rho' x1r == vx) = ()

let lemma_half (x:real) : Lemma ((x /. 2.0R) +. (x /. 2.0R) == x) = ()

(* The witness step at one value of x, in a small context. *)
let halving_witness (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
                    (vx:TR.tvalue u sch real_s)
  : Lemma (let rho' = V.extend sigma scope [real_s] [vx] rho in
           let vy = TR.make #u #sigma real_s (TR.scalar #u #sigma real_s vx /. 2.0R) in
           TR.truth sch (ev u uf (real_s :: real_s :: scope)
                          (V.extend sigma (real_s :: scope) [real_s] [vy] rho') halves_r) == true) =
  let x = TR.scalar #u #sigma real_s vx in
  TR.lemma_make_scalar #u #sigma real_s vx;
  let rho' = V.extend sigma scope [real_s] [vx] rho in
  let y : real = x /. 2.0R in
  let vy = TR.make #u #sigma real_s y in
  let rho'' = V.extend sigma (real_s :: scope) [real_s] [vy] rho' in
  lemma_real_var u uf scope rho vx vy;
  lemma_add_real u uf (real_s :: real_s :: scope) rho'' y0r y0r y y;
  lemma_half x;
  lemma_real_equality u uf (real_s :: real_s :: scope) rho'' (add real_s y0r y0r) x1r (y +. y) x

(* forall x:Real. exists y:Real. y + y = x  is true (witness y = x / 2: a real, not an integer code) *)
let forall_halving_real (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope fa_halving_r /\ TR.truth sch (ev u uf scope rho fa_halving_r) == true) =
  let inner = Quantifier Exists_k [real_s] bool_sort halves_r in
  assert_norm (L.rev [real_s] == [real_s]);
  TR.lemma_eval_forall u sch uf scope rho [real_s] inner;
  let inst (vs:TR.targuments u sch (L.rev [real_s]))
    : Lemma (TR.truth sch (V.evaluate sigma (TR.standard u sch uf) (L.rev [real_s] @ scope)
               (V.extend sigma scope (L.rev [real_s]) vs rho) inner) == true) =
    assert_norm (L.rev [real_s] == [real_s]);
    match vs with
    | [vx] ->
      let rho' = V.extend sigma scope [real_s] [vx] rho in
      TR.lemma_eval_exists u sch uf (real_s :: scope) rho' [real_s] halves_r;
      let vy = TR.make #u #sigma real_s (TR.scalar #u #sigma real_s vx /. 2.0R) in
      halving_witness u uf scope rho vx;
      FStar.Classical.exists_intro
        (fun (ws:TR.targuments u sch (L.rev [real_s])) ->
          TR.truth sch (V.evaluate sigma (TR.standard u sch uf) (L.rev [real_s] @ (real_s :: scope))
            (V.extend sigma (real_s :: scope) (L.rev [real_s]) ws rho') halves_r) == true)
        [vy]
    | _ -> () in
  FStar.Classical.forall_intro inst

(* mutation: over Int, forall x. exists y. y + y = x  is false (x = 1) *)
let forall_halving_int_false (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope fa_halving_i /\ TR.truth sch (ev u uf scope rho fa_halving_i) == false) =
  let inner = Quantifier Exists_k [int_s] bool_sort halves_i in
  assert_norm (L.rev [int_s] == [int_s]);
  TR.lemma_eval_forall u sch uf scope rho [int_s] inner;
  let vx = TR.make #u #sigma int_s 1 in
  let rho' = V.extend sigma scope [int_s] [vx] rho in
  TR.lemma_eval_exists u sch uf (int_s :: scope) rho' [int_s] halves_i;
  let none (ws:TR.targuments u sch (L.rev [int_s]))
    : Lemma (TR.truth sch (V.evaluate sigma (TR.standard u sch uf) (L.rev [int_s] @ (int_s :: scope))
               (V.extend sigma (int_s :: scope) (L.rev [int_s]) ws rho') halves_i) == false) =
    assert_norm (L.rev [int_s] == [int_s]);
    match ws with
    | [vy] ->
      let y = TR.scalar #u #sigma int_s vy in
      TR.lemma_make_scalar #u #sigma int_s vy;
      let rho'' = V.extend sigma (int_s :: scope) [int_s] [vy] rho' in
      assert (ev u uf (int_s :: int_s :: scope) rho'' y0i == vy);
      assert (ev u uf (int_s :: int_s :: scope) rho'' x1i == vx);
      lemma_add_int u uf (int_s :: int_s :: scope) rho'' y0i y0i y y;
      assert_norm (TR.classify sigma (R.eq_decl int_s) == TR.Equality int_s);
      lemma_equality_any u uf (int_s :: int_s :: scope) rho'' int_s (add int_s y0i y0i) x1i
    | _ -> () in
  FStar.Classical.forall_intro none;
  assert (TR.truth sch (V.evaluate sigma (TR.standard u sch uf) (L.rev [int_s] @ scope)
            (V.extend sigma scope (L.rev [int_s]) [vx] rho) inner) == false)

(* --- Real division: standard when the divisor is nonzero, a FREE choice at 0 -- *)

let div_decl : func_decl =
  { decl_name = "/"; domain = [real_s; real_s]; range = real_s; interp = Some op_arith_div; int_params = [] }
let one_r : expr = rnum 1 1
let zero_r : expr = rnum 0 1
let two_r : expr = rnum 2 1
let div_by_two : expr = App div_decl [one_r; two_r]
let div_by_zero : expr = App div_decl [one_r; zero_r]

let lemma_real_constants (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
  : Lemma (ev u uf scope rho one_r == TR.make #u #sigma real_s (TR.rational 1 1) /\
           ev u uf scope rho zero_r == TR.make #u #sigma real_s (TR.rational 0 1) /\
           ev u uf scope rho two_r == TR.make #u #sigma real_s (TR.rational 2 1)) =
  assert_norm (TR.classify sigma (rnum_decl 1 1) == TR.Numeral real_s 1 1);
  assert_norm (TR.classify sigma (rnum_decl 0 1) == TR.Numeral real_s 0 1);
  assert_norm (TR.classify sigma (rnum_decl 2 1) == TR.Numeral real_s 2 1);
  lemma_rational u uf scope rho 1 1;
  lemma_rational u uf scope rho 0 1;
  lemma_rational u uf scope rho 2 1

(* 1/2 computed by division equals the numeral 1/2 *)
let division_by_two (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (eq div_by_two half) /\ TR.truth sch (ev u uf scope rho (eq div_by_two half)) == true) =
  lemma_real_constants u uf scope rho;
  assert_norm (TR.classify sigma div_decl == TR.Divide);
  TR.lemma_eval_interpreted u sch uf scope rho div_decl [one_r; two_r];
  assert_norm (TR.classify sigma (rnum_decl 1 2) == TR.Numeral real_s 1 2);
  lemma_rational u uf scope rho 1 2;
  lemma_real_equality u uf scope rho div_by_two half (TR.rational 1 1 /. TR.rational 2 1) (TR.rational 1 2)

(* 1/0 is exactly the model's free choice *)
let division_by_zero_is_free (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
  : Lemma (ev u uf scope rho div_by_zero ==
           uf.apply div_decl [TR.make #u #sigma real_s (TR.rational 1 1); TR.make #u #sigma real_s (TR.rational 0 1)]) =
  lemma_real_constants u uf scope rho;
  assert_norm (TR.classify sigma div_decl == TR.Divide);
  TR.lemma_eval_free_choice u sch uf scope rho div_decl [one_r; zero_r]

(* Two free-symbol choices that differ only in the value of x/0 for reals. *)
let uf_const (u:TR.uninterpreted) (k:real) : TR.symbols u sch = {
  TR.apply = (fun f _ ->
    if f.range = real_s then TR.make #u #sigma real_s k
    else S.value_inhabitant sch (TR.default_value u) f.range);
  TR.lambda = (fun bound t _ -> S.value_inhabitant sch (TR.default_value u) (ArraySort bound t));
}

(* Coverage control: both choices are standard root models (L1), yet they
   disagree on 1/0 = 0. The model class does not force division by zero. *)
let division_by_zero_not_forced (u:TR.uninterpreted) (scope:list sort) (rho:env u scope)
  : Lemma (TR.root_model u sch (TR.standard u sch (uf_const u 0.0R)) /\
           TR.root_model u sch (TR.standard u sch (uf_const u 1.0R)) /\
           D.scoped scope (eq div_by_zero zero_r) /\
           TR.truth sch (ev u (uf_const u 0.0R) scope rho (eq div_by_zero zero_r)) == true /\
           TR.truth sch (ev u (uf_const u 1.0R) scope rho (eq div_by_zero zero_r)) == false) =
  TR.lemma_standard_root u sch (uf_const u 0.0R);
  TR.lemma_standard_root u sch (uf_const u 1.0R);
  division_by_zero_is_free u (uf_const u 0.0R) scope rho;
  division_by_zero_is_free u (uf_const u 1.0R) scope rho;
  lemma_real_constants u (uf_const u 0.0R) scope rho;
  lemma_real_constants u (uf_const u 1.0R) scope rho;
  lemma_real_equality u (uf_const u 0.0R) scope rho div_by_zero zero_r 0.0R (TR.rational 0 1);
  lemma_real_equality u (uf_const u 1.0R) scope rho div_by_zero zero_r 1.0R (TR.rational 0 1)

(* --- Two-binder lambdas: index order versus de Bruijn order -------------------- *)

let lemma_select_lambda2 (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
                         (s1 s2 t:sort) (body e1 e2:expr)
                         (v1:TR.tvalue u sch s1) (v2:TR.tvalue u sch s2)
  : Lemma (requires D.scoped scope (Quantifier Lambda_k [s1; s2] (ArraySort [s1; s2] t) body) /\
                    get_sort body == t /\ D.scoped scope e1 /\ D.scoped scope e2 /\
                    get_sort e1 == s1 /\ get_sort e2 == s2 /\
                    D.scoped scope (App (TR.select_decl [s1; s2] t)
                                     [Quantifier Lambda_k [s1; s2] (ArraySort [s1; s2] t) body; e1; e2]) /\
                    ev u uf scope rho e1 == v1 /\ ev u uf scope rho e2 == v2 /\
                    TR.classify sigma (TR.select_decl [s1; s2] t) == TR.Select [s1; s2] t)
          (ensures ev u uf scope rho (App (TR.select_decl [s1; s2] t)
                                       [Quantifier Lambda_k [s1; s2] (ArraySort [s1; s2] t) body; e1; e2]) ==
                   ev u uf (s2 :: s1 :: scope) (V.extend sigma scope [s2; s1] [v2; v1] rho) body) =
  let lam = Quantifier Lambda_k [s1; s2] (ArraySort [s1; s2] t) body in
  assert_norm (L.rev [s1; s2] == [s2; s1]);
  assert_norm (TR.free sigma (ArraySort [s1; s2] t));
  TR.lemma_eval_interpreted u sch uf scope rho (TR.select_decl [s1; s2] t) [lam; e1; e2];
  let ix = TR.to_indices #u #sigma [s1; s2] [v1; v2] in
  TR.lemma_from_to #u #sigma [s1; s2] [v1; v2];
  assert_norm (TR.reverse_arguments sigma [s1; s2] [v1; v2] == [v2; v1]);
  TR.lemma_eval_lambda u sch uf scope rho [s1; s2] t body ix

let sub_decl : func_decl =
  { decl_name = "-"; domain = [int_s; int_s]; range = int_s; interp = Some op_arith_sub; int_params = [] }
let iii_s : sort = ArraySort [int_s; int_s] int_s
(* lambda (x:Int) (y:Int). x - y   -- inside the body y is Var 0, x is Var 1 *)
let minus_body : expr = App sub_decl [Var 1 int_s; Var 0 int_s]
let minus_lam : expr = Quantifier Lambda_k [int_s; int_s] iii_s minus_body
let five : expr = inum 5
let read_minus : expr = App (TR.select_decl [int_s; int_s] int_s) [minus_lam; five; two]

let lemma_read_minus (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
  : Lemma (ev u uf scope rho read_minus == TR.make #u #sigma int_s 3) =
  assert_norm (TR.classify sigma (inum_decl 5) == TR.Numeral int_s 5 1);
  assert_norm (TR.classify sigma (inum_decl 2) == TR.Numeral int_s 2 1);
  lemma_int_num u uf scope rho 5;
  lemma_int_num u uf scope rho 2;
  let v5 = TR.make #u #sigma int_s 5 in
  let v2 = TR.make #u #sigma int_s 2 in
  assert_norm (TR.classify sigma (TR.select_decl [int_s; int_s] int_s) == TR.Select [int_s; int_s] int_s);
  lemma_select_lambda2 u uf scope rho int_s int_s int_s minus_body five two v5 v2;
  let rho' = V.extend sigma scope [int_s; int_s] [v2; v5] rho in
  assert (ev u uf (int_s :: int_s :: scope) rho' (Var 1 int_s) == v5);
  assert (ev u uf (int_s :: int_s :: scope) rho' (Var 0 int_s) == v2);
  assert_norm (TR.classify sigma sub_decl == TR.Arith int_s Z3LinearArithmeticAst.Sub);
  TR.lemma_eval_interpreted u sch uf (int_s :: int_s :: scope) rho' sub_decl [Var 1 int_s; Var 0 int_s]

(* select (lambda x y. x - y) 5 2 = 3 *)
let minus_reads_three (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (eq read_minus three) /\ TR.truth sch (ev u uf scope rho (eq read_minus three)) == true) =
  lemma_read_minus u uf scope rho;
  assert_norm (TR.classify sigma (inum_decl 3) == TR.Numeral int_s 3 1);
  lemma_int_num u uf scope rho 3;
  assert_norm (TR.classify sigma (R.eq_decl int_s) == TR.Equality int_s);
  lemma_equality_any u uf scope rho int_s read_minus three

(* swapped-order mutant: = 2 - 5 = -3 is false *)
let minus_swapped_false (u:TR.uninterpreted) (uf:TR.symbols u sch) (scope:list sort) (rho:env u scope)
  : Lemma (D.scoped scope (eq read_minus (inum (-3))) /\
           TR.truth sch (ev u uf scope rho (eq read_minus (inum (-3)))) == false) =
  lemma_read_minus u uf scope rho;
  assert_norm (TR.classify sigma (inum_decl (-3)) == TR.Numeral int_s (-3) 1);
  lemma_int_num u uf scope rho (-3);
  assert_norm (TR.classify sigma (R.eq_decl int_s) == TR.Equality int_s);
  lemma_equality_any u uf scope rho int_s read_minus (inum (-3))

(* Heterogeneous lambda (x:Int) (p:Bool). ite p x (x + 1) at (Array Int Bool Int) *)
let ibi_s : sort = ArraySort [int_s; bool_sort] int_s
let choose_body : expr = App (TR.ite_decl int_s) [Var 0 bool_sort; Var 1 int_s; add int_s (Var 1 int_s) one]
let choose_lam : expr = Quantifier Lambda_k [int_s; bool_sort] ibi_s choose_body
let read_choose (p:expr) : expr = App (TR.select_decl [int_s; bool_sort] int_s) [choose_lam; five; p]

(* Closed terms: every environment of the empty scope. *)
let lemma_true_false (u:TR.uninterpreted) (uf:TR.symbols u sch) (rho:env u [])
  : Lemma (ev u uf [] rho R.true_expr == TR.boolean #u sch true /\
           ev u uf [] rho R.false_expr == TR.boolean #u sch false) =
  assert_norm (TR.classify sigma (App?.decl R.true_expr) == TR.Constant true);
  assert_norm (TR.classify sigma (App?.decl R.false_expr) == TR.Constant false);
  TR.lemma_eval_interpreted u sch uf [] rho (App?.decl R.true_expr) [];
  TR.lemma_eval_interpreted u sch uf [] rho (App?.decl R.false_expr) []

let lemma_choose_body (u:TR.uninterpreted) (uf:TR.symbols u sch) (rho:env u []) (b:bool)
  : Lemma (ev u uf [bool_sort; int_s]
             (V.extend sigma [] [bool_sort; int_s] [TR.boolean #u sch b; TR.make #u #sigma int_s 5] rho)
             choose_body == TR.make #u #sigma int_s (if b then 5 else 6)) =
  let v5 = TR.make #u #sigma int_s 5 in
  let vb = TR.boolean #u sch b in
  let scope' = [bool_sort; int_s] in
  let rho' = V.extend sigma [] [bool_sort; int_s] [vb; v5] rho in
  assert (ev u uf scope' rho' (Var 0 bool_sort) == vb);
  assert (ev u uf scope' rho' (Var 1 int_s) == v5);
  assert_norm (TR.classify sigma (inum_decl 1) == TR.Numeral int_s 1 1);
  lemma_int_num u uf scope' rho' 1;
  lemma_add_int u uf scope' rho' (Var 1 int_s) one 5 1;
  assert_norm (TR.classify sigma (TR.ite_decl int_s) == TR.Choice int_s);
  TR.lemma_eval_interpreted u sch uf scope' rho' (TR.ite_decl int_s)
    [Var 0 bool_sort; Var 1 int_s; add int_s (Var 1 int_s) one]

let lemma_read_choose (u:TR.uninterpreted) (uf:TR.symbols u sch) (rho:env u []) (p:expr) (b:bool)
  : Lemma (requires D.scoped [] p /\ get_sort p == bool_sort /\ D.scoped [] (read_choose p) /\
                    ev u uf [] rho p == TR.boolean #u sch b)
          (ensures ev u uf [] rho (read_choose p) == TR.make #u #sigma int_s (if b then 5 else 6)) =
  assert_norm (TR.classify sigma (inum_decl 5) == TR.Numeral int_s 5 1);
  lemma_int_num u uf [] rho 5;
  let v5 = TR.make #u #sigma int_s 5 in
  let vb = TR.boolean #u sch b in
  assert_norm (D.scoped [] choose_lam);
  assert_norm (TR.classify sigma (TR.select_decl [int_s; bool_sort] int_s) == TR.Select [int_s; bool_sort] int_s);
  lemma_select_lambda2 u uf [] rho int_s bool_sort int_s choose_body five p v5 vb;
  lemma_choose_body u uf rho b

(* select (lambda (x:Int) (p:Bool). ite p x (x+1)) 5 true = 5, ... 5 false = 6 *)
let choose_reads (u:TR.uninterpreted) (uf:TR.symbols u sch) (rho:env u [])
  : Lemma (D.scoped [] (read_choose R.true_expr) /\ D.scoped [] (read_choose R.false_expr) /\
           ev u uf [] rho (read_choose R.true_expr) == TR.make #u #sigma int_s 5 /\
           ev u uf [] rho (read_choose R.false_expr) == TR.make #u #sigma int_s 6) =
  assert_norm (D.scoped [] (read_choose R.true_expr));
  assert_norm (D.scoped [] (read_choose R.false_expr));
  lemma_true_false u uf rho;
  lemma_read_choose u uf rho R.true_expr true;
  lemma_read_choose u uf rho R.false_expr false

(* mutant: reading (5, true) as 6 is false *)
let choose_true_six_false (u:TR.uninterpreted) (uf:TR.symbols u sch) (rho:env u [])
  : Lemma (D.scoped [] (eq (read_choose R.true_expr) (inum 6)) /\
           TR.truth sch (ev u uf [] rho (eq (read_choose R.true_expr) (inum 6))) == false) =
  choose_reads u uf rho;
  assert_norm (TR.classify sigma (inum_decl 6) == TR.Numeral int_s 6 1);
  lemma_int_num u uf [] rho 6;
  assert_norm (TR.classify sigma (R.eq_decl int_s) == TR.Equality int_s);
  assert_norm (D.scoped [] (eq (read_choose R.true_expr) (inum 6)));
  lemma_equality_any u uf [] rho int_s (read_choose R.true_expr) (inum 6)

(* --- Compatibility with checked constructor trees (a nonempty schema) --------- *)

module DL = Z3DatatypeLemma

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

let evl (u:TR.uninterpreted) (uf:TR.symbols u lsch) (rho:V.environment (TR.carrier u) lsigma [])
        (e:expr{D.scoped [] e})
  : GTot (TR.tvalue u lsch (get_sort e)) =
  V.evaluate lsigma (TR.standard u lsch uf) [] rho e

let nil_e : expr = App nil_decl []
let cons_one_nil : expr = App cons_decl [one; nil_e]
let head_of (l:expr) : expr = App head_decl [l]

let lemma_list_values (u:TR.uninterpreted) (uf:TR.symbols u lsch) (rho:V.environment (TR.carrier u) lsigma [])
  : Lemma (evl u uf rho nil_e == V.Constructor nil_decl [] /\
           evl u uf rho cons_one_nil ==
           V.Constructor cons_decl [TR.make #u #lsigma int_s 1; V.Constructor nil_decl []]) =
  assert_norm (L.mem nil_decl lsigma /\ L.mem cons_decl lsigma);
  assert_norm (not (L.mem (inum_decl 1) lsigma));
  assert_norm (TR.classify lsigma (inum_decl 1) == TR.Numeral int_s 1 1);
  TR.lemma_eval_interpreted u lsch uf [] rho (inum_decl 1) []

(* the matching selector reads the constructor field *)
let head_of_cons (u:TR.uninterpreted) (uf:TR.symbols u lsch) (rho:V.environment (TR.carrier u) lsigma [])
  : Lemma (D.scoped [] (head_of cons_one_nil) /\
           evl u uf rho (head_of cons_one_nil) == TR.make #u #lsigma int_s 1) =
  lemma_list_values u uf rho;
  assert_norm (not (L.mem head_decl lsigma));
  assert_norm (None? (S.find_recognizer head_decl lsch.cases));
  assert_norm (Some? (S.find_accessor head_decl lsch.cases) /\
               (Some?.v (S.find_accessor head_decl lsch.cases)).matched_case == cons_case /\
               (Some?.v (S.find_accessor head_decl lsch.cases)).field == 0)

(* an ill-matched selector is the model's free choice (not forced) *)
let head_of_nil_is_free (u:TR.uninterpreted) (uf:TR.symbols u lsch) (rho:V.environment (TR.carrier u) lsigma [])
  : Lemma (D.scoped [] (head_of nil_e) /\
           evl u uf rho (head_of nil_e) == uf.apply head_decl [V.Constructor nil_decl []]) =
  lemma_list_values u uf rho;
  assert_norm (not (L.mem head_decl lsigma));
  assert_norm (None? (S.find_recognizer head_decl lsch.cases));
  assert_norm (Some? (S.find_accessor head_decl lsch.cases) /\
               (Some?.v (S.find_accessor head_decl lsch.cases)).matched_case == cons_case /\
               (Some?.v (S.find_accessor head_decl lsch.cases)).field == 0);
  assert_norm (TR.classify lsigma head_decl == TR.Other)

let uf_int (u:TR.uninterpreted) (k:int) : TR.symbols u lsch = {
  TR.apply = (fun f _ ->
    if f.range = int_s then TR.make #u #lsigma int_s k
    else S.value_inhabitant lsch (TR.default_value u) f.range);
  TR.lambda = (fun bound t _ -> S.value_inhabitant lsch (TR.default_value u) (ArraySort bound t));
}

(* Coverage control: two root models of the same datatype schema disagree on head(nil). *)
let head_of_nil_not_forced (u:TR.uninterpreted) (rho:V.environment (TR.carrier u) lsigma [])
  : Lemma (TR.root_model u lsch (TR.standard u lsch (uf_int u 0)) /\
           TR.root_model u lsch (TR.standard u lsch (uf_int u 1)) /\
           D.scoped [] (head_of nil_e) /\
           evl u (uf_int u 0) rho (head_of nil_e) == TR.make #u #lsigma int_s 0 /\
           evl u (uf_int u 1) rho (head_of nil_e) == TR.make #u #lsigma int_s 1) =
  TR.lemma_standard_root u lsch (uf_int u 0);
  TR.lemma_standard_root u lsch (uf_int u 1);
  head_of_nil_is_free u (uf_int u 0) rho;
  head_of_nil_is_free u (uf_int u 1) rho

(* --- Nested arrays: (Array Int (Array Int Real)) -------------------------------- *)

let nested_s : sort = ArraySort [int_s] arr_s

let nested_carrier (u:TR.uninterpreted)
  : Lemma (TR.carrier u nested_s ==
           TR.func_space (int & unit) (TR.func_space (int & unit) real)) =
  assert_norm (TR.carrier u nested_s ==
               TR.func_space (int & unit) (TR.func_space (int & unit) real))

let scope2 : list sort = [arr_s; nested_s]
let a_2 : expr = Var 0 arr_s
let b_2 : expr = Var 1 nested_s
let select_n : func_decl = TR.select_decl [int_s] arr_s
let store_n : func_decl = TR.store_decl [int_s] arr_s
let inner_store : expr = App store_ir [a_2; zero; half]
let outer_store : expr = App store_n [b_2; zero; inner_store]
let nested_read : expr = App select_ir [App select_n [outer_store; zero]; zero]

let lemma_inner_store (u:TR.uninterpreted) (uf:TR.symbols u sch) (rho:env u scope2)
  : Lemma (ev u uf scope2 rho inner_store ==
           TR.make #u #sigma arr_s
             (TR.write #(TR.indices u [int_s]) #(TR.carrier u real_s)
               (TR.scalar #u #sigma arr_s (rho 0)) (0, ()) (TR.rational 1 2))) =
  lemma_zero u uf scope2 rho;
  assert_norm (TR.classify sigma (rnum_decl 1 2) == TR.Numeral real_s 1 2);
  lemma_rational u uf scope2 rho 1 2;
  assert_norm (TR.classify sigma store_ir == TR.Store [int_s] real_s);
  TR.lemma_eval_interpreted u sch uf scope2 rho store_ir [a_2; zero; half]

let lemma_outer_read (u:TR.uninterpreted) (uf:TR.symbols u sch) (rho:env u scope2)
  : Lemma (requires D.scoped scope2 (App select_n [outer_store; zero]))
          (ensures ev u uf scope2 rho (App select_n [outer_store; zero]) == ev u uf scope2 rho inner_store) =
  lemma_zero u uf scope2 rho;
  assert_norm (TR.classify sigma store_n == TR.Store [int_s] arr_s);
  TR.lemma_eval_interpreted u sch uf scope2 rho store_n [b_2; zero; inner_store];
  assert_norm (TR.classify sigma select_n == TR.Select [int_s] arr_s);
  TR.lemma_eval_interpreted u sch uf scope2 rho select_n [outer_store; zero]

(* select (select (store b 0 (store a 0 1/2)) 0) 0 = 1/2 *)
let nested_read_back (u:TR.uninterpreted) (uf:TR.symbols u sch) (rho:env u scope2)
  : Lemma (requires D.scoped scope2 (eq nested_read half))
          (ensures TR.truth sch (ev u uf scope2 rho (eq nested_read half)) == true) =
  assert_norm (D.scoped scope2 (App select_n [outer_store; zero]));
  lemma_inner_store u uf rho;
  lemma_outer_read u uf rho;
  lemma_zero u uf scope2 rho;
  assert_norm (TR.classify sigma select_ir == TR.Select [int_s] real_s);
  TR.lemma_eval_interpreted u sch uf scope2 rho select_ir [App select_n [outer_store; zero]; zero];
  lemma_rational u uf scope2 rho 1 2;
  lemma_real_equality u uf scope2 rho nested_read half (TR.rational 1 2) (TR.rational 1 2)

(* The precondition is a closed, checkable syntactic fact. *)
let nested_read_scoped () : Lemma (D.scoped scope2 (eq nested_read half)) =
  assert_norm (D.scoped scope2 (eq nested_read half))

(* --- The support gate is NOT implied by the old schema validator --------------- *)

let r_s : sort = BaseSort "Real"
let mk_real_decl : func_decl =
  { decl_name = "mk"; domain = []; range = r_s; interp = Some DL.op_constructor; int_params = [0; 0; 0] }
let is_mk_decl : func_decl =
  { decl_name = "is-mk"; domain = [r_s]; range = bool_sort; interp = Some DL.op_recognizer; int_params = [0; 0] }
let real_named_datatype : S.schema =
  { S.sorts = [r_s]; S.cases = [{ S.constructor = mk_real_decl; S.recognizer = is_mk_decl; S.accessors = [] }] }

(* A datatype registered under the primitive name Real passes S.valid but is
   rejected by the root support check. *)
let real_datatype_valid_but_unsupported ()
  : Lemma (S.valid real_named_datatype /\ not (TR.supported real_named_datatype)) =
  assert_norm (S.valid real_named_datatype /\ not (TR.supported real_named_datatype))

let ai_s : sort = ArraySort [int_s] int_s
let mk_arr_decl : func_decl =
  { decl_name = "mka"; domain = []; range = ai_s; interp = Some DL.op_constructor; int_params = [1; 0; 0] }
let is_mka_decl : func_decl =
  { decl_name = "is-mka"; domain = [ai_s]; range = bool_sort; interp = Some DL.op_recognizer; int_params = [1; 0] }
let array_owned_datatype : S.schema =
  { S.sorts = [ai_s]; S.cases = [{ S.constructor = mk_arr_decl; S.recognizer = is_mka_decl; S.accessors = [] }] }

(* A constructor whose range is an array sort passes S.valid but is rejected
   by the root support check (array sorts must keep their function carrier). *)
let array_datatype_valid_but_unsupported ()
  : Lemma (S.valid array_owned_datatype /\ not (TR.supported array_owned_datatype)) =
  assert_norm (S.valid array_owned_datatype /\ not (TR.supported array_owned_datatype))
