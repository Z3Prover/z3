module Z3SortedBvTests

open Z3AstTheory
module B = Z3BvSyntax
module S = Z3SortedBv
module D = Z3ExprScope
module V = Z3DatatypeValue
module L = FStar.List.Tot
module R = Z3ClauseSyntax
module BS = Z3BooleanSyntax
module X = Z3BooleanRewriteSyntax
module DS = Z3DatatypeSignature
module T = Z3SortedSemantics

let constant (w:pos) (name:string) : expr =
  App { decl_name = name; domain = []; range = B.bv_sort w;
        interp = None; int_params = [] } []

let nadd (w:pos) (args:list expr) : expr =
  App { decl_name = "bvadd"; domain = L.map (fun _ -> B.bv_sort w) args;
        range = B.bv_sort w; interp = Some B.op_add; int_params = [w] } args

let x : expr = constant 8 "x"
let y : expr = constant 8 "y"
let n (v:int) : expr = B.literal 8 v
let add (a b:expr) : expr = nadd 8 [a; b]

let wrapping ()
  : Lemma (B.equivalent (add (add (n 255) x) (n 1)) x /\
           B.equivalent (nadd 8 [n 1; x; n 2; y]) (nadd 8 [n 3; x; y]) /\
           not (B.equivalent (nadd 8 [n 1; x; n 2; y]) (nadd 8 [n 3; y; x])) /\
           not (B.equivalent (add (n 200) (n 100)) (n 45))) =
  assert_norm (B.equivalent (add (add (n 255) x) (n 1)) x);
  assert_norm (B.equivalent (nadd 8 [n 1; x; n 2; y]) (nadd 8 [n 3; x; y]));
  assert_norm (not (B.equivalent (nadd 8 [n 1; x; n 2; y]) (nadd 8 [n 3; y; x])));
  assert_norm (not (B.equivalent (add (n 200) (n 100)) (n 45)))

let malformed : expr =
  App { decl_name = "bad"; domain = []; range = B.bv_sort 8;
        interp = Some B.op_numeral; int_params = [8; 256] } []

let rec chain (depth:nat) : Tot expr (decreases depth) =
  if depth = 0 then x else add (chain (depth - 1)) (n 0)

let guards ()
  : Lemma (B.numeral (B.literal 8 255) == Some (8, 255) /\
           B.numeral (B.literal 8 256) == None /\
           B.numeral (B.literal 4096 0) == Some (4096, 0) /\
           B.numeral (B.literal 4097 0) == None /\
           not (B.equivalent (add malformed (n 0)) (add malformed (n 0))) /\
           not (B.equivalent (add (Var 0 (B.bv_sort 8)) (n 0))
                             (add (Var 0 (B.bv_sort 8)) (n 0)))) =
  assert_norm (B.numeral (B.literal 8 255) == Some (8, 255));
  assert_norm (B.numeral (B.literal 8 256) == None);
  assert_norm (B.numeral (B.literal 4096 0) == Some (4096, 0));
  assert_norm (B.numeral (B.literal 4097 0) == None);
  assert_norm (not (B.equivalent (add malformed (n 0)) (add malformed (n 0))));
  assert_norm (not (B.equivalent (add (Var 0 (B.bv_sort 8)) (n 0))
                                 (add (Var 0 (B.bv_sort 8)) (n 0))))

let number_sound (number:expr -> GTot int)
  : Lemma (requires S.add_model number)
          (ensures number (add (add (n 255) x) (n 1)) == number x) =
  wrapping ();
  S.lemma_equivalent number (add (add (n 255) x) (n 1)) x

let budget ()
  : Lemma (B.equivalent (chain 255) x /\ not (B.equivalent (chain 256) x)) =
  assert_norm (B.equivalent (chain 255) x);
  assert_norm (not (B.equivalent (chain 256) x))

let typed_sound (#base:sort -> Type0) (sigma:V.signature)
                (i:V.interpretation base sigma) (rho:V.environment base sigma [])
                (project:(s:sort -> V.value base sigma s -> GTot int))
  : Lemma (requires S.add_model (S.typed_number sigma i rho project) /\
                    (forall (w:pos) (a b:expr).
                      D.scoped [] a /\ D.scoped [] b /\
                      get_sort a == B.bv_sort w /\ get_sort b == B.bv_sort w /\
                      project (get_sort a) (V.evaluate sigma i [] rho a) ==
                      project (get_sort b) (V.evaluate sigma i [] rho b) ==>
                      V.evaluate sigma i [] rho a == V.evaluate sigma i [] rho b))
          (ensures V.evaluate sigma i [] rho (add (add (n 255) x) (n 1)) ==
                   V.evaluate sigma i [] rho x) =
  wrapping ();
  S.lemma_equivalent_typed sigma i rho project (add (add (n 255) x) (n 1)) x

let p : expr =
  App { decl_name = "p"; domain = []; range = bool_sort;
        interp = None; int_params = [] } []
let q : expr =
  App { decl_name = "q"; domain = []; range = bool_sort;
        interp = None; int_params = [] } []
let w2 : expr = B.word [p; q]
let w2b : expr = B.word [R.mk_not_expr (R.mk_not_expr p); q]
let x2 : expr = constant 2 "x2"
let y2 : expr = constant 2 "y2"
let proj2 : expr = B.word (B.projection_bits 2 x2 0 2)

let word_equivalence_paths ()
  : Lemma (B.literal_equivalent (B.word [R.true_expr; R.false_expr]) (B.literal 2 1) /\
           B.word_equivalent_all (B.literal 2 1) (B.word [R.true_expr; R.false_expr]) /\
           B.word_equivalent w2 w2b /\
           B.projection_equivalent x2 proj2 /\
           B.projection_equivalent (constant 1 "x1")
             (B.word (B.projection_bits 1 (constant 1 "x1") 0 1)) /\
           B.word_equivalent_all x2 proj2 /\ B.word_equivalent_all proj2 x2 /\
           not (B.word_equivalent_all x2 (B.word [B.projection 2 x2 1; B.projection 2 x2 0])) /\
           not (B.word_equivalent_all (Var 0 (B.bv_sort 2)) (Var 0 (B.bv_sort 2)))) =
  assert_norm (B.literal_equivalent (B.word [R.true_expr; R.false_expr]) (B.literal 2 1));
  assert_norm (B.word_equivalent_all (B.literal 2 1) (B.word [R.true_expr; R.false_expr]));
  assert_norm (B.word_equivalent w2 w2b);
  assert_norm (B.projection_equivalent x2 proj2);
  assert_norm (B.projection_equivalent (constant 1 "x1")
    (B.word (B.projection_bits 1 (constant 1 "x1") 0 1)));
  assert_norm (B.word_equivalent_all x2 proj2 /\ B.word_equivalent_all proj2 x2);
  assert_norm (not (B.word_equivalent_all x2 (B.word [B.projection 2 x2 1; B.projection 2 x2 0])));
  assert_norm (not (B.word_equivalent_all (Var 0 (B.bv_sort 2)) (Var 0 (B.bv_sort 2))))

let concat3 : expr =
  App { decl_name = "concat"; domain = [B.bv_sort 2; B.bv_sort 2; B.bv_sort 2];
        range = B.bv_sort 6; interp = Some B.op_concat; int_params = [2; 2; 2] }
      [x2; y2; x2]
let eq (a b:expr) : expr = R.mk_eq_expr a b
let word_concat : expr = B.concat 2 2 w2 w2b
let sym_concat : expr = B.concat 2 2 x2 y2
let nested_concat : expr = B.concat 4 2 sym_concat x2

let word_rewrite_paths ()
  : Lemma (Some? (B.equality_rewrite (eq w2 w2b)) /\
           Some? (B.concat_equality_rewrite (eq sym_concat (B.literal 4 3))) /\
           Some? (B.extract_rewrite (B.order_slice 2 1 0 w2)) /\
           Some? (B.concat_rewrite word_concat) /\
           Some? (B.addition_rewrite (nadd 2 [w2; w2b])) /\
           Some? (B.concat3_rewrite concat3) /\
           Some? (B.concat_association_rewrite nested_concat) /\
           Some? (B.not_concat_rewrite (B.complement 4 sym_concat)) /\
           Some? (B.word_rewrite (eq w2 w2b)) /\
           Some? (B.word_rewrite (eq sym_concat (B.literal 4 3))) /\
           Some? (B.word_rewrite (B.order_slice 2 1 0 w2)) /\
           Some? (B.word_rewrite word_concat) /\
           Some? (B.word_rewrite (nadd 2 [w2; w2b])) /\
           Some? (B.word_rewrite concat3) /\
           Some? (B.word_rewrite nested_concat) /\
           Some? (B.word_rewrite (B.complement 4 sym_concat)) /\
           B.word_rewrite (Var 0 (B.bv_sort 2)) == None) =
  assert_norm (Some? (B.equality_rewrite (eq w2 w2b)));
  assert_norm (Some? (B.concat_equality_rewrite (eq sym_concat (B.literal 4 3))));
  assert_norm (Some? (B.extract_rewrite (B.order_slice 2 1 0 w2)));
  assert_norm (Some? (B.concat_rewrite word_concat));
  assert_norm (Some? (B.addition_rewrite (nadd 2 [w2; w2b])));
  assert_norm (Some? (B.concat3_rewrite concat3));
  assert_norm (Some? (B.concat_association_rewrite nested_concat));
  assert_norm (Some? (B.not_concat_rewrite (B.complement 4 sym_concat)));
  assert_norm (Some? (B.word_rewrite (eq w2 w2b)));
  assert_norm (Some? (B.word_rewrite (eq sym_concat (B.literal 4 3))));
  assert_norm (Some? (B.word_rewrite (B.order_slice 2 1 0 w2)));
  assert_norm (Some? (B.word_rewrite word_concat));
  assert_norm (Some? (B.word_rewrite (nadd 2 [w2; w2b])));
  assert_norm (Some? (B.word_rewrite concat3));
  assert_norm (Some? (B.word_rewrite nested_concat));
  assert_norm (Some? (B.word_rewrite (B.complement 4 sym_concat)));
  assert_norm (B.word_rewrite (Var 0 (B.bv_sort 2)) == None)

let mixed : expr =
  eq (App (B.term_ite_decl (B.bv_sort 2)) [p; B.literal 2 1; x2]) (B.literal 2 1)

let order_rewrite_paths ()
  : Lemma (Some? (B.mixed_equality mixed) /\ Some? (B.order_rewrite_all mixed) /\
           B.order_rewrite_all (B.unsigned 2 B.op_ult x2 x2) == Some R.false_expr /\
           B.order_rewrite_all (B.unsigned 2 B.op_ule x2 x2) == Some R.true_expr /\
           Some? (B.order_rewrite_all (B.unsigned 2 B.op_ult x2 y2)) /\
           Some? (B.order_rewrite_all (B.unsigned 2 B.op_uge x2 y2)) /\
           B.order_rewrite_all (B.unsigned 2 B.op_ule (B.literal 2 0) x2) == Some R.true_expr /\
           Some? (B.order_rewrite_all (B.unsigned 2 B.op_ule w2 w2b)) /\
           Some? (B.split_rewrite (B.unsigned 2 B.op_ule (B.literal 2 1) x2)) /\
           Some? (B.order_rewrite_all (B.unsigned 2 B.op_ule (B.literal 2 1) x2)) /\
           B.order_rewrite_all (B.unsigned 2 B.op_ule x2 y2) == None /\
           B.order_rewrite_all (B.unsigned 4097 B.op_ult
             (constant 4097 "x") (constant 4097 "y")) == None) =
  assert_norm (Some? (B.mixed_equality mixed) /\ Some? (B.order_rewrite_all mixed));
  assert_norm (B.order_rewrite_all (B.unsigned 2 B.op_ult x2 x2) == Some R.false_expr);
  assert_norm (B.order_rewrite_all (B.unsigned 2 B.op_ule x2 x2) == Some R.true_expr);
  assert_norm (Some? (B.order_rewrite_all (B.unsigned 2 B.op_ult x2 y2)));
  assert_norm (Some? (B.order_rewrite_all (B.unsigned 2 B.op_uge x2 y2)));
  assert_norm (B.order_rewrite_all (B.unsigned 2 B.op_ule (B.literal 2 0) x2) == Some R.true_expr);
  assert_norm (Some? (B.order_rewrite_all (B.unsigned 2 B.op_ule w2 w2b)));
  assert_norm (Some? (B.split_rewrite (B.unsigned 2 B.op_ule (B.literal 2 1) x2)));
  assert_norm (Some? (B.order_rewrite_all (B.unsigned 2 B.op_ule (B.literal 2 1) x2)));
  assert_norm (B.order_rewrite_all (B.unsigned 2 B.op_ule x2 y2) == None);
  assert_norm (B.order_rewrite_all (B.unsigned 4097 B.op_ult
    (constant 4097 "x") (constant 4097 "y")) == None)

let connective_identity (args:list expr) (equal:bool)
  : Lemma (X.connective_decl X.Conjunction args == R.and_decl args /\
           X.connective_decl X.Disjunction args == R.or_decl args /\
           X.connective_decl (if equal then X.Disjunction else X.Conjunction) args ==
             (if equal then R.or_decl args else R.and_decl args) /\
           X.boolean_xor_decl == BS.boolean_xor_decl /\
           X.boolean_ite_decl == BS.boolean_ite_decl) = ()

let typed_equivalence_paths (#base:sort -> Type0) (s:DS.checked_schema)
                   (bc:DS.boolean_carrier base) (model:T.scalar_model base)
                   (other:V.interpretation base (DS.signature s))
                   (rho:V.environment base (DS.signature s) [])
                   (project:(t:sort -> V.value base (DS.signature s) t -> GTot int))
  : Lemma (requires S.order_model
                    (S.typed_number (DS.signature s) (T.interpretation s bc model other) rho project)
                    (T.truth_at s bc model other [] rho) /\
                    S.word_reflection (DS.signature s) (T.interpretation s bc model other) rho project /\
                    D.scoped [] w2 /\ D.scoped [] w2b /\ D.scoped [] x2 /\ D.scoped [] proj2)
          (ensures V.evaluate (DS.signature s) (T.interpretation s bc model other) [] rho w2 ==
                   V.evaluate (DS.signature s) (T.interpretation s bc model other) [] rho w2b /\
                   V.evaluate (DS.signature s) (T.interpretation s bc model other) [] rho x2 ==
                   V.evaluate (DS.signature s) (T.interpretation s bc model other) [] rho proj2) =
  word_equivalence_paths ();
  S.lemma_word_equivalent_all_typed s bc model other rho project w2 w2b;
  S.lemma_word_equivalent_all_typed s bc model other rho project x2 proj2

let nmul (w:pos) (args:list expr) : expr =
  App { decl_name = "bvmul"; domain = L.map (fun _ -> B.bv_sort w) args;
        range = B.bv_sort w; interp = Some B.op_mul; int_params = [w] } args

let extract_distrib_add_a : expr = B.order_slice 8 1 0 (nadd 8 [x; y; x])
let extract_distrib_add_b : expr =
  nadd 2 [B.order_slice 8 1 0 x; B.order_slice 8 1 0 y; B.order_slice 8 1 0 x]
let extract_distrib_mul_a : expr = B.order_slice 8 1 0 (nmul 8 [x; y])
let extract_distrib_mul_b : expr = nmul 2 [B.order_slice 8 1 0 x; B.order_slice 8 1 0 y]
let extract_ite_a : expr = B.order_slice 8 3 1 (App (B.term_ite_decl (B.bv_sort 8)) [p; x; y])
let extract_ite_b : expr = App (B.term_ite_decl (B.bv_sort 3))
  [p; B.order_slice 8 3 1 x; B.order_slice 8 3 1 y]

let extract_paths ()
  : Lemma (B.extract_check extract_distrib_add_a extract_distrib_add_b /\
           B.extract_check extract_distrib_mul_a extract_distrib_mul_b /\
           B.extract_check extract_ite_a extract_ite_b /\
           B.slice 4 2 1 (B.order_slice 8 5 2 x) (B.order_slice 8 4 3 x) /\
           B.extract_check (B.order_slice 4 1 0 sym_concat) y2 /\
           B.extract_check (B.order_slice 4 3 2 sym_concat) x2 /\
           B.extract_check (B.order_slice 4 2 1 sym_concat)
             (B.concat 1 1 (B.order_slice 2 0 0 x2) (B.order_slice 2 1 1 y2)) /\
           not (B.extract_check extract_distrib_add_b extract_distrib_add_a) /\
           not (B.extract_check (B.order_slice 8 2 1 (nadd 8 [x; y]))
             (nadd 2 [B.order_slice 8 2 1 x; B.order_slice 8 2 1 y]))) =
  assert_norm (B.extract_check extract_distrib_add_a extract_distrib_add_b);
  assert_norm (B.extract_check extract_distrib_mul_a extract_distrib_mul_b);
  assert_norm (B.extract_check extract_ite_a extract_ite_b);
  assert_norm (B.slice 4 2 1 (B.order_slice 8 5 2 x) (B.order_slice 8 4 3 x));
  assert_norm (B.extract_check (B.order_slice 4 1 0 sym_concat) y2);
  assert_norm (B.extract_check (B.order_slice 4 3 2 sym_concat) x2);
  assert_norm (B.extract_check (B.order_slice 4 2 1 sym_concat)
    (B.concat 1 1 (B.order_slice 2 0 0 x2) (B.order_slice 2 1 1 y2)));
  assert_norm (not (B.extract_check extract_distrib_add_b extract_distrib_add_a));
  assert_norm (not (B.extract_check (B.order_slice 8 2 1 (nadd 8 [x; y]))
    (nadd 2 [B.order_slice 8 2 1 x; B.order_slice 8 2 1 y])))

let zero_extend (w:pos) (k:nat) (a:expr) : expr =
  App { decl_name = "zero_extend"; domain = [B.bv_sort w]; range = B.bv_sort (w + k);
        interp = Some B.op_zero_extend; int_params = [w; k] } [a]
let exhaustive_expr : expr =
  eq (nadd 2 [x2; B.literal 2 0]) x2
let exhaustive_bad_num : expr = B.literal 2 4
let exhaustive_bad_add : expr =
  App { decl_name = "bvadd"; domain = [B.bv_sort 2; B.bv_sort 2]; range = B.bv_sort 2;
        interp = Some B.op_add; int_params = [1] } [B.literal 2 0; x2]
let thirteen_bit_word : expr = B.concat 5 8 (constant 5 "a") (constant 8 "b")
let exhaustive_reflexive (e:expr) : expr = eq (nadd 2 [e; B.literal 2 0]) (nadd 2 [e; B.literal 2 0])
let clash : expr =
  App { decl_name = "="; domain = [B.bv_sort 2; B.bv_sort 2]; range = bool_sort;
        interp = Some B.op_ult; int_params = [2] } [B.literal 2 0; B.literal 2 0]

let exhaustive_paths ()
  : Lemma (B.exhaustive_valid R.true_expr /\ not (B.exhaustive_valid R.false_expr) /\
           B.exhaustive_valid exhaustive_expr /\
           B.exhaustive_valid (eq (zero_extend 2 1 x2) (B.concat 1 2 (B.literal 1 0) x2)) /\
           not (B.exhaustive_valid (eq (nadd 2 [x2; B.literal 2 1]) x2)) /\
           B.within_bits [(constant 8 "b", 8); (constant 4 "c", 4)] 0 /\
           not (B.within_bits [(constant 8 "b", 8); (constant 5 "c", 5)] 0) /\
           B.leaf [(Var 0 (B.bv_sort 2), 2)] (fun _ -> 0) 2 (Var 0 (B.bv_sort 2)) == None /\
           B.eval_bv [(Var 0 (B.bv_sort 2), 2)] (fun _ -> 0) 2 (Var 0 (B.bv_sort 2)) == None /\
           B.leaves_bv [] 2 (Var 0 (B.bv_sort 2)) == [(Var 0 (B.bv_sort 2), 2)] /\
           B.eval_bool [] (fun _ -> 0) (Var 0 bool_sort) == None /\
           not (B.exhaustive_valid
             (Quantifier Forall_k [B.bv_sort 2] bool_sort
               (eq (Var 0 (B.bv_sort 2)) (Var 0 (B.bv_sort 2))))) /\
           not (B.exhaustive_valid (exhaustive_reflexive exhaustive_bad_num)) /\
           not (B.exhaustive_valid (exhaustive_reflexive exhaustive_bad_add)) /\
           not (B.exhaustive_valid (eq (nadd 13 [thirteen_bit_word; B.literal 13 0]) thirteen_bit_word)) /\
           not (B.exhaustive_valid clash) /\ B.exhaustive_valid (R.mk_not_expr clash) /\
           not (B.exhaustive_valid (eq (Var 0 (B.bv_sort 2)) (Var 0 (B.bv_sort 2)))) /\
           not (B.exhaustive_valid (eq (nadd 2 [malformed; B.literal 2 0])
                                      (nadd 2 [malformed; B.literal 2 0])))) =
  assert_norm (B.exhaustive_valid R.true_expr);
  assert_norm (not (B.exhaustive_valid R.false_expr));
  assert_norm (B.exhaustive_valid exhaustive_expr);
  assert_norm (B.exhaustive_valid (eq (zero_extend 2 1 x2) (B.concat 1 2 (B.literal 1 0) x2)));
  assert_norm (not (B.exhaustive_valid (eq (nadd 2 [x2; B.literal 2 1]) x2)));
  assert_norm (B.within_bits [(constant 8 "b", 8); (constant 4 "c", 4)] 0);
  assert_norm (not (B.within_bits [(constant 8 "b", 8); (constant 5 "c", 5)] 0));
  assert_norm (B.leaf [(Var 0 (B.bv_sort 2), 2)] (fun _ -> 0) 2 (Var 0 (B.bv_sort 2)) == None);
  assert_norm (B.eval_bv [(Var 0 (B.bv_sort 2), 2)] (fun _ -> 0) 2 (Var 0 (B.bv_sort 2)) == None);
  assert_norm (B.leaves_bv [] 2 (Var 0 (B.bv_sort 2)) == [(Var 0 (B.bv_sort 2), 2)]);
  assert_norm (B.eval_bool [] (fun _ -> 0) (Var 0 bool_sort) == None);
  assert_norm (not (B.exhaustive_valid
    (Quantifier Forall_k [B.bv_sort 2] bool_sort
      (eq (Var 0 (B.bv_sort 2)) (Var 0 (B.bv_sort 2))))));
  assert_norm (not (B.exhaustive_valid (exhaustive_reflexive exhaustive_bad_num)));
  assert_norm (not (B.exhaustive_valid (exhaustive_reflexive exhaustive_bad_add)));
  assert_norm (not (B.exhaustive_valid (eq (nadd 13 [thirteen_bit_word; B.literal 13 0]) thirteen_bit_word)));
  assert_norm (not (B.exhaustive_valid clash) /\ B.exhaustive_valid (R.mk_not_expr clash));
  assert_norm (not (B.exhaustive_valid (eq (Var 0 (B.bv_sort 2)) (Var 0 (B.bv_sort 2)))));
  assert_norm (not (B.exhaustive_valid (eq (nadd 2 [malformed; B.literal 2 0])
    (nadd 2 [malformed; B.literal 2 0]))))

let extract_typed_example (#base:sort -> Type0) (sigma:V.signature)
                    (i:V.interpretation base sigma) (rho:V.environment base sigma [])
                    (project:(s:sort -> V.value base sigma s -> GTot int))
                    (bproject:(s:sort -> V.value base sigma s -> GTot bool))
  : Lemma (requires D.scoped [] extract_distrib_mul_a /\ D.scoped [] extract_distrib_mul_b /\
                    S.word_model (S.typed_number sigma i rho project) (S.typed_truth sigma i rho bproject) /\
                    S.arith_model (S.typed_number sigma i rho project) /\
                    S.choice_model (S.typed_number sigma i rho project) (S.typed_truth sigma i rho bproject) /\
                    S.word_reflection sigma i rho project)
          (ensures V.evaluate sigma i [] rho extract_distrib_mul_a ==
                   V.evaluate sigma i [] rho extract_distrib_mul_b) =
  extract_paths ();
  S.lemma_extract_check_typed sigma i rho project bproject extract_distrib_mul_a extract_distrib_mul_b

let exhaustive_typed_example (#base:sort -> Type0) (s:DS.checked_schema)
                   (bc:DS.boolean_carrier base) (model:T.scalar_model base)
                   (other:V.interpretation base (DS.signature s))
                   (rho:V.environment base (DS.signature s) [])
                   (project:(t:sort -> V.value base (DS.signature s) t -> GTot int))
  : Lemma (requires D.scoped [] (nadd 2 [x2; B.literal 2 0]) /\ D.scoped [] x2 /\
                    S.exhaustive_model
                      (S.typed_number (DS.signature s) (T.interpretation s bc model other) rho project)
                      (T.truth_at s bc model other [] rho))
          (ensures V.evaluate (DS.signature s) (T.interpretation s bc model other) [] rho
                     (nadd 2 [x2; B.literal 2 0]) ==
                   V.evaluate (DS.signature s) (T.interpretation s bc model other) [] rho x2) =
  assert_norm (B.exhaustive_equivalent (nadd 2 [x2; B.literal 2 0]) x2);
  S.lemma_exhaustive_equivalent_typed s bc model other rho project (nadd 2 [x2; B.literal 2 0]) x2
