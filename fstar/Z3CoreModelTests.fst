(* Tests for the typed canonical core contract (`Z3CoreModel`) and the core
   kernel theorem (`Z3CoreKernel`): positive model realization, accepted
   kernel nodes holding in every core model, canonical dispatch rejecting
   look-alike declarations, typed environments, and the obstructions that
   still keep `Z3UnifiedProof.model_sound` without a model. *)
module Z3CoreModelTests

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3UnifiedProof
module CO = Z3CoreModel
module K = Z3CoreKernel
module C = Z3CanonicalOps
module D = Z3Definitions
module DV = Z3DatatypeValue
module A = Z3ArrayLemma
module LE = Z3LinearArithmeticEmbed
module LA = Z3LinearArithmeticAst
module QN = Z3QuantifierNnf
module CM = Z3Commutativity
module PT = Z3ProofTheory
module QI = Z3QuantifierInstantiation

(* --- The contract has a model ------------------------------------------- *)

let inhabited () : Lemma (exists (i:interpretation value) (dom:CO.domains). CO.core_model i dom)
  = CO.lemma_core_inhabited ()

(* --- Typed environments --------------------------------------------------- *)

(* An open Bool variable under a non-Boolean value is not a typed environment of
   any core model (the legacy `boolean_model` was refuted by exactly this). *)
let wrong_environment (i:interpretation value) (dom:CO.domains)
  : Lemma (requires CO.core_model i dom) (ensures ~(CO.env_typed dom [bool_sort] (fun _ -> VInt 0)))
  = assert (~(dom bool_sort (VInt 0)))

let open_bool (i:interpretation value) (dom:CO.domains) (rho:env value)
  : Lemma (requires CO.core_model i dom /\ CO.env_typed dom [bool_sort] rho)
          (ensures VBool? (eval i (Var 0 bool_sort) rho))
  = CO.lemma_typed_eval i dom [bool_sort] (Var 0 bool_sort) rho

(* A lambda body is typed by the innermost-first argument list. *)
let int_s : sort = BaseSort "Int"
let open_lambda : expr = Quantifier Lambda_k [int_s; bool_sort] (ArraySort [int_s; bool_sort] bool_sort) (Var 0 bool_sort)

let lambda_typed (i:interpretation value) (dom:CO.domains) (rho:env value)
  : Lemma (requires CO.core_model i dom)
          (ensures dom (ArraySort [int_s; bool_sort] bool_sort) (eval i open_lambda rho))
  = assert_norm (D.scoped [] open_lambda);
    CO.lemma_typed_eval i dom [] open_lambda rho

(* --- Content: what every core model forces ------------------------------- *)

let content (i:interpretation value) (dom:CO.domains) (s:sort) (rho:env value)
  : Lemma (requires CO.core_model i dom /\ CO.env_typed dom [s] rho)
          (ensures lit_true i rho true_expr /\ ~(lit_true i rho false_expr) /\
                   ~(lit_true i rho (mk_not_expr true_expr)) /\
                   lit_true i rho (mk_eq_expr (Var 0 s) (Var 0 s)))
  = assert (C.canonical_eq (eq_decl s));
    DV.lemma_sort_eq s s;
    assert (D.scoped [s] (mk_eq_expr (Var 0 s) (Var 0 s)))

(* --- Canonical keys: look-alike declarations are ordinary atoms ----------- *)

let clash_eq : func_decl =
  { decl_name = "="; domain = [BaseSort "BV2"; BaseSort "BV2"]; range = bool_sort;
    interp = Some 114; int_params = [2] }
let clash_true : func_decl =
  { decl_name = "true"; domain = []; range = BaseSort "BV1"; interp = Some 108; int_params = [1; 1] }
let accessor_and : func_decl =
  { decl_name = "and"; domain = [BaseSort "D"]; range = bool_sort; interp = Some 202; int_params = [0; 0; 0] }
let constructor_implies : func_decl =
  { decl_name = "=>"; domain = [int_s; int_s]; range = BaseSort "D"; interp = Some 200; int_params = [0; 0; 2] }

let not_canonical ()
  : Lemma (~(C.canonical_connective clash_eq) /\ ~(C.canonical_connective clash_true) /\
           ~(C.canonical_connective accessor_and) /\ ~(C.canonical_connective constructor_implies))
  = ()

(* The accessor named `and` is not forced to be a conjunction: two witness
   models give it different values. *)
let d_const : expr = App { decl_name = "d"; domain = []; range = BaseSort "D"; interp = None; int_params = [] } []
let accessor_app : expr = App accessor_and [d_const]

let accessor_free (rho:env value)
  : Lemma (eval (CO.witness (fun _ _ -> 0)) accessor_app rho == VBool false /\
           eval (CO.witness (fun _ _ -> 1)) accessor_app rho == VBool true)
  = assert_norm (eval (CO.witness (fun _ _ -> 0)) accessor_app rho == VBool false);
    assert_norm (eval (CO.witness (fun _ _ -> 1)) accessor_app rho == VBool true)

(* --- Accepted kernel nodes hold in every core model --------------------------- *)

let atom (n:string) : expr =
  App { decl_name = n; domain = []; range = bool_sort; interp = None; int_params = [] } []
let p : expr = atom "p"
let q : expr = atom "q"
let conj : expr = App (C.and_decl 2) [p; q]
let disj : expr = App (C.or_decl 2) [p; q]

let fact (j:judgment) : checked_fact = { conclusion = j; hypotheses = [] }

let and_node : proof_node =
  { kind = AndElimination; conclusion = Holds q; premises = [fact (Holds conj)] }

(* not (or p q) |- not p *)
let not_or_node : proof_node =
  { kind = NotOrElimination; conclusion = Holds (mk_not_expr p);
    premises = [fact (Holds (mk_not_expr disj))] }

(* (or p q), (not p) |- q *)
let resolution_node : proof_node =
  { kind = UnitResolution; conclusion = Holds q;
    premises = [fact (Holds disj); fact (Holds (mk_not_expr p))] }

let accepted_and () : Lemma (check_node_with_context [] false [] and_node == Some (fact (Holds q), 0))
  = assert_norm (check_node_with_context [] false [] and_node == Some (fact (Holds q), 0))

let accepted_not_or ()
  : Lemma (check_node_with_context [] false [] not_or_node == Some (fact (Holds (mk_not_expr p)), 0))
  = assert_norm (check_node_with_context [] false [] not_or_node == Some (fact (Holds (mk_not_expr p)), 0))

let accepted_resolution ()
  : Lemma (check_node_with_context [] false [] resolution_node == Some (fact (Holds q), 0))
  = assert_norm (check_node_with_context [] false [] resolution_node == Some (fact (Holds q), 0))

let scoped_and () : Lemma (K.core_rule and_node /\ K.judgment_scoped [] (Holds q) /\ K.facts_scoped [] and_node.premises)
  = assert_norm (K.judgment_scoped [] (Holds q) /\ K.facts_scoped [] and_node.premises)

let scoped_not_or ()
  : Lemma (K.core_rule not_or_node /\ K.judgment_scoped [] (Holds (mk_not_expr p)) /\
           K.facts_scoped [] not_or_node.premises)
  = assert_norm (K.judgment_scoped [] (Holds (mk_not_expr p)) /\ K.facts_scoped [] not_or_node.premises)

let scoped_resolution ()
  : Lemma (K.core_rule resolution_node /\ K.judgment_scoped [] (Holds q) /\
           K.facts_scoped [] resolution_node.premises)
  = assert_norm (K.judgment_scoped [] (Holds q) /\ K.facts_scoped [] resolution_node.premises)

(* The kernel theorem, instantiated: in every core model and environment, the
   premises' truth gives the accepted conclusion. *)
let resolution_premises (i:interpretation value) (rho:env value)
  : Lemma (requires lit_true i rho disj /\ lit_true i rho (mk_not_expr p))
          (ensures premises_sound i rho resolution_node.premises)
  = ()

let resolution_sound (i:interpretation value) (dom:CO.domains) (rho:env value)
  : Lemma (requires CO.core_model i dom /\ lit_true i rho disj /\ lit_true i rho (mk_not_expr p))
          (ensures lit_true i rho q)
  = accepted_resolution (); scoped_resolution ();
    resolution_premises i rho;
    CO.lemma_env_closed dom rho;
    K.lemma_core_check_node_sound [] i dom [] rho false [] resolution_node

let and_sound (i:interpretation value) (dom:CO.domains) (rho:env value)
  : Lemma (requires CO.core_model i dom /\ lit_true i rho conj) (ensures lit_true i rho q)
  = accepted_and (); scoped_and ();
    CO.lemma_env_closed dom rho;
    K.lemma_core_check_node_sound [] i dom [] rho false [] and_node

let not_or_sound (i:interpretation value) (dom:CO.domains) (rho:env value)
  : Lemma (requires CO.core_model i dom /\ lit_true i rho (mk_not_expr disj))
          (ensures lit_true i rho (mk_not_expr p))
  = accepted_not_or (); scoped_not_or ();
    CO.lemma_env_closed dom rho;
    K.lemma_core_check_node_sound [] i dom [] rho false [] not_or_node

(* The premises are satisfiable in the witness, so the instantiated theorem is
   not vacuous: with every opaque Boolean constant true, (or p q) holds. *)
let premise_satisfiable (rho:env value)
  : Lemma (CO.core_model (CO.witness (fun _ _ -> 1)) CO.witness_domains /\
           lit_true (CO.witness (fun _ _ -> 1)) rho conj /\
           lit_true (CO.witness (fun _ _ -> 1)) rho q)
  = CO.lemma_witness (fun _ _ -> 1);
    assert_norm (lit_true (CO.witness (fun _ _ -> 1)) rho conj);
    assert_norm (lit_true (CO.witness (fun _ _ -> 1)) rho q)

(* --- Canonical dispatch in the kernel ---------------------------------------- *)

(* The same shapes over a declaration that only carries the connective's name
   are rejected by the migrated kernel; the name-keyed kernel accepted them. *)
let fake_and : func_decl =
  { decl_name = "and"; domain = [bool_sort; bool_sort]; range = bool_sort; interp = Some 202; int_params = [0; 0; 0] }
let fake_not : func_decl =
  { decl_name = "not"; domain = [bool_sort]; range = bool_sort; interp = None; int_params = [] }

let fake_and_node : proof_node =
  { kind = AndElimination; conclusion = Holds q; premises = [fact (Holds (App fake_and [p; q]))] }
let fake_resolution_node : proof_node =
  { kind = UnitResolution; conclusion = Holds q;
    premises = [fact (Holds disj); fact (Holds (App fake_not [p]))] }

let rejected ()
  : Lemma (check_node_with_context [] false [] fake_and_node == None /\
           check_node_with_context [] false [] fake_resolution_node == None)
  = assert_norm (check_node_with_context [] false [] fake_and_node == None);
    assert_norm (check_node_with_context [] false [] fake_resolution_node == None)

(* Both would be unsound to accept: in a core model the look-alike conjunction
   can be true while its second argument is false. *)
let fake_and_countermodel (rho:env value)
  : Lemma (let i = CO.witness (fun f _ -> if f.decl_name = "q" then 0 else 1) in
           lit_true i rho (App fake_and [p; q]) /\ ~(lit_true i rho q))
  = assert_norm (let i = CO.witness (fun f _ -> if f.decl_name = "q" then 0 else 1) in
                 lit_true i rho (App fake_and [p; q]) /\ ~(lit_true i rho q))

(* --- Remaining blockers of the legacy global contract ------------------------ *)

(* O1: array_model and numeric_model conflict on the closed, well-sorted term
   (store a 0 1/2) with a : (Array Int Real). Typed environments do not repair it. *)
let real_s : sort = LA.real_s
let real_array : sort = ArraySort [int_s] real_s
let int_numeral (n:int) : expr =
  App { decl_name = "num"; domain = []; range = int_s; interp = Some op_num_rational; int_params = [n; 1] } []
let half : expr =
  App { decl_name = "num"; domain = []; range = real_s; interp = Some op_num_rational; int_params = [1; 2] } []
let array_constant : expr =
  App { decl_name = "a"; domain = []; range = real_array; interp = None; int_params = [] } []
let store_decl : func_decl =
  { decl_name = "store"; domain = [real_array; int_s; real_s]; range = real_array;
    interp = Some op_store; int_params = [] }
let real_store : expr = App store_decl [array_constant; int_numeral 0; half]

let array_numeric_clash (i:interpretation value) (nu:value -> FStar.Real.real) (rho:env value)
  : Lemma (requires A.array_model i /\ LE.numeric_model i nu) (ensures False)
  = assert_norm (D.scoped [] real_store);
    assert_norm (A.store_parts real_store == Some (array_constant, int_numeral 0, half));
    A.lemma_store_parts i rho real_store array_constant (int_numeral 0) half;
    assert (LA.numeral half == Some (1, 2));
    assert (FStar.Real.of_int 2 `FStar.Real.op_Star_Dot` nu (eval i half rho) == FStar.Real.of_int 1);
    match eval i half rho with
    | VInt n -> assert (nu (VInt n) == FStar.Real.of_int n)
    | _ -> ()

let model_sound_closed_clash (i:interpretation value)
  : Lemma (requires model_sound i) (ensures False)
  = let aux (nu:value -> FStar.Real.real) : Lemma (requires LE.numeric_model i nu) (ensures False)
      = array_numeric_clash i nu (fun _ -> VInt 0) in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

(* O2: quantifier_model reads bodies under untyped value lists, so the valid
   forall x:Int. x + 0 = x is false in every model of it with integer `+`. *)
let plus_decl : func_decl =
  { decl_name = "+"; domain = [int_s; int_s]; range = int_s; interp = Some op_plus; int_params = [] }
let body : expr = mk_eq_expr (App plus_decl [Var 0 int_s; int_numeral 0]) (Var 0 int_s)
let valid_forall : expr = Quantifier Forall_k [int_s] bool_sort body

let untyped_quantifier_unfaithful (i:interpretation value) (rho:env value)
  : Lemma (requires QN.quantifier_model i /\ CM.arithmetic_model i /\ eq_sound i)
          (ensures D.scoped [] valid_forall /\ ~(lit_true i rho valid_forall))
  = assert_norm (D.scoped [] valid_forall);
    let sigma = shift [VBool true] rho in
    assert (eval i (Var 0 int_s) sigma == VBool true);
    assert (CM.arithmetic_decl plus_decl);
    assert (eval i (App plus_decl [Var 0 int_s; int_numeral 0]) sigma == VInt 0);
    assert (~(lit_true i sigma body));
    QN.lemma_quantifier_truth i rho Forall_k [int_s] body

(* --- Canonical dispatch in the migrated recognizers --------------------------- *)


let fake_or : func_decl =
  { decl_name = "or"; domain = [bool_sort; bool_sort]; range = bool_sort; interp = None; int_params = [] }
let fake_true : expr =
  App { decl_name = "true"; domain = []; range = bool_sort; interp = Some 202; int_params = [0; 0; 0] } []

(* forall x:Bool. x, instantiated at true *)
let identity_forall : expr = Quantifier Forall_k [bool_sort] bool_sort (Var 0 bool_sort)

let inst_formula (f:func_decl) (n:func_decl) : expr =
  App f [App n [identity_forall]; true_expr]

let recognizers ()
  : Lemma (PT.is_not (App fake_not [p]) == None /\ PT.is_not (mk_not_expr p) == Some p /\
           complementary (mk_not_expr p) p /\ ~(complementary (App fake_not [p]) p) /\
           complementary true_expr false_expr /\ ~(complementary fake_true false_expr) /\
           formula_clause disj == [p; q] /\ formula_clause (App fake_or [p; q]) == [App fake_or [p; q]] /\
           QI.check [true_expr] (inst_formula (C.or_decl 2) not_decl) /\
           ~(QI.check [true_expr] (inst_formula fake_or not_decl)) /\
           ~(QI.check [true_expr] (inst_formula (C.or_decl 2) fake_not)))
  = assert_norm (PT.is_not (App fake_not [p]) == None /\ PT.is_not (mk_not_expr p) == Some p);
    assert_norm (complementary (mk_not_expr p) p /\ ~(complementary (App fake_not [p]) p));
    assert_norm (complementary true_expr false_expr /\ ~(complementary fake_true false_expr));
    assert_norm (formula_clause disj == [p; q] /\
                 formula_clause (App fake_or [p; q]) == [App fake_or [p; q]]);
    assert_norm (QI.check [true_expr] (inst_formula (C.or_decl 2) not_decl));
    assert_norm (~(QI.check [true_expr] (inst_formula fake_or not_decl)));
    assert_norm (~(QI.check [true_expr] (inst_formula (C.or_decl 2) fake_not)))
