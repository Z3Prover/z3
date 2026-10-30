(* Tests for the typed canonical core contract (`Z3CoreModel`) and the core
   kernel theorem (`Z3CoreKernel`): positive model realization, accepted
   kernel nodes holding in every core model with premises satisfiable in a
   witness core model (closed and open scopes, bit-vector steps), the
   typed-environment and `core_rule` hypotheses being load-bearing,
   canonical dispatch rejecting look-alike declarations, and finite
   clause-instance evidence for obstructions that still keep
   `Z3UnifiedProof.model_sound` without a model. *)
module Z3CoreModelTests

open FStar.Real
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
module AT = Z3ArrayTheory
module LE = Z3LinearArithmeticEmbed
module LA = Z3LinearArithmeticAst
module QN = Z3QuantifierNnf
module CM = Z3Commutativity
module PT = Z3ProofTheory
module QI = Z3QuantifierInstantiation
module SM = Z3StandardModel
module BV = Z3BvLemma
module DL = Z3DatatypeLemma
module L = FStar.List.Tot

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

(* --- The legacy connective contracts, keyed by the canonical predicates ------ *)

(* The connective conjuncts of `model_sound` (`not_sound` ... `false_sound`) are
   keyed by `Z3CanonicalOps`, exactly as the core contract's connectives, so
   every core model satisfies them. *)
let legacy_connectives (i:interpretation value) (dom:CO.domains)
  : Lemma (requires CO.core_model i dom)
          (ensures not_sound i /\ and_sound i /\ or_sound i /\ implies_sound i /\
                   true_sound i /\ false_sound i)
  = ()

(* Closed instances that the name-keyed contracts forced into contradiction
   with the bit-vector and datatype contracts. The canonical keys do not
   constrain them, and in a core model (which satisfies the re-keyed
   contracts) they take the values of their own theory, which the old
   name-keyed instances excluded. *)
let zero2 : expr = BV.literal 2 0
let clash_eq_app : expr = App clash_eq [zero2; zero2]
let true_numeral (n:int) : func_decl =
  { decl_name = "true"; domain = []; range = BV.bv_sort 1; interp = Some BV.op_numeral; int_params = [1; n] }

(* `=` tagged `bvult`: the comparison 0 <u 0 is false although its arguments
   are equal; name-keyed `eq_sound` made it true. *)
let clash_eq_excluded (rho:env value)
  : Lemma (~(C.canonical_eq clash_eq) /\ clash_eq.decl_name == "=" /\
           CO.core_model (CO.witness (fun _ _ -> 0)) CO.witness_domains /\
           eval (CO.witness (fun _ _ -> 0)) clash_eq_app rho == VBool false)
  = CO.lemma_witness (fun _ _ -> 0);
    assert_norm (eval (CO.witness (fun _ _ -> 0)) clash_eq_app rho == VBool false)

(* Bit-vector numerals named `true`: they denote 0 and 1; name-keyed
   `true_sound` made both `VBool true`, so their projections would agree. *)
let true_numerals_excluded (rho:env value)
  : Lemma (~(C.canonical_true (true_numeral 0)) /\ ~(C.canonical_true (true_numeral 1)) /\
           SM.std_project 1 (eval (CO.witness (fun _ _ -> 0)) (App (true_numeral 0) []) rho) == 0 /\
           SM.std_project 1 (eval (CO.witness (fun _ _ -> 0)) (App (true_numeral 1) []) rho) == 1)
  = assert_norm (SM.std_project 1 (eval (CO.witness (fun _ _ -> 0)) (App (true_numeral 0) []) rho) == 0 /\
                 SM.std_project 1 (eval (CO.witness (fun _ _ -> 0)) (App (true_numeral 1) []) rho) == 1)

(* A datatype `T = mk (and:Bool) (or:Bool) (not:Bool)`, as the native bridge
   marshals it: the accessor `and` of `mk true b b` is its first field, true,
   for both values of `b`, and the two constructions differ. Name-keyed
   `and_sound` made the accessor a conjunction of the (non-Boolean) record. *)
let t_sort : sort = BaseSort "T"
let mk_decl : func_decl =
  { decl_name = "mk"; domain = [bool_sort; bool_sort; bool_sort]; range = t_sort;
    interp = Some DL.op_constructor; int_params = [7; 9; 3] }
let and_field : func_decl =
  { decl_name = "and"; domain = [t_sort]; range = bool_sort; interp = Some DL.op_accessor; int_params = [7; 9; 0] }
let mk_app (b:expr) : expr = App mk_decl [true_expr; b; b]
let bit (v:value) : int = match v with VBool true -> 1 | _ -> 0
(* `mk` encodes its fields as bits; the accessor `and` reads the first one. *)
let record_base : func_decl -> list value -> int = fun f vs ->
  if f.decl_name = "mk" then (match vs with [a; b; c] -> 4 * bit a + 2 * bit b + bit c | _ -> 0)
  else if f.decl_name = "and" then (match vs with [VInt n] -> (n / 4) % 2 | _ -> 0)
  else 0
let record_fields (v:value) : list value =
  match v with VInt n -> [VBool ((n / 4) % 2 = 1); VBool ((n / 2) % 2 = 1); VBool (n % 2 = 1)] | _ -> []

let datatype_and_excluded (rho:env value)
  : Lemma (~(C.canonical_and and_field) /\
           CO.core_model (CO.witness record_base) CO.witness_domains /\
           record_fields (eval (CO.witness record_base) (mk_app true_expr) rho) ==
             [VBool true; VBool true; VBool true] /\
           record_fields (eval (CO.witness record_base) (mk_app false_expr) rho) ==
             [VBool true; VBool false; VBool false] /\
           eval (CO.witness record_base) (App and_field [mk_app true_expr]) rho == VBool true /\
           eval (CO.witness record_base) (App and_field [mk_app false_expr]) rho == VBool true /\
           ~(conj_holds (CO.witness record_base) rho [mk_app true_expr]))
  = CO.lemma_witness record_base;
    assert_norm (record_fields (eval (CO.witness record_base) (mk_app true_expr) rho) ==
                   [VBool true; VBool true; VBool true] /\
                 record_fields (eval (CO.witness record_base) (mk_app false_expr) rho) ==
                   [VBool true; VBool false; VBool false]);
    assert_norm (eval (CO.witness record_base) (App and_field [mk_app true_expr]) rho == VBool true /\
                 eval (CO.witness record_base) (App and_field [mk_app false_expr]) rho == VBool true);
    assert_norm (~(conj_holds (CO.witness record_base) rho [mk_app true_expr]))

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

(* The premises are satisfiable in witness core models, so each instantiated
   theorem above is not vacuous: the premises hold and the theorem then gives
   the conclusion in the same model. *)
let base_p0 : func_decl -> list value -> int = fun f _ -> if f.decl_name = "p" then 0 else 1

let premise_satisfiable (rho:env value)
  : Lemma (CO.core_model (CO.witness (fun _ _ -> 1)) CO.witness_domains /\
           lit_true (CO.witness (fun _ _ -> 1)) rho conj /\
           lit_true (CO.witness (fun _ _ -> 1)) rho q)
  = CO.lemma_witness (fun _ _ -> 1);
    assert_norm (lit_true (CO.witness (fun _ _ -> 1)) rho conj);
    and_sound (CO.witness (fun _ _ -> 1)) CO.witness_domains rho

(* (or p q) and (not p) hold when p is false and q true. *)
let resolution_satisfiable (rho:env value)
  : Lemma (CO.core_model (CO.witness base_p0) CO.witness_domains /\
           lit_true (CO.witness base_p0) rho disj /\ lit_true (CO.witness base_p0) rho (mk_not_expr p) /\
           lit_true (CO.witness base_p0) rho q)
  = CO.lemma_witness base_p0;
    assert_norm (lit_true (CO.witness base_p0) rho disj /\ lit_true (CO.witness base_p0) rho (mk_not_expr p));
    resolution_sound (CO.witness base_p0) CO.witness_domains rho

(* not (or p q) holds when p and q are false. *)
let not_or_satisfiable (rho:env value)
  : Lemma (CO.core_model (CO.witness (fun _ _ -> 0)) CO.witness_domains /\
           lit_true (CO.witness (fun _ _ -> 0)) rho (mk_not_expr disj) /\
           lit_true (CO.witness (fun _ _ -> 0)) rho (mk_not_expr p))
  = CO.lemma_witness (fun _ _ -> 0);
    assert_norm (lit_true (CO.witness (fun _ _ -> 0)) rho (mk_not_expr disj));
    not_or_sound (CO.witness (fun _ _ -> 0)) CO.witness_domains rho

(* --- An open scope: the theorem under a typed environment -------------------- *)

(* (or v q), (not v) |- q with v = Var 0 Bool, scoped in [Bool] but not in []. *)
let vb : expr = Var 0 bool_sort
let open_node : proof_node =
  { kind = UnitResolution; conclusion = Holds q;
    premises = [fact (Holds (App (C.or_decl 2) [vb; q])); fact (Holds (mk_not_expr vb))] }

let open_accepted () : Lemma (check_node_with_context [] false [] open_node == Some (fact (Holds q), 0))
  = assert_norm (check_node_with_context [] false [] open_node == Some (fact (Holds q), 0))

let open_scoped ()
  : Lemma (K.core_rule open_node /\ K.judgment_scoped [bool_sort] open_node.conclusion /\
           K.facts_scoped [bool_sort] open_node.premises /\ not (K.facts_scoped [] open_node.premises))
  = assert_norm (K.core_rule open_node /\ K.judgment_scoped [bool_sort] open_node.conclusion /\
                 K.facts_scoped [bool_sort] open_node.premises /\ not (K.facts_scoped [] open_node.premises))

let open_premises (i:interpretation value) (rho:env value)
  : Lemma (requires lit_true i rho (App (C.or_decl 2) [vb; q]) /\ lit_true i rho (mk_not_expr vb))
          (ensures premises_sound i rho open_node.premises)
  = ()

let open_sound (i:interpretation value) (dom:CO.domains) (rho:env value)
  : Lemma (requires CO.core_model i dom /\ CO.env_typed dom [bool_sort] rho /\
                    lit_true i rho (App (C.or_decl 2) [vb; q]) /\ lit_true i rho (mk_not_expr vb))
          (ensures lit_true i rho q)
  = open_accepted (); open_scoped (); open_premises i rho;
    K.lemma_core_check_node_sound [] i dom [bool_sort] rho false [] open_node

let rho_false : env value = fun _ -> VBool false

let typed_false () : Lemma (CO.env_typed CO.witness_domains [bool_sort] rho_false)
  = assert_norm (SM.fits bool_sort (VBool false) == true);
    let aux (n:nat) : Lemma (n < L.length [bool_sort] ==> CO.witness_domains (L.index [bool_sort] n) (rho_false n)) = () in
    FStar.Classical.forall_intro aux

(* Satisfiable at the typed environment v := false, with q true. *)
let open_satisfiable ()
  : Lemma (lit_true (CO.witness (fun _ _ -> 1)) rho_false (App (C.or_decl 2) [vb; q]) /\
           lit_true (CO.witness (fun _ _ -> 1)) rho_false (mk_not_expr vb) /\
           lit_true (CO.witness (fun _ _ -> 1)) rho_false q)
  = assert_norm (lit_true (CO.witness (fun _ _ -> 1)) rho_false (App (C.or_decl 2) [vb; q]) /\
                 lit_true (CO.witness (fun _ _ -> 1)) rho_false (mk_not_expr vb));
    CO.lemma_witness (fun _ _ -> 1); typed_false ();
    open_sound (CO.witness (fun _ _ -> 1)) CO.witness_domains rho_false

(* --- The typed environment is load-bearing ------------------------------------ *)

(* Discharging the hypothesis v = Var 0 Bool into (not v) is accepted, is a core
   rule and is scoped in [Bool]. In a core model, under the untyped environment
   v := 0, or under an environment typed for the binder-swapped scope
   [Int; Bool], the premise holds and the conclusion is false. *)
let hfact (j:judgment) (hs:list expr) : checked_fact = { conclusion = j; hypotheses = hs }
let lemma_node : proof_node =
  { kind = LemmaRule; conclusion = Holds (mk_not_expr vb); premises = [hfact (Holds false_expr) [vb]] }

let lemma_node_facts ()
  : Lemma (check_node_with_context [] false [] lemma_node == Some (fact (Holds (mk_not_expr vb)), 0) /\
           K.core_rule lemma_node /\
           K.judgment_scoped [bool_sort] lemma_node.conclusion /\ K.facts_scoped [bool_sort] lemma_node.premises /\
           not (K.judgment_scoped [] lemma_node.conclusion) /\
           not (K.judgment_scoped [int_s; bool_sort] lemma_node.conclusion))
  = assert_norm (check_node_with_context [] false [] lemma_node == Some (fact (Holds (mk_not_expr vb)), 0));
    assert_norm (K.core_rule lemma_node /\
                 K.judgment_scoped [bool_sort] lemma_node.conclusion /\ K.facts_scoped [bool_sort] lemma_node.premises /\
                 not (K.judgment_scoped [] lemma_node.conclusion) /\
                 not (K.judgment_scoped [int_s; bool_sort] lemma_node.conclusion))

let rho_int : env value = fun _ -> VInt 0
let rho_mixed : env value = fun n -> if n = 0 then VInt 0 else VBool true

let untyped_countermodel ()
  : Lemma (CO.core_model (CO.witness (fun _ _ -> 0)) CO.witness_domains /\
           premises_sound (CO.witness (fun _ _ -> 0)) rho_int lemma_node.premises /\
           ~(lit_true (CO.witness (fun _ _ -> 0)) rho_int (mk_not_expr vb)) /\
           ~(CO.env_typed CO.witness_domains [bool_sort] rho_int))
  = CO.lemma_witness (fun _ _ -> 0);
    assert_norm (premises_sound (CO.witness (fun _ _ -> 0)) rho_int lemma_node.premises);
    assert_norm (~(lit_true (CO.witness (fun _ _ -> 0)) rho_int (mk_not_expr vb)));
    assert_norm (SM.fits bool_sort (VInt 0) == false);
    let nt () : Lemma (requires CO.env_typed CO.witness_domains [bool_sort] rho_int) (ensures False)
      = assert (CO.witness_domains (L.index [bool_sort] 0) (rho_int 0)) in
    FStar.Classical.move_requires nt ()

let swapped_countermodel ()
  : Lemma (CO.env_typed CO.witness_domains [int_s; bool_sort] rho_mixed /\
           premises_sound (CO.witness (fun _ _ -> 0)) rho_mixed lemma_node.premises /\
           ~(lit_true (CO.witness (fun _ _ -> 0)) rho_mixed (mk_not_expr vb)))
  = assert_norm (SM.fits int_s (VInt 0) == true /\ SM.fits bool_sort (VBool true) == true);
    let aux (n:nat)
      : Lemma (n < L.length [int_s; bool_sort] ==> CO.witness_domains (L.index [int_s; bool_sort] n) (rho_mixed n))
      = () in
    FStar.Classical.forall_intro aux;
    assert_norm (premises_sound (CO.witness (fun _ _ -> 0)) rho_mixed lemma_node.premises);
    assert_norm (~(lit_true (CO.witness (fun _ _ -> 0)) rho_mixed (mk_not_expr vb)))

(* --- Bounded bit-vector steps: `Some` is not a check, `core_rule` is ---------- *)

let bv2 : sort = BV.bv_sort 2
let u : expr = App { decl_name = "u"; domain = []; range = bv2; interp = None; int_params = [] } []
let ult2 (a b:expr) : expr =
  App { decl_name = "bvult"; domain = [bv2; bv2]; range = bool_sort; interp = Some BV.op_ult; int_params = [2] } [a; b]
let bv_taut : expr = App (C.or_decl 2) [ult2 u (BV.literal 2 2); mk_not_expr (ult2 u (BV.literal 2 2))]
let bv_lemma_node : proof_node = { kind = Unverified "th-lemma"; conclusion = Holds bv_taut; premises = [] }
let bv_rewrite_node : proof_node =
  { kind = RewriteRule; conclusion = Equal (BV.binary 2 BV.op_add u (BV.literal 2 0)) u; premises = [] }
(* A contingent equation: the kernel returns `Some` for it, with a pending
   obligation, but it is not a core rule. *)
let bv_bad_node : proof_node = { kind = Unverified "th-lemma"; conclusion = Equal u (BV.literal 2 1); premises = [] }

let bv_core ()
  : Lemma (K.core_rule bv_lemma_node /\ K.judgment_scoped [] bv_lemma_node.conclusion /\
           K.core_rule bv_rewrite_node /\ K.judgment_scoped [] bv_rewrite_node.conclusion /\
           not (K.core_rule bv_bad_node))
  = assert_norm (K.core_rule bv_lemma_node /\ K.judgment_scoped [] bv_lemma_node.conclusion);
    assert_norm (K.core_rule bv_rewrite_node /\ K.judgment_scoped [] bv_rewrite_node.conclusion);
    assert_norm (not (K.core_rule bv_bad_node))

let bv_some ()
  : Lemma (Some? (check_node_with_context [] false [] bv_lemma_node) /\
           Some? (check_node_with_context [] false [] bv_rewrite_node) /\
           Some? (check_node_with_context [] false [] bv_bad_node))
  = assert_norm (well_formed bv_lemma_node.conclusion /\ well_formed bv_rewrite_node.conclusion /\
                 well_formed bv_bad_node.conclusion)

let bv_sound (i:interpretation value) (dom:CO.domains) (rho:env value)
  : Lemma (requires CO.core_model i dom)
          (ensures lit_true i rho bv_taut /\ eval i (BV.binary 2 BV.op_add u (BV.literal 2 0)) rho == eval i u rho)
  = bv_core (); bv_some (); CO.lemma_env_closed dom rho;
    K.lemma_core_check_node_sound [] i dom [] rho false [] bv_lemma_node;
    K.lemma_core_check_node_sound [] i dom [] rho false [] bv_rewrite_node

let bv_bad_countermodel (rho:env value)
  : Lemma (CO.core_model (CO.witness (fun _ _ -> 0)) CO.witness_domains /\
           ~(eval (CO.witness (fun _ _ -> 0)) u rho == eval (CO.witness (fun _ _ -> 0)) (BV.literal 2 1) rho))
  = CO.lemma_witness (fun _ _ -> 0);
    assert_norm (~(eval (CO.witness (fun _ _ -> 0)) u rho == eval (CO.witness (fun _ _ -> 0)) (BV.literal 2 1) rho))

(* --- Canonical dispatch in the kernel ---------------------------------------- *)

(* The same shapes over a declaration that only carries the connective's name
   are rejected by the migrated kernel; the earlier name-keyed kernel accepted them. *)
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

(* Discharging a hypothesis needs a canonical complement: over a look-alike
   `not` the lemma rule is still accepted, but it keeps the look-alike term as
   a hypothesis instead of discharging it, which is sound. *)
let fake_lemma_node : proof_node =
  { kind = LemmaRule; conclusion = Holds p; premises = [hfact (Holds false_expr) [App fake_not [p]]] }

let fake_lemma_kept ()
  : Lemma (check_node_with_context [] false [] fake_lemma_node == Some (hfact (Holds p) [App fake_not [p]], 0))
  = assert_norm (check_node_with_context [] false [] fake_lemma_node == Some (hfact (Holds p) [App fake_not [p]], 0))

(* --- Obstructions of the legacy global contract, as finite clause instances --- *)

(* O1. Three closed clause instances at the well-sorted term (store a 0 1/2)
   with a : (Array Int Real) are jointly unsatisfiable (`o1_clash`):
   S, the store clause of `Z3ArrayLemma.array_model`, which asks for a `VInt`
   element; N, the numeral clause of `Z3LinearArithmeticEmbed.numeric_operators`
   at 1/2; I, its clause `nu (VInt n) = n`. Every two of them are satisfiable
   (`drop_s`, `drop_n`, `drop_i`). No open term or environment is involved, so
   typed environments cannot repair it: `array_model` has to be restricted to
   Int-represented element sorts or the array value domain generalized.
   (`array_model` and `numeric_model` are also each refuted on their own over
   open terms, `Z3ScopedModelTests`, so a contract-level contradiction from
   them would not be separate evidence.) *)
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

let s_inst (i:interpretation value) (rho:env value) : prop =
  match eval i array_constant rho, eval i (int_numeral 0) rho, eval i half rho with
  | VArr av, VInt kv, VInt vv -> eval i real_store rho == VArr (AT.store av kv vv)
  | _, _, _ -> False
let n_inst (i:interpretation value) (nu:value -> real) (rho:env value) : prop =
  of_int 2 *. nu (eval i half rho) == of_int 1
let i_inst (nu:value -> real) : prop = forall (n:int). nu (VInt n) == of_int n

let o1_clash (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires s_inst i rho /\ n_inst i nu rho /\ i_inst nu) (ensures False)
  = match eval i half rho with
    | VInt n -> assert (nu (VInt n) == of_int n)
    | _ -> ()

(* The instances are consequences of the legacy conjuncts they are named after. *)
let o1_closed ()
  : Lemma (D.scoped [] real_store /\ A.store_parts real_store == Some (array_constant, int_numeral 0, half) /\
           A.scalar_sort real_s /\ LA.numeral half == Some (1, 2))
  = assert_norm (D.scoped [] real_store /\ A.store_parts real_store == Some (array_constant, int_numeral 0, half) /\
                 A.scalar_sort real_s /\ LA.numeral half == Some (1, 2))

let s_from_array_model (i:interpretation value) (rho:env value)
  : Lemma (requires A.array_model i) (ensures s_inst i rho)
  = o1_closed ();
    A.lemma_store_parts i rho real_store array_constant (int_numeral 0) half

let ni_from_numeric_operators (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires LE.numeric_operators i nu) (ensures n_inst i nu rho /\ i_inst nu)
  = o1_closed ();
    assert (of_int 2 *. nu (eval i half rho) == of_int 1)

let i_false : interpretation value =
  { interp_app = (fun _ _ -> VBool false); uninterp_app = (fun _ _ -> VBool false);
    interp_quant = (fun _ _ _ -> VBool false) }
let nu_half : value -> real = fun v -> match v with VInt n -> of_int n | _ -> of_int 1 /. of_int 2
let i_store : interpretation value =
  { interp_app = (fun f vs -> if f.interp = Some op_store
                              then (match vs with [VArr av; VInt k; VInt v] -> VArr (AT.store av k v) | _ -> VInt 0)
                              else VInt 0);
    uninterp_app = (fun _ _ -> VArr (AT.const_arr 0));
    interp_quant = (fun _ _ _ -> VBool false) }
let nu_int : value -> real = fun v -> match v with VInt n -> of_int n | _ -> of_int 0
let nu_bad : value -> real = fun v -> match v with VInt n -> if n = 0 then of_int 1 /. of_int 2 else of_int n | _ -> of_int 0

let drop_s (rho:env value) : Lemma (n_inst i_false nu_half rho /\ i_inst nu_half /\ ~(s_inst i_false rho))
  = assert_norm (eval i_false half rho == VBool false);
    assert_norm (~(s_inst i_false rho))

let drop_n (rho:env value) : Lemma (s_inst i_store rho /\ i_inst nu_int /\ ~(n_inst i_store nu_int rho))
  = assert_norm (eval i_store half rho == VInt 0);
    assert_norm (s_inst i_store rho)

let drop_i (rho:env value) : Lemma (s_inst i_store rho /\ n_inst i_store nu_bad rho /\ ~(i_inst nu_bad))
  = assert_norm (eval i_store half rho == VInt 0);
    assert_norm (s_inst i_store rho);
    assert (~(nu_bad (VInt 0) == of_int 0))

(* O2. The quantifier contract reads bodies under untyped value lists. Three
   clause instances make the valid closed formula forall x:Int. x + 0 = x
   false (`o2_unfaithful`): Q, the `Z3QuantifierNnf.quantifier_model` clause
   at the ill-typed list [true]; A, the `arithmetic_model` clause at x + 0;
   E, the untyped `eq_sound` clause at the body. Dropping any one leaves the
   formula true in a model of the other two (`drop_q`, `drop_a`, `drop_e`), and
   the typed restriction of Q holds in a witness core model (`typed_q`). This
   does not show that these three contracts have a model; it shows that every
   model of them, if one exists, falsifies this valid formula. *)
let plus_decl : func_decl =
  { decl_name = "+"; domain = [int_s; int_s]; range = int_s; interp = Some op_plus; int_params = [] }
let plus_x0 : expr = App plus_decl [Var 0 int_s; int_numeral 0]
let body : expr = mk_eq_expr plus_x0 (Var 0 int_s)
let valid_forall : expr = Quantifier Forall_k [int_s] bool_sort body
let sigma (rho:env value) : env value = shift [VBool true] rho

let q_inst (i:interpretation value) (rho:env value) : prop =
  lit_true i rho valid_forall ==> lit_true i (sigma rho) body
let a_inst (i:interpretation value) (rho:env value) : prop =
  eval i plus_x0 (sigma rho) ==
    (match eval i (Var 0 int_s) (sigma rho), eval i (int_numeral 0) (sigma rho) with
     | VInt a, VInt b -> VInt (a + b) | _, _ -> VInt 0)
let e_inst (i:interpretation value) (rho:env value) : prop =
  (eval i body (sigma rho) == VBool true <==> eval i plus_x0 (sigma rho) == eval i (Var 0 int_s) (sigma rho))

let o2_unfaithful (i:interpretation value) (rho:env value)
  : Lemma (requires q_inst i rho /\ a_inst i rho /\ e_inst i rho) (ensures ~(lit_true i rho valid_forall))
  = assert (eval i (Var 0 int_s) (sigma rho) == VBool true)

let o2_closed () : Lemma (D.scoped [] valid_forall /\ get_sort body == bool_sort /\ CM.arithmetic_decl plus_decl)
  = assert_norm (D.scoped [] valid_forall /\ get_sort body == bool_sort /\ CM.arithmetic_decl plus_decl)

let q_from_quantifier_model (i:interpretation value) (rho:env value)
  : Lemma (requires QN.quantifier_model i) (ensures q_inst i rho)
  = o2_closed ();
    QN.lemma_quantifier_truth i rho Forall_k [int_s] body;
    assert (L.length [VBool true] = L.length [int_s])

let a_from_arithmetic_model (i:interpretation value) (rho:env value)
  : Lemma (requires CM.arithmetic_model i) (ensures a_inst i rho)
  = o2_closed ()

let e_from_eq_sound (i:interpretation value) (rho:env value)
  : Lemma (requires eq_sound i) (ensures e_inst i rho)
  = assert_norm (body == App (eq_decl int_s) [plus_x0; Var 0 int_s]);
    assert (C.canonical_eq (eq_decl int_s) /\ (eq_decl int_s).decl_name == "=")

let w0 : interpretation value = CO.witness (fun _ _ -> 0)

let drop_q (rho:env value)
  : Lemma (lit_true w0 rho valid_forall /\ a_inst w0 rho /\ e_inst w0 rho /\ ~(q_inst w0 rho))
  = assert_norm (lit_true w0 rho valid_forall);
    assert_norm (eval w0 plus_x0 (sigma rho) == VInt 0);
    assert_norm (eval w0 (Var 0 int_s) (sigma rho) == VBool true);
    assert_norm (eval w0 (int_numeral 0) (sigma rho) == VInt 0);
    assert_norm (eval w0 body (sigma rho) == VBool false)

let typed_q (rho:env value) (n:int)
  : Lemma (CO.args_typed CO.witness_domains [int_s] [VInt n] /\ lit_true w0 (shift [VInt n] rho) body)
  = assert_norm (SM.fits int_s (VInt n) == true);
    assert_norm (lit_true w0 (shift [VInt n] rho) body)

let i_plus_first : interpretation value =
  { w0 with interp_app = (fun f vs -> if f = plus_decl then (match vs with [v; _] -> v | _ -> VInt 0) else w0.interp_app f vs) }
let i_eq_true : interpretation value =
  { w0 with interp_app = (fun f vs -> if f.decl_name = "=" then VBool true else w0.interp_app f vs) }

let drop_a (rho:env value)
  : Lemma (lit_true i_plus_first rho valid_forall /\ q_inst i_plus_first rho /\ e_inst i_plus_first rho /\
           ~(a_inst i_plus_first rho))
  = assert_norm (lit_true i_plus_first rho valid_forall);
    assert_norm (eval i_plus_first plus_x0 (sigma rho) == VBool true);
    assert_norm (eval i_plus_first (Var 0 int_s) (sigma rho) == VBool true);
    assert_norm (eval i_plus_first (int_numeral 0) (sigma rho) == VInt 0);
    assert_norm (eval i_plus_first body (sigma rho) == VBool true)

let drop_e (rho:env value)
  : Lemma (lit_true i_eq_true rho valid_forall /\ q_inst i_eq_true rho /\ a_inst i_eq_true rho /\
           ~(e_inst i_eq_true rho))
  = assert_norm (lit_true i_eq_true rho valid_forall);
    assert_norm (eval i_eq_true plus_x0 (sigma rho) == VInt 0);
    assert_norm (eval i_eq_true (Var 0 int_s) (sigma rho) == VBool true);
    assert_norm (eval i_eq_true (int_numeral 0) (sigma rho) == VInt 0);
    assert_norm (eval i_eq_true body (sigma rho) == VBool true)

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
