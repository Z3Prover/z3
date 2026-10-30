(*
   Z3CoreKernel.fst

   Kernel soundness for the Boolean, equality and congruence rules of
   `Z3UnifiedProof`, proved from the inhabited typed canonical contract
   `Z3CoreModel.core_model` instead of the uninhabited `model_sound`.

   `lemma_core_check_node_sound` is about the kernel's own acceptance
   function `check_node_with_context`. For every node for which it
   returns `Some` and whose rule is a core rule (`core_rule`), the
   returned checked fact holds in every model of `core_model`, under every
   environment typed for a scope the node's judgments and premises are
   scoped in, given that its premises and the assertions hold there. The
   proof uses no `model_sound` conjunct, so it is not vacuous:
   `Z3CoreModel.lemma_core_inhabited` gives a model, and
   `Z3CoreModelTests` checks accepted nodes against it.

   `Some` is not "zero obligations": for a theory-lemma or rewrite node
   (which may also have premises) the kernel can return `Some` with a
   pending obligation, including for a false conclusion. The guarantee
   for those nodes comes from `core_rule`, which requires the bounded
   bit-vector evaluator itself to decide the conclusion; the theorem
   ignores the obligation count. It is a theorem about one node, not
   about a proof DAG or a document.

   Core rules: assertion, hypothesis, lemma (hypothesis discharge),
   reflexivity, symmetry, transitivity, transitivity path, congruence,
   commutativity, `iff~`, `mp`, `mp~`, unit resolution, and-elimination,
   not-or-elimination, iff-true, iff-false, a theory lemma decided by the
   bounded bit-vector evaluator (`Z3BvExhaustive.valid`) and a rewrite
   decided by it (`Z3BvExhaustive.equivalent`).

   NOT covered: quantifier and binder rules, definitions and their
   axioms, the other rewrite and theory-lemma checkers (arrays,
   arithmetic, datatypes, finite fields, normalization), Skolemization
   and the document layer. Those still rest on `model_sound`, which has
   no model. The exceptions are quantifier instantiation and a fragment of
   quantifier introduction: `Z3QuantifierKernel` proves checked
   instantiation nodes sound from the inhabited
   `Z3TypedQuantifier.quantifier_model` (the core contracts, typed
   quantifiers and quantifier extensionality) and extends this theorem to
   them (`lemma_typed_check_node_sound`); `Z3BinderKernel` does the same
   for introduction nodes whose certificates contain only closed inputs,
   core rules and exact forall/exists introductions. No F* lemma connects
   document entries to scope `[]`: for documents whose expression table is
   ground, `Z3ProofDocument` does not check entry scope and relies on the
   native side listing every subexpression in the table.
*)
module Z3CoreKernel

open Z3AstTheory
open Z3ValueTheory
open Z3ProofTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
open Z3UnifiedProof
module CO = Z3CoreModel
module C = Z3CanonicalOps
module D = Z3Definitions
module CM = Z3Commutativity
module DV = Z3DatatypeValue
module SM = Z3StandardModel
module BE = Z3BvExhaustive
module SK = Z3Skolemization
module L = FStar.List.Tot

(* --- Scoped judgments ---------------------------------------------------- *)

let judgment_scoped (scope:list sort) (j:judgment) : bool =
  match j with
  | Holds e -> D.scoped scope e
  | Equal a b | Observational a b -> D.scoped scope a && D.scoped scope b

let rec judgments_scoped (scope:list sort) (js:list judgment) : Tot bool (decreases js) =
  match js with
  | [] -> true
  | j :: rest -> judgment_scoped scope j && judgments_scoped scope rest

let rec facts_scoped (scope:list sort) (ps:list checked_fact) : Tot bool (decreases ps) =
  match ps with
  | [] -> true
  | p :: rest -> judgment_scoped scope p.conclusion && D.scoped_args scope p.hypotheses &&
                 facts_scoped scope rest

let rec lemma_scoped_member (scope:list sort) (es:list expr) (e:expr)
  : Lemma (requires D.scoped_args scope es /\ L.memP e es) (ensures D.scoped scope e) (decreases es)
  = match es with
    | x :: rest -> FStar.Classical.or_elim #(x == e) #(L.memP e rest) #(fun _ -> D.scoped scope e)
                     (fun _ -> ()) (fun _ -> lemma_scoped_member scope rest e)

let rec lemma_boolean_member (es:list expr) (e:expr)
  : Lemma (requires boolean_formulas es /\ L.memP e es) (ensures get_sort e == bool_sort) (decreases es)
  = match es with
    | x :: rest -> FStar.Classical.or_elim #(x == e) #(L.memP e rest) #(fun _ -> get_sort e == bool_sort)
                     (fun _ -> ()) (fun _ -> lemma_boolean_member rest e)

let lemma_formula_clause_scoped (scope:list sort) (e:expr)
  : Lemma (requires D.scoped scope e) (ensures D.scoped_args scope (formula_clause e))
  = match e with App _ _ -> () | _ -> ()

let rec lemma_premise_judgments_scoped (scope:list sort) (ps:list checked_fact)
  : Lemma (requires facts_scoped scope ps) (ensures judgments_scoped scope (premise_judgments ps))
          (decreases ps)
  = match ps with
    | [] -> ()
    | _ :: rest -> lemma_premise_judgments_scoped scope rest

let rec lemma_add_hypotheses_scoped (scope:list sort) (xs ys:list expr)
  : Lemma (requires D.scoped_args scope xs /\ D.scoped_args scope ys)
          (ensures D.scoped_args scope (add_hypotheses xs ys)) (decreases xs)
  = match xs with
    | [] -> ()
    | x :: rest -> if L.mem x ys then lemma_add_hypotheses_scoped scope rest ys
                   else lemma_add_hypotheses_scoped scope rest (x :: ys)

let rec lemma_premise_hypotheses_scoped (scope:list sort) (ps:list checked_fact)
  : Lemma (requires facts_scoped scope ps) (ensures D.scoped_args scope (premise_hypotheses ps))
          (decreases ps)
  = match ps with
    | [] -> ()
    | p :: rest ->
      lemma_premise_hypotheses_scoped scope rest;
      lemma_add_hypotheses_scoped scope p.hypotheses (premise_hypotheses rest)

(* The context every core theorem is stated in. *)
let context (i:interpretation value) (dom:CO.domains) (scope:list sort) (rho:env value) : prop =
  CO.core_model i dom /\ CO.env_typed dom scope rho

(* --- Propositions -------------------------------------------------------- *)

let lemma_proposition (i:interpretation value) (dom:CO.domains) (scope:list sort) (rho:env value)
                      (j:judgment)
  : Lemma (requires context i dom scope rho /\ well_formed j /\ judgment_scoped scope j /\
                    Some? (proposition j))
          (ensures D.scoped scope (Some?.v (proposition j)) /\
                   (judgment_holds i rho j <==> lit_true i rho (Some?.v (proposition j))))
  = match j with
    | Holds _ -> ()
    | Equal a b -> CO.lemma_eq_scoped scope a b; CO.lemma_eq_expr i dom scope a b rho

let rec lemma_propositions (i:interpretation value) (dom:CO.domains) (scope:list sort) (rho:env value)
                           (js:list judgment)
  : Lemma (requires context i dom scope rho /\ judgments_wf js /\ judgments_scoped scope js /\
                    Some? (propositions js) /\ judgments_hold i rho js)
          (ensures D.scoped_args scope (Some?.v (propositions js)) /\
                   conj_holds i rho (Some?.v (propositions js)))
          (decreases js)
  = match js with
    | [] -> ()
    | j :: rest -> lemma_proposition i dom scope rho j; lemma_propositions i dom scope rho rest

(* --- Relational rules ------------------------------------------------------ *)

let lemma_edge_values (i:interpretation value) (dom:CO.domains) (scope:list sort) (rho:env value)
                      (r:relation) (j:judgment) (a b:expr)
  : Lemma (requires context i dom scope rho /\ well_formed j /\ judgment_scoped scope j /\
                    judgment_holds i rho j /\ edge r j = Some (a, b))
          (ensures eval i a rho == eval i b rho)
  = lemma_edge_sound i rho r j a b;
    match r with
    | Equality -> ()
    | Observation ->
      assert (D.scoped scope a /\ D.scoped scope b);
      if get_sort a = bool_sort then (
        CO.lemma_typed_bool i dom scope a rho;
        CO.lemma_typed_bool i dom scope b rho;
        match eval i a rho, eval i b rho with VBool _, VBool _ -> () | _, _ -> ())

let rec lemma_matching (i:interpretation value) (dom:CO.domains) (scope:list sort) (rho:env value)
                       (r:relation) (a b:expr) (js:list judgment)
  : Lemma (requires context i dom scope rho /\ judgments_wf js /\ judgments_scoped scope js /\
                    judgments_hold i rho js /\ matching r a b js)
          (ensures eval i a rho == eval i b rho)
          (decreases js)
  = match js with
    | [] -> ()
    | j :: rest ->
      if edge r j = Some (a, b) then lemma_edge_values i dom scope rho r j a b
      else lemma_matching i dom scope rho r a b rest

let rec lemma_arguments (i:interpretation value) (dom:CO.domains) (scope:list sort) (rho:env value)
                        (r:relation) (xs ys:list expr) (js:list judgment)
  : Lemma (requires context i dom scope rho /\ judgments_wf js /\ judgments_scoped scope js /\
                    judgments_hold i rho js /\ arguments_match r xs ys js)
          (ensures eval_args i xs rho == eval_args i ys rho)
          (decreases xs)
  = match xs, ys with
    | [], [] -> ()
    | x :: xs', y :: ys' ->
      (if x = y then () else lemma_matching i dom scope rho r x y js);
      lemma_arguments i dom scope rho r xs' ys' js

let lemma_bool_values (i:interpretation value) (dom:CO.domains) (scope:list sort) (rho:env value)
                      (a b:expr)
  : Lemma (requires context i dom scope rho /\ D.scoped scope a /\ D.scoped scope b /\
                    get_sort a == bool_sort /\ get_sort b == bool_sort /\
                    (lit_true i rho a <==> lit_true i rho b))
          (ensures eval i a rho == eval i b rho)
  = CO.lemma_typed_bool i dom scope a rho;
    CO.lemma_typed_bool i dom scope b rho;
    match eval i a rho, eval i b rho with VBool _, VBool _ -> () | _, _ -> ()

let lemma_commutativity (i:interpretation value) (dom:CO.domains) (scope:list sort) (rho:env value)
                        (a b:expr)
  : Lemma (requires context i dom scope rho /\ D.scoped scope a /\ D.scoped scope b /\
                    CM.commutativity_step a b)
          (ensures eval i a rho == eval i b rho)
  = match a, b with
    | App f [x; y], App g [u; v] ->
      if CM.arithmetic_decl f then CM.lemma_arithmetic_commutativity i rho f x y
      else if C.canonical_eq f then (
        CO.lemma_equality i dom scope f x y rho;
        CO.lemma_equality i dom scope f y x rho;
        lemma_bool_values i dom scope rho a b)
      else (
        assert (C.canonical_and f \/ C.canonical_or f);
        lemma_bool_values i dom scope rho a b)
    | _, _ -> ()

let core_relational (kind:rule) : bool =
  match kind with
  | Reflexivity | Symmetry | Transitivity | TransitivityPath | Congruence | Commutativity
  | IffObservational -> true
  | _ -> false

let lemma_relational_step (i:interpretation value) (dom:CO.domains) (scope:list sort) (rho:env value)
                          (kind:rule) (concl:judgment) (facts:list judgment)
  : Lemma (requires context i dom scope rho /\ well_formed concl /\ judgment_scoped scope concl /\
                    judgments_wf facts /\ judgments_scoped scope facts /\ judgments_hold i rho facts /\
                    core_relational kind /\ relational_step kind concl facts)
          (ensures judgment_holds i rho concl)
  = match relational concl with
    | None -> ()
    | Some (r, a, b) ->
      (match kind with
       | Commutativity ->
         lemma_commutativity i dom scope rho a b;
         lemma_relational_value_sound i rho concl r a b
       | Transitivity ->
         (match facts with
          | [p; q] ->
            (match edge r p, edge r q with
             | Some (s, t), Some (u, v) ->
               lemma_edge_sound i rho r p s t;
               lemma_edge_sound i rho r q u v
             | _, _ -> ())
          | _ -> ())
       | TransitivityPath ->
         assert (reachable_sound i rho r a [a]);
         lemma_reachable_sound i rho (L.length facts) r a facts [a];
         FStar.List.Tot.Properties.mem_memP b (reachable (L.length facts) r facts [a])
       | Congruence ->
         if a = b then () else (match a, b with
          | App f xs, App g ys ->
            lemma_fast_arguments_match r xs ys facts;
            lemma_arguments i dom scope rho r xs ys facts;
            lemma_relational_value_sound i rho concl r a b
          | _, _ -> ())
       | _ -> ())

(* --- Logical rules ------------------------------------------------------- *)

let rec lemma_boolean_clause (i:interpretation value) (dom:CO.domains) (scope:list sort) (rho:env value)
                             (es:list expr)
  : Lemma (requires context i dom scope rho /\ boolean_formulas es /\ D.scoped_args scope es)
          (ensures wf_clause i rho es)
          (decreases es)
  = match es with
    | [] -> ()
    | e :: rest ->
      CO.lemma_typed_bool i dom scope e rho;
      lemma_boolean_clause i dom scope rho rest

let core_logical (kind:rule) : bool =
  match kind with
  | ObservationalMP | ModusPonens | UnitResolution | AndElimination | NotOrElimination
  | IffTrue | IffFalse -> true
  | _ -> false

let lemma_not_or (i:interpretation value) (dom:CO.domains) (scope:list sort) (rho:env value)
                 (f g:func_decl) (args:list expr) (target:expr)
  : Lemma (requires context i dom scope rho /\ C.canonical_not f /\ C.canonical_or g /\
                    D.scoped scope (App f [App g args]) /\ lit_true i rho (App f [App g args]) /\
                    D.scoped scope target /\ get_sort target == bool_sort /\
                    (L.mem (mk_not_expr target) args \/
                     (match is_not target with
                      | Some t -> get_sort t = bool_sort && L.mem t args && target = App f [t]
                      | None -> false)))
          (ensures lit_true i rho target)
  = assert (eval i (App g args) rho == VBool false);
    assert (~(clause_holds i rho args));
    assert (D.scoped_args scope args);
    CO.lemma_typed_bool i dom scope target rho;
    if L.mem (mk_not_expr target) args then (
      FStar.List.Tot.Properties.mem_memP (mk_not_expr target) args;
      lemma_scoped_member scope args (mk_not_expr target);
      CO.lemma_typed_bool i dom scope (mk_not_expr target) rho;
      lemma_not_or_elim_sound i rho args (mk_not_expr target))
    else (match is_not target with
          | Some t ->
            FStar.List.Tot.Properties.mem_memP t args;
            lemma_scoped_member scope args t;
            CO.lemma_typed_bool i dom scope t rho;
            lemma_not_or_elim_sound i rho args t
          | None -> ())

(* Unit resolution: the clause's literals are Boolean and scoped, every unit holds. *)
let lemma_unit_resolution (i:interpretation value) (dom:CO.domains) (scope:list sort) (rho:env value)
                          (c:expr) (units:list expr) (target:expr)
  : Lemma (requires context i dom scope rho /\ D.scoped scope c /\ lit_true i rho c /\
                    conj_holds i rho units /\ boolean_formulas (formula_clause c) /\
                    clause_consequence (resolution_residual c units) target)
          (ensures lit_true i rho target)
  = lemma_formula_clause_scoped scope c;
    lemma_boolean_clause i dom scope rho (formula_clause c);
    let unit_sound (e:expr)
      : Lemma (requires L.memP e units) (ensures lit_true i rho e)
      = lemma_conj_member i rho units e in
    FStar.Classical.forall_intro (FStar.Classical.move_requires unit_sound);
    lemma_resolution_residual_sound i rho c units;
    lemma_clause_consequence i rho (resolution_residual c units) target

let lemma_propositional_step (i:interpretation value) (dom:CO.domains) (scope:list sort) (rho:env value)
                             (kind:rule) (es:list expr) (target:expr)
  : Lemma (requires context i dom scope rho /\ D.scoped_args scope es /\ conj_holds i rho es /\
                    D.scoped scope target /\ get_sort target == bool_sort /\
                    (match kind, es with
                     | ModusPonens, [a; App f [s; t]] ->
                       (C.canonical_implies f || C.canonical_eq f) && a = s && target = t
                     | UnitResolution, c :: units ->
                       boolean_formulas (formula_clause c) &&
                       clause_consequence (resolution_residual c units) target
                     | AndElimination, [App f args] -> C.canonical_and f && L.mem target args
                     | NotOrElimination, [App f [App g args]] ->
                       C.canonical_not f && C.canonical_or g &&
                       (L.mem (mk_not_expr target) args ||
                        (match is_not target with
                         | Some t -> get_sort t = bool_sort && L.mem t args && target = App f [t]
                         | None -> false))
                     | IffTrue, [a] -> target = mk_iff_expr a true_expr
                     | IffFalse, [n] ->
                       (match is_not n with Some a -> target = mk_iff_expr a false_expr | None -> false)
                     | _, _ -> false))
          (ensures lit_true i rho target)
  = match kind, es with
    | ModusPonens, [a; App f [s; t]] ->
      if C.canonical_implies f then ()
      else CO.lemma_equality i dom scope f s t rho
    | UnitResolution, c :: units -> lemma_unit_resolution i dom scope rho c units target
    | AndElimination, [App f args] ->
      FStar.List.Tot.Properties.mem_memP target args;
      lemma_and_elim_sound i rho args target
    | NotOrElimination, [App f [App g args]] -> lemma_not_or i dom scope rho f g args target
    | IffTrue, [a] -> CO.lemma_equality i dom scope (eq_decl bool_sort) a true_expr rho
    | IffFalse, [n] ->
      (match is_not n with
       | Some a -> CO.lemma_equality i dom scope (eq_decl bool_sort) a false_expr rho
       | None -> ())
    | _, _ -> ()

let lemma_logical_step (i:interpretation value) (dom:CO.domains) (scope:list sort) (rho:env value)
                       (kind:rule) (concl:judgment) (facts:list judgment)
  : Lemma (requires context i dom scope rho /\ well_formed concl /\ judgment_scoped scope concl /\
                    judgments_wf facts /\ judgments_scoped scope facts /\ judgments_hold i rho facts /\
                    core_logical kind /\ logical_step kind concl facts)
          (ensures judgment_holds i rho concl)
  = lemma_proposition i dom scope rho concl;
    match kind with
    | ObservationalMP ->
      (match facts with
       | [j; Observational a b] ->
         lemma_proposition i dom scope rho j;
         lemma_mp_oeq_sound i rho a b
       | _ -> ())
    | _ ->
      lemma_propositions i dom scope rho facts;
      lemma_propositional_step i dom scope rho kind (Some?.v (propositions facts))
        (Some?.v (proposition concl))

(* --- Hypothesis discharge (PR_LEMMA) ----------------------------------------- *)

let lemma_complement_from_false (i:interpretation value) (dom:CO.domains) (scope:list sort)
                                (rho:env value) (h e:expr)
  : Lemma (requires context i dom scope rho /\ D.scoped scope h /\ D.scoped scope e /\
                    get_sort h == bool_sort /\ get_sort e == bool_sort /\
                    complementary h e /\ ~(lit_true i rho e))
          (ensures lit_true i rho h)
  = CO.lemma_typed_bool i dom scope h rho;
    CO.lemma_typed_bool i dom scope e rho;
    match h with
    | App f [] -> (match e with | App g [] -> () | _ -> ())
    | App f [a] ->
      if C.canonical_not f && a = e then lemma_canonical_not_relates i rho f a
      else (match e with
            | App g [b] -> if C.canonical_not g && b = h then lemma_canonical_not_relates i rho g b
            | _ -> ())
    | _ ->
      (match e with
       | App g [b] -> if C.canonical_not g && b = h then lemma_canonical_not_relates i rho g b
       | _ -> ())

let rec lemma_discharged (i:interpretation value) (dom:CO.domains) (scope:list sort) (rho:env value)
                         (h:expr) (es:list expr)
  : Lemma (requires context i dom scope rho /\ D.scoped scope h /\ get_sort h == bool_sort /\
                    boolean_formulas es /\ D.scoped_args scope es /\ discharged h es /\
                    ~(clause_holds i rho es))
          (ensures lit_true i rho h)
          (decreases es)
  = match es with
    | [] -> ()
    | e :: rest ->
      if complementary h e then lemma_complement_from_false i dom scope rho h e
      else lemma_discharged i dom scope rho h rest

let lemma_formula_clause_false (i:interpretation value) (rho:env value) (e:expr)
  : Lemma (requires canonical_or_sound i /\ ~(lit_true i rho e))
          (ensures ~(clause_holds i rho (formula_clause e)))
  = match e with
    | App f args -> ()
    | _ -> ()

let rec lemma_remaining_hypotheses (i:interpretation value) (dom:CO.domains) (scope:list sort)
                                   (rho:env value) (hyps:list expr) (concl:expr)
  : Lemma (requires context i dom scope rho /\ boolean_formulas hyps /\ D.scoped_args scope hyps /\
                    get_sort concl == bool_sort /\ D.scoped scope concl /\
                    boolean_formulas (formula_clause concl) /\
                    conj_holds i rho (remaining_hypotheses hyps concl) /\ ~(lit_true i rho concl))
          (ensures conj_holds i rho hyps)
          (decreases hyps)
  = match hyps with
    | [] -> ()
    | h :: rest ->
      (if complementary h concl then lemma_complement_from_false i dom scope rho h concl
       else if discharged h (formula_clause concl) then (
         lemma_formula_clause_scoped scope concl;
         lemma_formula_clause_false i rho concl;
         lemma_discharged i dom scope rho h (formula_clause concl))
       else ());
      lemma_remaining_hypotheses i dom scope rho rest concl

(* --- Nodes ------------------------------------------------------------------ *)

(* A theory lemma or rewrite is a core node only when the bounded bit-vector
   evaluator itself decides it; the predicate is computable from the node. *)
let core_rule (node:proof_node) : bool =
  match node.kind with
  | Asserted | Hypothesis | LemmaRule
  | Reflexivity | Symmetry | Transitivity | TransitivityPath | Congruence | Commutativity
  | IffObservational | ObservationalMP | ModusPonens | UnitResolution | AndElimination
  | NotOrElimination | IffTrue | IffFalse -> true
  | Unverified tag ->
    tag = "th-lemma" &&
    (match proposition node.conclusion with Some e -> BE.valid e | None -> false)
  | RewriteRule ->
    (match relational node.conclusion with Some (_, a, b) -> BE.equivalent a b | None -> false)
  | _ -> false

let lemma_bv_theory_lemma (i:interpretation value) (dom:CO.domains) (scope:list sort) (rho:env value)
                          (concl:judgment) (e:expr)
  : Lemma (requires context i dom scope rho /\ well_formed concl /\ judgment_scoped scope concl /\
                    proposition concl == Some e /\ BE.valid e)
          (ensures judgment_holds i rho concl)
  = lemma_proposition i dom scope rho concl;
    CO.lemma_ground_model i dom;
    let valid (p:pos -> value -> int)
      : Lemma (requires SM.ground_model i p) (ensures lit_true i rho e)
      = BE.lemma_valid_ground e i p rho in
    FStar.Classical.forall_intro (FStar.Classical.move_requires valid)

let lemma_bv_rewrite (i:interpretation value) (dom:CO.domains) (rho:env value)
                     (concl:judgment) (r:relation) (a b:expr)
  : Lemma (requires CO.core_model i dom /\ well_formed concl /\ relational concl = Some (r, a, b) /\
                    BE.equivalent a b)
          (ensures judgment_holds i rho concl)
  = CO.lemma_ground_model i dom;
    let equivalent (p:pos -> value -> int)
      : Lemma (requires SM.ground_model i p) (ensures eval i a rho == eval i b rho)
      = BE.lemma_equivalent_ground a b i p rho in
    FStar.Classical.forall_intro (FStar.Classical.move_requires equivalent);
    lemma_relational_value_sound i rho concl r a b

let lemma_core_check_node_sound (skolems:list SK.definition) (i:interpretation value)
                                (dom:CO.domains) (scope:list sort) (rho:env value)
                                (strict:bool) (assertions:list judgment) (node:proof_node)
  : Lemma (requires CO.core_model i dom /\ CO.env_typed dom scope rho /\
                    judgments_hold i rho assertions /\ premises_sound i rho node.premises /\
                    judgment_scoped scope node.conclusion /\ facts_scoped scope node.premises /\
                    core_rule node /\
                    Some? (check_node_with_context skolems strict assertions node))
          (ensures scoped_holds i rho (fst (Some?.v (check_node_with_context skolems strict assertions node))))
  = let facts = premise_judgments node.premises in
    lemma_premise_judgments_scoped scope node.premises;
    lemma_premise_hypotheses_scoped scope node.premises;
    let aux (_:squash (conj_holds i rho
                       (fst (Some?.v (check_node_with_context skolems strict assertions node))).hypotheses))
      : Lemma (judgment_holds i rho node.conclusion) =
      match node.kind with
      | Asserted ->
        FStar.List.Tot.Properties.mem_memP node.conclusion assertions;
        lemma_judgment_member i rho assertions node.conclusion
      | Hypothesis -> lemma_proposition i dom scope rho node.conclusion
      | Unverified _ ->
        lemma_bv_theory_lemma i dom scope rho node.conclusion (Some?.v (proposition node.conclusion))
      | RewriteRule ->
        (match relational node.conclusion with
         | Some (r, a, b) -> lemma_bv_rewrite i dom rho node.conclusion r a b
         | None -> ())
      | LemmaRule ->
        lemma_proposition i dom scope rho node.conclusion;
        lemma_boolean_premises node.premises;
        (match proposition node.conclusion with
         | Some e ->
           FStar.Classical.excluded_middle (lit_true i rho e);
           FStar.Classical.or_elim #(lit_true i rho e) #(~(lit_true i rho e))
             #(fun () -> judgment_holds i rho node.conclusion)
             (fun _ -> ())
             (fun _ ->
               lemma_remaining_hypotheses i dom scope rho (premise_hypotheses node.premises) e;
               lemma_premises_sound i rho node.premises)
         | None -> ())
      | _ ->
        lemma_premises_sound i rho node.premises;
        if relational_step node.kind node.conclusion facts
        then lemma_relational_step i dom scope rho node.kind node.conclusion facts
        else lemma_logical_step i dom scope rho node.kind node.conclusion facts
    in FStar.Classical.impl_intro aux
