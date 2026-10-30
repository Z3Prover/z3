(*
   Z3QuantifierKernel.fst

   Kernel soundness of quantifier instantiation, proved from the inhabited
   typed quantifier contract `Z3TypedQuantifier.quantifier_model` instead of
   the uninhabited `Z3UnifiedProof.model_sound`.

   A `QuantifierInstantiation args` node concludes the instantiation clause
   `(or (not (forall bs. body)) inst)`. The kernel's executable decision is
   the existing `Z3QuantifierInstantiation.check`, unchanged: `args` are
   closed and their sorts are `bs` pointwise, the quantifier is closed, and
   `inst` is the capture-avoiding substitution of `L.rev args` into `body`
   (`Z3BinderSubstitution.substitute`).

   * `lemma_check_typed` (the typed replacement of the legacy
     `Z3QuantifierInstantiation.lemma_check_sound`): in every quantifier
     model, under every environment, an instantiation clause accepted by
     `check` is true. The proof types the EVALUATED arguments by
     `L.rev bs` (`Z3TypedQuantifier.lemma_reversed_arguments_typed`),
     eliminates the `forall` at exactly that typed list, relates the body
     there to `inst` with the existing substitution theorem
     `Z3BinderSubstitution.lemma_substitute` (which needs only
     `quant_extensional`), and closes the clause with the canonical
     `not`/`or` contracts and the core typing of `forall` (Boolean).
   * `Some` is not certification. For an instantiation node,
     `check_node_with_context` returns `Some` with pending obligation 0
     exactly when `check_step` accepts the step, and with pending 1
     otherwise, including for false conclusions
     (`lemma_instantiation_result`). The node theorems below therefore
     require pending 0, or the computable predicate `instantiation_rule`.
   * Both judgment shapes the dispatcher accepts are covered: a `Holds`
     conclusion is certified exactly when `check` accepts its formula; an
     `Equal` conclusion is never certified, since its proposition is a
     canonical `=`, not an `or` (`lemma_equal_never_checked`); an
     `Observational` conclusion is rejected (`None`).
   * `lemma_instantiation_node_sound`: the checked fact returned for an
     instantiation node with pending 0 holds in every quantifier model,
     under every environment. It has no premises and no hypotheses.
   * `lemma_typed_check_node_sound` extends `Z3CoreKernel.
     lemma_core_check_node_sound` to `typed_rule` = `core_rule` or a checked
     instantiation, under `quantifier_model` (which contains `core_model`),
     with the core theorem's own scoping, environment, assertion and premise
     hypotheses. Core nodes keep exactly their original guarantee.

   No `model_sound`, `boolean_model` or `forall_elimination_model` is used.
   The legacy lemma still requires them and remains vacuous; nothing here
   depends on it. `Z3GhostStandardModel.lemma_quantifier_model` gives a
   model; `Z3QuantifierKernelTests` checks accepted and rejected nodes
   against it.

   NOT covered: quantifier introduction and the other binder rules,
   definitions, Skolemization, lambdas, arrays beyond the core contracts,
   and the proof DAG and document layers.
*)
module Z3QuantifierKernel

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3UnifiedProof
module CO = Z3CoreModel
module TQ = Z3TypedQuantifier
module K = Z3CoreKernel
module Q = Z3QuantifierInstantiation
module S = Z3BinderSubstitution
module C = Z3CanonicalOps
module SK = Z3Skolemization
module L = FStar.List.Tot

(* --- The instantiation clause ----------------------------------------------- *)

let lemma_check_typed (i:interpretation value) (dom:CO.domains) (rho:env value)
                      (args:list expr) (formula:expr)
  : Lemma (requires TQ.quantifier_model i dom /\ Q.check args formula)
          (ensures lit_true i rho formula)
  = match formula with
    | App f [App n [Quantifier Forall_k bs s body]; inst] ->
      let q = Quantifier Forall_k bs s body in
      let vs = eval_args i (L.rev args) rho in
      TQ.lemma_reversed_arguments_typed i dom [] args bs rho;
      S.lemma_substitute i rho (L.rev args) body inst;
      assert (VBool? (eval i q rho));
      FStar.Classical.move_requires (TQ.lemma_forall_elim i dom rho bs s body) vs;
      assert (lit_true i rho q ==> lit_true i rho inst);
      assert (~(lit_true i rho q) ==> lit_true i rho (App n [q]));
      assert (clause_holds i rho [App n [q]; inst])
    | _ -> ()

(* --- What the dispatcher returns for an instantiation node ------------------- *)

let instantiation_rule (node:proof_node) : bool =
  match node.kind with
  | QuantifierInstantiation _ -> check_step node.kind node.conclusion (premise_judgments node.premises)
  | _ -> false

let lemma_premises_empty (ps:list checked_fact)
  : Lemma (premise_judgments ps == [] <==> ps == [])
  = match ps with [] -> () | _ :: _ -> ()

let lemma_instantiation_result (skolems:list SK.definition) (strict:bool)
                               (assertions:list judgment) (node:proof_node)
  : Lemma (requires QuantifierInstantiation? node.kind /\
                    Some? (check_node_with_context skolems strict assertions node))
          (ensures (let r = Some?.v (check_node_with_context skolems strict assertions node) in
                    node.premises == [] /\ Some? (proposition node.conclusion) /\
                    fst r == { conclusion = node.conclusion; hypotheses = [] } /\
                    (snd r == 0 \/ snd r == 1) /\
                    (snd r == 0 <==> instantiation_rule node)))
  = lemma_premises_empty node.premises

(* `check_step` of an instantiation is its logical step: `Q.check` of the
   conclusion's proposition. *)
let lemma_instantiation_step (args:list expr) (concl:judgment)
  : Lemma (requires check_step (QuantifierInstantiation args) concl [])
          (ensures well_formed concl /\ Some? (proposition concl) /\
                   Q.check args (Some?.v (proposition concl)))
  = ()

(* An `Equal` conclusion is never certified: its proposition is a canonical
   `=`, never the canonical `or` that `Q.check` requires. *)
let lemma_equal_never_checked (args:list expr) (a b:expr) (facts:list judgment)
  : Lemma (~(check_step (QuantifierInstantiation args) (Equal a b) facts))
  = C.lemma_canonical_exclusive (eq_decl (get_sort a))

let lemma_instantiation_step_sound (i:interpretation value) (dom:CO.domains) (rho:env value)
                                   (args:list expr) (concl:judgment)
  : Lemma (requires TQ.quantifier_model i dom /\ check_step (QuantifierInstantiation args) concl [])
          (ensures judgment_holds i rho concl)
  = lemma_instantiation_step args concl;
    match concl with
    | Holds e -> lemma_check_typed i dom rho args e
    | Equal a b -> lemma_equal_never_checked args a b []
    | Observational _ _ -> ()

(* --- Node theorems ----------------------------------------------------------- *)

let lemma_instantiation_node_sound (skolems:list SK.definition) (i:interpretation value)
                                   (dom:CO.domains) (rho:env value)
                                   (strict:bool) (assertions:list judgment) (node:proof_node)
  : Lemma (requires TQ.quantifier_model i dom /\ QuantifierInstantiation? node.kind /\
                    Some? (check_node_with_context skolems strict assertions node) /\
                    snd (Some?.v (check_node_with_context skolems strict assertions node)) == 0)
          (ensures scoped_holds i rho (fst (Some?.v (check_node_with_context skolems strict assertions node))))
  = lemma_instantiation_result skolems strict assertions node;
    match node.kind with
    | QuantifierInstantiation args -> lemma_instantiation_step_sound i dom rho args node.conclusion

(* `core_rule`, extended with the checked instantiations. Computable from the node. *)
let typed_rule (node:proof_node) : bool = K.core_rule node || instantiation_rule node

let lemma_instantiation_rule_sound (skolems:list SK.definition) (i:interpretation value)
                                   (dom:CO.domains) (rho:env value)
                                   (strict:bool) (assertions:list judgment) (node:proof_node)
  : Lemma (requires TQ.quantifier_model i dom /\ instantiation_rule node /\
                    Some? (check_node_with_context skolems strict assertions node))
          (ensures scoped_holds i rho (fst (Some?.v (check_node_with_context skolems strict assertions node))))
  = lemma_instantiation_result skolems strict assertions node;
    lemma_instantiation_node_sound skolems i dom rho strict assertions node

let lemma_typed_check_node_sound (skolems:list SK.definition) (i:interpretation value)
                                 (dom:CO.domains) (scope:list sort) (rho:env value)
                                 (strict:bool) (assertions:list judgment) (node:proof_node)
  : Lemma (requires TQ.quantifier_model i dom /\ CO.env_typed dom scope rho /\
                    judgments_hold i rho assertions /\ premises_sound i rho node.premises /\
                    K.judgment_scoped scope node.conclusion /\ K.facts_scoped scope node.premises /\
                    typed_rule node /\
                    Some? (check_node_with_context skolems strict assertions node))
          (ensures scoped_holds i rho (fst (Some?.v (check_node_with_context skolems strict assertions node))))
  = if K.core_rule node
    then K.lemma_core_check_node_sound skolems i dom scope rho strict assertions node
    else lemma_instantiation_rule_sound skolems i dom rho strict assertions node
