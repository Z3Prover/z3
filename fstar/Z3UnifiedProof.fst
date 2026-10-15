(* The full-DAG kernel. Premises are checked judgments, never synthetic
   Rewrite/Trusted leaves in one of the legacy recursive proof types. *)
module Z3UnifiedProof

open Z3AstTheory
open Z3ValueTheory
open Z3ProofTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
open Z3Commutativity
open Z3BooleanRewrite
open Z3ArrayLemma
module L = FStar.List.Tot

type judgment =
  | Holds : formula:expr -> judgment
  | Equal : left:expr -> right:expr -> judgment
  | Observational : left:expr -> right:expr -> judgment

type rule =
  | Asserted
  | DefAxiom
  | Hypothesis
  | LemmaRule
  | Unverified : name:string -> rule
  | RewriteRule
  | Reflexivity
  | Symmetry
  | Transitivity
  | TransitivityPath
  | Congruence
  | Commutativity
  | ModusPonens
  | ObservationalMP
  | IffObservational
  | UnitResolution
  | AndElimination
  | NotOrElimination
  | IffTrue
  | IffFalse

type relation =
  | Equality
  | Observation

let identity_rewrite (x:expr) : option expr = Some x

let lemma_identity_rewrite_sound (i:interpretation value) (rho:env value) (x y:expr)
  : Lemma (requires identity_rewrite x == Some y)
          (ensures eval i x rho == eval i y rho)
  = ()

let proof_relation (e:expr) : bool =
  match e with
  | App f _ -> f.decl_name = "~" || f.interp = Some op_oeq
  | _ -> false

let rec ordinary_facts (xs:list expr) : Tot bool (decreases xs) =
  match xs with
  | [] -> true
  | x :: rest -> not (proof_relation x) && ordinary_facts rest

let classify_fact (e:expr) : option judgment =
  if get_sort e <> bool_sort then None
  else match is_oeq e with
  | Some (a, b) -> Some (Observational a b)
  | None ->
    if proof_relation e then None
    else match e with
    | App f [a; b] ->
      if f.decl_name = "=" then
        if f = eq_decl (get_sort a) && get_sort a = get_sort b
        then Some (Equal a b) else None
      else Some (Holds e)
    | _ -> Some (Holds e)

let proposition (j:judgment) : option expr =
  match j with
  | Holds e -> Some e
  | Equal a b -> Some (mk_eq_expr a b)
  | Observational _ _ -> None

let well_formed (j:judgment) : bool =
  match j with
  | Holds e -> classify_fact e = Some j
  | Equal a b ->
    get_sort a = get_sort b && not (proof_relation a) && not (proof_relation b)
  | Observational a b ->
    get_sort a = bool_sort && get_sort b = bool_sort &&
    not (proof_relation a) && not (proof_relation b)

let rec judgments_wf (js:list judgment) : Tot bool (decreases js) =
  match js with
  | [] -> true
  | j :: rest -> well_formed j && judgments_wf rest

let rec propositions (js:list judgment) : Tot (option (list expr)) (decreases js) =
  match js with
  | [] -> Some []
  | j :: rest ->
    (match proposition j, propositions rest with
     | Some e, Some es -> Some (e :: es)
     | _, _ -> None)

let relational (j:judgment) : option (relation & expr & expr) =
  match j with
  | Equal a b -> Some (Equality, a, b)
  | Observational a b -> Some (Observation, a, b)
  | Holds _ -> None

let edge (r:relation) (j:judgment) : option (expr & expr) =
  match r, j with
  | Equality, Equal a b -> Some (a, b)
  | Observation, Observational a b -> Some (a, b)
  | Observation, Equal a b ->
    if get_sort a = bool_sort && get_sort b = bool_sort then Some (a, b) else None
  | _, _ -> None

let rec matching (r:relation) (a b:expr) (js:list judgment)
  : Tot bool (decreases js) =
  match js with
  | [] -> false
  | j :: rest -> edge r j = Some (a, b) || matching r a b rest

let rec arguments_match (r:relation) (xs ys:list expr) (js:list judgment)
  : Tot bool (decreases xs) =
  match xs, ys with
  | [], [] -> true
  | x :: xs', y :: ys' ->
    (x = y || matching r x y js) && arguments_match r xs' ys' js
  | _, _ -> false

let rec extend_reachable (r:relation) (js:list judgment) (known:list expr)
  : Tot (list expr) (decreases js) =
  match js with
  | [] -> known
  | j :: rest ->
    let known =
      match edge r j with
      | Some (a, b) ->
        if L.mem a known then b :: known
        else if L.mem b known then a :: known
        else known
      | None -> known
    in extend_reachable r rest known

let rec reachable (fuel:nat) (r:relation) (js:list judgment) (known:list expr)
  : Tot (list expr) (decreases fuel) =
  if fuel = 0 then known
  else reachable (fuel - 1) r js (extend_reachable r js known)

let rec all_edges (r:relation) (js:list judgment) : Tot bool (decreases js) =
  match js with
  | [] -> true
  | j :: rest -> Some? (edge r j) && all_edges r rest

let relational_step (kind:rule) (concl:judgment) (facts:list judgment) : bool =
  match relational concl with
  | None -> false
  | Some (r, a, b) ->
    (match kind with
     | Reflexivity -> facts = [] && a = b
     | RewriteRule ->
       facts = [] && (identity_rewrite a = Some b || flatten_rewrite a = Some b ||
                      boolean_equiv 8 10 a b)
     | Commutativity -> r = Equality && facts = [] && commutativity_step a b
     | Symmetry ->
       (match facts with
        | [j] ->
          (match relational j with
           | Some (r', s, t) -> r = r' && a = t && b = s
           | None -> false)
        | _ -> false)
     | Transitivity ->
       (match facts with
        | [p; q] ->
          (match edge r p, edge r q with
           | Some (s, t), Some (u, v) -> a = s && t = u && b = v
           | _, _ -> false)
        | _ -> false)
     | TransitivityPath ->
       all_edges r facts && L.mem b (reachable (L.length facts) r facts [a])
     | Congruence ->
       (match a, b with
        | App f xs, App g ys -> f = g && all_edges r facts && arguments_match r xs ys facts
        | _, _ -> false)
     | IffObservational ->
       (match r, facts with
        | Observation, [Equal s t] -> a = s && b = t
        | _, _ -> false)
     | _ -> false)

let rec boolean_formulas (es:list expr) : Tot bool (decreases es) =
  match es with
  | [] -> true
  | e :: rest -> get_sort e = bool_sort && boolean_formulas rest

let logical_step (kind:rule) (concl:judgment) (facts:list judgment) : bool =
  match proposition concl with
  | None -> false
  | Some target ->
    if kind = ObservationalMP then
      (match facts with
       | [j; Observational a b] -> proposition j = Some a && target = b
       | _ -> false)
    else
      match propositions facts with
      | None -> false
      | Some es ->
        (match kind, es with
         | ModusPonens, [a; App f [s; t]] ->
           (f.decl_name = "implies" || f.decl_name = "=>" || f.decl_name = "=") &&
           a = s && target = t
         | UnitResolution, c :: units ->
           boolean_formulas (formula_clause c) &&
           clause_consequence (resolution_residual c units) target
         | AndElimination, [App f args] ->
           f.decl_name = "and" && L.mem target args
         | NotOrElimination, [App f [App g args]] ->
           f.decl_name = "not" && g.decl_name = "or" &&
           (L.mem (mk_not_expr target) args ||
            (match is_not target with
             | Some t -> get_sort t = bool_sort && L.mem t args && target = App f [t]
             | None -> false))
         | IffTrue, [a] -> target = mk_iff_expr a true_expr
         | IffFalse, [n] ->
           (match is_not n with
            | Some a -> target = mk_iff_expr a false_expr
            | None -> false)
         | _, _ -> false)

let check_step (kind:rule) (concl:judgment) (facts:list judgment) : bool =
  well_formed concl && judgments_wf facts &&
  (relational_step kind concl facts || logical_step kind concl facts)

type checked_fact = {
  conclusion: judgment;
  hypotheses: list expr;
}

type proof_node = {
  kind: rule;
  conclusion: judgment;
  premises: list checked_fact;
}

let rec scopes_wf (ps:list checked_fact) : Tot bool (decreases ps) =
  match ps with
  | [] -> true
  | p :: rest -> boolean_formulas p.hypotheses && scopes_wf rest

let rec premise_judgments (ps:list checked_fact) : Tot (list judgment) (decreases ps) =
  match ps with
  | [] -> []
  | p :: rest -> p.conclusion :: premise_judgments rest

let rec add_hypotheses (xs ys:list expr) : Tot (list expr) (decreases xs) =
  match xs with
  | [] -> ys
  | x :: rest -> add_hypotheses rest (if L.mem x ys then ys else x :: ys)

let rec premise_hypotheses (ps:list checked_fact) : Tot (list expr) (decreases ps) =
  match ps with
  | [] -> []
  | p :: rest -> add_hypotheses p.hypotheses (premise_hypotheses rest)

let rec discharged (hyp:expr) (concl:clause) : Tot bool (decreases concl) =
  match concl with
  | [] -> false
  | e :: rest -> complementary hyp e || discharged hyp rest

let rec remaining_hypotheses (hyps:list expr) (concl:expr)
  : Tot (list expr) (decreases hyps) =
  match hyps with
  | [] -> []
  | h :: rest ->
    if complementary h concl || discharged h (formula_clause concl)
    then remaining_hypotheses rest concl
    else h :: remaining_hypotheses rest concl

let false_judgment (j:judgment) : bool = j = Holds false_expr

let checked_theory_lemma (kind:rule) (concl:judgment) (facts:list judgment) : bool =
  match kind, facts, proposition concl with
  | Unverified tag, [], Some e -> tag = "th-lemma" && array_lemma e
  | _, _, _ -> false

let check_node_with_inputs (strict:bool) (assertions:list judgment) (node:proof_node)
  : option (checked_fact & nat) =
  let facts = premise_judgments node.premises in
  let hyps = premise_hypotheses node.premises in
  let accept hs n = Some ({ conclusion = node.conclusion; hypotheses = hs }, n) in
  if not (well_formed node.conclusion && judgments_wf facts && scopes_wf node.premises) then None
  else
    match node.kind with
    | Asserted ->
      if facts = [] && Some? (proposition node.conclusion) && L.mem node.conclusion assertions
      then accept [] 0 else None
    | DefAxiom ->
      if facts = [] && Some? (proposition node.conclusion) &&
         (not strict || L.mem node.conclusion assertions)
      then accept [] 0 else None
    | Hypothesis ->
      (match facts, proposition node.conclusion with
       | [], Some e -> accept [e] 0
       | _, _ -> None)
    | LemmaRule ->
      (match facts, proposition node.conclusion with
       | [j], Some e ->
         if false_judgment j && boolean_formulas (formula_clause e)
         then accept (remaining_hypotheses hyps e) 0 else None
       | _, _ -> None)
    | Unverified _ -> accept hyps (if checked_theory_lemma node.kind node.conclusion facts then 0 else 1)
    | RewriteRule ->
      if facts = [] && Some? (relational node.conclusion)
      then accept hyps (if check_step RewriteRule node.conclusion facts then 0 else 1)
      else None
    | _ -> if check_step node.kind node.conclusion facts then accept hyps 0 else None

let check_node (assertions:list judgment) (node:proof_node)
  : option (checked_fact & nat) =
  check_node_with_inputs false assertions node

let judgment_holds (i:interpretation value) (rho:env value) (j:judgment) : prop =
  match j with
  | Holds e -> lit_true i rho e
  | Equal a b -> eval i a rho == eval i b rho
  | Observational a b -> observations_agree i rho a b

let rec judgments_hold (i:interpretation value) (rho:env value) (js:list judgment)
  : Tot prop (decreases js) =
  match js with
  | [] -> True
  | j :: rest -> judgment_holds i rho j /\ judgments_hold i rho rest

let model_sound (i:interpretation value) : prop =
  boolean_model i /\ not_sound i /\ and_sound i /\ or_sound i /\
  implies_sound i /\ eq_sound i /\ true_sound i /\ false_sound i /\
  arithmetic_model i /\ array_model i

let lemma_proposition_sound (i:interpretation value) (rho:env value) (j:judgment)
  : Lemma (requires eq_sound i /\ Some? (proposition j))
          (ensures judgment_holds i rho j <==>
                   lit_true i rho (Some?.v (proposition j)))
  = match j with
    | Holds _ | Equal _ _ -> ()
    | Observational _ _ -> ()

let rec lemma_propositions_sound (i:interpretation value) (rho:env value) (js:list judgment)
  : Lemma (requires eq_sound i /\ Some? (propositions js) /\ judgments_hold i rho js)
          (ensures conj_holds i rho (Some?.v (propositions js)))
          (decreases js)
  = match js with
    | [] -> ()
    | j :: rest ->
      lemma_proposition_sound i rho j;
      lemma_propositions_sound i rho rest

let related (i:interpretation value) (rho:env value) (r:relation) (a b:expr) : prop =
  match r with
  | Equality -> eval i a rho == eval i b rho
  | Observation -> observations_agree i rho a b

let lemma_edge_sound (i:interpretation value) (rho:env value)
                    (r:relation) (j:judgment) (a b:expr)
  : Lemma (requires well_formed j /\ judgment_holds i rho j /\ edge r j = Some (a, b))
          (ensures related i rho r a b)
  = match r, j with
    | _, _ -> ()

let lemma_edge_values (i:interpretation value) (rho:env value)
                     (r:relation) (j:judgment) (a b:expr)
  : Lemma (requires boolean_model i /\ well_formed j /\
                    judgment_holds i rho j /\ edge r j = Some (a, b))
          (ensures eval i a rho == eval i b rho)
  = lemma_edge_sound i rho r j a b;
    match r with
    | Equality -> ()
    | Observation -> lemma_observations_values i rho a b

let rec lemma_matching_sound (i:interpretation value) (rho:env value)
                             (r:relation) (a b:expr) (js:list judgment)
  : Lemma (requires boolean_model i /\ judgments_wf js /\
                    judgments_hold i rho js /\ matching r a b js)
          (ensures eval i a rho == eval i b rho)
          (decreases js)
  = match js with
    | [] -> ()
    | j :: rest ->
      if edge r j = Some (a, b) then lemma_edge_values i rho r j a b
      else lemma_matching_sound i rho r a b rest

let rec lemma_arguments_sound (i:interpretation value) (rho:env value)
                             (r:relation) (xs ys:list expr) (js:list judgment)
  : Lemma (requires boolean_model i /\ judgments_wf js /\
                    judgments_hold i rho js /\ arguments_match r xs ys js)
          (ensures eval_args i xs rho == eval_args i ys rho)
          (decreases xs)
  = match xs, ys with
    | [], [] -> ()
    | x :: xs', y :: ys' ->
      (if x = y then () else lemma_matching_sound i rho r x y js);
      lemma_arguments_sound i rho r xs' ys' js

let reachable_sound (i:interpretation value) (rho:env value)
                    (r:relation) (start:expr) (known:list expr) : prop =
  forall (e:expr). L.memP e known ==> related i rho r start e

let lemma_related_extend (i:interpretation value) (rho:env value)
                         (r:relation) (start a b:expr) (known:list expr)
  : Lemma (requires reachable_sound i rho r start known /\ L.mem a known /\
                    related i rho r a b)
          (ensures reachable_sound i rho r start (b :: known))
  = FStar.List.Tot.Properties.mem_memP a known;
    match r with
    | Equality | Observation -> ()

let rec lemma_extend_reachable_sound (i:interpretation value) (rho:env value)
                                     (r:relation) (start:expr)
                                     (js:list judgment) (known:list expr)
  : Lemma (requires judgments_wf js /\ judgments_hold i rho js /\
                    reachable_sound i rho r start known)
          (ensures reachable_sound i rho r start (extend_reachable r js known))
          (decreases js)
  = match js with
    | [] -> ()
    | j :: rest ->
      (match edge r j with
       | Some (a, b) ->
         lemma_edge_sound i rho r j a b;
         if L.mem a known then (
           lemma_related_extend i rho r start a b known;
           lemma_extend_reachable_sound i rho r start rest (b :: known))
         else if L.mem b known then (
           assert (related i rho r b a);
           lemma_related_extend i rho r start b a known;
           lemma_extend_reachable_sound i rho r start rest (a :: known))
         else lemma_extend_reachable_sound i rho r start rest known
       | None -> lemma_extend_reachable_sound i rho r start rest known)

let rec lemma_reachable_sound (i:interpretation value) (rho:env value)
                              (fuel:nat) (r:relation) (start:expr)
                              (js:list judgment) (known:list expr)
  : Lemma (requires judgments_wf js /\ judgments_hold i rho js /\
                    reachable_sound i rho r start known)
          (ensures reachable_sound i rho r start (reachable fuel r js known))
          (decreases fuel)
  = if fuel = 0 then ()
    else (
      lemma_extend_reachable_sound i rho r start js known;
      lemma_reachable_sound i rho (fuel - 1) r start js (extend_reachable r js known))

let lemma_relational_step_sound (i:interpretation value) (rho:env value)
                                (kind:rule) (concl:judgment) (facts:list judgment)
  : Lemma (requires model_sound i /\ well_formed concl /\ judgments_wf facts /\
                    judgments_hold i rho facts /\ relational_step kind concl facts)
          (ensures judgment_holds i rho concl)
  = match relational concl with
    | None -> ()
    | Some (r, a, b) ->
      (match kind with
       | RewriteRule ->
         if identity_rewrite a = Some b then lemma_identity_rewrite_sound i rho a b
         else if flatten_rewrite a = Some b then lemma_flatten_rewrite_sound i rho a b
         else lemma_boolean_equiv_sound 8 10 i rho a b
       | Commutativity -> lemma_commutativity_step_sound i rho a b
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
         (match a, b with
          | App f xs, App g ys -> lemma_arguments_sound i rho r xs ys facts
          | _, _ -> ())
       | _ -> ())

let rec lemma_boolean_clause (i:interpretation value) (rho:env value) (es:list expr)
  : Lemma (requires boolean_model i /\ boolean_formulas es)
          (ensures wf_clause i rho es)
          (decreases es)
  = match es with
    | [] -> ()
    | _ :: rest -> lemma_boolean_clause i rho rest

let rec lemma_conj_member (i:interpretation value) (rho:env value) (es:list expr) (e:expr)
  : Lemma (requires conj_holds i rho es /\ L.memP e es)
          (ensures lit_true i rho e)
          (decreases es)
  = match es with
    | [] -> ()
    | x :: rest -> if x = e then () else lemma_conj_member i rho rest e

let lemma_logical_step_sound (i:interpretation value) (rho:env value)
                             (kind:rule) (concl:judgment) (facts:list judgment)
  : Lemma (requires model_sound i /\ well_formed concl /\ judgments_wf facts /\
                    judgments_hold i rho facts /\ logical_step kind concl facts)
          (ensures judgment_holds i rho concl)
  = lemma_proposition_sound i rho concl;
    match kind with
    | ObservationalMP ->
      (match facts with
       | [j; Observational a b] ->
         lemma_proposition_sound i rho j;
         Z3ObservationalEquality.lemma_mp_oeq_sound i rho a b
       | _ -> ())
    | _ ->
      lemma_propositions_sound i rho facts;
      (match propositions facts with
       | None -> ()
       | Some es ->
         (match kind, es with
          | UnitResolution, c :: units ->
            lemma_boolean_clause i rho (formula_clause c);
            let unit_sound (e:expr)
              : Lemma (requires L.memP e units) (ensures lit_true i rho e)
              = lemma_conj_member i rho units e
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires unit_sound);
            lemma_resolution_residual_sound i rho c units;
            lemma_clause_consequence i rho (resolution_residual c units)
                                     (Some?.v (proposition concl))
          | AndElimination, [App f args] ->
            FStar.List.Tot.Properties.mem_memP (Some?.v (proposition concl)) args;
            lemma_and_elim_sound i rho args (Some?.v (proposition concl))
          | NotOrElimination, [App f [App g args]] ->
            let target = Some?.v (proposition concl) in
            if L.mem (mk_not_expr target) args then (
              FStar.List.Tot.Properties.mem_memP (mk_not_expr target) args;
              lemma_not_or_elim_sound i rho args (mk_not_expr target);
              match eval i target rho with VBool _ -> () | _ -> ())
            else
              (match is_not target with
               | Some t ->
                 FStar.List.Tot.Properties.mem_memP t args;
                 lemma_not_or_elim_sound i rho args t
               | None -> ())
          | IffTrue, [a] -> lemma_iff_true_sound i rho a
          | IffFalse, [n] ->
            (match is_not n with
             | Some a -> lemma_iff_false_sound i rho a
             | None -> ())
          | _, _ -> ()))

let lemma_check_step_sound (i:interpretation value) (rho:env value)
                           (kind:rule) (concl:judgment) (facts:list judgment)
  : Lemma (requires model_sound i /\ judgments_hold i rho facts /\
                    check_step kind concl facts)
          (ensures judgment_holds i rho concl)
  = if relational_step kind concl facts then
      lemma_relational_step_sound i rho kind concl facts
    else lemma_logical_step_sound i rho kind concl facts

let rec lemma_judgment_member (i:interpretation value) (rho:env value)
                              (js:list judgment) (j:judgment)
  : Lemma (requires judgments_hold i rho js /\ L.memP j js)
          (ensures judgment_holds i rho j)
          (decreases js)
  = match js with
    | [] -> ()
    | h :: rest -> if h = j then () else lemma_judgment_member i rho rest j

let rec lemma_add_hypotheses_sound (i:interpretation value) (rho:env value)
                                   (xs ys:list expr)
  : Lemma (requires conj_holds i rho (add_hypotheses xs ys))
          (ensures conj_holds i rho xs /\ conj_holds i rho ys)
          (decreases xs)
  = match xs with
    | [] -> ()
    | x :: rest ->
      if L.mem x ys then (
        lemma_add_hypotheses_sound i rho rest ys;
        FStar.List.Tot.Properties.mem_memP x ys;
        lemma_conj_member i rho ys x)
      else lemma_add_hypotheses_sound i rho rest (x :: ys)

let scoped_holds (i:interpretation value) (rho:env value) (p:checked_fact) : prop =
  conj_holds i rho p.hypotheses ==> judgment_holds i rho p.conclusion

let rec premises_sound (i:interpretation value) (rho:env value) (ps:list checked_fact)
  : Tot prop (decreases ps) =
  match ps with
  | [] -> True
  | p :: rest -> scoped_holds i rho p /\ premises_sound i rho rest

let rec lemma_premises_sound (i:interpretation value) (rho:env value) (ps:list checked_fact)
  : Lemma (requires premises_sound i rho ps /\ conj_holds i rho (premise_hypotheses ps))
          (ensures judgments_hold i rho (premise_judgments ps))
          (decreases ps)
  = match ps with
    | [] -> ()
    | p :: rest ->
      lemma_add_hypotheses_sound i rho p.hypotheses (premise_hypotheses rest);
      lemma_premises_sound i rho rest

let lemma_complement_from_false (i:interpretation value) (rho:env value) (h e:expr)
  : Lemma (requires model_sound i /\ get_sort h == bool_sort /\ get_sort e == bool_sort /\
                    complementary h e /\ ~(lit_true i rho e))
          (ensures lit_true i rho h)
  = match h with
    | App f [a] ->
      if f.decl_name = "not" && a = e then (
        lemma_not_relates i rho f a;
        match eval i e rho with | VBool _ -> () | _ -> ())
      else
        (match e with
         | App g [b] ->
           if g.decl_name = "not" && b = h then (
             lemma_not_relates i rho g b;
             match eval i h rho with | VBool _ -> () | _ -> ())
           else ()
         | _ -> ())
    | _ ->
      (match e with
       | App g [b] ->
         if g.decl_name = "not" && b = h then (
           lemma_not_relates i rho g b;
           match eval i h rho with | VBool _ -> () | _ -> ())
         else ()
       | _ -> ())

let rec lemma_discharged_sound (i:interpretation value) (rho:env value)
                               (h:expr) (es:list expr)
  : Lemma (requires model_sound i /\ get_sort h == bool_sort /\
                    boolean_formulas es /\ discharged h es /\ ~(clause_holds i rho es))
          (ensures lit_true i rho h)
          (decreases es)
  = match es with
    | [] -> ()
    | e :: rest ->
      if complementary h e then lemma_complement_from_false i rho h e
      else lemma_discharged_sound i rho h rest

let lemma_formula_clause_false (i:interpretation value) (rho:env value) (e:expr)
  : Lemma (requires or_sound i /\ ~(lit_true i rho e))
          (ensures ~(clause_holds i rho (formula_clause e)))
  = match e with
    | App f args -> ()
    | _ -> ()

let rec lemma_remaining_hypotheses_sound (i:interpretation value) (rho:env value)
                                         (hyps:list expr) (concl:expr)
  : Lemma (requires model_sound i /\ boolean_formulas hyps /\
                    get_sort concl == bool_sort /\ boolean_formulas (formula_clause concl) /\
                    conj_holds i rho (remaining_hypotheses hyps concl) /\ ~(lit_true i rho concl))
          (ensures conj_holds i rho hyps)
          (decreases hyps)
  = match hyps with
    | [] -> ()
    | h :: rest ->
      (if complementary h concl then lemma_complement_from_false i rho h concl
       else if discharged h (formula_clause concl) then (
         lemma_formula_clause_false i rho concl;
         lemma_discharged_sound i rho h (formula_clause concl))
       else ());
      lemma_remaining_hypotheses_sound i rho rest concl

let rec lemma_boolean_union (xs ys:list expr)
  : Lemma (requires boolean_formulas xs /\ boolean_formulas ys)
          (ensures boolean_formulas (add_hypotheses xs ys))
          (decreases xs)
  = match xs with
    | [] -> ()
    | x :: rest ->
      if L.mem x ys then lemma_boolean_union rest ys
      else lemma_boolean_union rest (x :: ys)

let rec lemma_boolean_premises (ps:list checked_fact)
  : Lemma (requires scopes_wf ps)
          (ensures boolean_formulas (premise_hypotheses ps))
          (decreases ps)
  = match ps with
    | [] -> ()
    | p :: rest ->
      lemma_boolean_premises rest;
      lemma_boolean_union p.hypotheses (premise_hypotheses rest)

let node_obligation (i:interpretation value) (rho:env value) (strict:bool) (node:proof_node) : prop =
  match node.kind with
  | DefAxiom -> if strict then True else judgment_holds i rho node.conclusion
  | RewriteRule ->
    not (check_step RewriteRule node.conclusion (premise_judgments node.premises)) ==>
    (conj_holds i rho (premise_hypotheses node.premises) ==>
     judgment_holds i rho node.conclusion)
  | Unverified _ ->
    not (checked_theory_lemma node.kind node.conclusion (premise_judgments node.premises)) ==>
    (conj_holds i rho (premise_hypotheses node.premises) ==>
     judgment_holds i rho node.conclusion)
  | _ -> True

let lemma_check_node_sound (i:interpretation value) (rho:env value)
                           (strict:bool) (assertions:list judgment) (node:proof_node)
  : Lemma (requires model_sound i /\ judgments_hold i rho assertions /\
                    premises_sound i rho node.premises /\ node_obligation i rho strict node /\
                    Some? (check_node_with_inputs strict assertions node))
          (ensures scoped_holds i rho (fst (Some?.v (check_node_with_inputs strict assertions node))))
  = let aux (_:squash (conj_holds i rho (fst (Some?.v (check_node_with_inputs strict assertions node))).hypotheses))
      : Lemma (judgment_holds i rho node.conclusion) =
      match node.kind with
      | Asserted ->
        FStar.List.Tot.Properties.mem_memP node.conclusion assertions;
        lemma_judgment_member i rho assertions node.conclusion
      | DefAxiom ->
        if strict then (
          FStar.List.Tot.Properties.mem_memP node.conclusion assertions;
          lemma_judgment_member i rho assertions node.conclusion)
      | Hypothesis -> lemma_proposition_sound i rho node.conclusion
      | Unverified _ ->
        if checked_theory_lemma node.kind node.conclusion (premise_judgments node.premises) then (
          lemma_proposition_sound i rho node.conclusion;
          match proposition node.conclusion with
          | Some e -> lemma_array_lemma_sound i rho e
          | None -> ())
      | RewriteRule ->
        if check_step RewriteRule node.conclusion (premise_judgments node.premises)
        then lemma_check_step_sound i rho RewriteRule node.conclusion (premise_judgments node.premises)
      | LemmaRule ->
        lemma_proposition_sound i rho node.conclusion;
        lemma_boolean_premises node.premises;
        (match proposition node.conclusion with
         | Some e ->
           FStar.Classical.excluded_middle (lit_true i rho e);
           FStar.Classical.or_elim #(lit_true i rho e) #(~(lit_true i rho e))
             #(fun () -> judgment_holds i rho node.conclusion)
             (fun _ -> ())
             (fun _ ->
               lemma_remaining_hypotheses_sound i rho (premise_hypotheses node.premises) e;
               lemma_premises_sound i rho node.premises)
         | None -> ())
      | _ ->
        lemma_premises_sound i rho node.premises;
        lemma_check_step_sound i rho node.kind node.conclusion (premise_judgments node.premises)
    in FStar.Classical.impl_intro aux

let lemma_obligation_free_node_sound (i:interpretation value) (rho:env value)
                                     (strict:bool) (assertions:list judgment) (node:proof_node)
  : Lemma (requires model_sound i /\ judgments_hold i rho assertions /\
                    premises_sound i rho node.premises /\
                    (node.kind == DefAxiom /\ not strict ==> judgment_holds i rho node.conclusion) /\
                    Some? (check_node_with_inputs strict assertions node) /\
                    snd (Some?.v (check_node_with_inputs strict assertions node)) == 0)
          (ensures scoped_holds i rho (fst (Some?.v (check_node_with_inputs strict assertions node))))
  = lemma_check_node_sound i rho strict assertions node
