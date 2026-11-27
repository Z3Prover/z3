module Z3UnifiedProofSyntax

open Z3AstTheory
open Z3OperatorTags
open Z3ClauseSyntax
open Z3ClausalSemantics
open Z3ObservationalSyntax
module LA = Z3LinearArithmeticAst
module GS = Z3LpGomorySyntax
module FC = Z3FiniteFieldCertificate
module SK = Z3SkolemSyntax
module L = FStar.List.Tot

type judgment =
  | Holds : formula:expr -> judgment
  | Equal : left:expr -> right:expr -> judgment
  | Observational : left:expr -> right:expr -> judgment

type binder_entry = {
  binder_name: string;
  binder_formula: expr;
  binder_premises: list int;
  binder_sorts: option (list sort);
}

type binder_certificate = {
  binder_entries: list binder_entry;
  binder_root: int;
}

type rule =
  | Asserted
  | DefAxiom
  | DefinitionIntroduction
  | ApplyDefinition
  | Hypothesis
  | LemmaRule
  | Unverified : name:string -> rule
  | ArithmeticFarkas : coefficients:list LA.coefficient -> rule
  | ArithmeticBound : coefficients:list LA.coefficient -> rule
  | ArithmeticGomory : certificate:GS.certificate -> rule
  | FiniteFieldPac : certificate:FC.certificate -> rule
  | RewriteRule
  | PullQuantifier
  | DestructiveEqualityResolution
  | Skolemization
  | ElimUnused
  | PushQuantifier
  | DestructiveEquality
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
  | QuantifierIntroduction : certificate:binder_certificate -> rule
  | QuantifierInstantiation : arguments:list expr -> rule
  | ArithmeticLattice : certificate:GS.certificate -> rule

type relation =
  | Equality
  | Observation

type checked_fact = {
  conclusion: judgment;
  hypotheses: list expr;
}

type proof_node = {
  kind: rule;
  conclusion: judgment;
  premises: list checked_fact;
}


let identity_rewrite (x:expr) : option expr = Some x

let constant_quantifier_rewrite (a b:expr) : bool =
  match a with
  | Quantifier k bs s body ->
    (k = Forall_k || k = Exists_k) && s = bool_sort &&
    (body = true_expr || body = false_expr) && b = body
  | _ -> false

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
    get_sort a = get_sort b &&
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
    if get_sort a = get_sort b then Some (a, b) else None
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

let rec ordered_arguments_match (r:relation) (xs ys:list expr) (js:list judgment)
  : Tot bool (decreases xs) =
  match xs, ys with
  | [], [] -> true
  | x :: rest, y :: remaining ->
    if x = y then ordered_arguments_match r rest remaining js
    else (match js with
          | j :: facts -> edge r j = Some (x, y) &&
                          ordered_arguments_match r rest remaining facts
          | [] -> false)
  | _, _ -> false

let fast_arguments_match (r:relation) (xs ys:list expr) (js:list judgment) : bool =
  ordered_arguments_match r xs ys js || arguments_match r xs ys js

let rec lemma_arguments_match_cons (r:relation) (xs ys:list expr) (js:list judgment) (j:judgment)
  : Lemma (requires arguments_match r xs ys js)
          (ensures arguments_match r xs ys (j :: js))
          (decreases xs)
  = match xs, ys with
    | x :: rest, y :: remaining -> lemma_arguments_match_cons r rest remaining js j
    | _, _ -> ()

let rec lemma_ordered_arguments_match (r:relation) (xs ys:list expr) (js:list judgment)
  : Lemma (requires ordered_arguments_match r xs ys js)
          (ensures arguments_match r xs ys js)
          (decreases xs)
  = match xs, ys with
    | x :: rest, y :: remaining ->
      if x = y then lemma_ordered_arguments_match r rest remaining js
      else (match js with
            | j :: facts ->
              lemma_ordered_arguments_match r rest remaining facts;
              lemma_arguments_match_cons r rest remaining facts j
            | [] -> ())
    | _, _ -> ()

let lemma_fast_arguments_match (r:relation) (xs ys:list expr) (js:list judgment)
  : Lemma (fast_arguments_match r xs ys js == arguments_match r xs ys js)
  = if ordered_arguments_match r xs ys js then lemma_ordered_arguments_match r xs ys js


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

let rec boolean_formulas (es:list expr) : Tot bool (decreases es) =
  match es with
  | [] -> true
  | e :: rest -> get_sort e = bool_sort && boolean_formulas rest

let basic_rule_of_name (name:string) : option rule =
  if name = "rewrite" then Some RewriteRule
  else if name = "elim-unused" then Some ElimUnused
  else if name = "push-quant" then Some PushQuantifier
  else if name = "der" then Some DestructiveEquality
  else if name = "pull-quant" then Some PullQuantifier
  else if name = "sk" then Some Skolemization
  else if name = "refl" || name = "reflexivity" then Some Reflexivity
  else if name = "symm" then Some Symmetry
  else if name = "trans" then Some Transitivity
  else if name = "trans*" then Some TransitivityPath
  else if name = "monotonicity" then Some Congruence
  else if name = "commutativity" then Some Commutativity
  else if name = "mp" then Some ModusPonens
  else if name = "mp~" then Some ObservationalMP
  else if name = "iff~" then Some IffObservational
  else if name = "unit-resolution" then Some UnitResolution
  else if name = "and-elim" then Some AndElimination
  else if name = "not-or-elim" then Some NotOrElimination
  else if name = "iff-true" then Some IffTrue
  else if name = "iff-false" then Some IffFalse
  else if name = "def-axiom" || name = "true-axiom" then Some DefAxiom
  else if name = "th-lemma" then Some (Unverified "th-lemma")
  else None

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


let negative_replacement (e a b:expr) : bool =
  get_sort e = bool_sort && get_sort b = bool_sort && a = mk_not_expr e

let rec premise_replacement (r:relation) (e:expr) (facts:list judgment)
  : Tot (option expr) (decreases facts) =
  match facts with
  | [] -> None
  | j :: rest ->
    (match edge r j with
     | Some (a, b) ->
       if e = a then Some b
       else if negative_replacement e a b then Some (mk_not_expr b)
       else premise_replacement r e rest
     | None -> premise_replacement r e rest)

let rec replace_premises (r:relation) (facts:list judgment) (e:expr)
  : Tot expr (decreases e) =
  match premise_replacement r e facts with
  | Some replacement -> replacement
  | None ->
    (match e with
     | App f args -> App f (replace_premise_args r facts args)
     | Quantifier k bs s body -> Quantifier k bs s (replace_premises r facts body)
     | _ -> e)

and replace_premise_args (r:relation) (facts:list judgment) (args:list expr)
  : Tot (list expr) (decreases args) =
  match args with
  | [] -> []
  | a :: rest -> replace_premises r facts a :: replace_premise_args r facts rest

let rec reverse_judgments (facts:list judgment) : Tot (list judgment) (decreases facts) =
  match facts with
  | [] -> []
  | j :: rest ->
    (match j with
     | Equal a b -> Equal b a
     | Observational a b -> Observational b a
     | Holds e -> Holds e) :: reverse_judgments rest

let skolem_step (skolems:list SK.definition) (concl:judgment) (facts:list judgment) : bool =
  match concl, facts with
  | Observational a b, [] -> well_formed concl && SK.check skolems a b
  | _, _ -> false

