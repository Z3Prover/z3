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
open Z3ProofIndex
module A = Z3ArrayRewrite
module D = Z3Definitions
module LA = Z3LinearArithmeticAst
module LE = Z3LinearArithmeticEmbed
module AR = Z3ArithmeticRewrite
module AF = Z3ArithmeticFactor
module BX = Z3BvExtract
module IR = Z3IntegerRewrite
module ID = Z3IntegerDivision
module CR = Z3ConditionalRewrite
module LP = Z3LpReplay
module G = Z3LpGomory
module IC = Z3LpIntegerCut
module Q = Z3QuantifierInstantiation
module QN = Z3QuantifierNnf
module QV = Z3QuantifierVacuity
module QP = Z3QuantifierPull
module QD = Z3QuantifierDer
module SK = Z3Skolemization
module QR = Z3QuantifierReduce
module DE = Z3DestructiveEquality
module LR = Z3LambdaRewrite
module TN = Z3TheoryNormalize
module FF = Z3FiniteFieldLemma
module FP = Z3FiniteFieldPac
module BE = Z3BvExhaustive
module BN = Z3BvAddNormalize
module L = FStar.List.Tot
module C = Z3CanonicalOps

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
  | ArithmeticGomory : certificate:G.certificate -> rule
  | FiniteFieldPac : certificate:FP.certificate -> rule
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

type relation =
  | Equality
  | Observation

let identity_rewrite (x:expr) : option expr = Some x

let constant_quantifier_rewrite (a b:expr) : bool =
  match a with
  | Quantifier k bs s body ->
    (k = Forall_k || k = Exists_k) && s = bool_sort &&
    (body = true_expr || body = false_expr) && b = body
  | _ -> false

let constant_quantifier_model (i:interpretation value) : prop =
  forall (k:quantifier_kind) (bs:list sort) (v:value).
    (k = Forall_k \/ k = Exists_k) /\ (v == VBool true \/ v == VBool false) ==>
    i.interp_quant k bs (fun _ -> v) == v

let lemma_quantifier_constant (i:interpretation value) (k:quantifier_kind)
                              (bs:list sort) (v:value)
  : Lemma (requires constant_quantifier_model i /\
                    (k = Forall_k \/ k = Exists_k) /\
                    (v == VBool true \/ v == VBool false))
          (ensures i.interp_quant k bs (fun _ -> v) == v)
  = ()

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

let relational_step (kind:rule) (concl:judgment) (facts:list judgment) : bool =
  match relational concl with
  | None -> false
  | Some (r, a, b) ->
    (match kind with
     | Reflexivity -> facts = [] && a = b
     | PullQuantifier -> facts = [] && (QP.check a b || QR.equivalent 64 a b || TN.equivalent a b)
     | ElimUnused -> facts = [] && QR.equivalent 64 a b
     | PushQuantifier -> facts = [] && QR.push_check a b
     | DestructiveEquality | DestructiveEqualityResolution ->
       facts = [] && (QD.equivalent 64 a b || DE.check a b)
     | RewriteRule | ApplyDefinition ->
       (* The Boolean equivalence test boolean_equiv 8 10 a b is the first test of
          QR.equivalent 64 a b, so it is not repeated as a separate alternative:
          the alternatives accept the same pairs, and the full Boolean normal
          form of a large step is computed once rather than once per alternative. *)
       (kind = ApplyDefinition || facts = []) &&
                     (identity_rewrite a = Some b || flatten_rewrite a = Some b ||
                      Z3DistinctAst.duplicate_rewrite a b ||
                      Z3DistinctEmbed.expansion_rewrite a b ||
                      constant_quantifier_rewrite a b ||
                     A.equivalent 64 a b || AR.equivalent a b ||
                      AF.check a b || BX.check a b ||
                      QR.equivalent 64 a b || LR.rewrite a b ||
                      CR.equivalent a b || IR.equivalent a b || ID.equivalent a b ||
                      ID.equivalent b a || QV.equivalent 64 a b ||
                      TN.equivalent a b ||
                      boolean_search a b ||
                      (kind = RewriteRule && (BE.equivalent a b || BN.equivalent a b)))
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
       a = b || (match a, b with
        | App f xs, App g ys -> f = g && all_edges r facts && fast_arguments_match r xs ys facts
        | _, _ -> false)
     | IffObservational ->
       (match r, facts with
        | Observation, [Equal s t] -> get_sort a = bool_sort && a = s && b = t
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
         | DefinitionIntroduction, [] | DefAxiom, [] ->
           D.tautology 128 target || TN.tautology target
         | Unverified "th-lemma", _ -> TN.consequence es target
         | QuantifierInstantiation args, [] -> Q.check args target
         | ModusPonens, [a; App f [s; t]] ->
           (C.canonical_implies f || C.canonical_eq f) && a = s && target = t
         | UnitResolution, c :: units ->
           boolean_formulas (formula_clause c) &&
           clause_consequence (resolution_residual c units) target
         | AndElimination, [App f args] ->
           C.canonical_and f && L.mem target args
         | NotOrElimination, [App f [App g args]] ->
           C.canonical_not f && C.canonical_or g &&
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

let binder_quantifier_step (sorts:list sort) (concl:judgment) (facts:list judgment) : bool =
  match relational concl, facts with
  | Some (r, Quantifier k bs s a, Quantifier k' bs' s' b), [j] ->
    k = k' && bs = sorts && bs' = sorts &&
    s = quant_sort k bs (get_sort a) && s' = quant_sort k' bs' (get_sort b) &&
    (k = Lambda_k || (get_sort a = bool_sort && get_sort b = bool_sort)) &&
    (match edge r j with
     | Some (source, target) -> QR.equivalent 64 a source && QR.equivalent 64 target b
     | None -> false)
  | _, _ -> false

let binder_negative_quantifier_step (sorts:list sort) (concl:judgment)
                                    (facts:list judgment) : bool =
  match relational concl, facts with
  | Some (r, App n [Quantifier k bs s a], Quantifier k' bs' s' b), [j] ->
    n = not_decl && (k = Forall_k || k = Exists_k) && k' = QN.dual k &&
    bs = sorts && bs' = sorts && s = bool_sort && s' = bool_sort &&
    get_sort a = bool_sort && get_sort b = bool_sort &&
    (match edge r j with
     | Some (source, target) ->
       QR.equivalent 64 (mk_not_expr a) source && QR.equivalent 64 target b
     | None -> false)
  | _, _ -> false

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

let binder_boolean_step (negative:bool) (concl:judgment) (facts:list judgment) : bool =
  match relational concl with
  | Some (r, a, b) ->
    get_sort a = bool_sort && get_sort b = bool_sort &&
    (match a with
     | Quantifier _ _ _ _ -> false
     | App n [Quantifier _ _ _ _] -> n <> not_decl
     | _ -> true) &&
    (not negative || Some? (D.negation a)) && all_edges r facts &&
    (boolean_equiv 8 10 (replace_premises r facts a) b ||
     boolean_equiv 8 10 a (replace_premises r (reverse_judgments facts) b) ||
     QR.equivalent 64 (replace_premises r facts a) b ||
     TN.equivalent (replace_premises r facts a) b)
  | None -> false

let binder_step (e:binder_entry) (concl:judgment) (facts:list judgment) : bool =
  well_formed concl && judgments_wf facts &&
  (if e.binder_name = "quant-intro" then
     match e.binder_sorts with
     | Some sorts -> binder_quantifier_step sorts concl facts
     | None -> false
   else if e.binder_name = "nnf-pos" || e.binder_name = "nnf-neg" then
     let negative = e.binder_name = "nnf-neg" in
     match e.binder_sorts with
     | Some sorts ->
       if negative then binder_negative_quantifier_step sorts concl facts
       else binder_quantifier_step sorts concl facts
     | None -> binder_boolean_step negative concl facts
   else match basic_rule_of_name e.binder_name with
   | Some kind -> e.binder_sorts = None && check_step kind concl facts
   | None -> false)

let binder_step_with_inputs (assertions:list judgment) (e:binder_entry)
                            (concl:judgment) (facts:list judgment) : bool =
  binder_step e concl facts ||
  (e.binder_name = "asserted" && e.binder_sorts = None && facts = [] &&
   well_formed concl && Some? (proposition concl) &&
   D.scoped [] e.binder_formula && L.mem concl assertions)

let skolem_step (skolems:list SK.definition) (concl:judgment) (facts:list judgment) : bool =
  match concl, facts with
  | Observational a b, [] -> well_formed concl && SK.check skolems a b
  | _, _ -> false

let binder_step_with_context (skolems:list SK.definition) (assertions:list judgment)
                             (e:binder_entry) (concl:judgment) (facts:list judgment) : bool =
  binder_step_with_inputs assertions e concl facts ||
  (e.binder_name = "sk" && e.binder_sorts = None && skolem_step skolems concl facts)

let rec check_binder_entries (skolems:list SK.definition) (assertions:list judgment)
                            (entries:list binder_entry)
                            (cache:Z3ProofIndex.index_tree judgment) (next:nat)
  : Tot (option (Z3ProofIndex.index_tree judgment)) (decreases entries) =
  match entries with
  | [] -> Some cache
  | e :: rest ->
    classify_fact e.binder_formula >>= (fun concl ->
    opt_map (Z3ProofIndex.index_find cache) e.binder_premises >>= (fun facts ->
    if binder_step_with_context skolems assertions e concl facts then
      check_binder_entries skolems assertions rest (Z3ProofIndex.index_put cache next concl) (next + 1)
    else None))

(* --- Scopes of binder entries ----------------------------------------------- *)

(* A certificate's entries are judgments at different binder depths: the
   premise of a quantifier-introduction entry is the body judgment, open under
   the entry's binders. `check_binder_entries` does not check scopes, so an
   entry whose variables disagree with the binders that bind them (for example
   `Var 0` annotated Bool under an Int binder) was accepted, and the Boolean
   wrapper of `binder_quantifier_step` could then certify a false equation
   between quantifiers. `binder_scoped` assigns every entry the scopes at which
   the root uses it and requires the entry's judgment to be scoped
   (`Z3Definitions.scoped`) at each of them:

   * the root is an entry index and is used at the closed top-level scope `[]`;
   * an entry used at `scope` with binder sorts `bs` uses its premises at
     `L.rev bs @ scope` (`Var 0` is the last binder), any other entry at
     `scope` itself; every premise must be an earlier entry;
   * one entry may be used at several scopes (a closed subproof inside and
     outside a binder, or a shared body proof under different binders); it is
     checked at each. Entries the root does not use get no scope and no check.

   The scopes are collected backwards (premises precede their users). The
   forward check confirms, for every scope of every entry, that the entry's
   judgment is scoped there and that each premise is an earlier entry that was
   assigned the scope its user needs; it does not rely on the backward pass.
   `Z3BinderScope` proves what an accepted certificate then satisfies.

   Resources. Shared entries under differently nested binders can need
   exponentially many scopes, and `Z3Definitions.scoped` walks expressions
   and sorts as trees (shared subterms and shared sorts are walked again).
   The guard is therefore bounded, and exceeding a bound rejects the
   certificate (the node keeps a pending obligation):

   * a DEMANDED (stored) scope has at most `binder_scope_limit` sorts,
     checked before it is built; an entry is assigned at most
     `binder_entry_scope_limit` scopes; at most `binder_demand_limit n`
     scopes are assigned for `n` entries;
   * both passes share one work budget, `binder_work_limit n` units, and
     every step is charged before it is taken: one unit per entry, per index
     lookup or update, per list cell counted or compared, per expression node
     walked, per sort node compared (both sorts are walked together, so a
     comparison costs at most the smaller unfolded sort), the lengths of both
     names (`FStar.String.strlen`) before two base-sort names are compared,
     and one unit per variable index step; `2 m + 1` units to build the scope
     under `m` binders, also inside expressions, where scopes are not capped
     by `binder_scope_limit` but every cell built or indexed is charged; and
     `len + 2` units per assigned scope of length `len`.

   The units are an abstract count, not a time bound: a lookup in
   `Z3ProofIndex.index_tree` costs up to `log2 n + 1` steps, and an integer
   (bignum) comparison or update is one primitive operation. A name's length
   is computed before it is charged: both runtimes count one character per
   UTF-8 lead byte (`ocaml_runtime/fStar_String.ml` steps like the Cherry
   runtime), in as many steps as the count, which is at least a quarter of
   the name's bytes also for malformed UTF-8; so the uncharged work is that
   of the one name whose length exceeds the remaining budget, and comparing
   two names costs at most four units per charged character. Linear passes
   over the entry list itself (its length and reversal), and
   `check_binder_entries`, which runs before the guard, are not charged; the
   budget bounds the guard's own work. The guard only rejects certificates;
   it accepts nothing new. *)
let binder_scope_limit : nat = 1024

let binder_entry_scope_limit : nat = 64

let binder_demand_limit (n:nat) : nat = 4 * n + 1024

(* 65536 units per entry: the expression budget the document layer allows one
   input (`Z3ProofDocument.document_definitions`). *)
let binder_work_limit (n:nat) : nat = 65536 * (n + 1)

let scope_charge (work cost:nat) : option nat =
  if cost <= work then Some (work - cost) else None

(* The length of `l`, one unit per element. *)
let rec scope_length_within (#a:Type) (work:nat) (l:list a)
  : Tot (option (nat & nat)) (decreases l) =
  match l with
  | [] -> Some (0, work)
  | _ :: rest ->
    if work = 0 then None
    else (match scope_length_within (work - 1) rest with
          | Some (n, w) -> Some (n + 1, w)
          | None -> None)

(* `sort_eq s t` and `sort_list_eq l1 l2` (structural sort equality), one
   unit per sort node and list cell visited, and the two names' lengths
   before two base-sort names are compared. *)
let rec sort_eq_within (work:nat) (s t:sort) : Tot (option (bool & nat)) (decreases s) =
  match scope_charge work 1 with
  | None -> None
  | Some w ->
    (match s, t with
     | BaseSort a, BaseSort b ->
       (match scope_charge w (FStar.String.strlen a + FStar.String.strlen b) with
        | Some w' -> Some (a = b, w')
        | None -> None)
     | ArraySort d1 r1, ArraySort d2 r2 ->
       (match sort_list_eq_within w d1 d2 with
        | Some (true, w') -> sort_eq_within w' r1 r2
        | r -> r)
     | _, _ -> Some (false, w))

and sort_list_eq_within (work:nat) (l1 l2:list sort) : Tot (option (bool & nat)) (decreases l1) =
  match scope_charge work 1 with
  | None -> None
  | Some w ->
    (match l1, l2 with
     | [], [] -> Some (true, w)
     | a :: l1', b :: l2' ->
       (match sort_eq_within w a b with
        | Some (true, w') -> sort_list_eq_within w' l1' l2'
        | r -> r)
     | _, _ -> Some (false, w))

(* `sorts_match args dom`. *)
let rec sorts_match_within (work:nat) (args:list expr) (dom:list sort)
  : Tot (option (bool & nat)) (decreases args) =
  match scope_charge work 1 with
  | None -> None
  | Some w ->
    (match args, dom with
     | [], [] -> Some (true, w)
     | a :: args', d :: dom' ->
       (match sort_eq_within w (get_sort a) d with
        | Some (true, w') -> sorts_match_within w' args' dom'
        | r -> r)
     | _, _ -> Some (false, w))

(* Whether `scope` is among `scopes`. *)
let rec scope_mem_within (work:nat) (scope:list sort) (scopes:list (list sort))
  : Tot (option (bool & nat)) (decreases scopes) =
  match scopes with
  | [] -> Some (false, work)
  | x :: rest ->
    (match sort_list_eq_within work x scope with
     | Some (true, w) -> Some (true, w)
     | Some (false, w) -> scope_mem_within w scope rest
     | None -> None)

(* The sort at index `n` of `scope`. *)
let rec scope_nth (scope:list sort) (n:nat) : Tot (option sort) (decreases scope) =
  match scope with
  | [] -> None
  | s :: rest -> if n = 0 then Some s else scope_nth rest (n - 1)

(* `Z3Definitions.scoped scope e`, for `len` the length of `scope`. *)
let rec scoped_within (work:nat) (scope:list sort) (len:nat) (e:expr)
  : Tot (option (bool & nat)) (decreases e) =
  match scope_charge work 1 with
  | None -> None
  | Some w ->
    (match e with
     | Var n s ->
       if n < len then
         (match scope_charge w (n + 1) with
          | Some w' ->
            (match scope_nth scope n with
             | Some s' -> sort_eq_within w' s' s
             | None -> Some (false, w'))
          | None -> None)
       else Some (false, w)
     | App f args ->
       (match sorts_match_within w args f.domain with
        | Some (true, w') -> scoped_args_within w' scope len args
        | r -> r)
     | Quantifier k bs s b ->
       (match scope_length_within w bs with
        | Some (m, w1) ->
          (match scope_charge w1 (2 * m + 1) with
           | Some w2 ->
             (match sort_eq_within w2 s (quant_sort k bs (get_sort b)) with
              | Some (true, w3) ->
                (match (if k = Lambda_k then Some (true, w3) else sort_eq_within w3 (get_sort b) bool_sort) with
                 | Some (true, w4) -> scoped_within w4 (L.append (L.rev bs) scope) (m + len) b
                 | r -> r)
              | r -> r)
           | None -> None)
        | None -> None))

and scoped_args_within (work:nat) (scope:list sort) (len:nat) (args:list expr)
  : Tot (option (bool & nat)) (decreases args) =
  match args with
  | [] -> Some (true, work)
  | a :: rest ->
    (match scoped_within work scope len a with
     | Some (true, w) -> scoped_args_within w scope len rest
     | Some (false, w) -> Some (false, w)
     | None -> None)

let judgment_scoped_within (work:nat) (scope:list sort) (len:nat) (j:judgment)
  : option (bool & nat) =
  match j with
  | Holds e -> scoped_within work scope len e
  | Equal a b | Observational a b ->
    (match scoped_within work scope len a with
     | Some (true, w) -> scoped_within w scope len b
     | r -> r)

(* The scope of an entry's premises, and its length, when the entry is used
   at `scope` of length `len`; `None` beyond `binder_scope_limit`. *)
let binder_premise_scope_within (work:nat) (e:binder_entry) (scope:list sort) (len:nat)
  : option (list sort & nat & nat) =
  match e.binder_sorts with
  | None -> Some (scope, len, work)
  | Some bs ->
    (match scope_length_within work bs with
     | Some (m, w) ->
       if m + len > binder_scope_limit then None
       else (match scope_charge w (2 * m + 1) with
             | Some w' -> Some (L.append (L.rev bs) scope, m + len, w')
             | None -> None)
     | None -> None)

type scope_demands = Z3ProofIndex.index_tree (list (list sort))

let scope_demanded (t:scope_demands) (k:int) : list (list sort) =
  match Z3ProofIndex.index_find t k with
  | Some scopes -> scopes
  | None -> []

(* Assign `scope` (of length `len`) to the entry `k`; `count` assignments and
   `work` units are left. *)
let scope_demand (t:scope_demands) (k:nat) (scope:list sort) (len:nat) (count work:nat)
  : option (scope_demands & nat & nat) =
  match scope_charge work 1 with
  | None -> None
  | Some w ->
    let old = scope_demanded t k in
    (match scope_mem_within w scope old with
     | Some (true, w1) -> Some (t, count, w1)
     | Some (false, w1) ->
       (match scope_length_within w1 old with
        | Some (m, w2) ->
          if count = 0 || m >= binder_entry_scope_limit then None
          else (match scope_charge w2 (len + 2) with
                | Some w3 -> Some (Z3ProofIndex.index_put t k (scope :: old), count - 1, w3)
                | None -> None)
        | None -> None)
     | None -> None)

(* The premises `ps` of the entry `k`, used at `scope`. *)
let rec scope_demand_premises (t:scope_demands) (k:int) (ps:list int) (scope:list sort) (len:nat)
                              (count work:nat)
  : Tot (option (scope_demands & nat & nat)) (decreases ps) =
  match ps with
  | [] -> Some (t, count, work)
  | p :: rest ->
    if 0 <= p && p < k then
      (match scope_demand t p scope len count work with
       | Some (t', count', work') -> scope_demand_premises t' k rest scope len count' work'
       | None -> None)
    else None

let rec scope_demand_entry (t:scope_demands) (k:int) (e:binder_entry) (scopes:list (list sort))
                           (count work:nat)
  : Tot (option (scope_demands & nat & nat)) (decreases scopes) =
  match scopes with
  | [] -> Some (t, count, work)
  | s :: rest ->
    (match scope_length_within work s with
     | Some (len, w) ->
       (match binder_premise_scope_within w e s len with
        | Some (s', len', w') ->
          (match scope_demand_premises t k e.binder_premises s' len' count w' with
           | Some (t', count', work') -> scope_demand_entry t' k e rest count' work'
           | None -> None)
        | None -> None)
     | None -> None)

(* `reversed` lists the entries last first; `k` is the index of its head. *)
let rec scope_demand_entries (t:scope_demands) (k:int) (reversed:list binder_entry) (count work:nat)
  : Tot (option (scope_demands & nat)) (decreases reversed) =
  match reversed with
  | [] -> Some (t, work)
  | e :: rest ->
    (match scope_charge work 1 with
     | Some w ->
       (match scope_demand_entry t k e (scope_demanded t k) count w with
        | Some (t', count', work') -> scope_demand_entries t' (k - 1) rest count' work'
        | None -> None)
     | None -> None)

let rec scope_premises_demanded (t:scope_demands) (k:int) (ps:list int) (scope:list sort) (work:nat)
  : Tot (option nat) (decreases ps) =
  match ps with
  | [] -> Some work
  | p :: rest ->
    if 0 <= p && p < k then
      (match scope_charge work 1 with
       | Some w ->
         (match scope_mem_within w scope (scope_demanded t p) with
          | Some (true, w') -> scope_premises_demanded t k rest scope w'
          | _ -> None)
       | None -> None)
    else None

let rec scope_entry_checked (t:scope_demands) (k:int) (e:binder_entry) (j:judgment)
                            (scopes:list (list sort)) (work:nat)
  : Tot (option nat) (decreases scopes) =
  match scopes with
  | [] -> Some work
  | s :: rest ->
    (match scope_length_within work s with
     | Some (len, w) ->
       (match judgment_scoped_within w s len j with
        | Some (true, w1) ->
          (match binder_premise_scope_within w1 e s len with
           | Some (s', _, w2) ->
             (match scope_premises_demanded t k e.binder_premises s' w2 with
              | Some w3 -> scope_entry_checked t k e j rest w3
              | None -> None)
           | None -> None)
        | _ -> None)
     | None -> None)

let rec scope_entries_checked (t:scope_demands) (cache:Z3ProofIndex.index_tree judgment) (k:nat)
                              (entries:list binder_entry) (work:nat)
  : Tot (option nat) (decreases entries) =
  match entries with
  | [] -> Some work
  | e :: rest ->
    (match scope_charge work 1 with
     | Some w ->
       (match Z3ProofIndex.index_find cache k with
        | Some j ->
          (match scope_entry_checked t k e j (scope_demanded t k) w with
           | Some w' -> scope_entries_checked t cache (k + 1) rest w'
           | None -> None)
        | None -> None)
     | None -> None)

(* The scopes assigned by the backward pass, starting from the root at `[]`,
   and the work left; `None` when a bound is exceeded or a premise is not an
   earlier entry. *)
let binder_scopes (count work:nat) (certificate:binder_certificate) : option (scope_demands & nat) =
  let n = L.length certificate.binder_entries in
  let root = certificate.binder_root in
  if 0 <= root && root < n then
    scope_demand_entries (Z3ProofIndex.index_put Z3ProofIndex.Empty root [[]]) (n - 1)
                         (L.rev certificate.binder_entries) count work
  else None

(* The guard with explicit bounds (the checker uses `binder_demand_limit` and
   `binder_work_limit`). *)
let binder_scoped_within (count work:nat) (certificate:binder_certificate)
                         (cache:Z3ProofIndex.index_tree judgment) : bool =
  let root = certificate.binder_root in
  0 <= root && root < L.length certificate.binder_entries &&
  (match binder_scopes count work certificate with
   | Some (t, w) ->
     L.mem [] (scope_demanded t root) &&
     Some? (scope_entries_checked t cache 0 certificate.binder_entries w)
   | None -> false)

let binder_scoped (certificate:binder_certificate) (cache:Z3ProofIndex.index_tree judgment) : bool =
  let n = L.length certificate.binder_entries in
  binder_scoped_within (binder_demand_limit n) (binder_work_limit n) certificate cache

let check_binder_with_context (skolems:list SK.definition) (assertions:list judgment)
                            (certificate:binder_certificate) (concl:judgment) : bool =
  match check_binder_entries skolems assertions certificate.binder_entries Z3ProofIndex.Empty 0 with
  | Some cache -> Z3ProofIndex.index_find cache certificate.binder_root = Some concl &&
                  binder_scoped certificate cache
  | None -> false

let check_binder_with_inputs (assertions:list judgment)
                            (certificate:binder_certificate) (concl:judgment) : bool =
  check_binder_with_context [] assertions certificate concl

let check_binder (certificate:binder_certificate) (concl:judgment) : bool =
  check_binder_with_inputs [] certificate concl

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

(* A finite-field lemma carrying its recorded ideal certificate; the
   certificate is replayed only after the exhaustive check. *)
let pac_lemma (kind:rule) (e:expr) : bool =
  match kind with
  | FiniteFieldPac c -> FP.check c e
  | _ -> false

let checked_theory_lemma (kind:rule) (concl:judgment) (facts:list judgment) : bool =
  match kind, proposition concl, propositions facts with
  | ArithmeticGomory c, Some e, Some es -> G.check c e es
  | Unverified "th-lemma", Some e, Some es
  | FiniteFieldPac _, Some e, Some es ->
    (es = [] && (array_lemma e || AR.triangle_equality e || ID.check e || FF.exhaustive_clause e ||
                 pac_lemma kind e)) ||
    TN.consequence es e || LP.implied_equality e es ||
    (Some? (LA.comparison e) && LP.inferred_bound e es) ||
    G.inferred_split e es || IC.inferred e es || (es = [] && BE.valid e)
  | Unverified tag, Some e, Some es ->
    tag = "arith/lp-integer-tighten" && LP.check_tightening e es
  | ArithmeticFarkas cs, Some e, Some es -> LA.check cs e es || LP.linear_identity e
  | _, _, _ -> false

let check_node_with_membership (skolems:list SK.definition) (strict:bool)
                               (assertions:list judgment) (contains:judgment -> bool)
                               (node:proof_node)
  : option (checked_fact & nat) =
  let facts = premise_judgments node.premises in
  let hyps = premise_hypotheses node.premises in
  let accept hs n = Some ({ conclusion = node.conclusion; hypotheses = hs }, n) in
  if not (well_formed node.conclusion && judgments_wf facts && scopes_wf node.premises) then None
  else
    match node.kind with
    | Asserted ->
      if facts = [] && Some? (proposition node.conclusion) && contains node.conclusion
      then accept [] 0 else None
    | DefAxiom ->
      if facts = [] && Some? (proposition node.conclusion)
      then accept [] (if check_step DefAxiom node.conclusion facts then 0 else 1)
      else None
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
    | Unverified _ | ArithmeticFarkas _ | ArithmeticGomory _ | FiniteFieldPac _ ->
      accept hyps (if checked_theory_lemma node.kind node.conclusion facts then 0 else 1)
    | RewriteRule | PullQuantifier | ElimUnused | PushQuantifier
    | DestructiveEquality | DestructiveEqualityResolution ->
      if facts = [] && Some? (relational node.conclusion)
      then accept hyps (if check_step node.kind node.conclusion facts then 0 else 1)
      else None
    | Skolemization ->
      if facts = [] && Observational? node.conclusion
      then accept [] (if skolem_step skolems node.conclusion facts then 0 else 1)
      else None
    | QuantifierIntroduction certificate ->
      if facts = [] && Some? (relational node.conclusion)
      then accept [] (if check_binder_with_context skolems assertions certificate node.conclusion then 0 else 1)
      else None
    | QuantifierInstantiation _ ->
      if facts = [] && Some? (proposition node.conclusion)
      then accept [] (if check_step node.kind node.conclusion facts then 0 else 1)
      else None
    | _ -> if check_step node.kind node.conclusion facts then accept hyps 0 else None

let check_node_with_context (skolems:list SK.definition) (strict:bool)
                            (assertions:list judgment) (node:proof_node)
  : option (checked_fact & nat) =
  check_node_with_membership skolems strict assertions (fun query -> L.mem query assertions) node

let check_node_with_inputs (strict:bool) (assertions:list judgment) (node:proof_node)
  : option (checked_fact & nat) =
  check_node_with_context [] strict assertions node

let lemma_check_node_membership (skolems:list SK.definition) (strict:bool) (assertions:list judgment)
                                (contains:judgment -> bool) (node:proof_node)
  : Lemma (requires contains node.conclusion == L.mem node.conclusion assertions)
          (ensures check_node_with_membership skolems strict assertions contains node ==
                   check_node_with_context skolems strict assertions node)
  = match node.kind with Asserted -> () | _ -> ()

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
  arithmetic_model i /\ array_model i /\ ite_sound i /\ xor_sound i /\ A.term_ite_sound i /\
  D.forall_sound i /\ Z3DistinctEmbed.distinct_sound i /\
  quant_extensional i /\
  constant_quantifier_model i /\
  Q.forall_elimination_model i /\
  QN.quantifier_model i /\
  LR.lambda_model i /\
  TN.normalization_model i /\
  (exists (nu:value -> FStar.Real.real). LE.numeric_model i nu) /\ ID.division_model i

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

let lemma_constant_quantifier_sound (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (requires model_sound i /\ constant_quantifier_rewrite a b)
          (ensures eval i a rho == eval i b rho)
  = match a with
    | Quantifier k bs s body ->
      let bodies (vs:list value{L.length vs = L.length bs})
        : Lemma (eval i body (shift vs rho) == eval i body rho) = () in
      FStar.Classical.forall_intro bodies;
      assert (i.interp_quant k bs (fun vs -> eval i body (shift vs rho)) ==
              i.interp_quant k bs (fun _ -> eval i body rho));
      assert (eval i body rho == VBool true \/ eval i body rho == VBool false);
      lemma_quantifier_constant i k bs (eval i body rho)
    | _ -> ()

let lemma_relational_value_sound (i:interpretation value) (rho:env value)
                                 (concl:judgment) (r:relation) (a b:expr)
  : Lemma (requires well_formed concl /\ relational concl = Some (r, a, b) /\
                    eval i a rho == eval i b rho)
          (ensures judgment_holds i rho concl)
  = match concl with
    | Equal _ _ | Observational _ _ -> ()
    | Holds _ -> ()

let lemma_relational_step_sound (i:interpretation value) (rho:env value)
                                (kind:rule) (concl:judgment) (facts:list judgment)
  : Lemma (requires model_sound i /\ well_formed concl /\ judgments_wf facts /\
                    judgments_hold i rho facts /\ relational_step kind concl facts)
          (ensures judgment_holds i rho concl)
  = match relational concl with
    | None -> ()
    | Some (r, a, b) ->
      (match kind with
       | PullQuantifier ->
         if QP.check a b then QP.lemma_check_sound i rho a b
         else if QR.equivalent 64 a b then QR.lemma_equivalent 64 i rho a b
         else TN.lemma_equivalent i rho a b
       | ElimUnused -> QR.lemma_equivalent 64 i rho a b
       | PushQuantifier -> QR.lemma_push_check i rho a b
       | DestructiveEquality | DestructiveEqualityResolution ->
         if QD.equivalent 64 a b then QD.lemma_equivalent_sound 64 a b i rho
         else DE.lemma_check i rho a b
       | RewriteRule | ApplyDefinition ->
         (if identity_rewrite a = Some b then lemma_identity_rewrite_sound i rho a b
         else if flatten_rewrite a = Some b then lemma_flatten_rewrite_sound i rho a b
         else if Z3DistinctAst.duplicate_rewrite a b then
           Z3DistinctEmbed.lemma_duplicate_rewrite_sound i rho a b
         else if Z3DistinctEmbed.expansion_rewrite a b then
           Z3DistinctEmbed.lemma_expansion_rewrite_sound i rho a b
         else if constant_quantifier_rewrite a b then lemma_constant_quantifier_sound i rho a b
         else if A.equivalent 64 a b then A.lemma_equivalent_sound 64 i rho a b
         else if AR.equivalent a b then AR.lemma_equivalent_with_numeric_model a b i rho
         else if AF.check a b then AF.lemma_check_sound a b i rho
         else if BX.check a b then BX.lemma_check_sound a b i rho
         else if QR.equivalent 64 a b then QR.lemma_equivalent 64 i rho a b
         else if LR.rewrite a b then LR.lemma_rewrite i rho a b
         else if CR.equivalent a b then CR.lemma_equivalent_sound i rho a b
         else if IR.equivalent a b then IR.lemma_equivalent_sound i rho a b
         else if ID.equivalent a b then ID.lemma_equivalent a b i rho
         else if ID.equivalent b a then ID.lemma_equivalent b a i rho
         else if QV.equivalent 64 a b then QV.lemma_equivalent_sound 64 a b i rho
         else if TN.equivalent a b then TN.lemma_equivalent i rho a b
         else if boolean_search a b then lemma_boolean_search_sound i rho a b
         else if BE.equivalent a b then BE.lemma_equivalent_sound a b i rho
         else BN.lemma_equivalent_sound a b i rho);
         lemma_relational_value_sound i rho concl r a b
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
         if a = b then () else (match a, b with
          | App f xs, App g ys ->
            lemma_fast_arguments_match r xs ys facts;
            lemma_arguments_sound i rho r xs ys facts
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
    lemma_legacy_canonical i;
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
          | DefinitionIntroduction, [] | DefAxiom, [] ->
            let target = Some?.v (proposition concl) in
            if D.tautology 128 target then D.lemma_tautology_sound 128 i rho target
            else TN.lemma_tautology i rho target
          | Unverified "th-lemma", _ ->
            TN.lemma_consequence i rho es (Some?.v (proposition concl))
          | QuantifierInstantiation args, [] ->
            Q.lemma_check_sound i rho args (Some?.v (proposition concl))
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

let lemma_binder_quantifier_sound (i:interpretation value) (rho:env value)
                                 (sorts:list sort) (concl:judgment) (facts:list judgment)
  : Lemma (requires model_sound i /\ well_formed concl /\ judgments_wf facts /\
                    (forall (sigma:env value). judgments_hold i sigma facts) /\
                    binder_quantifier_step sorts concl facts)
          (ensures judgment_holds i rho concl)
  = match relational concl, facts with
    | Some (r, Quantifier k bs s a, Quantifier k' bs' s' b), [j] ->
      let bodies (vs:list value{L.length vs = L.length bs})
        : Lemma (eval i a (shift vs rho) == eval i b (shift vs rho))
        = match edge r j with
          | Some (source, target) ->
            QR.lemma_equivalent 64 i (shift vs rho) a source;
            lemma_edge_values i (shift vs rho) r j source target;
            QR.lemma_equivalent 64 i (shift vs rho) target b
          | None -> () in
      FStar.Classical.forall_intro bodies
    | _, _ -> ()

let lemma_binder_negative_quantifier_sound (i:interpretation value) (rho:env value)
                                          (sorts:list sort) (concl:judgment)
                                          (facts:list judgment)
  : Lemma (requires model_sound i /\ well_formed concl /\ judgments_wf facts /\
                    (forall (sigma:env value). judgments_hold i sigma facts) /\
                    binder_negative_quantifier_step sorts concl facts)
          (ensures judgment_holds i rho concl)
  = match relational concl, facts with
    | Some (r, App n [Quantifier k bs s a], Quantifier k' bs' s' b), [j] ->
      let bodies (vs:list value{L.length vs = L.length bs})
        : Lemma (eval i (mk_not_expr a) (shift vs rho) == eval i b (shift vs rho))
        = match edge r j with
          | Some (source, target) ->
            QR.lemma_equivalent 64 i (shift vs rho) (mk_not_expr a) source;
            lemma_edge_values i (shift vs rho) r j source target;
            QR.lemma_equivalent 64 i (shift vs rho) target b
          | None -> () in
      FStar.Classical.forall_intro bodies;
      QN.lemma_duality i rho k bs a;
      assert (eval i (Quantifier (QN.dual k) bs bool_sort (mk_not_expr a)) rho ==
              eval i (Quantifier k' bs' s' b) rho)
    | _, _ -> ()

let rec lemma_premise_replacement_sound (i:interpretation value) (rho:env value)
                                        (r:relation) (e replacement:expr)
                                        (facts:list judgment)
  : Lemma (requires boolean_model i /\ not_sound i /\ judgments_wf facts /\ judgments_hold i rho facts /\
                    premise_replacement r e facts == Some replacement)
          (ensures eval i e rho == eval i replacement rho)
          (decreases facts)
  = match facts with
    | [] -> ()
    | j :: rest ->
      (match edge r j with
       | Some (a, b) ->
         if e = a then lemma_edge_values i rho r j a b
         else if negative_replacement e a b then (
           lemma_edge_values i rho r j a b;
           QN.lemma_not_truth i rho e;
           QN.lemma_not_truth i rho b;
           match eval i e rho, eval i b rho with VBool _, VBool _ -> () | _, _ -> ())
         else lemma_premise_replacement_sound i rho r e replacement rest
       | None -> lemma_premise_replacement_sound i rho r e replacement rest)

let rec lemma_replace_premises_sound (i:interpretation value) (rho:env value)
                                     (r:relation) (facts:list judgment) (e:expr)
  : Lemma (requires quant_extensional i /\ boolean_model i /\ not_sound i /\ judgments_wf facts /\
                    (forall (sigma:env value). judgments_hold i sigma facts))
          (ensures eval i (replace_premises r facts e) rho == eval i e rho)
          (decreases e)
  = match premise_replacement r e facts with
    | Some replacement -> lemma_premise_replacement_sound i rho r e replacement facts
    | None ->
      (match e with
       | App _ args -> lemma_replace_premise_args_sound i rho r facts args
       | Quantifier _ bs _ body ->
         let bodies (vs:list value{L.length vs = L.length bs})
           : Lemma (eval i (replace_premises r facts body) (shift vs rho) ==
                    eval i body (shift vs rho))
           = lemma_replace_premises_sound i (shift vs rho) r facts body in
         FStar.Classical.forall_intro bodies
       | _ -> ())

and lemma_replace_premise_args_sound (i:interpretation value) (rho:env value)
                                     (r:relation) (facts:list judgment) (args:list expr)
  : Lemma (requires quant_extensional i /\ boolean_model i /\ not_sound i /\ judgments_wf facts /\
                    (forall (sigma:env value). judgments_hold i sigma facts))
          (ensures eval_args i (replace_premise_args r facts args) rho == eval_args i args rho)
          (decreases args)
  = match args with
    | [] -> ()
    | a :: rest ->
      lemma_replace_premises_sound i rho r facts a;
      lemma_replace_premise_args_sound i rho r facts rest

let rec lemma_reverse_judgments_sound (i:interpretation value) (rho:env value)
                                      (facts:list judgment)
  : Lemma (requires judgments_wf facts /\ judgments_hold i rho facts)
          (ensures judgments_wf (reverse_judgments facts) /\
                   judgments_hold i rho (reverse_judgments facts))
          (decreases facts) =
  match facts with
  | [] -> ()
  | j :: rest ->
    lemma_reverse_judgments_sound i rho rest;
    (match j with Holds _ | Equal _ _ | Observational _ _ -> ())

let lemma_binder_boolean_sound (i:interpretation value) (rho:env value)
                              (negative:bool) (concl:judgment) (facts:list judgment)
  : Lemma (requires model_sound i /\ well_formed concl /\ judgments_wf facts /\
                    (forall (sigma:env value). judgments_hold i sigma facts) /\
                    binder_boolean_step negative concl facts)
          (ensures judgment_holds i rho concl)
  = match relational concl with
    | Some (r, a, b) ->
      if boolean_equiv 8 10 (replace_premises r facts a) b then (
        lemma_replace_premises_sound i rho r facts a;
        lemma_boolean_equiv_sound 8 10 i rho (replace_premises r facts a) b)
      else if boolean_equiv 8 10 a (replace_premises r (reverse_judgments facts) b) then (
        let reversed (sigma:env value)
          : Lemma (judgments_hold i sigma (reverse_judgments facts))
          = lemma_reverse_judgments_sound i sigma facts in
        FStar.Classical.forall_intro reversed;
        lemma_reverse_judgments_sound i rho facts;
        lemma_replace_premises_sound i rho r (reverse_judgments facts) b;
        lemma_boolean_equiv_sound 8 10 i rho a (replace_premises r (reverse_judgments facts) b))
      else (
        lemma_replace_premises_sound i rho r facts a;
        if QR.equivalent 64 (replace_premises r facts a) b
        then QR.lemma_equivalent 64 i rho (replace_premises r facts a) b
        else TN.lemma_equivalent i rho (replace_premises r facts a) b)
    | None -> ()

let lemma_binder_step_sound (i:interpretation value) (rho:env value)
                           (e:binder_entry) (concl:judgment) (facts:list judgment)
  : Lemma (requires model_sound i /\
                    (forall (sigma:env value). judgments_hold i sigma facts) /\
                    binder_step e concl facts)
          (ensures judgment_holds i rho concl)
  = if e.binder_name = "quant-intro" then
      match e.binder_sorts with
      | Some sorts -> lemma_binder_quantifier_sound i rho sorts concl facts
      | None -> ()
    else if e.binder_name = "nnf-pos" || e.binder_name = "nnf-neg" then
      let negative = e.binder_name = "nnf-neg" in
      match e.binder_sorts with
      | Some sorts ->
        if negative then lemma_binder_negative_quantifier_sound i rho sorts concl facts
        else lemma_binder_quantifier_sound i rho sorts concl facts
      | None -> lemma_binder_boolean_sound i rho negative concl facts
    else match basic_rule_of_name e.binder_name with
    | Some kind -> lemma_check_step_sound i rho kind concl facts
    | None -> ()

let rec lemma_judgment_member (i:interpretation value) (rho:env value)
                              (js:list judgment) (j:judgment)
  : Lemma (requires judgments_hold i rho js /\ L.memP j js)
          (ensures judgment_holds i rho j)
          (decreases js)
  = match js with
    | [] -> ()
    | h :: rest -> if h = j then () else lemma_judgment_member i rho rest j

let lemma_binder_step_with_inputs_sound (i:interpretation value) (rho sigma:env value)
                                       (assertions:list judgment)
                                       (e:binder_entry) (concl:judgment) (facts:list judgment)
  : Lemma (requires model_sound i /\ judgments_hold i rho assertions /\
                    classify_fact e.binder_formula == Some concl /\
                    (forall (eta:env value). judgments_hold i eta facts) /\
                    binder_step_with_inputs assertions e concl facts)
          (ensures judgment_holds i sigma concl) =
  if binder_step e concl facts then lemma_binder_step_sound i sigma e concl facts
  else (
    FStar.List.Tot.Properties.mem_memP concl assertions;
    lemma_judgment_member i rho assertions concl;
    Q.lemma_scoped_closed [] e.binder_formula;
    lemma_closed_eval_env_irrelevant i e.binder_formula 0 rho sigma;
    assert (proposition concl == Some e.binder_formula);
    lemma_proposition_sound i rho concl;
    lemma_proposition_sound i sigma concl)

let lemma_skolem_step_sound (skolems:list SK.definition) (i:interpretation value)
                            (rho:env value) (concl:judgment) (facts:list judgment)
  : Lemma (requires model_sound i /\ SK.context_model skolems i /\ skolem_step skolems concl facts)
          (ensures judgment_holds i rho concl) =
  match concl with
  | Observational a b -> SK.lemma_check_sound skolems a b i rho
  | _ -> ()

let lemma_binder_step_with_context_sound (skolems:list SK.definition)
                                         (i:interpretation value) (rho sigma:env value)
                                         (assertions:list judgment)
                                         (e:binder_entry) (concl:judgment) (facts:list judgment)
  : Lemma (requires model_sound i /\ SK.context_model skolems i /\ judgments_hold i rho assertions /\
                    classify_fact e.binder_formula == Some concl /\
                    (forall (eta:env value). judgments_hold i eta facts) /\
                    binder_step_with_context skolems assertions e concl facts)
          (ensures judgment_holds i sigma concl) =
  if binder_step_with_inputs assertions e concl facts
  then lemma_binder_step_with_inputs_sound i rho sigma assertions e concl facts
  else lemma_skolem_step_sound skolems i sigma concl facts

let binder_cache_sound (i:interpretation value) (cache:Z3ProofIndex.index_tree judgment) : prop =
  forall (key:int) (j:judgment) (rho:env value).
    Z3ProofIndex.index_find cache key == Some j ==> judgment_holds i rho j

let rec lemma_binder_premises (i:interpretation value) (rho:env value)
                              (cache:Z3ProofIndex.index_tree judgment)
                              (ids:list int) (facts:list judgment)
  : Lemma (requires binder_cache_sound i cache /\
                    opt_map (Z3ProofIndex.index_find cache) ids == Some facts)
          (ensures judgments_hold i rho facts)
          (decreases ids)
  = match ids, facts with
    | _ :: rest, _ :: remaining -> lemma_binder_premises i rho cache rest remaining
    | _, _ -> ()

let lemma_binder_cache_put (i:interpretation value) (cache:Z3ProofIndex.index_tree judgment)
                           (next:nat) (concl:judgment)
  : Lemma (requires binder_cache_sound i cache /\
                    (forall (rho:env value). judgment_holds i rho concl))
          (ensures binder_cache_sound i (Z3ProofIndex.index_put cache next concl))
  = let at (key:int) (j:judgment) (rho:env value)
      : Lemma (requires Z3ProofIndex.index_find
                          (Z3ProofIndex.index_put cache next concl) key == Some j)
              (ensures judgment_holds i rho j)
      = if key < 0 then () else Z3ProofIndex.lemma_index_put cache next concl key in
    FStar.Classical.forall_intro
      (fun key -> FStar.Classical.forall_intro
        (fun j -> FStar.Classical.forall_intro
          (FStar.Classical.move_requires (at key j))))

let rec lemma_binder_entries_sound (skolems:list SK.definition)
                                   (i:interpretation value) (rho:env value)
                                   (assertions:list judgment) (entries:list binder_entry)
                                   (cache:Z3ProofIndex.index_tree judgment) (next:nat)
  : Lemma (requires model_sound i /\ SK.context_model skolems i /\
                    judgments_hold i rho assertions /\ binder_cache_sound i cache /\
                    Some? (check_binder_entries skolems assertions entries cache next))
          (ensures binder_cache_sound i (Some?.v (check_binder_entries skolems assertions entries cache next)))
          (decreases entries)
  = match entries with
    | [] -> ()
    | e :: rest ->
      let concl = Some?.v (classify_fact e.binder_formula) in
      let facts = Some?.v (opt_map (Z3ProofIndex.index_find cache) e.binder_premises) in
      let premise_env (rho:env value) : Lemma (judgments_hold i rho facts)
        = lemma_binder_premises i rho cache e.binder_premises facts in
      FStar.Classical.forall_intro premise_env;
      let conclusion_env (sigma:env value) : Lemma (judgment_holds i sigma concl)
        = lemma_binder_step_with_context_sound skolems i rho sigma assertions e concl facts in
      FStar.Classical.forall_intro conclusion_env;
      lemma_binder_cache_put i cache next concl;
      lemma_binder_entries_sound skolems i rho assertions rest
        (Z3ProofIndex.index_put cache next concl) (next + 1)

let lemma_check_binder_with_context_sound (skolems:list SK.definition)
                                         (i:interpretation value) (rho:env value)
                                         (assertions:list judgment)
                                         (certificate:binder_certificate) (concl:judgment)
  : Lemma (requires model_sound i /\ SK.context_model skolems i /\ judgments_hold i rho assertions /\
                    check_binder_with_context skolems assertions certificate concl)
          (ensures judgment_holds i rho concl)
  = assert (binder_cache_sound i Z3ProofIndex.Empty);
    lemma_binder_entries_sound skolems i rho assertions certificate.binder_entries Z3ProofIndex.Empty 0

let lemma_check_binder_with_inputs_sound (i:interpretation value) (rho:env value)
                                         (assertions:list judgment)
                                         (certificate:binder_certificate) (concl:judgment)
  : Lemma (requires model_sound i /\ judgments_hold i rho assertions /\
                    check_binder_with_inputs assertions certificate concl)
          (ensures judgment_holds i rho concl)
  = lemma_check_binder_with_context_sound [] i rho assertions certificate concl

let lemma_check_binder_sound (i:interpretation value) (rho:env value)
                             (certificate:binder_certificate) (concl:judgment)
  : Lemma (requires model_sound i /\ check_binder certificate concl)
          (ensures judgment_holds i rho concl)
  = lemma_check_binder_with_inputs_sound i rho [] certificate concl

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
    | App f [] -> (match e with | App g [] -> () | _ -> ())
    | App f [a] ->
      if C.canonical_not f && a = e then (
        lemma_not_relates i rho f a;
        match eval i e rho with | VBool _ -> () | _ -> ())
      else
        (match e with
         | App g [b] ->
           if C.canonical_not g && b = h then (
             lemma_not_relates i rho g b;
             match eval i h rho with | VBool _ -> () | _ -> ())
           else ()
         | _ -> ())
    | _ ->
      (match e with
       | App g [b] ->
         if C.canonical_not g && b = h then (
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

(* Kept out of lemma_check_node_sound: only the existing model contract is used. *)
let lemma_pac_lemma_sound (i:interpretation value) (rho:env value) (kind:rule) (e:expr)
  : Lemma (requires model_sound i /\ pac_lemma kind e) (ensures lit_true i rho e)
  = match kind with FiniteFieldPac c -> FP.lemma_check_sound i rho c e

let node_obligation (skolems:list SK.definition) (i:interpretation value) (rho:env value) (strict:bool)
                    (assertions:list judgment) (node:proof_node) : prop =
  match node.kind with
  | DefAxiom ->
    not (check_step DefAxiom node.conclusion (premise_judgments node.premises)) ==>
    judgment_holds i rho node.conclusion
  | RewriteRule | PullQuantifier | ElimUnused | PushQuantifier | DestructiveEquality
  | DestructiveEqualityResolution | QuantifierInstantiation _ ->
    not (check_step node.kind node.conclusion (premise_judgments node.premises)) ==>
    (conj_holds i rho (premise_hypotheses node.premises) ==>
     judgment_holds i rho node.conclusion)
  | Unverified _ | ArithmeticFarkas _ | ArithmeticGomory _ | FiniteFieldPac _ ->
    not (checked_theory_lemma node.kind node.conclusion (premise_judgments node.premises)) ==>
    (conj_holds i rho (premise_hypotheses node.premises) ==>
     judgment_holds i rho node.conclusion)
  | QuantifierIntroduction certificate ->
    not (check_binder_with_context skolems assertions certificate node.conclusion) ==>
    judgment_holds i rho node.conclusion
  | Skolemization ->
    not (skolem_step skolems node.conclusion (premise_judgments node.premises)) ==>
    judgment_holds i rho node.conclusion
  | _ -> True

let lemma_check_node_sound (skolems:list SK.definition) (i:interpretation value) (rho:env value)
                           (strict:bool) (assertions:list judgment) (node:proof_node)
  : Lemma (requires model_sound i /\ SK.context_model skolems i /\ judgments_hold i rho assertions /\
                    premises_sound i rho node.premises /\ node_obligation skolems i rho strict assertions node /\
                    Some? (check_node_with_context skolems strict assertions node))
          (ensures scoped_holds i rho (fst (Some?.v (check_node_with_context skolems strict assertions node))))
  = let aux (_:squash (conj_holds i rho
                       (fst (Some?.v (check_node_with_context skolems strict assertions node))).hypotheses))
      : Lemma (judgment_holds i rho node.conclusion) =
      match node.kind with
      | Asserted ->
        FStar.List.Tot.Properties.mem_memP node.conclusion assertions;
        lemma_judgment_member i rho assertions node.conclusion
      | DefAxiom ->
        if check_step DefAxiom node.conclusion (premise_judgments node.premises)
        then lemma_check_step_sound i rho DefAxiom node.conclusion (premise_judgments node.premises)
      | Hypothesis -> lemma_proposition_sound i rho node.conclusion
      | Unverified _ | ArithmeticFarkas _ | ArithmeticGomory _ | FiniteFieldPac _ ->
        if checked_theory_lemma node.kind node.conclusion (premise_judgments node.premises) then (
          lemma_proposition_sound i rho node.conclusion;
          lemma_premises_sound i rho node.premises;
          lemma_propositions_sound i rho (premise_judgments node.premises);
          match proposition node.conclusion with
          | Some e ->
            (match node.kind with
             | ArithmeticGomory c ->
               G.lemma_check_sound c e
                 (Some?.v (propositions (premise_judgments node.premises))) i rho
             | ArithmeticFarkas cs ->
               if LA.check cs e (Some?.v (propositions (premise_judgments node.premises)))
               then LE.lemma_check_with_numeric_model cs e
                      (Some?.v (propositions (premise_judgments node.premises))) i rho
               else LP.lemma_linear_identity_sound e i rho
             | Unverified "arith/lp-integer-tighten" ->
               LP.lemma_tightening_sound e (Some?.v (propositions (premise_judgments node.premises))) i rho
             | _ ->
               if array_lemma e then lemma_array_lemma_sound i rho e
               else if AR.triangle_equality e then AR.lemma_triangle_with_numeric_model e i rho
               else if ID.check e then ID.lemma_check e i rho
               else if FF.exhaustive_clause e then FF.lemma_exhaustive_clause_sound i rho e
               else if pac_lemma node.kind e then lemma_pac_lemma_sound i rho node.kind e
               else
                 let es = Some?.v (propositions (premise_judgments node.premises)) in
                 if TN.consequence es e then TN.lemma_consequence i rho es e
                 else if LP.implied_equality e es then LP.lemma_implied_equality e es i rho
                 else if Some? (LA.comparison e) && LP.inferred_bound e es
                 then LP.lemma_inferred_bound e es i rho
                 else if G.inferred_split e es then G.lemma_inferred_split_sound e es i rho
                 else if IC.inferred e es then IC.lemma_inferred_sound e es i rho
                 else BE.lemma_valid_sound e i rho)
          | None -> ())
      | RewriteRule | PullQuantifier | ElimUnused | PushQuantifier | DestructiveEquality
      | DestructiveEqualityResolution | QuantifierInstantiation _ ->
        if check_step node.kind node.conclusion (premise_judgments node.premises)
        then lemma_check_step_sound i rho node.kind node.conclusion (premise_judgments node.premises)
      | QuantifierIntroduction certificate ->
        if check_binder_with_context skolems assertions certificate node.conclusion
        then lemma_check_binder_with_context_sound skolems i rho assertions certificate node.conclusion
      | Skolemization ->
        if skolem_step skolems node.conclusion (premise_judgments node.premises)
        then lemma_skolem_step_sound skolems i rho node.conclusion (premise_judgments node.premises)
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

let lemma_check_node_membership_sound (skolems:list SK.definition)
                                      (i:interpretation value) (rho:env value)
                                      (strict:bool) (assertions:list judgment)
                                      (contains:judgment -> bool) (node:proof_node)
  : Lemma (requires model_sound i /\ SK.context_model skolems i /\ judgments_hold i rho assertions /\
                    contains node.conclusion == L.mem node.conclusion assertions /\
                    premises_sound i rho node.premises /\ node_obligation skolems i rho strict assertions node /\
                    Some? (check_node_with_membership skolems strict assertions contains node))
          (ensures scoped_holds i rho
            (fst (Some?.v (check_node_with_membership skolems strict assertions contains node))))
  = lemma_check_node_membership skolems strict assertions contains node;
    lemma_check_node_sound skolems i rho strict assertions node

let lemma_obligation_free_node_sound (skolems:list SK.definition) (i:interpretation value) (rho:env value)
                                     (strict:bool) (assertions:list judgment) (node:proof_node)
  : Lemma (requires model_sound i /\ SK.context_model skolems i /\ judgments_hold i rho assertions /\
                    premises_sound i rho node.premises /\
                    Some? (check_node_with_context skolems strict assertions node) /\
                    snd (Some?.v (check_node_with_context skolems strict assertions node)) == 0)
          (ensures scoped_holds i rho (fst (Some?.v (check_node_with_context skolems strict assertions node))))
  = lemma_check_node_sound skolems i rho strict assertions node

let lemma_choice_obligation_free_node_sound (choice:SK.hilbert_choice)
                                            (skolems:list SK.definition)
                                            (base:interpretation value) (rho:env value)
                                            (strict:bool) (assertions:list judgment) (node:proof_node)
  : Lemma (requires SK.ordered_context skolems /\ quant_extensional base /\
                    model_sound (SK.build_interpretation choice skolems base) /\
                    judgments_hold (SK.build_interpretation choice skolems base) rho assertions /\
                    premises_sound (SK.build_interpretation choice skolems base) rho node.premises /\
                    Some? (check_node_with_context skolems strict assertions node) /\
                    snd (Some?.v (check_node_with_context skolems strict assertions node)) == 0)
          (ensures scoped_holds (SK.build_interpretation choice skolems base) rho
            (fst (Some?.v (check_node_with_context skolems strict assertions node)))) =
  SK.lemma_build_context choice skolems base;
  lemma_obligation_free_node_sound skolems (SK.build_interpretation choice skolems base)
    rho strict assertions node
