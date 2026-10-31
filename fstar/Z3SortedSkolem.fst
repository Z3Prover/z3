module Z3SortedSkolem

open Z3AstTheory
open FStar.List.Tot
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module I = Z3SortedInteger
module Q = Z3SortedQuantifier
module SK = Z3Skolemization
module D = Z3Definitions
module R = Z3ResolutionProofTheory
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties

let constant_safe (s:S.checked_schema) (f:func_decl) : bool =
  f.domain = [] && f.interp = None && f.int_params = [] &&
  not (L.mem f (S.signature s)) && T.classify f = T.Other &&
  I.classify f = I.Other && S.find_recognizer f s.cases = None &&
  S.find_accessor f s.cases = None

let rec safe_witnesses (s:S.checked_schema) (ws:list SK.witness) : Tot bool (decreases ws) =
  match ws with [] -> true | (_, f) :: rest -> constant_safe s f && safe_witnesses s rest

let variables (d:SK.definition) : list nat = L.map fst d.witnesses
let terms (d:SK.definition) : list expr = L.map (fun (_, f) -> App f []) d.witnesses

let eligible (s:S.checked_schema) (d:SK.definition) : bool =
  SK.valid d && d.dependencies = [] && safe_witnesses s d.witnesses &&
  D.scoped (L.rev d.bound_sorts) d.body &&
  (match SK.instantiation d, SK.substitute 0 (L.length d.bound_sorts) [] d.witnesses d.body with
   | Some b, Some target ->
     D.scoped [] b && D.scoped [] target &&
     SK.definition_of (SK.source d) b = Some d &&
     D.instantiate 0 (variables d) (terms d) d.body = Some target
   | _, _ -> false)

type definition (s:S.checked_schema) = d:SK.definition{eligible s d}

let definition_of (s:S.checked_schema) (a b:expr) : option (definition s) =
  match SK.definition_of a b with
  | Some d ->
    if eligible s d && D.scoped [] a && D.scoped [] b
    then Some d else None
  | None -> None

noeq
type hilbert_choice (base:sort -> Type0) (s:S.checked_schema) = {
  epsilon: ss:list sort ->
    predicate:(V.arguments base (S.signature s) ss -> prop) ->
    Tot (vs:V.arguments base (S.signature s) ss{
      (exists (ws:V.arguments base (S.signature s) ss). predicate ws) ==> predicate vs});
}

let rec tuple_at (#base:sort -> Type0) (sigma:V.signature) (ss:list sort)
                 (vs:V.arguments base sigma ss) (n:nat{n < L.length ss})
  : Tot (V.value base sigma (L.index ss n)) (decreases ss) =
  match ss, vs with
  | _ :: rest, v :: tail -> if n = 0 then v else tuple_at sigma rest tail (n - 1)
  | _, _ -> FStar.Pervasives.false_elim ()

let rec lemma_component (ss:list sort) (ws:list SK.witness) (f:func_decl) (n:nat)
  : Lemma (requires SK.valid_witnesses ss [] ws /\ SK.component f ws == Some n)
          (ensures n < L.length ss /\ f.range == L.index ss n /\ f.domain == [] /\ f.interp == None)
          (decreases ws) =
  match ws with
  | [] -> ()
  | (_, g) :: rest -> if f <> g then lemma_component ss rest f n

let override (#base:sort -> Type0) (s:S.checked_schema) (d:definition s)
             (vs:V.arguments base (S.signature s) (L.rev d.bound_sorts))
             (other:V.interpretation base (S.signature s))
  : V.interpretation base (S.signature s) = {
  application = (fun f args ->
    match SK.component f d.witnesses with
    | Some n ->
      lemma_component (L.rev d.bound_sorts) d.witnesses f n;
      V.lemma_sort_eq f.range (L.index (L.rev d.bound_sorts) n);
      tuple_at (S.signature s) (L.rev d.bound_sorts) vs n
    | None -> other.application f args);
  quantification = other.quantification;
}

let goal (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
         (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
         (d:definition s) (vs:V.arguments base (S.signature s) (L.rev d.bound_sorts)) : prop =
  T.truth_at s bc eq other (L.rev d.bound_sorts)
    (V.extend (S.signature s) [] (L.rev d.bound_sorts) vs (T.empty_environment (S.signature s)))
    d.body == not d.negative

let selected (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
             (eq:T.scalar_model base) (choice:hilbert_choice base s)
             (other:V.interpretation base (S.signature s)) (d:definition s)
  : vs:V.arguments base (S.signature s) (L.rev d.bound_sorts){
      (exists (ws:V.arguments base (S.signature s) (L.rev d.bound_sorts)).
        goal s bc eq other d ws) ==> goal s bc eq other d vs} =
  choice.epsilon (L.rev d.bound_sorts) (goal s bc eq other d)

let exists_model (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                 (other:V.interpretation base (S.signature s)) : prop =
  forall (bound:list sort)
         (body:V.arguments base (S.signature s) (L.rev bound) ->
               V.value base (S.signature s) bool_sort).
    T.truth_value s bc (other.quantification Exists_k bound bool_sort body) <==>
    (exists (vs:V.arguments base (S.signature s) (L.rev bound)).
       T.truth_value s bc (body vs))

let lemma_application_fresh (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                            (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                            (d:definition s) (vs:V.arguments base (S.signature s) (L.rev d.bound_sorts))
                            (f:func_decl) (args:V.arguments base (S.signature s) f.domain)
  : Lemma (requires SK.component f d.witnesses == None)
          (ensures T.application s bc eq other f args ==
                   T.application s bc eq (override s d vs other) f args) =
  ()

let rec lemma_fresh (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                    (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                    (d:definition s) (vs:V.arguments base (S.signature s) (L.rev d.bound_sorts))
                    (scope:list sort) (rho:V.environment base (S.signature s) scope) (e:expr)
  : Lemma (requires D.scoped scope e /\ SK.fresh d.witnesses e)
          (ensures T.evaluate_at s bc eq other scope rho e ==
                   T.evaluate_at s bc eq (override s d vs other) scope rho e)
          (decreases e) =
  match e with
  | Var _ _ -> ()
  | App f args ->
    lemma_fresh_args s bc eq other d vs scope rho args f.domain;
    lemma_application_fresh s bc eq other d vs f
      (V.evaluate_args (S.signature s) (T.interpretation s bc eq other) scope rho args f.domain)
  | Quantifier k bound _ body ->
    let pointwise (ws:V.arguments base (S.signature s) (L.rev bound))
      : Lemma (
          T.evaluate_at s bc eq other (L.rev bound @ scope)
            (V.extend (S.signature s) scope (L.rev bound) ws rho) body ==
          T.evaluate_at s bc eq (override s d vs other) (L.rev bound @ scope)
            (V.extend (S.signature s) scope (L.rev bound) ws rho) body) =
      lemma_fresh s bc eq other d vs (L.rev bound @ scope)
        (V.extend (S.signature s) scope (L.rev bound) ws rho) body in
    FStar.Classical.forall_intro pointwise;
    let left = V.evaluate_body (S.signature s) (T.interpretation s bc eq other) scope rho bound body in
    let right = V.evaluate_body (S.signature s) (T.interpretation s bc eq (override s d vs other))
      scope rho bound body in
    assert (FStar.FunctionalExtensionality.feq left right);
    FStar.FunctionalExtensionality.extensionality
      (V.arguments base (S.signature s) (L.rev bound)) (fun _ -> V.tree base) left right

and lemma_fresh_args (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                    (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                    (d:definition s) (vs:V.arguments base (S.signature s) (L.rev d.bound_sorts))
                    (scope:list sort) (rho:V.environment base (S.signature s) scope)
                    (args:list expr) (ss:list sort)
  : Lemma (requires D.scoped_args scope args /\ sorts_match args ss /\ SK.fresh_args d.witnesses args)
          (ensures V.evaluate_args (S.signature s) (T.interpretation s bc eq other) scope rho args ss ==
                   V.evaluate_args (S.signature s) (T.interpretation s bc eq (override s d vs other))
                     scope rho args ss)
          (decreases args) =
  match args, ss with
  | e :: rest, _ :: tail ->
    lemma_fresh s bc eq other d vs scope rho e;
    lemma_fresh_args s bc eq other d vs scope rho rest tail
  | _, _ -> ()

let rec lemma_terms (s:S.checked_schema) (ws:list SK.witness)
  : Lemma (requires safe_witnesses s ws)
          (ensures D.scoped_args [] (L.map (fun (_, f) -> App f []) ws))
          (decreases ws) =
  match ws with [] -> () | _ :: rest -> lemma_terms s rest

let rec lemma_argument (ws:list SK.witness) (n:nat) (term:expr)
  : Lemma (requires D.argument n (L.map fst ws) (L.map (fun (_, f) -> App f []) ws) == Some term)
          (ensures exists (f:func_decl). term == App f [] /\ SK.lookup n ws == Some f)
          (decreases ws) =
  match ws with
  | [] -> ()
  | (m, _) :: rest -> if n <> m then lemma_argument rest n term

let rec lemma_lookup_safe (s:S.checked_schema) (ws:list SK.witness) (n:nat) (f:func_decl)
  : Lemma (requires safe_witnesses s ws /\ SK.lookup n ws == Some f)
          (ensures constant_safe s f)
          (decreases ws) =
  match ws with [] -> () | (m, _) :: rest -> if n <> m then lemma_lookup_safe s rest n f

let rec lemma_extend_at (#base:sort -> Type0) (sigma:V.signature) (ss:list sort)
                        (vs:V.arguments base sigma ss) (n:nat{n < L.length ss})
  : Lemma (V.extend sigma [] ss vs (T.empty_environment sigma) n == tuple_at sigma ss vs n)
          (decreases ss) =
  match ss, vs with
  | _ :: rest, _ :: tail -> if n > 0 then lemma_extend_at sigma rest tail (n - 1)
  | _, _ -> ()

let lemma_instance_environment (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                               (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                               (d:definition s) (vs:V.arguments base (S.signature s) (L.rev d.bound_sorts))
  : Lemma (Q.instance_environments (S.signature s) (T.interpretation s bc eq (override s d vs other))
            [] (L.rev d.bound_sorts) (variables d) (terms d)
            (V.extend (S.signature s) [] (L.rev d.bound_sorts) vs (T.empty_environment (S.signature s)))
            (T.empty_environment (S.signature s)) (T.empty_environment (S.signature s))) =
  LP.append_length (L.rev d.bound_sorts) [];
  let at (n:nat{n < L.length ([] @ L.rev d.bound_sorts)})
    : Lemma (
        forall (term:expr{D.scoped [] term}).
          D.argument n (variables d) (terms d) == Some term ==>
          V.extend (S.signature s) [] (L.rev d.bound_sorts) vs
            (T.empty_environment (S.signature s)) n ==
          T.evaluate s bc eq (override s d vs other) term) =
    let term_at (term:expr{D.scoped [] term})
      : Lemma (D.argument n (variables d) (terms d) == Some term ==>
                       V.extend (S.signature s) [] (L.rev d.bound_sorts) vs
                         (T.empty_environment (S.signature s)) n ==
                       T.evaluate s bc eq (override s d vs other) term) =
      if D.argument n (variables d) (terms d) = Some term then (
      lemma_argument d.witnesses n term;
      let use (f:func_decl)
        : Lemma ((term == App f [] /\ SK.lookup n d.witnesses == Some f) ==>
                         V.extend (S.signature s) [] (L.rev d.bound_sorts) vs
                           (T.empty_environment (S.signature s)) n ==
                         T.evaluate s bc eq (override s d vs other) term) =
        if term = App f [] && SK.lookup n d.witnesses = Some f then (
        SK.lemma_witness_lookup (L.rev d.bound_sorts) [] d.witnesses n f;
        lemma_component (L.rev d.bound_sorts) d.witnesses f n;
        lemma_lookup_safe s d.witnesses n f;
        lemma_extend_at (S.signature s) (L.rev d.bound_sorts) vs n) in
      FStar.Classical.forall_intro use) in
    FStar.Classical.forall_intro term_at in
  FStar.Classical.forall_intro at

let lemma_instance_value (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                         (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                         (d:definition s) (vs:V.arguments base (S.signature s) (L.rev d.bound_sorts))
                         (target:expr)
  : Lemma (requires D.scoped [] target /\
                    D.instantiate 0 (variables d) (terms d) d.body == Some target)
          (ensures T.evaluate_at s bc eq (override s d vs other) (L.rev d.bound_sorts)
                     (V.extend (S.signature s) [] (L.rev d.bound_sorts) vs
                       (T.empty_environment (S.signature s))) d.body ==
                   T.evaluate s bc eq (override s d vs other) target) =
  lemma_terms s d.witnesses;
  let i = T.interpretation s bc eq (override s d vs other) in
  let empty = T.empty_environment (S.signature s) in
  Q.lemma_closed_values (S.signature s) i empty (terms d);
  lemma_instance_environment s bc eq other d vs;
  Q.lemma_instantiate (S.signature s) i [] (L.rev d.bound_sorts) (variables d) (terms d)
    (V.extend (S.signature s) [] (L.rev d.bound_sorts) vs empty) empty empty d.body target

let lemma_negate (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                 (eq:T.scalar_model base) (other:V.interpretation base (S.signature s)) (e:expr)
  : Lemma (requires D.scoped [] e /\ get_sort e == bool_sort)
          (ensures D.scoped [] (SK.negate e) /\ get_sort (SK.negate e) == bool_sort /\
                   T.truth s bc eq other (SK.negate e) == not (T.truth s bc eq other e)) =
  match e with
  | App f [a] ->
    if f = R.not_decl then T.lemma_evaluate_core s bc eq other f [a]
    else T.lemma_evaluate_core s bc eq other R.not_decl [e]
  | _ -> T.lemma_evaluate_core s bc eq other R.not_decl [e]

let lemma_source_goal (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                      (d:definition s)
  : Lemma (requires Q.forall_model s bc other /\ exists_model s bc other)
          (ensures T.truth s bc eq other (SK.source d) <==>
            (exists (vs:V.arguments base (S.signature s) (L.rev d.bound_sorts)).
              goal s bc eq other d vs)) =
  let kind = if d.negative then Forall_k else Exists_k in
  let q = Quantifier kind d.bound_sorts bool_sort d.body in
  let f = V.typed_body (S.signature s) d.bound_sorts bool_sort
    (V.evaluate_body (S.signature s) (T.interpretation s bc eq other)
      [] (T.empty_environment (S.signature s)) d.bound_sorts d.body) in
  if d.negative then (
    Q.lemma_forall_truth s bc eq other [] (T.empty_environment (S.signature s)) d.bound_sorts d.body;
    T.lemma_evaluate_core s bc eq other R.not_decl [q])
  else
    assert (T.truth_value s bc (other.quantification Exists_k d.bound_sorts bool_sort f) <==>
      (exists (vs:V.arguments base (S.signature s) (L.rev d.bound_sorts)).
        T.truth_value s bc (f vs)))

let lemma_definition_parts (s:S.checked_schema) (a b:expr) (d:definition s)
  : Lemma (requires definition_of s a b == Some d)
          (ensures SK.source d == a /\ SK.instantiation d == Some b /\
                   D.scoped [] a /\ D.scoped [] b /\
                   get_sort a == bool_sort /\ get_sort b == bool_sort /\
                   Some? (SK.substitute 0 (L.length d.bound_sorts) [] d.witnesses d.body) /\
                   D.instantiate 0 (variables d) (terms d) d.body ==
                     SK.substitute 0 (L.length d.bound_sorts) [] d.witnesses d.body) =
  let target = Some?.v (SK.substitute 0 (L.length d.bound_sorts) [] d.witnesses d.body) in
  SK.lemma_substitute_sort 0 (L.length d.bound_sorts) [] d.witnesses d.body target

let lemma_epsilon_instance (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (eq:T.scalar_model base) (choice:hilbert_choice base s)
                          (other:V.interpretation base (S.signature s))
                          (a b:expr) (d:definition s)
  : Lemma (requires definition_of s a b == Some d /\ Q.forall_model s bc other /\ exists_model s bc other)
          (ensures
            (let vs = selected s bc eq choice other d in
             T.truth s bc eq other a == T.truth s bc eq (override s d vs other) b)) =
  lemma_definition_parts s a b d;
  let vs = selected s bc eq choice other d in
  let target = Some?.v (SK.substitute 0 (L.length d.bound_sorts) [] d.witnesses d.body) in
  SK.lemma_substitute_sort 0 (L.length d.bound_sorts) [] d.witnesses d.body target;
  if d.negative then (
    lemma_negate s bc eq (override s d vs other) target)
  else ();
  lemma_source_goal s bc eq other d;
  lemma_instance_value s bc eq other d vs target;
  lemma_fresh s bc eq other d vs (L.rev d.bound_sorts)
    (V.extend (S.signature s) [] (L.rev d.bound_sorts) vs
      (T.empty_environment (S.signature s))) d.body;
  if T.truth_at s bc eq other (L.rev d.bound_sorts)
       (V.extend (S.signature s) [] (L.rev d.bound_sorts) vs
         (T.empty_environment (S.signature s))) d.body = not d.negative then
    FStar.Classical.exists_intro (goal s bc eq other d) vs

let rec lemma_disjoint_lookup (newer older:list SK.witness) (n:nat) (f:func_decl)
  : Lemma (requires SK.disjoint newer older /\ SK.lookup n older == Some f)
          (ensures SK.component f newer == None)
          (decreases older) =
  match older with [] -> () | (m, _) :: rest -> if n <> m then lemma_disjoint_lookup newer rest n f

let rec lemma_interpreted_fresh (ss:list sort) (ws:list SK.witness) (f:func_decl)
  : Lemma (requires SK.valid_witnesses ss [] ws /\ f.interp <> None)
          (ensures SK.component f ws == None)
          (decreases ws) =
  match ws with [] -> () | _ :: rest -> lemma_interpreted_fresh ss rest f

let rec lemma_substitute_fresh (newer older:list SK.witness) (depth count:nat) (e target:expr)
  : Lemma (requires SK.fresh newer e /\ SK.disjoint newer older /\
                    SK.substitute depth count [] older e == Some target)
          (ensures SK.fresh newer target)
          (decreases e) =
  match e with
  | Var n _ ->
    if n >= depth && n < depth + count then
      lemma_disjoint_lookup newer older (n - depth) (Some?.v (SK.lookup (n - depth) older))
  | App _ args -> lemma_substitute_args_fresh newer older depth count args
                    (match target with App _ xs -> xs | _ -> [])
  | Quantifier _ bs _ body ->
    lemma_substitute_fresh newer older (depth + L.length bs) count body
      (match target with Quantifier _ _ _ b -> b | _ -> target)

and lemma_substitute_args_fresh (newer older:list SK.witness) (depth count:nat) (args targets:list expr)
  : Lemma (requires SK.fresh_args newer args /\ SK.disjoint newer older /\
                    SK.substitute_args depth count [] older args == Some targets)
          (ensures SK.fresh_args newer targets)
          (decreases args) =
  match args, targets with
  | e :: rest, target :: tail ->
    lemma_substitute_fresh newer older depth count e target;
    lemma_substitute_args_fresh newer older depth count rest tail
  | _, _ -> ()

let lemma_source_scoped (s:S.checked_schema) (d:definition s)
  : Lemma (D.scoped [] (SK.source d) /\ get_sort (SK.source d) == bool_sort) =
  Q.lemma_closed_syntax (L.rev d.bound_sorts) [] 0 0 d.body

let lemma_source_fresh (s:S.checked_schema) (newer:definition s) (older:SK.definition)
  : Lemma (requires SK.fresh newer.witnesses older.body)
          (ensures SK.fresh newer.witnesses (SK.source older)) =
  lemma_interpreted_fresh (L.rev newer.bound_sorts) newer.witnesses R.not_decl

let lemma_instance_fresh (s:S.checked_schema) (newer older:definition s) (b:expr)
  : Lemma (requires SK.safe_extension newer [older] /\ SK.instantiation older == Some b)
          (ensures SK.fresh newer.witnesses b) =
  let target = Some?.v (SK.substitute 0 (L.length older.bound_sorts) [] older.witnesses older.body) in
  lemma_substitute_fresh newer.witnesses older.witnesses 0 (L.length older.bound_sorts) older.body target;
  lemma_interpreted_fresh (L.rev newer.bound_sorts) newer.witnesses R.not_decl

let instance_holds (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                   (d:definition s) : prop =
  forall (b:expr). SK.instantiation d == Some b ==>
    T.truth s bc eq other (SK.source d) == T.truth s bc eq other b

let rec context_model (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                      (ds:list (definition s)) : Tot prop (decreases ds) =
  match ds with [] -> True | d :: rest -> instance_holds s bc eq other d /\ context_model s bc eq other rest

let rec lemma_context_member (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                             (ds:list (definition s)) (d:definition s)
  : Lemma (requires context_model s bc eq other ds /\ L.mem d ds)
          (ensures instance_holds s bc eq other d)
          (decreases ds) =
  match ds with [] -> () | head :: rest -> if head <> d then lemma_context_member s bc eq other rest d

let rec build (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
              (eq:T.scalar_model base) (choice:hilbert_choice base s)
              (ds:list (definition s)) (other:V.interpretation base (S.signature s))
  : Tot (V.interpretation base (S.signature s)) (decreases ds) =
  match ds with
  | [] -> other
  | d :: rest ->
    let older = build s bc eq choice rest other in
    override s d (selected s bc eq choice older d) older

let rec lemma_build_quantification (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                   (eq:T.scalar_model base) (choice:hilbert_choice base s)
                                   (ds:list (definition s)) (other:V.interpretation base (S.signature s))
  : Lemma ((build s bc eq choice ds other).quantification == other.quantification)
          (decreases ds) =
  match ds with [] -> () | _ :: rest -> lemma_build_quantification s bc eq choice rest other

let rec erase (s:S.checked_schema) (ds:list (definition s)) : Tot (list SK.definition) (decreases ds) =
  match ds with [] -> [] | d :: rest -> (d <: SK.definition) :: erase s rest

let rec lemma_context_preserved (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                                (newer:definition s)
                                (vs:V.arguments base (S.signature s) (L.rev newer.bound_sorts))
                                (ds:list (definition s))
  : Lemma (requires SK.safe_extension newer (erase s ds) /\ context_model s bc eq other ds)
          (ensures context_model s bc eq (override s newer vs other) ds)
          (decreases ds) =
  match ds with
  | [] -> ()
  | d :: rest ->
    lemma_source_scoped s d;
    lemma_source_fresh s newer d;
    lemma_fresh s bc eq other newer vs [] (T.empty_environment (S.signature s)) (SK.source d);
    let at (b:expr) : Lemma (SK.instantiation d == Some b ==>
          T.truth s bc eq (override s newer vs other) (SK.source d) ==
          T.truth s bc eq (override s newer vs other) b) =
      if SK.instantiation d = Some b then (
        lemma_instance_fresh s newer d b;
        lemma_fresh s bc eq other newer vs [] (T.empty_environment (S.signature s)) b) in
    FStar.Classical.forall_intro at;
    lemma_context_preserved s bc eq other newer vs rest

noextract
let quantification_models (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
  (quantification:(k:quantifier_kind -> bound:list sort -> body_sort:sort ->
    (V.arguments base (S.signature s) (L.rev bound) -> V.value base (S.signature s) body_sort) ->
    V.value base (S.signature s) (quant_sort k bound body_sort))) : prop =
  (forall (bound:list sort)
          (body:V.arguments base (S.signature s) (L.rev bound) ->
                V.value base (S.signature s) bool_sort).
     T.truth_value s bc (quantification Forall_k bound bool_sort body) <==>
     (forall (vs:V.arguments base (S.signature s) (L.rev bound)). T.truth_value s bc (body vs))) /\
  (forall (bound:list sort)
          (body:V.arguments base (S.signature s) (L.rev bound) ->
                V.value base (S.signature s) bool_sort).
     T.truth_value s bc (quantification Exists_k bound bool_sort body) <==>
     (exists (vs:V.arguments base (S.signature s) (L.rev bound)). T.truth_value s bc (body vs)))

let lemma_quantification_models (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                (other newer:V.interpretation base (S.signature s))
  : Lemma (requires other.quantification == newer.quantification /\
                    Q.forall_model s bc other /\ exists_model s bc other)
          (ensures Q.forall_model s bc newer /\ exists_model s bc newer) =
  assert_norm (quantification_models s bc other.quantification ==
    (Q.forall_model s bc other /\ exists_model s bc other));
  assert_norm (quantification_models s bc newer.quantification ==
    (Q.forall_model s bc newer /\ exists_model s bc newer))

let rec lemma_build_context (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (eq:T.scalar_model base) (choice:hilbert_choice base s)
                           (ds:list (definition s)) (other:V.interpretation base (S.signature s))
  : Lemma (requires SK.ordered_context (erase s ds) /\ Q.forall_model s bc other /\ exists_model s bc other)
          (ensures context_model s bc eq (build s bc eq choice ds other) ds)
          (decreases ds) =
  match ds with
  | [] -> ()
  | d :: rest ->
    lemma_build_context s bc eq choice rest other;
    lemma_build_quantification s bc eq choice rest other;
    let older = build s bc eq choice rest other in
    lemma_quantification_models s bc other older;
    let vs = selected s bc eq choice older d in
    lemma_source_scoped s d;
    lemma_source_fresh s d d;
    lemma_fresh s bc eq older d vs [] (T.empty_environment (S.signature s)) (SK.source d);
    let at (b:expr) : Lemma (SK.instantiation d == Some b ==>
          T.truth s bc eq (override s d vs older) (SK.source d) ==
          T.truth s bc eq (override s d vs older) b) =
      if SK.instantiation d = Some b then (
        assert (definition_of s (SK.source d) b == Some d);
        lemma_epsilon_instance s bc eq choice older (SK.source d) b d) in
    FStar.Classical.forall_intro at;
    lemma_context_preserved s bc eq older d vs rest

let rec lemma_build_inputs (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (eq:T.scalar_model base) (choice:hilbert_choice base s)
                          (ds:list (definition s)) (other:V.interpretation base (S.signature s))
                          (inputs:list expr)
  : Lemma (requires SK.fresh_inputs (erase s ds) inputs)
          (ensures T.truths s bc eq other inputs == T.truths s bc eq (build s bc eq choice ds other) inputs)
          (decreases ds) =
  match ds with
  | [] -> ()
  | d :: rest ->
    lemma_build_inputs s bc eq choice rest other inputs;
    let older = build s bc eq choice rest other in
    let vs = selected s bc eq choice older d in
    let rec all (es:list expr)
      : Lemma (requires SK.fresh_args d.witnesses es)
              (ensures T.truths s bc eq older es == T.truths s bc eq (override s d vs older) es)
              (decreases es) =
      match es with
      | [] -> ()
      | e :: tail ->
        if D.scoped [] e && get_sort e = bool_sort then
          lemma_fresh s bc eq older d vs [] (T.empty_environment (S.signature s)) e;
        all tail in
    all inputs
