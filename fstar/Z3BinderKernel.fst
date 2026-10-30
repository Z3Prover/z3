(*
   Z3BinderKernel.fst

   Kernel soundness of quantifier introduction (`QuantifierIntroduction`
   nodes, checked by `Z3UnifiedProof.check_binder_with_context`) for a
   computable fragment of binder certificates, proved from the inhabited typed
   quantifier contract `Z3TypedQuantifier.quantifier_model`, NOT from the
   uninhabited `model_sound`, the old `binder_cache_sound` (every cached
   judgment true under every untyped environment) or any QR/normalization
   model.

   The certificate's own checked cache is the invariant's subject. With `t`
   the scopes the guard (`binder_scoped`) assigned to the entries, the typed
   cache invariant after the checker has stored entry `k` is

     for every entry k' <= k and every scope S assigned to k':
       the judgment j' at k' is scoped at S, and
       for every rho with CO.env_typed dom S rho, judgment_holds i rho j'.

   Scopes are explicit: the root is used at `[]`, and an introduction entry
   with binder sorts `bs` used at `S` reads its body premise at
   `L.rev bs @ S` (`Var 0` is the last binder). The structural facts come
   from `Z3BinderScope`; nothing assumes a scope.

   The fragment (`typed_entry`, `introduction_fragment`), checked on every
   entry of the certificate:

   * `asserted`: a closed original input (the checker requires
     `D.scoped []` and membership in the node's assertions). True under
     every environment because it is closed (`lemma_closed_eval_env_irrelevant`,
     which needs only quantifier extensionality), not because an assertion
     true at one environment is assumed true at another;
   * a core rule (`Z3CoreKernel.core_relational`/`core_logical`: reflexivity,
     symmetry, transitivity, transitivity path, congruence, commutativity,
     `iff~`, `mp`, `mp~`, unit resolution, and/or elimination, iff-true/false),
     whose premises are read at the entry's own scope and proved by the core
     kernel lemmas;
   * forall/exists introduction (`quant-intro`, or `nnf-pos` with sorts, which
     runs the same `binder_quantifier_step`) whose body edge is EXACTLY the two
     bodies of the conclusion, so both `QR.equivalent` wrappers hold by
     reflexivity and no QR theorem is used. The bodies agree at every value
     list typed by `L.rev bs` (`TQ.typed_quantifiers`), which decides typed
     forall/exists.

   NOT covered (an accepted certificate with such an entry is outside the
   theorem; its acceptance still rests on the legacy model): lambda
   introduction (no lambda semantics is modelled), Boolean `nnf-pos`/`nnf-neg`
   steps without sorts (`binder_boolean_step`, which rewrites premises inside
   quantifier bodies), negative `nnf-neg`, Skolemization (`sk`), `rewrite`,
   `th-lemma`, `def-axiom` and other basic rules, and introductions whose body
   edge differs from the bodies (non-reflexive QR normalization).

   * `lemma_introduction_node_sound`: a `QuantifierIntroduction` node checked
     by `check_node_with_context` with pending 0 whose certificate is in the
     fragment yields a fact that holds in every quantifier model, under every
     environment at which the node's assertions hold. Pending 0 is required:
     the dispatcher returns `Some` with pending 1 for rejected certificates
     (`lemma_introduction_result`).
   * `lemma_introduction_membership_sound`: the same for
     `check_node_with_membership`, which ignores `contains` for this rule.
   * `lemma_typed_binder_check_node_sound`: `Z3QuantifierKernel.
     lemma_typed_check_node_sound` (core rules and checked instantiations)
     extended with these introduction nodes, with its hypotheses unchanged.

   These are node theorems, not a proof-DAG or document theorem.
*)
module Z3BinderKernel

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3UnifiedProof
module CO = Z3CoreModel
module TQ = Z3TypedQuantifier
module K = Z3CoreKernel
module QK = Z3QuantifierKernel
module BS = Z3BinderScope
module D = Z3Definitions
module I = Z3ProofIndex
module Q = Z3QuantifierInstantiation
module SK = Z3Skolemization
module L = FStar.List.Tot

(* --- The fragment ------------------------------------------------------------------ *)

let core_entry_kind (name:string) : bool =
  match basic_rule_of_name name with
  | Some kind -> K.core_relational kind || K.core_logical kind
  | None -> false

(* Forall/exists introduction whose body edge is exactly the two bodies. *)
let exact_intro (e:binder_entry) (concl:judgment) (facts:list judgment) : bool =
  (e.binder_name = "quant-intro" || e.binder_name = "nnf-pos") && Some? e.binder_sorts &&
  (match relational concl, facts with
   | Some (r, Quantifier k _ _ a, Quantifier _ _ _ b), [j] ->
     (k = Forall_k || k = Exists_k) && edge r j = Some (a, b)
   | _, _ -> false)

let typed_entry (e:binder_entry) (concl:judgment) (facts:list judgment) : bool =
  e.binder_name = "asserted" || core_entry_kind e.binder_name || exact_intro e concl facts

(* Every entry, read in the checker's own cache. *)
let rec typed_entries (cache:I.index_tree judgment) (k:nat) (entries:list binder_entry)
  : Tot bool (decreases entries) =
  match entries with
  | [] -> true
  | e :: rest ->
    (match I.index_find cache k, I.opt_map (I.index_find cache) e.binder_premises with
     | Some concl, Some facts -> typed_entry e concl facts
     | _, _ -> false) &&
    typed_entries cache (k + 1) rest

let introduction_fragment (skolems:list SK.definition) (assertions:list judgment)
                          (c:binder_certificate) : bool =
  match check_binder_entries skolems assertions c.binder_entries I.Empty 0 with
  | Some cache -> typed_entries cache 0 c.binder_entries
  | None -> false

(* --- The checker's cache ----------------------------------------------------------- *)

let fresh (cache:I.index_tree judgment) (next:nat) : prop =
  forall (key:int). key >= next ==> I.index_find cache key == None

let extends (c1 c2:I.index_tree judgment) : prop =
  forall (key:int). Some? (I.index_find c1 key) ==> I.index_find c2 key == I.index_find c1 key

let lemma_put (cache:I.index_tree judgment) (next:nat) (j:judgment)
  : Lemma (requires fresh cache next)
          (ensures fresh (I.index_put cache next j) (next + 1) /\ extends cache (I.index_put cache next j) /\
                   I.index_find (I.index_put cache next j) next == Some j /\
                   (forall (key:int). key <> next ==> I.index_find (I.index_put cache next j) key == I.index_find cache key))
  = let aux (key:int)
      : Lemma (I.index_find (I.index_put cache next j) key ==
               (if key = next then Some j else I.index_find cache key))
      = if key < 0 then () else I.lemma_index_put cache next j key in
    FStar.Classical.forall_intro aux

let rec lemma_entries_extend (skolems:list SK.definition) (assertions:list judgment)
                             (entries:list binder_entry) (cache:I.index_tree judgment) (next:nat)
                             (final:I.index_tree judgment)
  : Lemma (requires check_binder_entries skolems assertions entries cache next == Some final /\
                    fresh cache next)
          (ensures extends cache final)
          (decreases entries)
  = match entries with
    | [] -> ()
    | e :: rest ->
      let concl = Some?.v (classify_fact e.binder_formula) in
      lemma_put cache next concl;
      lemma_entries_extend skolems assertions rest (I.index_put cache next concl) (next + 1) final

let rec lemma_opt_map_extends (c1 c2:I.index_tree judgment) (ps:list int) (facts:list judgment)
  : Lemma (requires I.opt_map (I.index_find c1) ps == Some facts /\ extends c1 c2)
          (ensures I.opt_map (I.index_find c2) ps == Some facts)
          (decreases ps)
  = match ps, facts with
    | p :: rest, _ :: remaining -> lemma_opt_map_extends c1 c2 rest remaining
    | _, _ -> ()

(* --- The typed cache invariant ------------------------------------------------------ *)

let valid (i:interpretation value) (dom:CO.domains) (s:list sort) (j:judgment) : prop =
  forall (rho:env value). CO.env_typed dom s rho ==> judgment_holds i rho j

(* Opaque to the solver; `lemma_entry_holds` unfolds it where it is used. *)
[@@"opaque_to_smt"]
let entry_holds (i:interpretation value) (dom:CO.domains) (t:scope_demands)
                (cache:I.index_tree judgment) (key:nat) : prop =
  forall (s:list sort). L.memP s (scope_demanded t key) ==>
    Some? (I.index_find cache key) /\
    BS.binder_judgment_scoped s (Some?.v (I.index_find cache key)) /\
    valid i dom s (Some?.v (I.index_find cache key))

let lemma_entry_holds (i:interpretation value) (dom:CO.domains) (t:scope_demands)
                      (cache:I.index_tree judgment) (key:nat)
  : Lemma (entry_holds i dom t cache key <==>
           (forall (s:list sort). L.memP s (scope_demanded t key) ==>
              Some? (I.index_find cache key) /\
              BS.binder_judgment_scoped s (Some?.v (I.index_find cache key)) /\
              valid i dom s (Some?.v (I.index_find cache key))))
  = reveal_opaque (`%entry_holds) (entry_holds i dom t cache key)

let inv (i:interpretation value) (dom:CO.domains) (t:scope_demands)
        (cache:I.index_tree judgment) (next:nat) : prop =
  forall (key:nat). key < next ==> entry_holds i dom t cache key

let lemma_scoped_same (s:list sort) (j:judgment)
  : Lemma (BS.binder_judgment_scoped s j == K.judgment_scoped s j)
  = ()

(* The premises of an entry read at `s'`: scoped there and true at every
   environment typed for it. *)
let rec lemma_premises (i:interpretation value) (dom:CO.domains) (t:scope_demands)
                       (cache:I.index_tree judgment) (next:nat) (k:int)
                       (ps:list int) (facts:list judgment) (s':list sort) (rho:env value)
  : Lemma (requires I.opt_map (I.index_find cache) ps == Some facts /\
                    BS.premises_demanded t k ps s' /\ k <= next /\ inv i dom t cache next /\
                    CO.env_typed dom s' rho)
          (ensures K.judgments_scoped s' facts /\ judgments_hold i rho facts)
          (decreases ps)
  = match ps, facts with
    | p :: rest, j :: remaining ->
      FStar.List.Tot.Properties.mem_memP s' (scope_demanded t p);
      let key : nat = p in
      assert (entry_holds i dom t cache key);
      lemma_entry_holds i dom t cache key;
      lemma_scoped_same s' j;
      lemma_premises i dom t cache next k rest remaining s' rho
    | _, _ -> ()

(* --- Steps ---------------------------------------------------------------------------- *)

let lemma_names ()
  : Lemma (basic_rule_of_name "asserted" == None /\ basic_rule_of_name "quant-intro" == None /\
           basic_rule_of_name "nnf-pos" == None /\ basic_rule_of_name "nnf-neg" == None /\
           basic_rule_of_name "sk" == Some Skolemization)
  = assert_norm (basic_rule_of_name "asserted" == None /\ basic_rule_of_name "quant-intro" == None /\
                 basic_rule_of_name "nnf-pos" == None /\ basic_rule_of_name "nnf-neg" == None /\
                 basic_rule_of_name "sk" == Some Skolemization)

(* A classified closed formula: its judgment is scoped at `[]` and its
   proposition is the formula itself. *)
let lemma_formula_judgment (formula:expr) (concl:judgment)
  : Lemma (requires classify_fact formula == Some concl /\ D.scoped [] formula /\ Some? (proposition concl))
          (ensures K.judgment_scoped [] concl /\ proposition concl == Some formula)
  = match formula with
    | App f [a; b] -> assert (D.scoped_args [] [a; b]); assert (D.scoped_args [] [b])
    | _ -> ()

(* A closed input: true under every environment. *)
let lemma_asserted_step (skolems:list SK.definition) (i:interpretation value) (dom:CO.domains)
                        (rho0:env value) (assertions:list judgment)
                        (e:binder_entry) (concl:judgment) (facts:list judgment) (s:list sort)
  : Lemma (requires TQ.quantifier_model i dom /\ judgments_hold i rho0 assertions /\
                    e.binder_name = "asserted" /\ classify_fact e.binder_formula == Some concl /\
                    binder_step_with_context skolems assertions e concl facts)
          (ensures valid i dom s concl)
  = lemma_names ();
    assert (~(binder_step e concl facts));
    assert (D.scoped [] e.binder_formula /\ L.mem concl assertions /\ Some? (proposition concl) /\
            well_formed concl);
    lemma_formula_judgment e.binder_formula concl;
    FStar.List.Tot.Properties.mem_memP concl assertions;
    lemma_judgment_member i rho0 assertions concl;
    K.lemma_proposition i dom [] rho0 concl;
    Q.lemma_scoped_closed [] e.binder_formula;
    let at (rho:env value) : Lemma (CO.env_typed dom s rho ==> judgment_holds i rho concl)
      = lemma_closed_eval_env_irrelevant i e.binder_formula 0 rho0 rho;
        K.lemma_proposition i dom [] rho concl in
    FStar.Classical.forall_intro at

(* A core step at its own scope. *)
let lemma_core_at (i:interpretation value) (dom:CO.domains) (t:scope_demands)
                  (cache:I.index_tree judgment) (next:nat) (e:binder_entry) (kind:rule)
                  (concl:judgment) (facts:list judgment) (s:list sort) (rho:env value)
  : Lemma (requires TQ.quantifier_model i dom /\ (K.core_relational kind || K.core_logical kind) /\
                    check_step kind concl facts /\
                    I.opt_map (I.index_find cache) e.binder_premises == Some facts /\
                    K.judgment_scoped s concl /\
                    BS.premises_demanded t next e.binder_premises s /\
                    inv i dom t cache next /\ CO.env_typed dom s rho)
          (ensures judgment_holds i rho concl)
  = lemma_premises i dom t cache next next e.binder_premises facts s rho;
    if relational_step kind concl facts
    then K.lemma_relational_step i dom s rho kind concl facts
    else K.lemma_logical_step i dom s rho kind concl facts

let lemma_core_step (skolems:list SK.definition) (i:interpretation value) (dom:CO.domains)
                    (assertions:list judgment) (t:scope_demands) (cache:I.index_tree judgment)
                    (next:nat) (e:binder_entry) (concl:judgment) (facts:list judgment) (s:list sort)
  : Lemma (requires TQ.quantifier_model i dom /\ core_entry_kind e.binder_name /\
                    binder_step_with_context skolems assertions e concl facts /\
                    I.opt_map (I.index_find cache) e.binder_premises == Some facts /\
                    BS.binder_judgment_scoped s concl /\
                    BS.premises_demanded t next e.binder_premises (BS.premise_scope_of e s) /\
                    inv i dom t cache next)
          (ensures valid i dom s concl)
  = lemma_names ();
    let kind = Some?.v (basic_rule_of_name e.binder_name) in
    assert (e.binder_name <> "asserted" /\ e.binder_name <> "sk" /\ e.binder_name <> "quant-intro" /\
            e.binder_name <> "nnf-pos" /\ e.binder_name <> "nnf-neg");
    assert (binder_step e concl facts);
    assert (e.binder_sorts == None /\ check_step kind concl facts);
    assert (BS.premise_scope_of e s == s);
    lemma_scoped_same s concl;
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires (lemma_core_at i dom t cache next e kind concl facts s))

(* Typed forall/exists are equal when their bodies agree at every typed value list. *)
let lemma_typed_congruence (i:interpretation value) (dom:CO.domains) (rho:env value)
                           (k:quantifier_kind) (bs:list sort) (sa sb:sort) (a b:expr)
  : Lemma (requires TQ.quantifier_model i dom /\ (k = Forall_k \/ k = Exists_k) /\
                    (forall (vs:list value). CO.args_typed dom (L.rev bs) vs ==>
                       eval i a (shift vs rho) == eval i b (shift vs rho)))
          (ensures eval i (Quantifier k bs sa a) rho == eval i (Quantifier k bs sb b) rho)
  = let truth (s:sort) (body:expr)
      : Lemma ((eval i (Quantifier Forall_k bs s body) rho == VBool true <==>
                (forall (vs:list value). CO.args_typed dom (L.rev bs) vs ==> eval i body (shift vs rho) == VBool true)) /\
               (eval i (Quantifier Exists_k bs s body) rho == VBool true <==>
                (exists (vs:list value). CO.args_typed dom (L.rev bs) vs /\ eval i body (shift vs rho) == VBool true)))
      = eliminate forall (bs':list sort) (s':sort) (body':expr) (rho':env value).
          (eval i (Quantifier Forall_k bs' s' body') rho' == VBool true <==>
           (forall (vs':list value). CO.args_typed dom (L.rev bs') vs' ==>
                                    eval i body' (shift vs' rho') == VBool true)) /\
          (eval i (Quantifier Exists_k bs' s' body') rho' == VBool true <==>
           (exists (vs':list value). CO.args_typed dom (L.rev bs') vs' /\
                                    eval i body' (shift vs' rho') == VBool true))
        with bs s body rho in
    truth sa a;
    truth sb b;
    assert (VBool? (eval i (Quantifier k bs sa a) rho));
    assert (VBool? (eval i (Quantifier k bs sb b) rho))

(* Forall/exists introduction with an exact body edge. *)
let lemma_intro_at (i:interpretation value) (dom:CO.domains) (t:scope_demands)
                   (cache:I.index_tree judgment) (next:nat) (e:binder_entry)
                   (concl:judgment) (j:judgment) (r:relation) (k:quantifier_kind) (bs:list sort)
                   (sa sb:sort) (a b:expr) (s:list sort) (rho:env value)
  : Lemma (requires TQ.quantifier_model i dom /\ (k = Forall_k \/ k = Exists_k) /\
                    well_formed concl /\ well_formed j /\
                    relational concl == Some (r, Quantifier k bs sa a, Quantifier k bs sb b) /\
                    edge r j == Some (a, b) /\
                    I.opt_map (I.index_find cache) e.binder_premises == Some [j] /\
                    BS.premises_demanded t next e.binder_premises (L.append (L.rev bs) s) /\
                    inv i dom t cache next /\ CO.env_typed dom s rho)
          (ensures judgment_holds i rho concl)
  = let s' = L.append (L.rev bs) s in
    let body (vs:list value)
      : Lemma (requires CO.args_typed dom (L.rev bs) vs)
              (ensures eval i a (shift vs rho) == eval i b (shift vs rho))
      = CO.lemma_env_shift dom (L.rev bs) s vs rho;
        lemma_premises i dom t cache next next e.binder_premises [j] s' (shift vs rho);
        K.lemma_edge_values i dom s' (shift vs rho) r j a b in
    FStar.Classical.forall_intro (FStar.Classical.move_requires body);
    lemma_typed_congruence i dom rho k bs sa sb a b;
    lemma_relational_value_sound i rho concl r (Quantifier k bs sa a) (Quantifier k bs sb b)

let lemma_intro_step (skolems:list SK.definition) (i:interpretation value) (dom:CO.domains)
                     (assertions:list judgment) (t:scope_demands) (cache:I.index_tree judgment)
                     (next:nat) (e:binder_entry) (concl:judgment) (facts:list judgment) (s:list sort)
  : Lemma (requires TQ.quantifier_model i dom /\ exact_intro e concl facts /\
                    binder_step_with_context skolems assertions e concl facts /\
                    I.opt_map (I.index_find cache) e.binder_premises == Some facts /\
                    BS.premises_demanded t next e.binder_premises (BS.premise_scope_of e s) /\
                    inv i dom t cache next)
          (ensures valid i dom s concl)
  = lemma_names ();
    assert (e.binder_name <> "asserted" /\ e.binder_name <> "sk");
    assert (binder_step e concl facts);
    let sorts = Some?.v e.binder_sorts in
    assert (binder_quantifier_step sorts concl facts);
    match relational concl, facts with
    | Some (r, Quantifier k bs sa a, Quantifier k' bs' sb b), [j] ->
      assert (k' = k /\ bs' = bs /\ bs = sorts /\ well_formed j);
      assert (BS.premise_scope_of e s == L.append (L.rev bs) s);
      FStar.Classical.forall_intro
        (FStar.Classical.move_requires
          (lemma_intro_at i dom t cache next e concl j r k bs sa sb a b s))
    | _, _ -> ()

let lemma_step (skolems:list SK.definition) (i:interpretation value) (dom:CO.domains)
               (rho0:env value) (assertions:list judgment) (t:scope_demands)
               (cache:I.index_tree judgment) (next:nat)
               (e:binder_entry) (concl:judgment) (facts:list judgment) (s:list sort)
  : Lemma (requires TQ.quantifier_model i dom /\ judgments_hold i rho0 assertions /\
                    classify_fact e.binder_formula == Some concl /\
                    binder_step_with_context skolems assertions e concl facts /\
                    typed_entry e concl facts /\
                    I.opt_map (I.index_find cache) e.binder_premises == Some facts /\
                    BS.binder_judgment_scoped s concl /\
                    BS.premises_demanded t next e.binder_premises (BS.premise_scope_of e s) /\
                    inv i dom t cache next)
          (ensures valid i dom s concl)
  = if e.binder_name = "asserted"
    then lemma_asserted_step skolems i dom rho0 assertions e concl facts s
    else if core_entry_kind e.binder_name
    then lemma_core_step skolems i dom assertions t cache next e concl facts s
    else lemma_intro_step skolems i dom assertions t cache next e concl facts s

(* --- The certificate ------------------------------------------------------------------- *)

(* The entry just stored holds at each scope assigned to it. *)
let lemma_entry_next (skolems:list SK.definition) (i:interpretation value) (dom:CO.domains)
                     (rho0:env value) (assertions:list judgment) (t:scope_demands)
                     (cache:I.index_tree judgment) (next:nat)
                     (e:binder_entry) (concl:judgment) (facts:list judgment)
  : Lemma (requires TQ.quantifier_model i dom /\ judgments_hold i rho0 assertions /\
                    classify_fact e.binder_formula == Some concl /\
                    binder_step_with_context skolems assertions e concl facts /\
                    typed_entry e concl facts /\
                    I.opt_map (I.index_find cache) e.binder_premises == Some facts /\
                    BS.entry_scoped t next e concl (scope_demanded t next) /\
                    inv i dom t cache next /\ fresh cache next)
          (ensures entry_holds i dom t (I.index_put cache next concl) next)
  = lemma_put cache next concl;
    let here (s:list sort)
      : Lemma (requires L.memP s (scope_demanded t next))
              (ensures BS.binder_judgment_scoped s concl /\ valid i dom s concl)
      = BS.lemma_entry_scoped t next e concl (scope_demanded t next) s;
        lemma_step skolems i dom rho0 assertions t cache next e concl facts s in
    FStar.Classical.forall_intro (FStar.Classical.move_requires here);
    lemma_entry_holds i dom t (I.index_put cache next concl) next

(* Storing at a fresh index keeps the earlier entries. *)
let lemma_entry_kept (i:interpretation value) (dom:CO.domains) (t:scope_demands)
                     (cache:I.index_tree judgment) (next:nat) (concl:judgment) (key:nat)
  : Lemma (requires inv i dom t cache next /\ key < next /\ fresh cache next)
          (ensures entry_holds i dom t (I.index_put cache next concl) key)
  = assert (entry_holds i dom t cache key);
    lemma_entry_holds i dom t cache key;
    lemma_put cache next concl;
    assert (I.index_find (I.index_put cache next concl) key == I.index_find cache key);
    lemma_entry_holds i dom t (I.index_put cache next concl) key

let lemma_inv_put (i:interpretation value) (dom:CO.domains) (t:scope_demands)
                  (cache:I.index_tree judgment) (next:nat) (concl:judgment)
  : Lemma (requires inv i dom t cache next /\ fresh cache next /\
                    entry_holds i dom t (I.index_put cache next concl) next)
          (ensures inv i dom t (I.index_put cache next concl) (next + 1))
  = let cache' = I.index_put cache next concl in
    let every (key:nat) : Lemma (key < next + 1 ==> entry_holds i dom t cache' key)
      = if key < next then lemma_entry_kept i dom t cache next concl key
        else if key = next then () in
    FStar.Classical.forall_intro every

let rec lemma_entries_typed (skolems:list SK.definition) (i:interpretation value) (dom:CO.domains)
                            (rho0:env value) (assertions:list judgment) (t:scope_demands)
                            (final:I.index_tree judgment)
                            (entries:list binder_entry) (cache:I.index_tree judgment) (next:nat)
  : Lemma (requires TQ.quantifier_model i dom /\ judgments_hold i rho0 assertions /\
                    check_binder_entries skolems assertions entries cache next == Some final /\
                    fresh cache next /\
                    BS.entries_scoped t final next entries /\
                    typed_entries final next entries /\
                    inv i dom t cache next)
          (ensures inv i dom t final (next + L.length entries))
          (decreases entries)
  = match entries with
    | [] -> ()
    | e :: rest ->
      let concl = Some?.v (classify_fact e.binder_formula) in
      let facts = Some?.v (I.opt_map (I.index_find cache) e.binder_premises) in
      let cache' = I.index_put cache next concl in
      lemma_put cache next concl;
      lemma_entries_extend skolems assertions rest cache' (next + 1) final;
      assert (I.index_find final next == Some concl);
      lemma_opt_map_extends cache final e.binder_premises facts;
      lemma_entry_next skolems i dom rho0 assertions t cache next e concl facts;
      lemma_inv_put i dom t cache next concl;
      lemma_entries_typed skolems i dom rho0 assertions t final rest cache' (next + 1)

(* The certificate's conclusion holds under every environment. *)
let lemma_certificate_sound (skolems:list SK.definition) (i:interpretation value) (dom:CO.domains)
                            (rho0:env value) (assertions:list judgment)
                            (c:binder_certificate) (concl:judgment) (rho:env value)
  : Lemma (requires TQ.quantifier_model i dom /\ judgments_hold i rho0 assertions /\
                    check_binder_with_context skolems assertions c concl /\
                    introduction_fragment skolems assertions c)
          (ensures judgment_holds i rho concl)
  = BS.lemma_checked_guard skolems assertions c concl;
    let final = Some?.v (check_binder_entries skolems assertions c.binder_entries I.Empty 0) in
    let n = L.length c.binder_entries in
    BS.lemma_guard (binder_demand_limit n) (binder_work_limit n) c final;
    let t = fst (Some?.v (binder_scopes (binder_demand_limit n) (binder_work_limit n) c)) in
    lemma_entries_typed skolems i dom rho0 assertions t final c.binder_entries I.Empty 0;
    let root : nat = c.binder_root in
    assert (L.memP [] (scope_demanded t root));
    assert (entry_holds i dom t final root);
    lemma_entry_holds i dom t final root;
    assert (CO.env_typed dom [] rho)

(* --- Nodes ------------------------------------------------------------------------------ *)

let lemma_introduction_result (skolems:list SK.definition) (strict:bool)
                              (assertions:list judgment) (node:proof_node)
  : Lemma (requires QuantifierIntroduction? node.kind /\
                    Some? (check_node_with_context skolems strict assertions node))
          (ensures (let r = Some?.v (check_node_with_context skolems strict assertions node) in
                    node.premises == [] /\ Some? (relational node.conclusion) /\
                    fst r == { conclusion = node.conclusion; hypotheses = [] } /\
                    (snd r == 0 \/ snd r == 1) /\
                    (snd r == 0 <==>
                       check_binder_with_context skolems assertions
                         (QuantifierIntroduction?.certificate node.kind) node.conclusion)))
  = QK.lemma_premises_empty node.premises

let introduction_rule (skolems:list SK.definition) (assertions:list judgment) (node:proof_node) : bool =
  match node.kind with
  | QuantifierIntroduction c ->
    check_binder_with_context skolems assertions c node.conclusion &&
    introduction_fragment skolems assertions c
  | _ -> false

let lemma_introduction_node_sound (skolems:list SK.definition) (i:interpretation value)
                                  (dom:CO.domains) (rho:env value)
                                  (strict:bool) (assertions:list judgment) (node:proof_node)
  : Lemma (requires TQ.quantifier_model i dom /\ judgments_hold i rho assertions /\
                    QuantifierIntroduction? node.kind /\
                    introduction_fragment skolems assertions (QuantifierIntroduction?.certificate node.kind) /\
                    Some? (check_node_with_context skolems strict assertions node) /\
                    snd (Some?.v (check_node_with_context skolems strict assertions node)) == 0)
          (ensures scoped_holds i rho (fst (Some?.v (check_node_with_context skolems strict assertions node))))
  = lemma_introduction_result skolems strict assertions node;
    lemma_certificate_sound skolems i dom rho assertions
      (QuantifierIntroduction?.certificate node.kind) node.conclusion rho

let lemma_introduction_rule_sound (skolems:list SK.definition) (i:interpretation value)
                                  (dom:CO.domains) (rho:env value)
                                  (strict:bool) (assertions:list judgment) (node:proof_node)
  : Lemma (requires TQ.quantifier_model i dom /\ judgments_hold i rho assertions /\
                    introduction_rule skolems assertions node /\
                    Some? (check_node_with_context skolems strict assertions node))
          (ensures scoped_holds i rho (fst (Some?.v (check_node_with_context skolems strict assertions node))))
  = lemma_introduction_result skolems strict assertions node;
    lemma_introduction_node_sound skolems i dom rho strict assertions node

let lemma_introduction_membership_irrelevant (skolems:list SK.definition)
                                            (strict:bool) (assertions:list judgment)
                                            (contains:judgment -> bool) (node:proof_node)
  : Lemma (requires QuantifierIntroduction? node.kind)
          (ensures check_node_with_membership skolems strict assertions contains node ==
                   check_node_with_context skolems strict assertions node)
  = match node.kind with QuantifierIntroduction _ -> ()

let lemma_introduction_membership_sound (skolems:list SK.definition) (i:interpretation value)
                                        (dom:CO.domains) (rho:env value)
                                        (strict:bool) (assertions:list judgment)
                                        (contains:judgment -> bool) (node:proof_node)
  : Lemma (requires TQ.quantifier_model i dom /\ judgments_hold i rho assertions /\
                    QuantifierIntroduction? node.kind /\
                    introduction_fragment skolems assertions (QuantifierIntroduction?.certificate node.kind) /\
                    Some? (check_node_with_membership skolems strict assertions contains node) /\
                    snd (Some?.v (check_node_with_membership skolems strict assertions contains node)) == 0)
          (ensures scoped_holds i rho
                     (fst (Some?.v (check_node_with_membership skolems strict assertions contains node))))
  = lemma_introduction_membership_irrelevant skolems strict assertions contains node;
    lemma_introduction_node_sound skolems i dom rho strict assertions node

(* `Z3QuantifierKernel.typed_rule` extended with the introductions above. *)
let typed_binder_rule (skolems:list SK.definition) (assertions:list judgment) (node:proof_node) : bool =
  QK.typed_rule node || introduction_rule skolems assertions node

let lemma_typed_binder_check_node_sound (skolems:list SK.definition) (i:interpretation value)
                                        (dom:CO.domains) (scope:list sort) (rho:env value)
                                        (strict:bool) (assertions:list judgment) (node:proof_node)
  : Lemma (requires TQ.quantifier_model i dom /\ CO.env_typed dom scope rho /\
                    judgments_hold i rho assertions /\ premises_sound i rho node.premises /\
                    K.judgment_scoped scope node.conclusion /\ K.facts_scoped scope node.premises /\
                    typed_binder_rule skolems assertions node /\
                    Some? (check_node_with_context skolems strict assertions node))
          (ensures scoped_holds i rho (fst (Some?.v (check_node_with_context skolems strict assertions node))))
  = if QK.typed_rule node
    then QK.lemma_typed_check_node_sound skolems i dom scope rho strict assertions node
    else lemma_introduction_rule_sound skolems i dom rho strict assertions node
