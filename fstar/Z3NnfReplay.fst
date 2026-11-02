(*
   Z3NnfReplay.fst

   Local replay of the negation-normal-form certificates that Z3's NNF
   converter (src/ast/normal_forms/nnf.cpp) attaches to `nnf-neg` and
   `nnf-pos` proof nodes, for the Sorted route (Z3SortedProof), with a
   soundness theorem in the Sorted semantics (Z3SortedSemantics) whose only
   model hypotheses are the universal and existential quantifier laws
   (Q.forall_model, E.exists_model). Z3SortedRootDocument derives both from
   R1 of one inhabited typed root model; nothing here assumes a cache or a
   body fact.

   Certificate protocol (the existing native marshalling, unchanged; see
   Z3NativeProof.marshal_binder): the node's premises are empty and its
   rule is `QuantifierIntroduction c`. The entries of `c` are the proof
   steps below the node, premises first; an entry built from a binder rule
   whose only premise is `proof-bind` records the binder sorts and has the
   body proof (an OPEN proof) as its premise. The certificate is replayed
   only when its ROOT entry is `nnf-neg` or `nnf-pos`; quant-intro roots and
   every other certificate keep the previous treatment.

   Judgments. Every replayed entry concludes `l ~ r` (or `l = r`): the
   values of l and r are equal. A NEGATIVE step `nnf-neg` concludes
   `(not s) ~ t`: its target t is equivalent to the negation of its source
   s. A POSITIVE step `nnf-pos` concludes `s ~ t`. The polarity of a child
   is a fixed function of the source connective and the child position
   (the process_ functions of nnf.cpp), and a child fact is
     P(c, r):  `c ~ r`                                  (positive child)
     N(c, r):  `(not c) ~ r`, or the skip `r ~ r` with r = mk_not(c)
               (ast_util.cpp mk_not: (not x) -> x, true -> false,
               false -> true, otherwise (not c))        (negative child)
   Operators are identified only by the canonical classifier
   `Z3SortedSemantics.classify` (name, domain, range, interpretation and
   parameters), never by name alone.

   The local rules (pol = true for nnf-pos, false for nnf-neg; Q = P if
   pol else N; children in the producer's order):
     and/or(c1..cn)  -> pol: same op, else dual op over (t1..tn);  Q(ci,ti)
     not(x)          -> t;                       [Q'(x,t)] with Q' = N if pol else P
     =>(a,b)         -> pol: (or na' b'), else (and a' b');  [Q'(a,_), Q(b,b')]
     ite(c,x,y):Bool -> (and (or nc' x') (or c' y'));  [P(c,c'), N(c,nc'), Q(x,x'), Q(y,y')]
     =(a,b):Bool / xor(a,b) -> with E = (pol for =, not pol for xor):
                        E: (and (or na' b') (or a' nb')), else (and (or a' b') (or na' nb'))
                        [P(a,a'), N(a,na'), P(b,b'), N(b,nb')]
     Q bs. A (forall/exists, sorts = bs)
                     -> pol: Q bs. B, else (dual Q) bs. B;  [Q(A,B) at L.rev bs @ scope]
   plus `refl`, `trans` (two premises, middle terms equal), `monotonicity`
   (same declaration; premises match the changed arguments in order, every
   premise consumed) and `sk`: a closed Skolem step `a ~ b` whose equation
   `(= a b)` is one of the node's assertions, or an OPEN (dependent) Skolem
   step whose universal closure `(forall cb. (= a b))` is one of them and
   whose dependencies are typed at every scope the guard assigns it. On the
   epsilon route those assertions include the choice equations of the
   certified epsilon context (Z3SortedProof.epsilon_context) and the
   closures of the certified dependent context
   (Z3SortedProof.dependent_context, Z3SortedDependentSkolem), so an inner
   Skolem step is accepted only when its definition passed the eligibility,
   ordering and freshness gates, and it is TRUE only in the choice extension
   of the model (one joint choice per argument tuple for a dependent step),
   which is where the epsilon theorem evaluates the document. An open step
   is read at its scope through the closure by coincidence
   (lemma_closure_edge). Every other entry kind (rewrite, apply-def,
   quant-intro, labels, lambda, the hnf.cpp variant whose body is not the
   negation of its source, ...) leaves the node PENDING.

   Scopes. The existing guard (Z3UnifiedProof.binder_scopes /
   scope_entries_checked, Z3BinderScope) assigns every entry the scopes at
   which the root uses it: the root at `[]`, the premise of an entry with
   sorts bs used at S at `L.rev bs @ S` (`Var 0` is the last binder). The
   replay runs the guard FIRST and checks the local rule of every entry that
   has a scope; entries the root does not use are ignored. The invariant is

     for every entry k and every scope S assigned to k, the judgment of k
     holds at S for EVERY typed environment of S,

   proved entry by entry from the premises' invariant at their assigned
   scopes; a quantifier step reads its body ONLY at the extensions
   `V.extend S (L.rev bs) vs rho`. Nothing is assumed for an environment of
   another scope.

   Resources. Every walk is a loop (self tail call). The guard keeps its own
   bounds. The replay charges one budget of `U.binder_work_limit n` units
   (the guard's per-entry unit) before it compares terms: the node count of
   each used entry formula (counted by an explicit worklist), the counts of
   its premises' formulas at every use (a premise shared by m users is
   charged m times, so the comparisons stay linear in the budget), and one
   unit per assertion for each `sk` step. An exhausted budget leaves the node
   PENDING. Premise ids that are not earlier entries (forward, self or
   negative references) make the certificate MALFORMED, which the Sorted
   route reports as a rejected proof entry, not as a pending obligation.
*)
module Z3NnfReplay

open Z3AstTheory
open FStar.List.Tot
module U = Z3UnifiedProof
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module Q = Z3SortedQuantifier
module E = Z3SortedSkolem
module D = Z3Definitions
module R = Z3ResolutionProofTheory
module B = Z3BoundedBoolEquiv
module I = Z3ProofIndex
module BS = Z3BinderScope
module L = FStar.List.Tot
module SK = Z3Skolemization
module DS = Z3SortedDependentSkolem

(* ---------------------------------------------------------------------- *)
(* 1. The local rules (executable)                                          *)
(* ---------------------------------------------------------------------- *)

(* `l ~ r` and `l = r` both state equal values; the sides have one sort. *)
let edge (j:U.judgment) : option (expr & expr) =
  match j with
  | U.Equal a b | U.Observational a b -> if get_sort a = get_sort b then Some (a, b) else None
  | U.Holds _ -> None

(* `n` is the canonical negation of `c`. *)
let negation_of (c n:expr) : bool =
  match n with
  | App f [x] -> T.classify f = T.Negation && x = c
  | _ -> false

let constant_of (e:expr) (b:bool) : bool =
  match e with
  | App f [] -> T.classify f = T.Constant b
  | _ -> false

(* The producer's skip result for a negatively visited child c:
   r = mk_not(c), so that `r ~ r` is a negative child fact. *)
let skip_negation (c r:expr) : bool =
  negation_of c r || negation_of r c ||
  (constant_of c true && constant_of r false) || (constant_of c false && constant_of r true)

let positive (c r:expr) (j:U.judgment) : bool = edge j = Some (c, r)

let negative (c r:expr) (j:U.judgment) : bool =
  match edge j with
  | Some (l, r') -> r' = r && (negation_of c l || (l = r && skip_negation c r))
  | None -> false

let child (pol:bool) (c r:expr) (j:U.judgment) : bool =
  if pol then positive c r j else negative c r j

let dual_op (op:B.nary_op) : B.nary_op =
  match op with B.And -> B.Or | B.Or -> B.And | B.Xor -> B.Xor

let dual_kind (k:quantifier_kind) : quantifier_kind =
  match k with Forall_k -> Exists_k | Exists_k -> Forall_k | Lambda_k -> Lambda_k

let rec children_ok (pol:bool) (cs ts:list expr) (facts:list U.judgment) : Tot bool (decreases cs) =
  match cs, ts, facts with
  | [], [], [] -> true
  | c :: cs', t :: ts', j :: js -> if child pol c t j then children_ok pol cs' ts' js else false
  | _, _, _ -> false

(* t = (and (or x1 y1) (or x2 y2)) over canonical and/or. *)
let and_of_ors (t:expr) : option (expr & expr & expr & expr) =
  match t with
  | App a [App o1 [x1; y1]; App o2 [x2; y2]] ->
    if T.classify a = T.Nary B.And && T.classify o1 = T.Nary B.Or && T.classify o2 = T.Nary B.Or
    then Some (x1, y1, x2, y2) else None
  | _ -> None

let ite_ok (pol:bool) (c x y t:expr) (facts:list U.judgment) : bool =
  match and_of_ors t, facts with
  | Some (nc', x', c', y'), [jc; jn; jx; jy] ->
    positive c c' jc && negative c nc' jn && child pol x x' jx && child pol y y' jy
  | _, _ -> false

(* `equivalence`: t states a <=> b, else t states a xor b. *)
let iff_ok (equivalence:bool) (a b t:expr) (facts:list U.judgment) : bool =
  match and_of_ors t, facts with
  | Some (x1, y1, x2, y2), [ja; jna; jb; jnb] ->
    positive b y1 jb && negative b y2 jnb &&
    (if equivalence then negative a x1 jna && positive a x2 ja
     else positive a x1 ja && negative a x2 jna)
  | _, _ -> false

let implies_ok (pol:bool) (a b t:expr) (facts:list U.judgment) : bool =
  match t, facts with
  | App g [a'; b'], [ja; jb] ->
    T.classify g = T.Nary (if pol then B.Or else B.And) && child (not pol) a a' ja && child pol b b' jb
  | _, _ -> false

let boolean_ok (pol:bool) (src t:expr) (facts:list U.judgment) : bool =
  match src with
  | App f args ->
    (match T.classify f, args with
     | T.Nary B.Xor, [a; b] -> iff_ok (not pol) a b t facts
     | T.Nary op, _ ->
       op <> B.Xor &&
       (match t with
        | App g ts -> T.classify g = T.Nary (if pol then op else dual_op op) && children_ok pol args ts facts
        | _ -> false)
     | T.Negation, [x] -> (match facts with [j] -> child (not pol) x t j | _ -> false)
     | T.Implication, [a; b] -> implies_ok pol a b t facts
     | T.Choice s, [c; x; y] -> s = bool_sort && ite_ok pol c x y t facts
     | T.Equality s, [a; b] -> s = bool_sort && iff_ok pol a b t facts
     | _, _ -> false)
  | _ -> false

let quantifier_ok (pol:bool) (sorts:list sort) (src t:expr) (facts:list U.judgment) : bool =
  match src, t, facts with
  | Quantifier k bs s a, Quantifier k' bs' s' b, [j] ->
    (k = Forall_k || k = Exists_k) && k' = (if pol then k else dual_kind k) &&
    bs = sorts && bs' = sorts && s = bool_sort && s' = bool_sort && child pol a b j
  | _, _, _ -> false

let nnf_ok (pol:bool) (sorts:option (list sort)) (src t:expr) (facts:list U.judgment) : bool =
  match sorts with
  | Some bs -> quantifier_ok pol bs src t facts
  | None -> boolean_ok pol src t facts

(* Congruence: the premises match the changed arguments in order, and every
   premise is consumed. *)
let rec arguments_ok (xs ys:list expr) (facts:list U.judgment) : Tot bool (decreases xs) =
  match xs, ys with
  | [], [] -> Nil? facts
  | x :: xs', y :: ys' ->
    (match facts with
     | j :: js ->
       if edge j = Some (x, y) then arguments_ok xs' ys' js
       else if x = y then arguments_ok xs' ys' facts else false
     | [] -> if x = y then arguments_ok xs' ys' [] else false)
  | _, _ -> false

(* The binder list of an assertion that is the universal closure
   (forall cb. (= lhs rhs)) of an open equation: on the epsilon route, the
   closure of a dependent Skolem step of the certified dependent context
   (Z3SortedProof.dependent_context, Z3SortedDependentSkolem.closure). *)
let rec find_closure (lhs rhs:expr) (es:list expr) : Tot (option (list sort)) (decreases es) =
  match es with
  | [] -> None
  | a :: rest ->
    (match a with
     | Quantifier Forall_k cb s body ->
       if s = bool_sort && body = R.mk_eq_expr lhs rhs then Some cb else find_closure lhs rhs rest
     | _ -> find_closure lhs rhs rest)

let entry_ok (assertions:list expr) (e:U.binder_entry) (j:U.judgment) (facts:list U.judgment) : bool =
  match edge j with
  | None -> false
  | Some (lhs, rhs) ->
    let name = e.U.binder_name in
    if name = "nnf-neg" then
      (match lhs with
       | App n [src] -> T.classify n = T.Negation && nnf_ok false e.U.binder_sorts src rhs facts
       | _ -> false)
    else if name = "nnf-pos" then nnf_ok true e.U.binder_sorts lhs rhs facts
    else if Some? e.U.binder_sorts then false
    else if name = "refl" then Nil? facts && lhs = rhs
    else if name = "trans" then
      (match facts with
       | [p; q] ->
         (match edge p, edge q with
          | Some (a, b), Some (b', c) -> a = lhs && b = b' && c = rhs
          | _, _ -> false)
       | _ -> false)
    else if name = "monotonicity" then
      (match lhs, rhs with
       | App f xs, App g ys -> f = g && arguments_ok xs ys facts
       | _, _ -> false)
    else if name = "sk" then
      Nil? facts && U.Observational? j &&
      (L.mem (R.mk_eq_expr lhs rhs) assertions || Some? (find_closure lhs rhs assertions))
    else false

let rec all_typed (scopes:list (list sort)) (deps:list SK.dependency) : Tot bool (decreases scopes) =
  match scopes with [] -> true | sc :: rest -> DS.deps_typed sc deps && all_typed rest deps

(* An open Skolem step is used only at scopes where its dependencies are
   typed (every dependency index names a position of the scope with its
   sort). The replay's soundness does not need it (both sides of the step
   are typed at the scope and at its closure's scope, and lemma_closure_edge
   reads the closure there by coincidence); it keeps the runtime contract of
   a dependent step explicit. Closed steps pass unchanged. *)
let skolem_scopes_ok (e:U.binder_entry) (j:U.judgment) (scopes:list (list sort)) : bool =
  if e.U.binder_name <> "sk" then true
  else match edge j with
  | None -> true
  | Some (lhs, rhs) ->
    (D.scoped [] lhs && D.scoped [] rhs) ||
    (match SK.definition_of lhs rhs with
     | Some d -> all_typed scopes d.SK.dependencies
     | None -> false)

(* ---------------------------------------------------------------------- *)
(* 2. The certificate walk (executable, loops)                              *)
(* ---------------------------------------------------------------------- *)

let rec prepend (xs acc:list expr) : Tot (list expr) (decreases xs) =
  match xs with [] -> acc | x :: rest -> prepend rest (x :: acc)

(* The work left after one unit per node of the pending expressions (tree
   count), or None when the work does not suffice. *)
let rec nodes_within (work:nat) (pending:list expr) : Tot (option nat) (decreases work) =
  match pending with
  | [] -> Some work
  | e :: rest ->
    if work = 0 then None
    else match e with
      | App _ args -> nodes_within (work - 1) (prepend args rest)
      | Quantifier _ _ _ b -> nodes_within (work - 1) (b :: rest)
      | Var _ _ -> nodes_within (work - 1) rest

let rec premise_charge (sizes:I.index_tree nat) (ps:list int) (work:nat)
  : Tot (option nat) (decreases ps) =
  match ps with
  | [] -> Some work
  | p :: rest ->
    (match I.index_find sizes p with
     | Some n -> if n + 1 <= work then premise_charge sizes rest (work - (n + 1)) else None
     | None -> None)

let rec premises_earlier (ps:list int) (k:nat) : Tot bool (decreases ps) =
  match ps with
  | [] -> true
  | p :: rest -> if 0 <= p && p < k then premises_earlier rest k else false

let rec well_indexed (entries:list U.binder_entry) (k:nat) : Tot bool (decreases entries) =
  match entries with
  | [] -> true
  | e :: rest -> if premises_earlier e.U.binder_premises k then well_indexed rest (k + 1) else false

(* The judgment of every entry, by entry index. *)
let rec judgments_of (entries:list U.binder_entry) (cache:I.index_tree U.judgment) (k:nat)
  : Tot (option (I.index_tree U.judgment)) (decreases entries) =
  match entries with
  | [] -> Some cache
  | e :: rest ->
    (match U.classify_fact e.U.binder_formula with
     | Some j -> judgments_of rest (I.index_put cache k j) (k + 1)
     | None -> None)

(* The local rule of every entry the guard assigned a scope, within the work;
   entries without a scope are not used by the root and are skipped. *)
let rec steps_ok (assertions:list expr) (count:nat) (t:U.scope_demands) (cache:I.index_tree U.judgment)
                 (sizes:I.index_tree nat) (k:nat) (entries:list U.binder_entry) (work:nat)
  : Tot bool (decreases entries) =
  match entries with
  | [] -> true
  | e :: rest ->
    if Nil? (U.scope_demanded t k) then steps_ok assertions count t cache sizes (k + 1) rest work
    else match nodes_within work [e.U.binder_formula] with
    | None -> false
    | Some w1 ->
      let size : nat = if w1 <= work then work - w1 else 0 in
      (match premise_charge sizes e.U.binder_premises w1 with
       | None -> false
       | Some w2 ->
         let w3 = if e.U.binder_name = "sk" then (if count <= w2 then Some (w2 - count) else None) else Some w2 in
         (match w3, I.index_find cache k, I.opt_map_tail (I.index_find cache) e.U.binder_premises with
          | Some w, Some j, Some facts ->
            if entry_ok assertions e j facts && skolem_scopes_ok e j (U.scope_demanded t k)
            then steps_ok assertions count t cache (I.index_put sizes k size) (k + 1) rest w
            else false
          | _, _, _ -> false))

let rec entry_at (entries:list U.binder_entry) (n:nat) : Tot (option U.binder_entry) (decreases entries) =
  match entries with
  | [] -> None
  | e :: rest -> if n = 0 then Some e else entry_at rest (n - 1)

(* The certificates this replay consumes: an nnf-neg or nnf-pos root. *)
let nnf_root (c:U.binder_certificate) : bool =
  0 <= c.U.binder_root &&
  (match entry_at c.U.binder_entries c.U.binder_root with
   | Some e -> e.U.binder_name = "nnf-neg" || e.U.binder_name = "nnf-pos"
   | None -> false)

type verdict =
  | Replayed     (* every used entry replayed: the node is checked *)
  | Unreplayed   (* not an NNF certificate, outside the calculus, or over budget: PENDING *)
  | Malformed    (* a premise id is not an earlier entry: a rejected proof entry *)

let replay (assertions:list expr) (c:U.binder_certificate) (concl:U.judgment) : verdict =
  if not (nnf_root c) then Unreplayed
  else if not (well_indexed c.U.binder_entries 0) then Malformed
  else
    let n = U.count_cells 0 c.U.binder_entries in
    let root = c.U.binder_root in
    match judgments_of c.U.binder_entries I.Empty 0 with
    | None -> Unreplayed
    | Some cache ->
      if not (0 <= root && root < n && I.index_find cache root = Some concl) then Unreplayed
      else match U.binder_scopes (U.binder_demand_limit n) (U.binder_work_limit n) c with
      | None -> Unreplayed
      | Some (t, w) ->
        if L.mem [] (U.scope_demanded t root) &&
           Some? (U.scope_entries_checked t cache 0 c.U.binder_entries w) &&
           steps_ok assertions (U.count_cells 0 assertions) t cache I.Empty 0 c.U.binder_entries
             (U.binder_work_limit n)
        then Replayed else Unreplayed

(* The scope guard alone, on the classified certificate (used by the root
   coverage gate). *)
let certificate_scoped (c:U.binder_certificate) : bool =
  match judgments_of c.U.binder_entries I.Empty 0 with
  | Some cache -> U.binder_scoped c cache
  | None -> false

(* ---------------------------------------------------------------------- *)
(* 3. Semantics of one judgment at one typed environment                    *)
(* ---------------------------------------------------------------------- *)

let same_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
            (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
            (scope:list sort) (rho:V.environment base (S.signature s) scope) (a b:expr) : GTot bool =
  D.scoped scope a && D.scoped scope b &&
  T.equal_tree eq.T.reflection (T.evaluate_at s bc eq other scope rho a) (T.evaluate_at s bc eq other scope rho b)

let holds_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
             (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
             (scope:list sort) (rho:V.environment base (S.signature s) scope) (j:U.judgment) : GTot bool =
  match j with
  | U.Holds e -> T.truth_at s bc eq other scope rho e
  | U.Equal a b | U.Observational a b -> same_at s bc eq other scope rho a b

let rec all_hold (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                 (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                 (scope:list sort) (rho:V.environment base (S.signature s) scope)
                 (facts:list U.judgment) : GTot bool (decreases facts) =
  match facts with
  | [] -> true
  | j :: rest -> holds_at s bc eq other scope rho j && all_hold s bc eq other scope rho rest

(* A judgment VALID at a scope: true at every typed environment of it. *)
let valid (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
          (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
          (scope:list sort) (j:U.judgment) : prop =
  forall (rho:V.environment base (S.signature s) scope). holds_at s bc eq other scope rho j

let rec all_valid (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                  (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                  (scope:list sort) (facts:list U.judgment) : Tot prop (decreases facts) =
  match facts with
  | [] -> True
  | j :: rest -> valid s bc eq other scope j /\ all_valid s bc eq other scope rest

let rec lemma_all_hold (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (scope:list sort) (rho:V.environment base (S.signature s) scope)
                       (facts:list U.judgment)
  : Lemma (requires all_valid s bc eq other scope facts)
          (ensures all_hold s bc eq other scope rho facts)
          (decreases facts) =
  match facts with
  | [] -> ()
  | _ :: rest -> lemma_all_hold s bc eq other scope rho rest

let lemma_same_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                  (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                  (scope:list sort) (rho:V.environment base (S.signature s) scope) (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b)
          (ensures same_at s bc eq other scope rho a b <==>
                   T.evaluate_at s bc eq other scope rho a == T.evaluate_at s bc eq other scope rho b) =
  T.lemma_equal_tree eq.T.reflection (T.evaluate_at s bc eq other scope rho a)
    (T.evaluate_at s bc eq other scope rho b)

(* A relational fact read through its edge: equal values, equal truth. *)
let lemma_edge (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
               (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
               (scope:list sort) (rho:V.environment base (S.signature s) scope) (j:U.judgment) (a b:expr)
  : Lemma (requires edge j == Some (a, b) /\ holds_at s bc eq other scope rho j)
          (ensures D.scoped scope a /\ D.scoped scope b /\ get_sort a == get_sort b /\
                   T.evaluate_at s bc eq other scope rho a == T.evaluate_at s bc eq other scope rho b /\
                   T.truth_at s bc eq other scope rho a == T.truth_at s bc eq other scope rho b) =
  lemma_same_at s bc eq other scope rho a b

(* Equal truth of two scoped Boolean terms is equality of their values. *)
let lemma_same_truth (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                     (scope:list sort) (rho:V.environment base (S.signature s) scope) (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ get_sort a == bool_sort /\ get_sort b == bool_sort /\
                    T.truth_at s bc eq other scope rho a == T.truth_at s bc eq other scope rho b)
          (ensures same_at s bc eq other scope rho a b) =
  T.lemma_boolean s bc (T.evaluate_at s bc eq other scope rho a);
  T.lemma_boolean s bc (T.evaluate_at s bc eq other scope rho b);
  lemma_same_at s bc eq other scope rho a b

(* ---------------------------------------------------------------------- *)
(* 4. Canonical connectives at a scope                                      *)
(* ---------------------------------------------------------------------- *)

let lemma_truth_not (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                    (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                    (scope:list sort) (rho:V.environment base (S.signature s) scope) (f:func_decl) (x:expr)
  : Lemma (requires D.scoped scope (App f [x]) /\ T.classify f == T.Negation)
          (ensures D.scoped scope x /\ get_sort x == bool_sort /\ get_sort (App f [x]) == bool_sort /\
                   T.truth_at s bc eq other scope rho (App f [x]) == not (T.truth_at s bc eq other scope rho x)) =
  T.lemma_evaluate_core_at s bc eq other scope rho f [x];
  V.lemma_sort_eq (get_sort x) bool_sort

let lemma_truth_constant (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                         (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                         (scope:list sort) (rho:V.environment base (S.signature s) scope) (e:expr) (b:bool)
  : Lemma (requires D.scoped scope e /\ constant_of e b)
          (ensures get_sort e == bool_sort /\ T.truth_at s bc eq other scope rho e == b) =
  match e with
  | App f [] -> T.lemma_evaluate_core_at s bc eq other scope rho f []
  | _ -> ()

let lemma_truth_nary (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                     (scope:list sort) (rho:V.environment base (S.signature s) scope)
                     (f:func_decl) (args:list expr) (op:B.nary_op)
  : Lemma (requires D.scoped scope (App f args) /\ T.classify f == T.Nary op)
          (ensures get_sort (App f args) == bool_sort /\
                   T.truth_at s bc eq other scope rho (App f args) ==
                   B.geval_args (T.truth_at s bc eq other scope rho) op (L.map B.Atom args)) =
  T.lemma_evaluate_core_at s bc eq other scope rho f args;
  T.lemma_boolean_arguments_at s bc eq other scope rho args f.domain op

let lemma_pair (rho:expr -> GTot bool) (op:B.nary_op) (x y:expr)
  : Lemma (B.geval_args rho op (L.map B.Atom [x; y]) == B.combine op (rho x) (B.combine op (rho y) (B.neutral op))) =
  assert_norm (L.map B.Atom [x; y] == [B.Atom x; B.Atom y])

let lemma_truth_or2 (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                    (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                    (scope:list sort) (rho:V.environment base (S.signature s) scope)
                    (f:func_decl) (x y:expr) (op:B.nary_op)
  : Lemma (requires D.scoped scope (App f [x; y]) /\ T.classify f == T.Nary op)
          (ensures get_sort (App f [x; y]) == bool_sort /\
                   T.truth_at s bc eq other scope rho (App f [x; y]) ==
                   B.combine op (T.truth_at s bc eq other scope rho x)
                     (B.combine op (T.truth_at s bc eq other scope rho y) (B.neutral op))) =
  lemma_truth_nary s bc eq other scope rho f [x; y] op;
  lemma_pair (T.truth_at s bc eq other scope rho) op x y

let lemma_truth_implies (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                        (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                        (scope:list sort) (rho:V.environment base (S.signature s) scope)
                        (f:func_decl) (a b:expr)
  : Lemma (requires D.scoped scope (App f [a; b]) /\ T.classify f == T.Implication)
          (ensures D.scoped scope a /\ D.scoped scope b /\ get_sort a == bool_sort /\ get_sort b == bool_sort /\
                   get_sort (App f [a; b]) == bool_sort /\
                   T.truth_at s bc eq other scope rho (App f [a; b]) ==
                   (not (T.truth_at s bc eq other scope rho a) || T.truth_at s bc eq other scope rho b)) =
  V.lemma_sort_eq (get_sort a) bool_sort;
  V.lemma_sort_eq (get_sort b) bool_sort;
  T.lemma_evaluate_core_at s bc eq other scope rho f [a; b];
  assert_norm (T.evaluate_arguments_at s bc eq other scope rho [a; b] [bool_sort; bool_sort] ==
               [T.evaluate_at s bc eq other scope rho a; T.evaluate_at s bc eq other scope rho b])

let lemma_truth_ite (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                    (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                    (scope:list sort) (rho:V.environment base (S.signature s) scope)
                    (f:func_decl) (c x y:expr)
  : Lemma (requires D.scoped scope (App f [c; x; y]) /\ T.classify f == T.Choice bool_sort)
          (ensures D.scoped scope c /\ D.scoped scope x /\ D.scoped scope y /\
                   get_sort c == bool_sort /\ get_sort x == bool_sort /\ get_sort y == bool_sort /\
                   get_sort (App f [c; x; y]) == bool_sort /\
                   T.truth_at s bc eq other scope rho (App f [c; x; y]) ==
                   (if T.truth_at s bc eq other scope rho c
                    then T.truth_at s bc eq other scope rho x else T.truth_at s bc eq other scope rho y)) =
  assert (f == T.ite_decl bool_sort);
  V.lemma_sort_eq (get_sort c) bool_sort;
  V.lemma_sort_eq (get_sort x) bool_sort;
  V.lemma_sort_eq (get_sort y) bool_sort;
  T.lemma_evaluate_core_at s bc eq other scope rho f [c; x; y];
  assert_norm (T.evaluate_arguments_at s bc eq other scope rho [c; x; y] [bool_sort; bool_sort; bool_sort] ==
               [T.evaluate_at s bc eq other scope rho c; T.evaluate_at s bc eq other scope rho x;
                T.evaluate_at s bc eq other scope rho y])

let lemma_truth_iff (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                    (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                    (scope:list sort) (rho:V.environment base (S.signature s) scope)
                    (f:func_decl) (a b:expr)
  : Lemma (requires D.scoped scope (App f [a; b]) /\ T.classify f == T.Equality bool_sort)
          (ensures D.scoped scope a /\ D.scoped scope b /\ get_sort a == bool_sort /\ get_sort b == bool_sort /\
                   get_sort (App f [a; b]) == bool_sort /\
                   T.truth_at s bc eq other scope rho (App f [a; b]) ==
                   (T.truth_at s bc eq other scope rho a = T.truth_at s bc eq other scope rho b)) =
  assert (f == R.eq_decl bool_sort);
  V.lemma_sort_eq (get_sort a) bool_sort;
  V.lemma_sort_eq (get_sort b) bool_sort;
  assert (App f [a; b] == R.mk_eq_expr a b);
  T.lemma_boolean_equality_at s bc eq other scope rho a b

(* Universal and existential truth at a scope, from the quantifier laws. *)
let lemma_exists_truth (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (scope:list sort) (rho:V.environment base (S.signature s) scope)
                       (bound:list sort) (body:expr)
  : Lemma (requires E.exists_model s bc other /\
                    D.scoped (L.rev bound @ scope) body /\ get_sort body == bool_sort)
          (ensures
            T.truth_at s bc eq other scope rho (Quantifier Exists_k bound bool_sort body) <==>
            (exists (vs:V.arguments base (S.signature s) (L.rev bound)).
               T.truth_at s bc eq other (L.rev bound @ scope)
                 (V.extend (S.signature s) scope (L.rev bound) vs rho) body)) =
  let f = V.typed_body (S.signature s) bound bool_sort
    (V.evaluate_body (S.signature s) (T.interpretation s bc eq other) scope rho bound body) in
  assert (E.exists_case s bc other bound f);
  assert (T.truth_value s bc (other.V.quantification Exists_k bound bool_sort f) <==>
          (exists (vs:V.arguments base (S.signature s) (L.rev bound)).
             T.truth_value s bc (f vs)))

(* ---------------------------------------------------------------------- *)
(* 5. Child facts and the local rules                                       *)
(* ---------------------------------------------------------------------- *)

let lemma_positive (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                   (scope:list sort) (rho:V.environment base (S.signature s) scope)
                   (c r:expr) (j:U.judgment)
  : Lemma (requires positive c r j /\ holds_at s bc eq other scope rho j)
          (ensures D.scoped scope c /\ D.scoped scope r /\ get_sort c == get_sort r /\
                   T.evaluate_at s bc eq other scope rho c == T.evaluate_at s bc eq other scope rho r /\
                   T.truth_at s bc eq other scope rho r == T.truth_at s bc eq other scope rho c) =
  lemma_edge s bc eq other scope rho j c r

let lemma_negative (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                   (scope:list sort) (rho:V.environment base (S.signature s) scope)
                   (c r:expr) (j:U.judgment)
  : Lemma (requires negative c r j /\ holds_at s bc eq other scope rho j /\
                    D.scoped scope c /\ get_sort c == bool_sort)
          (ensures D.scoped scope r /\ get_sort r == bool_sort /\
                   T.truth_at s bc eq other scope rho r == not (T.truth_at s bc eq other scope rho c)) =
  match edge j with
  | Some (l, _) ->
    lemma_edge s bc eq other scope rho j l r;
    if negation_of c l then (
      match l with App f [x] -> lemma_truth_not s bc eq other scope rho f x | _ -> ())
    else if negation_of c r then (
      match r with App f [x] -> lemma_truth_not s bc eq other scope rho f x | _ -> ())
    else if negation_of r c then (
      match c with App f [x] -> lemma_truth_not s bc eq other scope rho f x | _ -> ())
    else if constant_of c true then (
      lemma_truth_constant s bc eq other scope rho c true;
      lemma_truth_constant s bc eq other scope rho r false)
    else (
      lemma_truth_constant s bc eq other scope rho c false;
      lemma_truth_constant s bc eq other scope rho r true)
  | None -> ()

let lemma_child (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                (scope:list sort) (rho:V.environment base (S.signature s) scope)
                (pol:bool) (c r:expr) (j:U.judgment)
  : Lemma (requires child pol c r j /\ holds_at s bc eq other scope rho j /\
                    D.scoped scope c /\ get_sort c == bool_sort)
          (ensures D.scoped scope r /\ get_sort r == bool_sort /\
                   T.truth_at s bc eq other scope rho r ==
                   (if pol then T.truth_at s bc eq other scope rho c else not (T.truth_at s bc eq other scope rho c))) =
  if pol then lemma_positive s bc eq other scope rho c r j
  else lemma_negative s bc eq other scope rho c r j

let rec pointwise (pol:bool) (rho:expr -> GTot bool) (cs ts:list expr) : GTot bool (decreases cs) =
  match cs, ts with
  | [], [] -> true
  | c :: cs', t :: ts' -> rho t = (if pol then rho c else not (rho c)) && pointwise pol rho cs' ts'
  | _, _ -> false

let rec lemma_children (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (scope:list sort) (rho:V.environment base (S.signature s) scope)
                       (pol:bool) (cs ts:list expr) (dom:list sort) (facts:list U.judgment)
  : Lemma (requires children_ok pol cs ts facts /\ all_hold s bc eq other scope rho facts /\
                    D.scoped_args scope cs /\ sorts_match cs dom /\ T.boolean_sorts dom)
          (ensures pointwise pol (T.truth_at s bc eq other scope rho) cs ts)
          (decreases cs) =
  match cs, ts, facts, dom with
  | c :: cs', t :: ts', j :: js, d :: dom' ->
    V.lemma_sort_eq (get_sort c) d;
    lemma_child s bc eq other scope rho pol c t j;
    lemma_children s bc eq other scope rho pol cs' ts' dom' js
  | _, _, _, _ -> ()

(* n-ary De Morgan (and the positive congruence), by list induction. *)
let rec lemma_dual_args (pol:bool) (rho:expr -> GTot bool) (op:B.nary_op) (cs ts:list expr)
  : Lemma (requires op <> B.Xor /\ pointwise pol rho cs ts)
          (ensures B.geval_args rho (if pol then op else dual_op op) (L.map B.Atom ts) ==
                   (if pol then B.geval_args rho op (L.map B.Atom cs)
                    else not (B.geval_args rho op (L.map B.Atom cs))))
          (decreases cs) =
  match cs, ts with
  | _ :: cs', _ :: ts' -> lemma_dual_args pol rho op cs' ts'
  | _, _ -> ()

let lemma_nary_ok (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                  (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                  (scope:list sort) (rho:V.environment base (S.signature s) scope)
                  (pol:bool) (f g:func_decl) (op:B.nary_op) (args ts:list expr) (facts:list U.judgment)
  : Lemma (requires T.classify f == T.Nary op /\ op <> B.Xor /\
                    T.classify g == T.Nary (if pol then op else dual_op op) /\
                    children_ok pol args ts facts /\ all_hold s bc eq other scope rho facts /\
                    D.scoped scope (App f args) /\ D.scoped scope (App g ts))
          (ensures get_sort (App f args) == bool_sort /\ get_sort (App g ts) == bool_sort /\
                   T.truth_at s bc eq other scope rho (App g ts) ==
                   (if pol then T.truth_at s bc eq other scope rho (App f args)
                    else not (T.truth_at s bc eq other scope rho (App f args)))) =
  lemma_children s bc eq other scope rho pol args ts f.domain facts;
  lemma_dual_args pol (T.truth_at s bc eq other scope rho) op args ts;
  lemma_truth_nary s bc eq other scope rho f args op;
  lemma_truth_nary s bc eq other scope rho g ts (if pol then op else dual_op op)

let lemma_and_of_ors (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                     (scope:list sort) (rho:V.environment base (S.signature s) scope)
                     (t x1 y1 x2 y2:expr)
  : Lemma (requires D.scoped scope t /\ and_of_ors t == Some (x1, y1, x2, y2))
          (ensures get_sort t == bool_sort /\
                   T.truth_at s bc eq other scope rho t ==
                   ((T.truth_at s bc eq other scope rho x1 || T.truth_at s bc eq other scope rho y1) &&
                    (T.truth_at s bc eq other scope rho x2 || T.truth_at s bc eq other scope rho y2))) =
  match t with
  | App a [App o1 [_; _]; App o2 [_; _]] ->
    lemma_truth_or2 s bc eq other scope rho a (App o1 [x1; y1]) (App o2 [x2; y2]) B.And;
    lemma_truth_or2 s bc eq other scope rho o1 x1 y1 B.Or;
    lemma_truth_or2 s bc eq other scope rho o2 x2 y2 B.Or
  | _ -> ()

let lemma_ite_ok (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                 (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                 (scope:list sort) (rho:V.environment base (S.signature s) scope)
                 (pol:bool) (f:func_decl) (c x y t:expr) (facts:list U.judgment)
  : Lemma (requires T.classify f == T.Choice bool_sort /\ ite_ok pol c x y t facts /\
                    all_hold s bc eq other scope rho facts /\
                    D.scoped scope (App f [c; x; y]) /\ D.scoped scope t)
          (ensures get_sort t == bool_sort /\
                   T.truth_at s bc eq other scope rho t ==
                   (if pol then T.truth_at s bc eq other scope rho (App f [c; x; y])
                    else not (T.truth_at s bc eq other scope rho (App f [c; x; y])))) =
  lemma_truth_ite s bc eq other scope rho f c x y;
  match and_of_ors t, facts with
  | Some (nc', x', c', y'), [jc; jn; jx; jy] ->
    lemma_and_of_ors s bc eq other scope rho t nc' x' c' y';
    lemma_positive s bc eq other scope rho c c' jc;
    lemma_negative s bc eq other scope rho c nc' jn;
    lemma_child s bc eq other scope rho pol x x' jx;
    lemma_child s bc eq other scope rho pol y y' jy
  | _, _ -> ()

(* `equivalence`: t is equivalent to (a <=> b); otherwise to (a xor b). *)
let lemma_iff_ok (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                 (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                 (scope:list sort) (rho:V.environment base (S.signature s) scope)
                 (equivalence:bool) (a b t:expr) (facts:list U.judgment)
  : Lemma (requires iff_ok equivalence a b t facts /\ all_hold s bc eq other scope rho facts /\
                    D.scoped scope a /\ D.scoped scope b /\ get_sort a == bool_sort /\ get_sort b == bool_sort /\
                    D.scoped scope t)
          (ensures get_sort t == bool_sort /\
                   T.truth_at s bc eq other scope rho t ==
                   (if equivalence then T.truth_at s bc eq other scope rho a = T.truth_at s bc eq other scope rho b
                    else T.truth_at s bc eq other scope rho a <> T.truth_at s bc eq other scope rho b)) =
  match and_of_ors t, facts with
  | Some (x1, y1, x2, y2), [ja; jna; jb; jnb] ->
    lemma_and_of_ors s bc eq other scope rho t x1 y1 x2 y2;
    lemma_positive s bc eq other scope rho b y1 jb;
    lemma_negative s bc eq other scope rho b y2 jnb;
    if equivalence then (
      lemma_negative s bc eq other scope rho a x1 jna;
      lemma_positive s bc eq other scope rho a x2 ja)
    else (
      lemma_positive s bc eq other scope rho a x1 ja;
      lemma_negative s bc eq other scope rho a x2 jna)
  | _, _ -> ()

let lemma_implies_ok (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                     (scope:list sort) (rho:V.environment base (S.signature s) scope)
                     (pol:bool) (f:func_decl) (a b t:expr) (facts:list U.judgment)
  : Lemma (requires T.classify f == T.Implication /\ implies_ok pol a b t facts /\
                    all_hold s bc eq other scope rho facts /\
                    D.scoped scope (App f [a; b]) /\ D.scoped scope t)
          (ensures get_sort t == bool_sort /\
                   T.truth_at s bc eq other scope rho t ==
                   (if pol then T.truth_at s bc eq other scope rho (App f [a; b])
                    else not (T.truth_at s bc eq other scope rho (App f [a; b])))) =
  lemma_truth_implies s bc eq other scope rho f a b;
  match t, facts with
  | App g [a'; b'], [ja; jb] ->
    lemma_truth_or2 s bc eq other scope rho g a' b' (if pol then B.Or else B.And);
    lemma_child s bc eq other scope rho (not pol) a a' ja;
    lemma_child s bc eq other scope rho pol b b' jb
  | _, _ -> ()

let lemma_boolean_ok (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                     (scope:list sort) (rho:V.environment base (S.signature s) scope)
                     (pol:bool) (src t:expr) (facts:list U.judgment)
  : Lemma (requires boolean_ok pol src t facts /\ all_hold s bc eq other scope rho facts /\
                    D.scoped scope src /\ D.scoped scope t)
          (ensures get_sort src == bool_sort /\ get_sort t == bool_sort /\
                   T.truth_at s bc eq other scope rho t ==
                   (if pol then T.truth_at s bc eq other scope rho src else not (T.truth_at s bc eq other scope rho src))) =
  match src with
  | App f args ->
    (match T.classify f, args with
     | T.Nary B.Xor, [a; b] ->
       lemma_truth_or2 s bc eq other scope rho f a b B.Xor;
       V.lemma_sort_eq (get_sort a) bool_sort;
       V.lemma_sort_eq (get_sort b) bool_sort;
       lemma_iff_ok s bc eq other scope rho (not pol) a b t facts
     | T.Nary op, _ ->
       (match t with
        | App g ts -> lemma_nary_ok s bc eq other scope rho pol f g op args ts facts
        | _ -> ())
     | T.Negation, [x] ->
       lemma_truth_not s bc eq other scope rho f x;
       (match facts with [j] -> lemma_child s bc eq other scope rho (not pol) x t j | _ -> ())
     | T.Implication, [a; b] -> lemma_implies_ok s bc eq other scope rho pol f a b t facts
     | T.Choice _, [c; x; y] -> lemma_ite_ok s bc eq other scope rho pol f c x y t facts
     | T.Equality _, [a; b] ->
       lemma_truth_iff s bc eq other scope rho f a b;
       lemma_iff_ok s bc eq other scope rho pol a b t facts
     | _, _ -> ())
  | _ -> ()

(* Quantifier steps: the body premise is read ONLY at the extensions of the
   environment by the binder values, at the scope `L.rev bs @ scope`. *)
let lemma_quantifier_ok (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                        (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                        (scope:list sort) (rho:V.environment base (S.signature s) scope)
                        (pol:bool) (bs:list sort) (src t:expr) (facts:list U.judgment)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    quantifier_ok pol bs src t facts /\
                    all_valid s bc eq other (L.rev bs @ scope) facts /\
                    D.scoped scope src /\ D.scoped scope t)
          (ensures get_sort src == bool_sort /\ get_sort t == bool_sort /\
                   (if pol then same_at s bc eq other scope rho src t
                    else T.truth_at s bc eq other scope rho t == not (T.truth_at s bc eq other scope rho src))) =
  match src, t, facts with
  | Quantifier k _ _ a, Quantifier k' _ _ b, [j] ->
    let sigma = S.signature s in
    let inner = L.rev bs @ scope in
    let at (vs:V.arguments base sigma (L.rev bs))
      : Lemma (D.scoped inner b /\ get_sort b == bool_sort /\
               (if pol then
                  T.evaluate_at s bc eq other inner (V.extend sigma scope (L.rev bs) vs rho) a ==
                  T.evaluate_at s bc eq other inner (V.extend sigma scope (L.rev bs) vs rho) b
                else
                  T.truth_at s bc eq other inner (V.extend sigma scope (L.rev bs) vs rho) b ==
                  not (T.truth_at s bc eq other inner (V.extend sigma scope (L.rev bs) vs rho) a))) =
      let rho' = V.extend sigma scope (L.rev bs) vs rho in
      assert (holds_at s bc eq other inner rho' j);
      if pol then lemma_positive s bc eq other inner rho' a b j
      else lemma_negative s bc eq other inner rho' a b j in
    FStar.Classical.forall_intro at;
    if pol then (
      V.lemma_quantifier_congruence sigma (T.interpretation s bc eq other) scope rho k bs bool_sort a b;
      lemma_same_at s bc eq other scope rho src t)
    else if k = Exists_k then (
      lemma_exists_truth s bc eq other scope rho bs a;
      Q.lemma_forall_truth s bc eq other scope rho bs b)
    else (
      Q.lemma_forall_truth s bc eq other scope rho bs a;
      lemma_exists_truth s bc eq other scope rho bs b)
  | _, _, _ -> ()

(* Congruence. *)
let rec lemma_arguments_ok (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                           (scope:list sort) (rho:V.environment base (S.signature s) scope)
                           (xs ys:list expr) (dom:list sort) (facts:list U.judgment)
  : Lemma (requires arguments_ok xs ys facts /\ all_hold s bc eq other scope rho facts /\
                    D.scoped_args scope xs /\ D.scoped_args scope ys /\ sorts_match xs dom /\ sorts_match ys dom)
          (ensures V.evaluate_args (S.signature s) (T.interpretation s bc eq other) scope rho xs dom ==
                   V.evaluate_args (S.signature s) (T.interpretation s bc eq other) scope rho ys dom)
          (decreases xs) =
  match xs, ys, dom with
  | x :: xs', y :: ys', d :: dom' ->
    V.lemma_sort_eq (get_sort x) d;
    V.lemma_sort_eq (get_sort y) d;
    (match facts with
     | j :: js ->
       if edge j = Some (x, y) then (
         lemma_edge s bc eq other scope rho j x y;
         lemma_arguments_ok s bc eq other scope rho xs' ys' dom' js)
       else lemma_arguments_ok s bc eq other scope rho xs' ys' dom' facts
     | [] -> lemma_arguments_ok s bc eq other scope rho xs' ys' dom' [])
  | _, _, _ -> ()

(* A closed assertion equation holds at every scope. *)
let rec lemma_member_truth (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                           (es:list expr) (e:expr)
  : Lemma (requires T.truths s bc eq other es /\ L.mem e es)
          (ensures T.truth s bc eq other e)
          (decreases es) =
  match es with [] -> () | x :: rest -> if x <> e then lemma_member_truth s bc eq other rest e

let lemma_assertion_edge (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                         (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                         (assertions:list expr) (scope:list sort) (rho:V.environment base (S.signature s) scope)
                         (a b:expr)
  : Lemma (requires T.truths s bc eq other assertions /\ L.mem (R.mk_eq_expr a b) assertions /\
                    D.scoped scope a /\ D.scoped scope b)
          (ensures same_at s bc eq other scope rho a b) =
  let sigma = S.signature s in
  let i = T.interpretation s bc eq other in
  let empty = T.empty_environment #base sigma in
  lemma_member_truth s bc eq other assertions (R.mk_eq_expr a b);
  assert (D.scoped [] (R.mk_eq_expr a b));
  assert (D.scoped [] a /\ D.scoped [] b);
  V.lemma_sort_eq (get_sort b) (get_sort a);
  T.lemma_equality s bc eq other a b;
  Q.lemma_closed_values sigma i empty [a; b];
  assert (V.evaluate sigma i scope rho a == V.evaluate sigma i [] empty a);
  assert (V.evaluate sigma i scope rho b == V.evaluate sigma i [] empty b);
  lemma_same_at s bc eq other scope rho a b

let rec lemma_find_closure (lhs rhs:expr) (es:list expr) (cb:list sort)
  : Lemma (requires find_closure lhs rhs es == Some cb)
          (ensures L.mem (Quantifier Forall_k cb bool_sort (R.mk_eq_expr lhs rhs)) es)
          (decreases es) =
  match es with
  | [] -> ()
  | a :: rest ->
    (match a with
     | Quantifier Forall_k cb' s body ->
       if s = bool_sort && body = R.mk_eq_expr lhs rhs then () else lemma_find_closure lhs rhs rest cb
     | _ -> lemma_find_closure lhs rhs rest cb)

(* An argument tuple for the closure's binders built from an environment of
   the step's scope: the environment's value where the two scopes have the
   same sort, any value of the sort elsewhere (a ghost value of the
   interpretation itself; every carrier of an interpretation is inhabited by
   its constants). Never executed. *)
let inhabitant_decl (t:sort) : func_decl =
  { decl_name = "inhabitant"; domain = []; range = t; interp = None; int_params = [] }

let rec transport (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                  (scope:list sort) (rho:V.environment base sigma scope) (offset:nat) (ss:list sort)
  : GTot (V.arguments base sigma ss) (decreases ss) =
  match ss with
  | [] -> []
  | t :: rest ->
    let v : V.value base sigma t =
      if offset < L.length scope && L.index scope offset = t then rho offset
      else i.V.application (inhabitant_decl t) [] in
    v :: transport sigma i scope rho (offset + 1) rest

let rec lemma_transport (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                        (scope:list sort) (rho:V.environment base sigma scope) (offset:nat) (ss:list sort)
                        (n:nat{n < L.length ss})
  : Lemma (requires offset + n < L.length scope /\ L.index scope (offset + n) == L.index ss n)
          (ensures (E.tuple_at sigma ss (transport sigma i scope rho offset ss) n <: V.tree base) ==
                   (rho (offset + n) <: V.tree base))
          (decreases ss) =
  match ss with
  | _ :: rest -> if n > 0 then lemma_transport sigma i scope rho (offset + 1) rest (n - 1)

(* A dependent Skolem step read through its closure: if the universal
   closure (forall cb. (= a b)) is an assertion, the equation holds at every
   environment of every scope at which both sides are typed (coincidence
   between the closure's scope and that scope, Z3SortedDependentSkolem). *)
let lemma_closure_edge (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (assertions:list expr) (scope:list sort) (rho:V.environment base (S.signature s) scope)
                       (a b:expr) (cb:list sort)
  : Lemma (requires Q.forall_model s bc other /\ T.truths s bc eq other assertions /\
                    L.mem (Quantifier Forall_k cb bool_sort (R.mk_eq_expr a b)) assertions /\
                    D.scoped scope a /\ D.scoped scope b /\ get_sort a == get_sort b)
          (ensures same_at s bc eq other scope rho a b) =
  let sigma = S.signature s in
  let i = T.interpretation s bc eq other in
  let empty = T.empty_environment #base sigma in
  let eqn = R.mk_eq_expr a b in
  let c = L.rev cb @ [] in
  lemma_member_truth s bc eq other assertions (Quantifier Forall_k cb bool_sort eqn);
  assert (D.scoped c eqn);
  Q.lemma_forall_truth s bc eq other [] empty cb eqn;
  let vs = transport sigma other scope rho 0 (L.rev cb) in
  let eta : V.environment base sigma c = V.extend sigma [] (L.rev cb) vs empty in
  assert (T.truth_at s bc eq other c eta eqn);
  let at (n:nat{n < L.length c /\ n < L.length scope})
    : Lemma (L.index c n == L.index scope n ==> (eta n <: V.tree base) == (rho n <: V.tree base)) =
    DS.lemma_extend_index sigma [] (L.rev cb) vs empty n;
    DS.lemma_index_split (L.rev cb) [] n;
    if L.index c n = L.index scope n then lemma_transport sigma other scope rho 0 (L.rev cb) n in
  FStar.Classical.forall_intro at;
  assert (DS.compatible sigma c scope eta rho);
  assert (D.scoped scope eqn);
  DS.lemma_coincide sigma i c scope eta rho eqn;
  T.lemma_equality_at s bc eq other scope rho a b;
  lemma_same_at s bc eq other scope rho a b

(* ---------------------------------------------------------------------- *)
(* 6. One entry at one assigned scope                                       *)
(* ---------------------------------------------------------------------- *)

let lemma_entry_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                   (assertions:list expr) (e:U.binder_entry) (j:U.judgment) (facts:list U.judgment)
                   (scope:list sort) (rho:V.environment base (S.signature s) scope)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    T.truths s bc eq other assertions /\
                    entry_ok assertions e j facts /\ BS.binder_judgment_scoped scope j /\
                    all_valid s bc eq other (BS.premise_scope_of e scope) facts)
          (ensures holds_at s bc eq other scope rho j) =
  match edge j with
  | None -> ()
  | Some (lhs, rhs) ->
    assert (D.scoped scope lhs /\ D.scoped scope rhs);
    let name = e.U.binder_name in
    if name = "nnf-neg" then (
      match lhs with
      | App n [src] ->
        lemma_truth_not s bc eq other scope rho n src;
        (match e.U.binder_sorts with
         | Some bs -> lemma_quantifier_ok s bc eq other scope rho false bs src rhs facts
         | None ->
           lemma_all_hold s bc eq other scope rho facts;
           lemma_boolean_ok s bc eq other scope rho false src rhs facts);
        lemma_same_truth s bc eq other scope rho lhs rhs
      | _ -> ())
    else if name = "nnf-pos" then (
      match e.U.binder_sorts with
      | Some bs -> lemma_quantifier_ok s bc eq other scope rho true bs lhs rhs facts
      | None ->
        lemma_all_hold s bc eq other scope rho facts;
        lemma_boolean_ok s bc eq other scope rho true lhs rhs facts;
        lemma_same_truth s bc eq other scope rho lhs rhs)
    else (
      lemma_all_hold s bc eq other scope rho facts;
      if name = "refl" then lemma_same_at s bc eq other scope rho lhs rhs
      else if name = "trans" then (
        match facts with
        | [p; q] ->
          (match edge p, edge q with
           | Some (a, b), Some (b', c) ->
             lemma_edge s bc eq other scope rho p a b;
             lemma_edge s bc eq other scope rho q b' c;
             lemma_same_at s bc eq other scope rho lhs rhs
           | _, _ -> ())
        | _ -> ())
      else if name = "monotonicity" then (
        match lhs, rhs with
        | App f xs, App _ ys ->
          lemma_arguments_ok s bc eq other scope rho xs ys f.domain facts;
          lemma_same_at s bc eq other scope rho lhs rhs
        | _, _ -> ())
      else if L.mem (R.mk_eq_expr lhs rhs) assertions then
        lemma_assertion_edge s bc eq other assertions scope rho lhs rhs
      else (
        let cb = Some?.v (find_closure lhs rhs assertions) in
        lemma_find_closure lhs rhs assertions cb;
        lemma_closure_edge s bc eq other assertions scope rho lhs rhs cb))

let lemma_entry_valid (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                      (assertions:list expr) (e:U.binder_entry) (j:U.judgment) (facts:list U.judgment)
                      (scope:list sort)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    T.truths s bc eq other assertions /\
                    entry_ok assertions e j facts /\ BS.binder_judgment_scoped scope j /\
                    all_valid s bc eq other (BS.premise_scope_of e scope) facts)
          (ensures valid s bc eq other scope j) =
  let at (rho:V.environment base (S.signature s) scope) : Lemma (holds_at s bc eq other scope rho j) =
    lemma_entry_at s bc eq other assertions e j facts scope rho in
  FStar.Classical.forall_intro at

(* ---------------------------------------------------------------------- *)
(* 7. The certificate: induction over the entries, on the final cache       *)
(* ---------------------------------------------------------------------- *)

[@@"opaque_to_smt"]
let entry_valid (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                (t:U.scope_demands) (cache:I.index_tree U.judgment) (key:nat) : prop =
  forall (sc:list sort). L.memP sc (U.scope_demanded t key) ==>
    Some? (I.index_find cache key) /\ valid s bc eq other sc (Some?.v (I.index_find cache key))

let lemma_entry_valid_def (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                          (t:U.scope_demands) (cache:I.index_tree U.judgment) (key:nat)
  : Lemma (entry_valid s bc eq other t cache key <==>
           (forall (sc:list sort). L.memP sc (U.scope_demanded t key) ==>
              Some? (I.index_find cache key) /\ valid s bc eq other sc (Some?.v (I.index_find cache key)))) =
  reveal_opaque (`%entry_valid) (entry_valid s bc eq other t cache key)

let prefix_valid (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                 (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                 (t:U.scope_demands) (cache:I.index_tree U.judgment) (next:nat) : prop =
  forall (key:nat). key < next ==> entry_valid s bc eq other t cache key

(* The premises of an entry, read at the scope its user demanded. *)
let rec lemma_premises (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (t:U.scope_demands) (cache:I.index_tree U.judgment) (k:nat)
                       (ps:list int) (facts:list U.judgment) (sc:list sort)
  : Lemma (requires I.opt_map (I.index_find cache) ps == Some facts /\
                    BS.premises_demanded t k ps sc /\ prefix_valid s bc eq other t cache k)
          (ensures all_valid s bc eq other sc facts)
          (decreases ps) =
  match ps, facts with
  | p :: rest, _ :: remaining ->
    FStar.List.Tot.Properties.mem_memP sc (U.scope_demanded t p);
    let key : nat = p in
    assert (entry_valid s bc eq other t cache key);
    lemma_entry_valid_def s bc eq other t cache key;
    lemma_premises s bc eq other t cache k rest remaining sc
  | _, _ -> ()

let lemma_prefix_extend (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                        (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                        (t:U.scope_demands) (cache:I.index_tree U.judgment) (k:nat)
  : Lemma (requires prefix_valid s bc eq other t cache k /\ entry_valid s bc eq other t cache k)
          (ensures prefix_valid s bc eq other t cache (k + 1)) = ()

let lemma_step (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
               (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
               (assertions:list expr) (t:U.scope_demands) (cache:I.index_tree U.judgment)
               (k:nat) (e:U.binder_entry) (j:U.judgment) (facts:list U.judgment)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    T.truths s bc eq other assertions /\
                    I.index_find cache k == Some j /\
                    I.opt_map (I.index_find cache) e.U.binder_premises == Some facts /\
                    entry_ok assertions e j facts /\
                    BS.entry_scoped t k e j (U.scope_demanded t k) /\
                    prefix_valid s bc eq other t cache k)
          (ensures entry_valid s bc eq other t cache k) =
  let here (sc:list sort)
    : Lemma (requires L.memP sc (U.scope_demanded t k))
            (ensures valid s bc eq other sc j) =
    BS.lemma_entry_scoped t k e j (U.scope_demanded t k) sc;
    lemma_premises s bc eq other t cache k e.U.binder_premises facts (BS.premise_scope_of e sc);
    lemma_entry_valid s bc eq other assertions e j facts sc in
  FStar.Classical.forall_intro (FStar.Classical.move_requires here);
  lemma_entry_valid_def s bc eq other t cache k

let lemma_unused (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                 (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                 (t:U.scope_demands) (cache:I.index_tree U.judgment) (k:nat)
  : Lemma (requires Nil? (U.scope_demanded t k))
          (ensures entry_valid s bc eq other t cache k) =
  lemma_entry_valid_def s bc eq other t cache k

let rec lemma_steps (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                    (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                    (assertions:list expr) (count:nat) (t:U.scope_demands) (cache:I.index_tree U.judgment)
                    (sizes:I.index_tree nat) (k:nat) (entries:list U.binder_entry) (work:nat)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    T.truths s bc eq other assertions /\
                    steps_ok assertions count t cache sizes k entries work /\
                    BS.entries_scoped t cache k entries /\
                    prefix_valid s bc eq other t cache k)
          (ensures prefix_valid s bc eq other t cache (k + L.length entries))
          (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    if Nil? (U.scope_demanded t k) then (
      lemma_unused s bc eq other t cache k;
      lemma_prefix_extend s bc eq other t cache k;
      lemma_steps s bc eq other assertions count t cache sizes (k + 1) rest work)
    else match nodes_within work [e.U.binder_formula] with
    | None -> ()
    | Some w1 ->
      let size : nat = if w1 <= work then work - w1 else 0 in
      (match premise_charge sizes e.U.binder_premises w1 with
       | None -> ()
       | Some w2 ->
         let w3 = if e.U.binder_name = "sk" then (if count <= w2 then Some (w2 - count) else None) else Some w2 in
         (match w3, I.index_find cache k, I.opt_map_tail (I.index_find cache) e.U.binder_premises with
          | Some w, Some j, Some facts ->
            lemma_step s bc eq other assertions t cache k e j facts;
            lemma_prefix_extend s bc eq other t cache k;
            lemma_steps s bc eq other assertions count t cache (I.index_put sizes k size) (k + 1) rest w
          | _, _, _ -> ()))

(* ---------------------------------------------------------------------- *)
(* 8. The theorem                                                           *)
(* ---------------------------------------------------------------------- *)

(* A replayed certificate's conclusion is scoped at `[]` and holds in the
   Sorted model `other` over (bc, eq), given the universal and existential
   quantifier laws of `other` and the truth of the assertions it reads
   (only `sk` steps read them). *)
let lemma_replay (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                 (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                 (assertions:list expr) (c:U.binder_certificate) (concl:U.judgment)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    T.truths s bc eq other assertions /\ replay assertions c concl == Replayed)
          (ensures BS.binder_judgment_scoped [] concl /\
                   holds_at s bc eq other [] (T.empty_environment (S.signature s)) concl) =
  let entries = c.U.binder_entries in
  let n = U.count_cells 0 entries in
  let root = c.U.binder_root in
  match judgments_of entries I.Empty 0 with
  | None -> ()
  | Some cache ->
    (match U.binder_scopes (U.binder_demand_limit n) (U.binder_work_limit n) c with
     | None -> ()
     | Some (t, w) ->
       assert (U.binder_scoped_within (U.binder_demand_limit n) (U.binder_work_limit n) c cache);
       BS.lemma_guard (U.binder_demand_limit n) (U.binder_work_limit n) c cache;
       BS.lemma_count_cells 0 entries;
       lemma_steps s bc eq other assertions (U.count_cells 0 assertions) t cache I.Empty 0 entries
         (U.binder_work_limit n);
       let key : nat = root in
       assert (entry_valid s bc eq other t cache key);
       lemma_entry_valid_def s bc eq other t cache key;
       BS.lemma_scoped_at t cache entries key [])
