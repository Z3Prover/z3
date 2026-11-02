module Z3SortedDependentSkolem

(* Dependent Skolem FUNCTIONS for the Sorted epsilon route (nnf-neg/nnf-pos
   certificates, Z3NnfReplay), in the Sorted semantics of
   Z3SortedSemantics, with ONE joint choice per typed argument tuple.

   A dependent Skolem step `sk` inside an NNF certificate concludes
       (exists bs. body) ~ body[f_k(x_1, .., x_m) / bound_k]
   (or the negative form (not (forall bs. body)) ~ (not body[..])) at an
   OPEN scope: its free variables x_1..x_m are outer binders. The definition
   d = Z3Skolemization.definition_of(source, target) records the bound
   sorts, the dependencies deps = [(n_1, t_1); ..; (n_m, t_m)] (de Bruijn
   index in the outer scope and sort, in the order of the functions'
   arguments) and the witness functions f_k (domain = dependency sorts,
   range = the k-th bound sort of L.rev bs).

   1. The executable gate (`eligible`): SK.valid (complete typed argument
      tuples: every witness has domain = dependency sorts and range = its
      bound sort; the body mentions only the dependencies; witnesses fresh in
      the body; no repeated dependency index), at least one dependency (the
      zero-dependency case is the closed route of Z3SortedSkolem), witnesses
      that are uninterpreted functions outside every theory and datatype
      operator (`function_safe`), a dependency scope of at most
      `scope_limit` positions in which every dependency is typed
      (`deps_typed`), and the CLOSURE of the step scoped at [].

   2. The closure. The open equation is closed by quantifying over the
      dependency scope: position n of `closure_scope d` has the sort of the
      dependency with index n, or Bool for a position the step does not
      mention; `closure d` = (forall cb. (= source instance)) with
      L.rev cb @ [] = closure_scope d. It is a closed Boolean formula and is
      the only form in which the epsilon route exports a dependent step: the
      replay accepts an open `sk` step at a scope S only when its closure is
      an assertion, and reads it at S through `lemma_coincide` (both sides
      are typed at S and at the closure scope; the environments agree on
      every position where both scopes have the same sort).

   3. The model (`doverride`, `build`): for each argument tuple `args`, ONE
      whole bound tuple is chosen by the Root ghost choice
      (E.hilbert_choice, FStar.IndefiniteDescription only) for the joint
      predicate `dgoal`: the body holds (is false, for a negative step) at
      every environment of the closure scope that has the values `args` at
      the dependencies, read in the PRE-extension interpretation `other`
      (the witnesses do not occur in the body, so this is not circular).
      Every witness function returns ITS coordinate of that SAME tuple; every
      other symbol and the quantifiers are unchanged.

   4. Proved: the instance lemma (`lemma_instance`: at EVERY environment of
      the closure scope, the source and the instance have the same truth in
      the extension; by the open substitution lemma `lemma_substitute` for
      SK.substitute with dependency_arguments, the evaluation of a witness
      application as the coordinate of the selected tuple, and the coverage
      coincidence `lemma_covered`), the closure lemma, the context model of
      an ordered list of definitions built one after another from one
      `other` (`lemma_build_context`), preservation of the original inputs
      (`lemma_build_inputs`) and of the closed epsilon context
      (`lemma_build_closed`) by freshness, and the quantifier laws
      (`lemma_build_quantification`). No assumption, axiom or admit. *)

open Z3AstTheory
open FStar.List.Tot
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module I = Z3SortedInteger
module Q = Z3SortedQuantifier
module E = Z3SortedSkolem
module SK = Z3Skolemization
module D = Z3Definitions
module R = Z3ResolutionProofTheory
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module FE = FStar.FunctionalExtensionality

(* ---------------------------------------------------------------------- *)
(* 1. The executable gate                                                   *)
(* ---------------------------------------------------------------------- *)

(* Every dependency names a position of `scope` with exactly its sort. *)
let rec deps_typed (scope:list sort) (deps:list SK.dependency) : Tot bool (decreases deps) =
  match deps with
  | [] -> true
  | (n, t) :: rest -> n < L.length scope && L.index scope n = t && deps_typed scope rest

let rec dependency_sort (deps:list SK.dependency) (n:nat) : Tot (option sort) (decreases deps) =
  match deps with
  | [] -> None
  | (m, t) :: rest -> if m = n then Some t else dependency_sort rest n

(* One more than the largest dependency index. *)
let rec dependency_bound (deps:list SK.dependency) : Tot nat (decreases deps) =
  match deps with
  | [] -> 0
  | (n, _) :: rest -> let b = dependency_bound rest in if n + 1 > b then n + 1 else b

(* Positions n .. n + count - 1 of the dependency scope. *)
let rec padded (deps:list SK.dependency) (n count:nat) : Tot (list sort) (decreases count) =
  if count = 0 then []
  else (match dependency_sort deps n with Some t -> t | None -> bool_sort) :: padded deps (n + 1) (count - 1)

(* A documented conservative cap on the size of a dependency scope (its
   positions are allocated); no realistic binder nesting reaches it. *)
let scope_limit : nat = 4096

let closure_binders (d:SK.definition) : list sort =
  if dependency_bound d.SK.dependencies <= scope_limit
  then L.rev (padded d.SK.dependencies 0 (dependency_bound d.SK.dependencies))
  else []

(* The scope of the closure's body (L.rev of its binder list, as D.scoped
   reads a quantifier). *)
let closure_scope (d:SK.definition) : list sort = L.rev (closure_binders d) @ []

let closure_of (d:SK.definition) (b:expr) : expr =
  Quantifier Forall_k (closure_binders d) bool_sort (R.mk_eq_expr (SK.source d) b)

(* A witness: an uninterpreted function outside every theory operator, the
   datatype signature, recognizers and accessors (E.constant_safe without
   the arity restriction). *)
let function_safe (s:S.checked_schema) (f:func_decl) : bool =
  f.interp = None && f.int_params = [] &&
  not (L.mem f (S.signature s)) && T.classify f = T.Other &&
  I.classify f = I.Other && S.find_recognizer f s.S.cases = None &&
  S.find_accessor f s.S.cases = None

let rec safe_functions (s:S.checked_schema) (ws:list SK.witness) : Tot bool (decreases ws) =
  match ws with [] -> true | (_, f) :: rest -> function_safe s f && safe_functions s rest

let eligible (s:S.checked_schema) (d:SK.definition) : bool =
  SK.valid d && Cons? d.SK.dependencies && safe_functions s d.SK.witnesses &&
  dependency_bound d.SK.dependencies <= scope_limit &&
  deps_typed (closure_scope d) d.SK.dependencies &&
  D.scoped (L.rev d.SK.bound_sorts @ closure_scope d) d.SK.body &&
  (match SK.substitute 0 (L.length d.SK.bound_sorts) d.SK.dependencies d.SK.witnesses d.SK.body,
         SK.instantiation d with
   | Some target, Some b -> D.scoped (closure_scope d) target && D.scoped [] (closure_of d b)
   | _, _ -> false)

type definition (s:S.checked_schema) = d:SK.definition{eligible s d}

(* The substituted body and the instance (the target, negated for a
   negative step) of an eligible definition. *)
let target_of (#s:S.checked_schema) (d:definition s) : expr =
  Some?.v (SK.substitute 0 (L.length d.SK.bound_sorts) d.SK.dependencies d.SK.witnesses d.SK.body)

let instance_of (#s:S.checked_schema) (d:definition s) : expr = Some?.v (SK.instantiation d)

let closure (#s:S.checked_schema) (d:definition s) : expr = closure_of d (instance_of d)

(* The definition of an `sk` step (source ~ target), when eligible. *)
let definition_of (s:S.checked_schema) (a b:expr) : option (definition s) =
  match SK.definition_of a b with
  | Some d -> if eligible s d then Some d else None
  | None -> None

let rec erase (s:S.checked_schema) (ds:list (definition s)) : Tot (list SK.definition) (decreases ds) =
  match ds with [] -> [] | d :: rest -> (d <: SK.definition) :: erase s rest

let rec closures (s:S.checked_schema) (ds:list (definition s)) : Tot (list expr) (decreases ds) =
  match ds with [] -> [] | d :: rest -> closure d :: closures s rest

(* ---------------------------------------------------------------------- *)
(* 2. Environments                                                          *)
(* ---------------------------------------------------------------------- *)

let rec lemma_index_split (xs ys:list sort) (n:nat{n < L.length (xs @ ys)})
  : Lemma (ensures (LP.append_length xs ys;
                    (n < L.length xs ==> L.index (xs @ ys) n == L.index xs n) /\
                    (n >= L.length xs ==> n - L.length xs < L.length ys /\
                                          L.index (xs @ ys) n == L.index ys (n - L.length xs))))
          (decreases xs) =
  LP.append_length xs ys;
  match xs with
  | [] -> ()
  | _ :: rest -> if n > 0 then lemma_index_split rest ys (n - 1)

let rec lemma_extend_index (#base:sort -> Type0) (sigma:V.signature) (scope bound:list sort)
                           (vs:V.arguments base sigma bound) (rho:V.environment base sigma scope)
                           (n:nat{n < L.length (bound @ scope)})
  : Lemma (ensures (LP.append_length bound scope;
                    (n < L.length bound ==>
                       (V.extend sigma scope bound vs rho n <: V.tree base) ==
                       (E.tuple_at sigma bound vs n <: V.tree base)) /\
                    (n >= L.length bound ==> n - L.length bound < L.length scope /\
                       (V.extend sigma scope bound vs rho n <: V.tree base) ==
                       (rho (n - L.length bound) <: V.tree base))))
          (decreases bound) =
  LP.append_length bound scope;
  match bound, vs with
  | [], [] -> ()
  | _ :: rest, _ :: tail -> if n > 0 then lemma_extend_index sigma scope rest tail rho (n - 1)
  | _, _ -> ()

(* Two environments of possibly different scopes agree at every position
   where both scopes have the same sort. *)
let compatible (#base:sort -> Type0) (sigma:V.signature) (a b:list sort)
               (rho:V.environment base sigma a) (eta:V.environment base sigma b) : prop =
  forall (n:nat{n < L.length a /\ n < L.length b}).
    L.index a n == L.index b n ==> (rho n <: V.tree base) == (eta n <: V.tree base)

let lemma_compatible_extend (#base:sort -> Type0) (sigma:V.signature) (a b bound:list sort)
                            (vs:V.arguments base sigma bound)
                            (rho:V.environment base sigma a) (eta:V.environment base sigma b)
  : Lemma (requires compatible sigma a b rho eta)
          (ensures compatible sigma (bound @ a) (bound @ b)
                     (V.extend sigma a bound vs rho) (V.extend sigma b bound vs eta)) =
  let at (n:nat{n < L.length (bound @ a) /\ n < L.length (bound @ b)})
    : Lemma (L.index (bound @ a) n == L.index (bound @ b) n ==>
             (V.extend sigma a bound vs rho n <: V.tree base) == (V.extend sigma b bound vs eta n <: V.tree base)) =
    lemma_extend_index sigma a bound vs rho n;
    lemma_extend_index sigma b bound vs eta n;
    lemma_index_split bound a n;
    lemma_index_split bound b n in
  FStar.Classical.forall_intro at

(* Coincidence across scopes: a term typed at both scopes has the same value
   at compatible environments. *)
let rec lemma_coincide (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                       (a b:list sort) (rho:V.environment base sigma a) (eta:V.environment base sigma b)
                       (e:expr)
  : Lemma (requires D.scoped a e /\ D.scoped b e /\ compatible sigma a b rho eta)
          (ensures (V.evaluate sigma i a rho e <: V.tree base) == (V.evaluate sigma i b eta e <: V.tree base))
          (decreases e) =
  match e with
  | Var n _ -> assert (L.index a n == L.index b n)
  | App f args -> lemma_coincide_args sigma i a b rho eta args f.domain
  | Quantifier k bound _ body ->
    let pointwise (vs:V.arguments base sigma (L.rev bound))
      : Lemma (V.evaluate sigma i (L.rev bound @ a) (V.extend sigma a (L.rev bound) vs rho) body ==
               V.evaluate sigma i (L.rev bound @ b) (V.extend sigma b (L.rev bound) vs eta) body) =
      lemma_compatible_extend sigma a b (L.rev bound) vs rho eta;
      lemma_coincide sigma i (L.rev bound @ a) (L.rev bound @ b)
        (V.extend sigma a (L.rev bound) vs rho) (V.extend sigma b (L.rev bound) vs eta) body in
    FStar.Classical.forall_intro pointwise;
    V.lemma_quantifier_environments sigma i a b rho eta k bound (get_sort body) body body

and lemma_coincide_args (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                        (a b:list sort) (rho:V.environment base sigma a) (eta:V.environment base sigma b)
                        (args:list expr) (ss:list sort)
  : Lemma (requires D.scoped_args a args /\ D.scoped_args b args /\ sorts_match args ss /\
                    compatible sigma a b rho eta)
          (ensures V.evaluate_args sigma i a rho args ss == V.evaluate_args sigma i b eta args ss)
          (decreases args) =
  match args, ss with
  | e :: rest, _ :: tail ->
    lemma_coincide sigma i a b rho eta e;
    lemma_coincide_args sigma i a b rho eta rest tail
  | _, _ -> ()

(* The positions an expression reads, by SK.covered: those below `depth`
   and the dependency indices above it. *)
let covered_agree (#base:sort -> Type0) (sigma:V.signature) (scope:list sort)
                  (rho eta:V.environment base sigma scope) (depth:nat) (deps:list SK.dependency) : prop =
  forall (n:nat{n < L.length scope}).
    (n < depth \/ L.mem (n - depth) (SK.dependency_indices deps)) ==> rho n == eta n

let lemma_covered_extend (#base:sort -> Type0) (sigma:V.signature) (scope bound:list sort)
                         (vs:V.arguments base sigma bound) (rho eta:V.environment base sigma scope)
                         (depth:nat) (deps:list SK.dependency)
  : Lemma (requires covered_agree sigma scope rho eta depth deps)
          (ensures covered_agree sigma (bound @ scope) (V.extend sigma scope bound vs rho)
                     (V.extend sigma scope bound vs eta) (depth + L.length bound) deps) =
  let at (n:nat{n < L.length (bound @ scope)})
    : Lemma ((n < depth + L.length bound \/ L.mem (n - (depth + L.length bound)) (SK.dependency_indices deps)) ==>
             V.extend sigma scope bound vs rho n == V.extend sigma scope bound vs eta n) =
    lemma_extend_index sigma scope bound vs rho n;
    lemma_extend_index sigma scope bound vs eta n;
    lemma_index_split bound scope n in
  FStar.Classical.forall_intro at

(* Coverage coincidence at one scope: an expression covered by `deps` has
   the same value at environments that agree on the positions it reads. *)
let rec lemma_covered (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                      (scope:list sort) (rho eta:V.environment base sigma scope)
                      (depth:nat) (deps:list SK.dependency) (e:expr)
  : Lemma (requires D.scoped scope e /\ SK.covered depth deps e /\ covered_agree sigma scope rho eta depth deps)
          (ensures V.evaluate sigma i scope rho e == V.evaluate sigma i scope eta e)
          (decreases e) =
  match e with
  | Var _ _ -> ()
  | App f args -> lemma_covered_args sigma i scope rho eta depth deps args f.domain
  | Quantifier k bound _ body ->
    LP.rev_length bound;
    let pointwise (vs:V.arguments base sigma (L.rev bound))
      : Lemma (V.evaluate sigma i (L.rev bound @ scope) (V.extend sigma scope (L.rev bound) vs rho) body ==
               V.evaluate sigma i (L.rev bound @ scope) (V.extend sigma scope (L.rev bound) vs eta) body) =
      lemma_covered_extend sigma scope (L.rev bound) vs rho eta depth deps;
      lemma_covered sigma i (L.rev bound @ scope) (V.extend sigma scope (L.rev bound) vs rho)
        (V.extend sigma scope (L.rev bound) vs eta) (depth + L.length bound) deps body in
    FStar.Classical.forall_intro pointwise;
    V.lemma_quantifier_environments sigma i scope scope rho eta k bound (get_sort body) body body

and lemma_covered_args (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                       (scope:list sort) (rho eta:V.environment base sigma scope)
                       (depth:nat) (deps:list SK.dependency) (args:list expr) (ss:list sort)
  : Lemma (requires D.scoped_args scope args /\ sorts_match args ss /\ SK.covered_args depth deps args /\
                    covered_agree sigma scope rho eta depth deps)
          (ensures V.evaluate_args sigma i scope rho args ss == V.evaluate_args sigma i scope eta args ss)
          (decreases args) =
  match args, ss with
  | e :: rest, _ :: tail ->
    lemma_covered sigma i scope rho eta depth deps e;
    lemma_covered_args sigma i scope rho eta depth deps rest tail
  | _, _ -> ()

(* ---------------------------------------------------------------------- *)
(* 3. Argument tuples                                                       *)
(* ---------------------------------------------------------------------- *)

(* The environment `rho` has the values `args` at the dependencies, read at
   positions shifted by `depth`. *)
let rec agrees (#base:sort -> Type0) (sigma:V.signature) (scope:list sort) (rho:V.environment base sigma scope)
               (depth:nat) (deps:list SK.dependency) (args:list (V.tree base)) : Tot prop (decreases deps) =
  match deps, args with
  | [], [] -> True
  | (n, _) :: rest, a :: tail ->
    depth + n < L.length scope /\ (rho (depth + n) <: V.tree base) == a /\ agrees sigma scope rho depth rest tail
  | _, _ -> False

(* The argument tuple of a typed environment. *)
let rec gather (#base:sort -> Type0) (sigma:V.signature) (scope:list sort) (rho:V.environment base sigma scope)
               (deps:list SK.dependency{deps_typed scope deps})
  : Tot (args:V.arguments base sigma (SK.dependency_sorts deps){agrees sigma scope rho 0 deps args})
        (decreases deps) =
  match deps with
  | [] -> []
  | (n, t) :: rest ->
    let v : V.value base sigma t = rho n in
    v :: gather sigma scope rho rest

let rec lemma_agrees_shift (#base:sort -> Type0) (sigma:V.signature) (scope bound:list sort)
                           (vs:V.arguments base sigma bound) (rho:V.environment base sigma scope)
                           (depth:nat) (deps:list SK.dependency) (args:list (V.tree base))
  : Lemma (requires agrees sigma scope rho depth deps args)
          (ensures agrees sigma (bound @ scope) (V.extend sigma scope bound vs rho) (depth + L.length bound) deps args)
          (decreases deps) =
  LP.append_length bound scope;
  match deps, args with
  | (n, _) :: rest, _ :: tail ->
    lemma_extend_index sigma scope bound vs rho (depth + L.length bound + n);
    lemma_agrees_shift sigma scope bound vs rho depth rest tail
  | _, _ -> ()

let rec lemma_agrees_same (#base:sort -> Type0) (sigma:V.signature) (scope:list sort)
                          (rho eta:V.environment base sigma scope)
                          (deps:list SK.dependency) (args:list (V.tree base)) (m:nat)
  : Lemma (requires agrees sigma scope rho 0 deps args /\ agrees sigma scope eta 0 deps args /\
                    L.mem m (SK.dependency_indices deps))
          (ensures m < L.length scope /\ rho m == eta m)
          (decreases deps) =
  match deps, args with
  | (n, _) :: rest, _ :: tail -> if m <> n then lemma_agrees_same sigma scope rho eta rest tail m
  | _, _ -> ()

(* The dependency arguments of a witness application evaluate to the tuple. *)
let rec lemma_dependency_arguments (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                                   (b:list sort) (eta:V.environment base sigma b) (depth:nat)
                                   (deps:list SK.dependency) (args:list (V.tree base)) (ss:list sort)
  : Lemma (requires agrees sigma b eta depth deps args /\
                    D.scoped_args b (SK.dependency_arguments depth deps) /\
                    sorts_match (SK.dependency_arguments depth deps) ss)
          (ensures (V.evaluate_args sigma i b eta (SK.dependency_arguments depth deps) ss <: list (V.tree base)) == args)
          (decreases deps) =
  match deps, args, ss with
  | (n, t) :: rest, _ :: tail, _ :: remaining ->
    lemma_dependency_arguments sigma i b eta depth rest tail remaining
  | _, _, _ -> ()

(* ---------------------------------------------------------------------- *)
(* 4. The open substitution lemma (SK.substitute with dependency_arguments) *)
(* ---------------------------------------------------------------------- *)

(* What a witness returns on the argument tuple (a tree; the default is
   never used: the domain is the dependency sorts by SK.valid_witnesses). *)
let witness_value (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                  (deps:list SK.dependency) (f:func_decl)
                  (args:V.arguments base sigma (SK.dependency_sorts deps)) : GTot (V.tree base) =
  if f.domain = SK.dependency_sorts deps then (i.V.application f args <: V.tree base) else V.Constructor f []

let coordinate (#base:sort -> Type0) (sigma:V.signature) (bound:list sort) (vs:V.arguments base sigma bound)
               (m:nat) : V.tree base =
  if m < L.length bound then (E.tuple_at sigma bound vs m <: V.tree base) else V.Constructor R.not_decl []

(* Every witness returns its coordinate of the ONE tuple `vs` on `args`. *)
let witness_selects (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                     (deps:list SK.dependency) (ws:list SK.witness) (bound:list sort)
                     (args:V.arguments base sigma (SK.dependency_sorts deps))
                     (vs:V.arguments base sigma bound) (m:nat) (f:func_decl) : prop =
  SK.lookup m ws == Some f ==>
    m < L.length bound /\ not (L.mem f sigma) /\ f.domain == SK.dependency_sorts deps /\
    witness_value sigma i deps f args == coordinate sigma bound vs m

let witnesses_select (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                     (deps:list SK.dependency) (ws:list SK.witness) (bound:list sort)
                     (args:V.arguments base sigma (SK.dependency_sorts deps))
                     (vs:V.arguments base sigma bound) : prop =
  forall (m:nat) (f:func_decl). witness_selects sigma i deps ws bound args vs m f

(* The environment of the substituted term (scope a) and of the result
   (scope b): equal below depth, the tuple vs at the substituted block, and
   shifted by the block above it. *)
let subst_envs (#base:sort -> Type0) (sigma:V.signature) (bound:list sort) (vs:V.arguments base sigma bound)
               (depth:nat) (a b:list sort) (rho:V.environment base sigma a) (eta:V.environment base sigma b)
  : prop =
  L.length a == L.length b + L.length bound /\ depth <= L.length b /\
  (forall (n:nat{n < L.length a}).
    (n < depth ==> (rho n <: V.tree base) == (eta n <: V.tree base)) /\
    (depth <= n /\ n < depth + L.length bound ==> (rho n <: V.tree base) == coordinate sigma bound vs (n - depth)) /\
    (depth + L.length bound <= n ==> (rho n <: V.tree base) == (eta (n - L.length bound) <: V.tree base)))

let lemma_subst_envs_extend (#base:sort -> Type0) (sigma:V.signature) (bound:list sort)
                            (vs:V.arguments base sigma bound) (depth:nat) (a b inner:list sort)
                            (ws:V.arguments base sigma inner)
                            (rho:V.environment base sigma a) (eta:V.environment base sigma b)
  : Lemma (requires subst_envs sigma bound vs depth a b rho eta)
          (ensures subst_envs sigma bound vs (depth + L.length inner) (inner @ a) (inner @ b)
                     (V.extend sigma a inner ws rho) (V.extend sigma b inner ws eta)) =
  LP.append_length inner a;
  LP.append_length inner b;
  let at (n:nat{n < L.length (inner @ a)})
    : Lemma ((n < depth + L.length inner ==>
                (V.extend sigma a inner ws rho n <: V.tree base) == (V.extend sigma b inner ws eta n <: V.tree base)) /\
             (depth + L.length inner <= n /\ n < depth + L.length inner + L.length bound ==>
                (V.extend sigma a inner ws rho n <: V.tree base) == coordinate sigma bound vs (n - (depth + L.length inner))) /\
             (depth + L.length inner + L.length bound <= n ==>
                (V.extend sigma a inner ws rho n <: V.tree base) ==
                (V.extend sigma b inner ws eta (n - L.length bound) <: V.tree base))) =
    lemma_extend_index sigma a inner ws rho n;
    if n < L.length inner then lemma_extend_index sigma b inner ws eta n
    else begin
      let k : nat = n - L.length inner in
      assert (k < L.length a);
      assert ((V.extend sigma a inner ws rho n <: V.tree base) == (rho k <: V.tree base));
      if k < depth then (
        lemma_extend_index sigma b inner ws eta n;
        assert ((V.extend sigma b inner ws eta n <: V.tree base) == (eta k <: V.tree base));
        assert ((rho k <: V.tree base) == (eta k <: V.tree base)))
      else if k < depth + L.length bound then
        assert ((rho k <: V.tree base) == coordinate sigma bound vs (k - depth))
      else (
        let n' : nat = n - L.length bound in
        assert (n' >= L.length inner /\ n' < L.length (inner @ b));
        lemma_extend_index sigma b inner ws eta n';
        assert (n' - L.length inner == k - L.length bound);
        assert ((V.extend sigma b inner ws eta n' <: V.tree base) == (eta (k - L.length bound) <: V.tree base));
        assert ((rho k <: V.tree base) == (eta (k - L.length bound) <: V.tree base)))
    end in
  FStar.Classical.forall_intro at

let rec lemma_substitute (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                         (deps:list SK.dependency) (ws:list SK.witness) (bound:list sort)
                         (args:V.arguments base sigma (SK.dependency_sorts deps))
                         (vs:V.arguments base sigma bound) (depth:nat) (a b:list sort)
                         (rho:V.environment base sigma a) (eta:V.environment base sigma b) (e r:expr)
  : Lemma (requires D.scoped a e /\ D.scoped b r /\
                    SK.substitute depth (L.length bound) deps ws e == Some r /\
                    subst_envs sigma bound vs depth a b rho eta /\
                    agrees sigma b eta depth deps args /\
                    witnesses_select sigma i deps ws bound args vs)
          (ensures (V.evaluate sigma i a rho e <: V.tree base) == (V.evaluate sigma i b eta r <: V.tree base))
          (decreases e) =
  match e with
  | Var n _ ->
    if n >= depth && n < depth + L.length bound then (
      let f = Some?.v (SK.lookup (n - depth) ws) in
      assert (r == App f (SK.dependency_arguments depth deps));
      assert (witness_selects sigma i deps ws bound args vs (n - depth) f);
      lemma_dependency_arguments sigma i b eta depth deps args f.domain)
  | App f xs ->
    (match r with
     | App _ ys -> lemma_substitute_args sigma i deps ws bound args vs depth a b rho eta xs ys f.domain
     | _ -> ())
  | Quantifier k inner _ body ->
    (match r with
     | Quantifier _ _ _ body' ->
       LP.rev_length inner;
       SK.lemma_substitute_sort (depth + L.length inner) (L.length bound) deps ws body body';
       let pointwise (us:V.arguments base sigma (L.rev inner))
         : Lemma (V.evaluate sigma i (L.rev inner @ a) (V.extend sigma a (L.rev inner) us rho) body ==
                  V.evaluate sigma i (L.rev inner @ b) (V.extend sigma b (L.rev inner) us eta) body') =
         lemma_subst_envs_extend sigma bound vs depth a b (L.rev inner) us rho eta;
         lemma_agrees_shift sigma b (L.rev inner) us eta depth deps args;
         lemma_substitute sigma i deps ws bound args vs (depth + L.length inner) (L.rev inner @ a) (L.rev inner @ b)
           (V.extend sigma a (L.rev inner) us rho) (V.extend sigma b (L.rev inner) us eta) body body' in
       FStar.Classical.forall_intro pointwise;
       V.lemma_quantifier_environments sigma i a b rho eta k inner (get_sort body) body body'
     | _ -> ())

and lemma_substitute_args (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                          (deps:list SK.dependency) (ws:list SK.witness) (bound:list sort)
                          (args:V.arguments base sigma (SK.dependency_sorts deps))
                          (vs:V.arguments base sigma bound) (depth:nat) (a b:list sort)
                          (rho:V.environment base sigma a) (eta:V.environment base sigma b)
                          (xs ys:list expr) (ss:list sort)
  : Lemma (requires D.scoped_args a xs /\ D.scoped_args b ys /\ sorts_match xs ss /\ sorts_match ys ss /\
                    SK.substitute_args depth (L.length bound) deps ws xs == Some ys /\
                    subst_envs sigma bound vs depth a b rho eta /\
                    agrees sigma b eta depth deps args /\
                    witnesses_select sigma i deps ws bound args vs)
          (ensures V.evaluate_args sigma i a rho xs ss == V.evaluate_args sigma i b eta ys ss)
          (decreases xs) =
  match xs, ys, ss with
  | x :: rest, y :: tail, _ :: remaining ->
    lemma_substitute sigma i deps ws bound args vs depth a b rho eta x y;
    lemma_substitute_args sigma i deps ws bound args vs depth a b rho eta rest tail remaining
  | _, _, _ -> ()

(* ---------------------------------------------------------------------- *)
(* 5. The model: ONE joint choice per typed argument tuple                  *)
(* ---------------------------------------------------------------------- *)

(* The joint goal for the argument tuple `args`: the body holds (is false,
   for a negative step) at EVERY environment of the closure scope with the
   values `args` at the dependencies, read in the pre-extension `other`. *)
let dgoal (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
          (eq:T.scalar_model base) (other:V.interpretation base (S.signature s)) (d:definition s)
          (args:V.arguments base (S.signature s) (SK.dependency_sorts d.SK.dependencies))
          (vs:V.arguments base (S.signature s) (L.rev d.SK.bound_sorts)) : prop =
  forall (rho:V.environment base (S.signature s) (closure_scope d)).
    agrees (S.signature s) (closure_scope d) rho 0 d.SK.dependencies args ==>
    T.truth_at s bc eq other (L.rev d.SK.bound_sorts @ closure_scope d)
      (V.extend (S.signature s) (closure_scope d) (L.rev d.SK.bound_sorts) vs rho) d.SK.body == not d.SK.negative

(* ONE choice of the whole bound tuple per argument tuple. *)
let dselected (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
              (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
              (other:V.interpretation base (S.signature s)) (d:definition s)
              (args:V.arguments base (S.signature s) (SK.dependency_sorts d.SK.dependencies))
  : GTot (vs:V.arguments base (S.signature s) (L.rev d.SK.bound_sorts){
      (exists (ws:V.arguments base (S.signature s) (L.rev d.SK.bound_sorts)).
         dgoal s bc eq other d args ws) ==>
      dgoal s bc eq other d args vs}) =
  choice.E.epsilon (L.rev d.SK.bound_sorts) (dgoal s bc eq other d args)

let rec lemma_witness (ss:list sort) (deps:list SK.dependency) (ws:list SK.witness) (f:func_decl) (n:nat)
  : Lemma (requires SK.valid_witnesses ss deps ws /\ SK.component f ws == Some n)
          (ensures n < L.length ss /\ f.range == L.index ss n /\
                   f.domain == SK.dependency_sorts deps /\ f.interp == None)
          (decreases ws) =
  match ws with
  | [] -> ()
  | (_, g) :: rest -> if f <> g then lemma_witness ss deps rest f n

(* The extension: every witness function returns its coordinate of the ONE
   tuple chosen for its arguments; everything else is `other`. *)
let doverride (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
              (eq:T.scalar_model base) (choice:E.hilbert_choice base s) (d:definition s)
              (other:V.interpretation base (S.signature s))
  : V.interpretation base (S.signature s) = {
  V.application = (fun f args ->
    match SK.component f d.SK.witnesses with
    | Some n ->
      lemma_witness (L.rev d.SK.bound_sorts) d.SK.dependencies d.SK.witnesses f n;
      let vs = dselected s bc eq choice other d args in
      V.lemma_sort_eq f.range (L.index (L.rev d.SK.bound_sorts) n);
      E.tuple_at (S.signature s) (L.rev d.SK.bound_sorts) vs n
    | None -> other.V.application f args);
  V.quantification = other.V.quantification;
}

let rec lemma_safe_component (s:S.checked_schema) (ws:list SK.witness) (f:func_decl)
  : Lemma (requires safe_functions s ws /\ Some? (SK.component f ws))
          (ensures function_safe s f)
          (decreases ws) =
  match ws with
  | [] -> ()
  | (_, g) :: rest -> if f <> g then lemma_safe_component s rest f

(* A safe function is read from `other` by the Sorted layers. *)
let lemma_safe_application (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                           (f:func_decl) (xs:V.arguments base (S.signature s) f.domain)
  : Lemma (requires function_safe s f)
          (ensures T.application s bc eq other f xs == other.V.application f xs) =
  ()

let lemma_select (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                 (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                 (other:V.interpretation base (S.signature s)) (d:definition s)
                 (args:V.arguments base (S.signature s) (SK.dependency_sorts d.SK.dependencies))
  : Lemma (witnesses_select (S.signature s) (T.interpretation s bc eq (doverride s bc eq choice d other))
             d.SK.dependencies d.SK.witnesses (L.rev d.SK.bound_sorts) args
             (dselected s bc eq choice other d args)) =
  let at (m:nat) (f:func_decl)
    : Lemma (witness_selects (S.signature s) (T.interpretation s bc eq (doverride s bc eq choice d other))
               d.SK.dependencies d.SK.witnesses (L.rev d.SK.bound_sorts) args
               (dselected s bc eq choice other d args) m f) =
    if SK.lookup m d.SK.witnesses = Some f then (
      SK.lemma_witness_lookup (L.rev d.SK.bound_sorts) d.SK.dependencies d.SK.witnesses m f;
      lemma_witness (L.rev d.SK.bound_sorts) d.SK.dependencies d.SK.witnesses f m;
      lemma_safe_component s d.SK.witnesses f;
      lemma_safe_application s bc eq (doverride s bc eq choice d other) f args) in
  FStar.Classical.forall_intro_2 at

(* Symbols other than the witnesses keep their meaning, so every term in
   which no witness occurs keeps its value. *)
let lemma_application_fresh (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                            (eq:T.scalar_model base) (choice:E.hilbert_choice base s) (d:definition s)
                            (other:V.interpretation base (S.signature s))
                            (f:func_decl) (args:V.arguments base (S.signature s) f.domain)
  : Lemma (requires SK.component f d.SK.witnesses == None)
          (ensures T.application s bc eq other f args ==
                   T.application s bc eq (doverride s bc eq choice d other) f args) =
  ()

let rec lemma_fresh (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                    (eq:T.scalar_model base) (choice:E.hilbert_choice base s) (d:definition s)
                    (other:V.interpretation base (S.signature s))
                    (scope:list sort) (rho:V.environment base (S.signature s) scope) (e:expr)
  : Lemma (requires D.scoped scope e /\ SK.fresh d.SK.witnesses e)
          (ensures T.evaluate_at s bc eq other scope rho e ==
                   T.evaluate_at s bc eq (doverride s bc eq choice d other) scope rho e)
          (decreases e) =
  match e with
  | Var _ _ -> ()
  | App f args ->
    lemma_fresh_args s bc eq choice d other scope rho args f.domain;
    lemma_application_fresh s bc eq choice d other f
      (V.evaluate_args (S.signature s) (T.interpretation s bc eq other) scope rho args f.domain)
  | Quantifier k bound _ body ->
    let pointwise (ws:V.arguments base (S.signature s) (L.rev bound))
      : Lemma (
          T.evaluate_at s bc eq other (L.rev bound @ scope)
            (V.extend (S.signature s) scope (L.rev bound) ws rho) body ==
          T.evaluate_at s bc eq (doverride s bc eq choice d other) (L.rev bound @ scope)
            (V.extend (S.signature s) scope (L.rev bound) ws rho) body) =
      lemma_fresh s bc eq choice d other (L.rev bound @ scope)
        (V.extend (S.signature s) scope (L.rev bound) ws rho) body in
    FStar.Classical.forall_intro pointwise;
    let left = V.evaluate_body (S.signature s) (T.interpretation s bc eq other) scope rho bound body in
    let right = V.evaluate_body (S.signature s) (T.interpretation s bc eq (doverride s bc eq choice d other))
      scope rho bound body in
    assert (FE.feq_g left right);
    FE.extensionality_g (V.arguments base (S.signature s) (L.rev bound)) (fun _ -> V.tree base) left right

and lemma_fresh_args (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (eq:T.scalar_model base) (choice:E.hilbert_choice base s) (d:definition s)
                     (other:V.interpretation base (S.signature s))
                     (scope:list sort) (rho:V.environment base (S.signature s) scope)
                     (args:list expr) (ss:list sort)
  : Lemma (requires D.scoped_args scope args /\ sorts_match args ss /\ SK.fresh_args d.SK.witnesses args)
          (ensures V.evaluate_args (S.signature s) (T.interpretation s bc eq other) scope rho args ss ==
                   V.evaluate_args (S.signature s) (T.interpretation s bc eq (doverride s bc eq choice d other))
                     scope rho args ss)
          (decreases args) =
  match args, ss with
  | e :: rest, _ :: tail ->
    lemma_fresh s bc eq choice d other scope rho e;
    lemma_fresh_args s bc eq choice d other scope rho rest tail
  | _, _ -> ()

(* ---------------------------------------------------------------------- *)
(* 6. The instance lemma                                                    *)
(* ---------------------------------------------------------------------- *)

let lemma_negate_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                    (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                    (scope:list sort) (rho:V.environment base (S.signature s) scope) (e:expr)
  : Lemma (requires D.scoped scope e /\ get_sort e == bool_sort)
          (ensures D.scoped scope (SK.negate e) /\ get_sort (SK.negate e) == bool_sort /\
                   T.truth_at s bc eq other scope rho (SK.negate e) == not (T.truth_at s bc eq other scope rho e)) =
  match e with
  | App f [a] ->
    if f = R.not_decl then T.lemma_evaluate_core_at s bc eq other scope rho f [a]
    else T.lemma_evaluate_core_at s bc eq other scope rho R.not_decl [e]
  | _ -> T.lemma_evaluate_core_at s bc eq other scope rho R.not_decl [e]

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

let lemma_subst_envs_base (#base:sort -> Type0) (sigma:V.signature) (scope bound:list sort)
                          (vs:V.arguments base sigma bound) (rho:V.environment base sigma scope)
  : Lemma (subst_envs sigma bound vs 0 (bound @ scope) scope (V.extend sigma scope bound vs rho) rho) =
  LP.append_length bound scope;
  let at (n:nat{n < L.length (bound @ scope)})
    : Lemma ((0 <= n /\ n < 0 + L.length bound ==>
                (V.extend sigma scope bound vs rho n <: V.tree base) == coordinate sigma bound vs (n - 0)) /\
             (0 + L.length bound <= n ==>
                (V.extend sigma scope bound vs rho n <: V.tree base) == (rho (n - L.length bound) <: V.tree base))) =
    lemma_extend_index sigma scope bound vs rho n in
  FStar.Classical.forall_intro at

(* The substituted body at `rho` is the body at the selected tuple, in the
   extension. *)
let lemma_target (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                 (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                 (other:V.interpretation base (S.signature s)) (d:definition s)
                 (rho:V.environment base (S.signature s) (closure_scope d))
  : Lemma (let args = gather (S.signature s) (closure_scope d) rho d.SK.dependencies in
           let vs = dselected s bc eq choice other d args in
           let j = doverride s bc eq choice d other in
           T.truth_at s bc eq j (L.rev d.SK.bound_sorts @ closure_scope d)
             (V.extend (S.signature s) (closure_scope d) (L.rev d.SK.bound_sorts) vs rho) d.SK.body ==
           T.truth_at s bc eq j (closure_scope d) rho (target_of d)) =
  let sigma = S.signature s in
  let c = closure_scope d in
  let bs = L.rev d.SK.bound_sorts in
  let args = gather sigma c rho d.SK.dependencies in
  let vs = dselected s bc eq choice other d args in
  let j = doverride s bc eq choice d other in
  LP.rev_length d.SK.bound_sorts;
  SK.lemma_substitute_sort 0 (L.length d.SK.bound_sorts) d.SK.dependencies d.SK.witnesses d.SK.body (target_of d);
  lemma_subst_envs_base sigma c bs vs rho;
  lemma_select s bc eq choice other d args;
  lemma_substitute sigma (T.interpretation s bc eq j) d.SK.dependencies d.SK.witnesses bs args vs 0
    (bs @ c) c (V.extend sigma c bs vs rho) rho d.SK.body (target_of d)

(* Two environments with the same values at the dependencies give the body
   the same truth at every bound tuple (coverage coincidence). *)
let lemma_agreeing (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (eq:T.scalar_model base) (other:V.interpretation base (S.signature s)) (d:definition s)
                   (args:list (V.tree base))
                   (ws:V.arguments base (S.signature s) (L.rev d.SK.bound_sorts))
                   (rho eta:V.environment base (S.signature s) (closure_scope d))
  : Lemma (requires agrees (S.signature s) (closure_scope d) rho 0 d.SK.dependencies args /\
                    agrees (S.signature s) (closure_scope d) eta 0 d.SK.dependencies args)
          (ensures T.truth_at s bc eq other (L.rev d.SK.bound_sorts @ closure_scope d)
                     (V.extend (S.signature s) (closure_scope d) (L.rev d.SK.bound_sorts) ws rho) d.SK.body ==
                   T.truth_at s bc eq other (L.rev d.SK.bound_sorts @ closure_scope d)
                     (V.extend (S.signature s) (closure_scope d) (L.rev d.SK.bound_sorts) ws eta) d.SK.body) =
  let sigma = S.signature s in
  let c = closure_scope d in
  let bs = L.rev d.SK.bound_sorts in
  LP.rev_length d.SK.bound_sorts;
  let base_agree (n:nat{n < L.length c})
    : Lemma (L.mem (n - 0) (SK.dependency_indices d.SK.dependencies) ==> rho n == eta n) =
    if L.mem n (SK.dependency_indices d.SK.dependencies) then
      lemma_agrees_same sigma c rho eta d.SK.dependencies args n in
  FStar.Classical.forall_intro base_agree;
  assert (covered_agree sigma c rho eta 0 d.SK.dependencies);
  lemma_covered_extend sigma c bs ws rho eta 0 d.SK.dependencies;
  lemma_covered sigma (T.interpretation s bc eq other) (bs @ c) (V.extend sigma c bs ws rho)
    (V.extend sigma c bs ws eta) (L.length d.SK.bound_sorts) d.SK.dependencies d.SK.body

(* A tuple satisfying the body at one environment satisfies the joint goal
   of that environment's argument tuple. *)
let lemma_goal (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
               (eq:T.scalar_model base) (other:V.interpretation base (S.signature s)) (d:definition s)
               (rho:V.environment base (S.signature s) (closure_scope d))
               (ws:V.arguments base (S.signature s) (L.rev d.SK.bound_sorts))
  : Lemma (requires T.truth_at s bc eq other (L.rev d.SK.bound_sorts @ closure_scope d)
                      (V.extend (S.signature s) (closure_scope d) (L.rev d.SK.bound_sorts) ws rho) d.SK.body ==
                    not d.SK.negative)
          (ensures dgoal s bc eq other d (gather (S.signature s) (closure_scope d) rho d.SK.dependencies) ws) =
  let args = gather (S.signature s) (closure_scope d) rho d.SK.dependencies in
  let at (eta:V.environment base (S.signature s) (closure_scope d))
    : Lemma (agrees (S.signature s) (closure_scope d) eta 0 d.SK.dependencies args ==>
             T.truth_at s bc eq other (L.rev d.SK.bound_sorts @ closure_scope d)
               (V.extend (S.signature s) (closure_scope d) (L.rev d.SK.bound_sorts) ws eta) d.SK.body ==
             not d.SK.negative) =
    FStar.Classical.move_requires (lemma_agreeing s bc eq other d args ws rho) eta in
  FStar.Classical.forall_intro at

(* The selected tuple satisfies the body at `rho` whenever some tuple does
   (in `other`, and so in the extension). *)
let lemma_forward (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                  (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                  (other:V.interpretation base (S.signature s)) (d:definition s)
                  (rho:V.environment base (S.signature s) (closure_scope d))
                  (ws:V.arguments base (S.signature s) (L.rev d.SK.bound_sorts))
  : Lemma (requires T.truth_at s bc eq (doverride s bc eq choice d other)
                      (L.rev d.SK.bound_sorts @ closure_scope d)
                      (V.extend (S.signature s) (closure_scope d) (L.rev d.SK.bound_sorts) ws rho) d.SK.body ==
                    not d.SK.negative)
          (ensures (let args = gather (S.signature s) (closure_scope d) rho d.SK.dependencies in
                    T.truth_at s bc eq (doverride s bc eq choice d other)
                      (L.rev d.SK.bound_sorts @ closure_scope d)
                      (V.extend (S.signature s) (closure_scope d) (L.rev d.SK.bound_sorts)
                        (dselected s bc eq choice other d args) rho) d.SK.body ==
                    not d.SK.negative)) =
  let sigma = S.signature s in
  let c = closure_scope d in
  let bs = L.rev d.SK.bound_sorts in
  let args = gather sigma c rho d.SK.dependencies in
  let vs = dselected s bc eq choice other d args in
  lemma_fresh s bc eq choice d other (bs @ c) (V.extend sigma c bs ws rho) d.SK.body;
  lemma_goal s bc eq other d rho ws;
  FStar.Classical.exists_intro (dgoal s bc eq other d args) ws;
  assert (dgoal s bc eq other d args vs);
  assert (agrees sigma c rho 0 d.SK.dependencies args);
  assert (T.truth_at s bc eq other (bs @ c) (V.extend sigma c bs vs rho) d.SK.body == not d.SK.negative);
  lemma_fresh s bc eq choice d other (bs @ c) (V.extend sigma c bs vs rho) d.SK.body

(* THE instance lemma: at EVERY environment of the closure scope the source
   and the instance of the step have the same truth in the extension. *)
let lemma_instance (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                   (other:V.interpretation base (S.signature s)) (d:definition s)
                   (rho:V.environment base (S.signature s) (closure_scope d))
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other)
          (ensures T.truth_at s bc eq (doverride s bc eq choice d other) (closure_scope d) rho (SK.source d) ==
                   T.truth_at s bc eq (doverride s bc eq choice d other) (closure_scope d) rho (instance_of d)) =
  let sigma = S.signature s in
  let c = closure_scope d in
  let bs = L.rev d.SK.bound_sorts in
  let j = doverride s bc eq choice d other in
  let args = gather sigma c rho d.SK.dependencies in
  let vs = dselected s bc eq choice other d args in
  E.lemma_quantification_models s bc other j;
  SK.lemma_substitute_sort 0 (L.length d.SK.bound_sorts) d.SK.dependencies d.SK.witnesses d.SK.body (target_of d);
  lemma_target s bc eq choice other d rho;
  FStar.Classical.forall_intro (FStar.Classical.move_requires (lemma_forward s bc eq choice other d rho));
  let q = Quantifier (if d.SK.negative then Forall_k else Exists_k) d.SK.bound_sorts bool_sort d.SK.body in
  if d.SK.negative then (
    Q.lemma_forall_truth s bc eq j c rho d.SK.bound_sorts d.SK.body;
    T.lemma_evaluate_core_at s bc eq j c rho R.not_decl [q];
    lemma_negate_at s bc eq j c rho (target_of d))
  else
    lemma_exists_truth s bc eq j c rho d.SK.bound_sorts d.SK.body

(* ---------------------------------------------------------------------- *)
(* 7. The closure, the context and its extension                            *)
(* ---------------------------------------------------------------------- *)

let lemma_closure (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                  (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                  (other:V.interpretation base (S.signature s)) (d:definition s)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other)
          (ensures T.truth s bc eq (doverride s bc eq choice d other) (closure d)) =
  let sigma = S.signature s in
  let j = doverride s bc eq choice d other in
  let cb = closure_binders d in
  let empty = T.empty_environment #base sigma in
  let eqn = R.mk_eq_expr (SK.source d) (instance_of d) in
  E.lemma_quantification_models s bc other j;
  SK.lemma_substitute_sort 0 (L.length d.SK.bound_sorts) d.SK.dependencies d.SK.witnesses d.SK.body (target_of d);
  assert (D.scoped (L.rev cb @ []) eqn);
  Q.lemma_forall_truth s bc eq j [] empty cb eqn;
  let at (vs:V.arguments base sigma (L.rev cb))
    : Lemma (T.truth_at s bc eq j (L.rev cb @ []) (V.extend sigma [] (L.rev cb) vs empty) eqn) =
    let rho : V.environment base sigma (closure_scope d) = V.extend sigma [] (L.rev cb) vs empty in
    lemma_instance s bc eq choice other d rho;
    if d.SK.negative then lemma_negate_at s bc eq j (closure_scope d) rho (target_of d);
    T.lemma_boolean_equality_at s bc eq j (closure_scope d) rho (SK.source d) (instance_of d) in
  FStar.Classical.forall_intro at

let rec build (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
              (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
              (ds:list (definition s)) (other:V.interpretation base (S.signature s))
  : GTot (V.interpretation base (S.signature s)) (decreases ds) =
  match ds with
  | [] -> other
  | d :: rest -> doverride s bc eq choice d (build s bc eq choice rest other)

let rec lemma_build_quantification (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                   (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                                   (ds:list (definition s)) (other:V.interpretation base (S.signature s))
  : Lemma ((build s bc eq choice ds other).V.quantification == other.V.quantification)
          (decreases ds) =
  match ds with [] -> () | _ :: rest -> lemma_build_quantification s bc eq choice rest other

let rec context_model (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                      (ds:list (definition s)) : Tot prop (decreases ds) =
  match ds with
  | [] -> True
  | d :: rest -> T.truth s bc eq other (closure d) == true /\ context_model s bc eq other rest

let rec lemma_context_truths (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                             (ds:list (definition s))
  : Lemma (requires context_model s bc eq other ds)
          (ensures T.truths s bc eq other (closures s ds))
          (decreases ds) =
  match ds with [] -> () | _ :: rest -> lemma_context_truths s bc eq other rest

(* Freshness of generated terms. *)
let rec lemma_uninterpreted (ss:list sort) (deps:list SK.dependency) (ws:list SK.witness) (f:func_decl)
  : Lemma (requires SK.valid_witnesses ss deps ws /\ f.interp <> None)
          (ensures SK.component f ws == None)
          (decreases ws) =
  match ws with [] -> () | _ :: rest -> lemma_uninterpreted ss deps rest f

let rec lemma_arguments_fresh (ws:list SK.witness) (depth:nat) (deps:list SK.dependency)
  : Lemma (SK.fresh_args ws (SK.dependency_arguments depth deps)) (decreases deps) =
  match deps with [] -> () | _ :: rest -> lemma_arguments_fresh ws depth rest

let rec lemma_substitute_fresh (newer older:list SK.witness) (deps:list SK.dependency)
                               (depth count:nat) (e target:expr)
  : Lemma (requires SK.fresh newer e /\ SK.disjoint newer older /\
                    SK.substitute depth count deps older e == Some target)
          (ensures SK.fresh newer target)
          (decreases e) =
  match e with
  | Var n _ ->
    if n >= depth && n < depth + count then (
      E.lemma_disjoint_lookup newer older (n - depth) (Some?.v (SK.lookup (n - depth) older));
      lemma_arguments_fresh newer depth deps)
  | App _ args ->
    lemma_substitute_args_fresh newer older deps depth count args (match target with App _ xs -> xs | _ -> [])
  | Quantifier _ bs _ body ->
    lemma_substitute_fresh newer older deps (depth + L.length bs) count body
      (match target with Quantifier _ _ _ b -> b | _ -> target)

and lemma_substitute_args_fresh (newer older:list SK.witness) (deps:list SK.dependency)
                                (depth count:nat) (args targets:list expr)
  : Lemma (requires SK.fresh_args newer args /\ SK.disjoint newer older /\
                    SK.substitute_args depth count deps older args == Some targets)
          (ensures SK.fresh_args newer targets)
          (decreases args) =
  match args, targets with
  | e :: rest, target :: tail ->
    lemma_substitute_fresh newer older deps depth count e target;
    lemma_substitute_args_fresh newer older deps depth count rest tail
  | _, _ -> ()

(* The source and the instance of an older definition (closed or dependent)
   are fresh for a newer valid definition that is a safe extension of it. *)
let lemma_parts_fresh (newer older:SK.definition) (b:expr)
  : Lemma (requires SK.valid newer /\ SK.disjoint newer.SK.witnesses older.SK.witnesses /\
                    SK.fresh newer.SK.witnesses older.SK.body /\ SK.instantiation older == Some b)
          (ensures SK.fresh newer.SK.witnesses (SK.source older) /\ SK.fresh newer.SK.witnesses b) =
  let ws = newer.SK.witnesses in
  lemma_uninterpreted (L.rev newer.SK.bound_sorts) newer.SK.dependencies ws R.not_decl;
  let target = Some?.v (SK.substitute 0 (L.length older.SK.bound_sorts) older.SK.dependencies
                          older.SK.witnesses older.SK.body) in
  lemma_substitute_fresh ws older.SK.witnesses older.SK.dependencies 0 (L.length older.SK.bound_sorts)
    older.SK.body target

let lemma_closure_fresh (#s:S.checked_schema) (newer:SK.definition) (older:definition s)
  : Lemma (requires SK.valid newer /\ SK.disjoint newer.SK.witnesses older.SK.witnesses /\
                    SK.fresh newer.SK.witnesses older.SK.body)
          (ensures SK.fresh newer.SK.witnesses (closure older)) =
  lemma_parts_fresh newer older (instance_of older);
  lemma_uninterpreted (L.rev newer.SK.bound_sorts) newer.SK.dependencies newer.SK.witnesses
    (R.eq_decl (get_sort (SK.source older)))

let rec lemma_context_preserved (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                                (newer:definition s) (other:V.interpretation base (S.signature s))
                                (ds:list (definition s))
  : Lemma (requires SK.safe_extension newer (erase s ds) /\ context_model s bc eq other ds)
          (ensures context_model s bc eq (doverride s bc eq choice newer other) ds)
          (decreases ds) =
  match ds with
  | [] -> ()
  | d :: rest ->
    lemma_closure_fresh newer d;
    lemma_fresh s bc eq choice newer other [] (T.empty_environment (S.signature s)) (closure d);
    lemma_context_preserved s bc eq choice newer other rest

(* The context model of an ordered list of definitions, built one after
   another from ONE interpretation `other` (each goal read in the model of
   the older definitions). *)
let rec lemma_build_context (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                            (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                            (ds:list (definition s)) (other:V.interpretation base (S.signature s))
  : Lemma (requires SK.ordered_context (erase s ds) /\ Q.forall_model s bc other /\ E.exists_model s bc other)
          (ensures context_model s bc eq (build s bc eq choice ds other) ds)
          (decreases ds) =
  match ds with
  | [] -> ()
  | d :: rest ->
    lemma_build_context s bc eq choice rest other;
    lemma_build_quantification s bc eq choice rest other;
    let older = build s bc eq choice rest other in
    E.lemma_quantification_models s bc other older;
    lemma_closure s bc eq choice older d;
    lemma_context_preserved s bc eq choice d older rest

(* The original inputs keep their truth (witnesses fresh in every input). *)
let rec lemma_build_inputs (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
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
    let rec all (es:list expr)
      : Lemma (requires SK.fresh_args d.SK.witnesses es)
              (ensures T.truths s bc eq older es == T.truths s bc eq (doverride s bc eq choice d older) es)
              (decreases es) =
      match es with
      | [] -> ()
      | e :: tail ->
        if D.scoped [] e && get_sort e = bool_sort then
          lemma_fresh s bc eq choice d older [] (T.empty_environment (S.signature s)) e;
        all tail in
    all inputs

(* Every definition of xs is a safe extension of all of ys. *)
let rec safe_over (xs ys:list SK.definition) : Tot bool (decreases xs) =
  match xs with [] -> true | d :: rest -> SK.safe_extension d ys && safe_over rest ys

let rec lemma_safe_append (d:SK.definition) (xs ys:list SK.definition)
  : Lemma (requires SK.safe_extension d (xs @ ys))
          (ensures SK.safe_extension d xs /\ SK.safe_extension d ys)
          (decreases xs) =
  match xs with [] -> () | _ :: rest -> lemma_safe_append d rest ys

let rec lemma_ordered_append (xs ys:list SK.definition)
  : Lemma (requires SK.ordered_context (xs @ ys))
          (ensures SK.ordered_context xs /\ SK.ordered_context ys /\ safe_over xs ys)
          (decreases xs) =
  match xs with
  | [] -> ()
  | d :: rest -> lemma_safe_append d rest ys; lemma_ordered_append rest ys

(* The closed epsilon context (Z3SortedSkolem) keeps its model under the
   dependent extension: its sources and instances are closed and fresh for
   every dependent witness. *)
let rec lemma_closed_preserved (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                               (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                               (newer:definition s) (other:V.interpretation base (S.signature s))
                               (cds:list (E.definition s))
  : Lemma (requires SK.safe_extension newer (E.erase s cds) /\ E.context_model s bc eq other cds)
          (ensures E.context_model s bc eq (doverride s bc eq choice newer other) cds)
          (decreases cds) =
  match cds with
  | [] -> ()
  | d :: rest ->
    let j = doverride s bc eq choice newer other in
    E.lemma_source_scoped s d;
    let at (b:expr) : Lemma (SK.instantiation d == Some b ==>
          T.truth s bc eq j (SK.source d) == T.truth s bc eq j b) =
      if SK.instantiation d = Some b then (
        lemma_parts_fresh newer d b;
        lemma_fresh s bc eq choice newer other [] (T.empty_environment (S.signature s)) (SK.source d);
        lemma_fresh s bc eq choice newer other [] (T.empty_environment (S.signature s)) b) in
    FStar.Classical.forall_intro at;
    lemma_closed_preserved s bc eq choice newer other rest

let rec lemma_build_closed (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                           (ds:list (definition s)) (other:V.interpretation base (S.signature s))
                           (cds:list (E.definition s))
  : Lemma (requires safe_over (erase s ds) (E.erase s cds) /\ E.context_model s bc eq other cds)
          (ensures E.context_model s bc eq (build s bc eq choice ds other) cds)
          (decreases ds) =
  match ds with
  | [] -> ()
  | d :: rest ->
    lemma_build_closed s bc eq choice rest other cds;
    lemma_closed_preserved s bc eq choice d (build s bc eq choice rest other) cds
