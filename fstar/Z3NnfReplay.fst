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
   only when its ROOT entry is `nnf-neg` or `nnf-pos` (an NNF certificate)
   or `quant-intro` (a scoped rewrite certificate, below); every other
   certificate keeps the previous treatment.

   Scoped rewrite certificates (quant-intro root, Z3 rewriter_def.h
   proof-bind/quant-intro). Under such a root, and ONLY there, two more
   entry kinds are replayed (an NNF certificate is replayed exactly as
   before):
     quant-intro (sorts bs, premise [j]):
                    `(Q bs. A) ~ (Q bs. B)` with Q forall or exists on BOTH
                    sides, both binder lists equal to bs, Boolean bodies,
                    and j concluding `A ~ B` (read at `L.rev bs @ scope`):
                    the positive quantifier step of the calculus below;
     rewrite (no sorts, no premise):
                    `l ~ r` accepted only by an executable local check
                    that makes it true at EVERY typed environment of every
                    scope where both sides are typed: the typed Int
                    equivalence Z3SortedArithmetic.equivalent (linear
                    normal forms over the Int carrier; opaque Int-valued
                    terms are atoms); one of the three ITE laws of
                    bool_rewriter::mk_ite_core at EVERY result sort (Bool,
                    Int, Real, uninterpreted, datatype, array), with one
                    canonical `ite` declaration (T.classify = Choice s,
                    i.e. exactly T.ite_decl s) on both sides and on the
                    nested ite, canonical not/or/and, and conditions and
                    branches compared by exact identity:
                      (ite (not c) x y) ~ (ite c y x), also oriented
                        (ite c x y) ~ (ite (not c) y x);
                      (ite c1 x (ite c2 x y)) ~ (ite (or c1 c2) x y);
                      (ite c1 (ite c2 x y) y) ~ (ite (and c1 c2) x y),
                    where the `or`/`and` is binary or flattened one level
                    (its operands are the operands of c1 followed by those
                    of c2, each opened only if it is the same canonical
                    connective, as the producer's mk_and builds it); their
                    meaning is the choice the Sorted semantics already
                    gives every `ite` (lemma_ite_rewritten_at), never the
                    values of the branches, so a Real or other theory
                    subterm stays an opaque operand; at Int, a permutation
                    and regrouping of the factors of nested canonical Int
                    products (product_permuted: a node is opened only when
                    its declaration is Z3SortedInteger's `Calculate Mul`;
                    every other expression, numerals included, is one
                    factor; equal factor multisets by exact identity, at
                    most 64 factors per side), true by the integer product
                    the Sorted semantics gives `*` (lemma_product_permuted_at);
                    for Boolean sides, a
                    regrouping of nested canonical and/or (equal operand
                    lists, or, for at most 12 operands per side, lists
                    included in each other; operands compared by exact
                    identity); or the
                    propositional equivalence of the Boolean cuts (T.cut
                    64, else the coarser T.cut 2, decided by
                    Z3SortedDatatype.bounded_propositional, the check the
                    Sorted route uses for top-level rewrites; atoms are
                    compared syntactically, so a de Bruijn index is read at
                    the one scope of the step).
     elim-unused (no sorts, no premise):
                    `(Q bs. body) ~ e` (ast_manager::mk_elim_unused_vars
                    exports iff(q, e)) with Q forall or exists, accepted
                    only when e is z3's elim_unused_vars result recomputed
                    from the left side: the same quantifier over the used
                    binders in order with the body renumbered, or the bare
                    renumbered body when no binder is used (at most 64
                    binders, both sides shallow). True at every typed
                    environment of every scope where both sides are typed
                    (lemma_unused_eliminated_at): a removed binder ranges
                    over a carrier the interpretation itself inhabits (the
                    value of a nullary symbol), so no hypothesis is added.
     der (no sorts, no premise):
                    `(forall bs. (or l1 .. ln)) ~ (forall bs. b')` (der.cpp
                    reduce1, ast_manager::mk_der exports iff(q, e)) with one
                    eliminated binder: the literals are read in the order of
                    z3's flatten_or, which reduce1 applies to the body (ln
                    l1 .. ln-1 when no literal is itself opened), or in
                    source order; li is the first literal `(not (= x t))`
                    or `(not (= t x))` with x a binder of bs not occurring
                    in t, and b' is the disjunction of the other literals in
                    that order (ast_util mk_or: false, the single literal,
                    or the canonical `or`) with x replaced by t lifted under
                    nested binders; the binder list is kept (elim-unused
                    drops x in a separate step). True at every typed
                    environment of every scope where both sides are typed
                    (lemma_der_at), from the universal law alone: the
                    witness for x is t's own value, no carrier is assumed
                    inhabited, and both orders have the truth of the
                    source disjunction (lemma_flat_order).
     pull-quant (no sorts, no premise):
                    `e ~ q` (pull_quant.cpp, ast_manager::mk_pull_quant
                    exports iff(e, q)): either e is a canonical and/or with
                    exactly one forall/exists child (Q bs. b) and q is
                    (Q bs. (op c1' .. b .. cn')) with every other child
                    lifted over bs (pulled), or e is a nested forall and q
                    its flattening (Z3SortedQuantifier.flatten); at most 64
                    pulled binders, both sides shallow. True at every typed
                    environment of every scope where both sides are typed
                    (lemma_pull_ok_at): forall under `and` and exists under
                    `or` read the inhabited carriers of the interpretation
                    (inhabitant_of), the other cases and the flattening
                    need none. Top-level pull-quant nodes keep the existing
                    closed flattening check (SP.quantifier_flattening).
   With `refl`, `trans` and `monotonicity` these replay the body proofs of
   a quant-intro root; nothing is read from the rule names alone.

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
   (lemma_closure_edge). Every other entry kind (apply-def, labels, lambda,
   the hnf.cpp variant whose body is not the negation of its source, ...,
   and `rewrite`/`quant-intro` under an NNF root) leaves the node PENDING.

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
   unit per assertion for each `sk` step. A `rewrite` leaf is decided only
   after its formula's node count is charged, so its local check reads a
   tree of at most the remaining budget. The regrouping and the ITE laws
   are linear in that charge: each operand walk pops at most 4096 stack
   entries (else refused) and pushes every argument of an opened
   connective once; a depth walk (at most 2^20 pops per side) admits only
   sides of depth at most 4096; equal operand lists, ITE conditions and
   branches are compared once (at most the smaller side's nodes); the
   order-free inclusion runs only for at most 12 operands per side, so it
   makes at most 2 * 12 * 12 operand comparisons, together at most 12
   times the charged size. Operands are compared by the kernel's
   structural equality (exact declarations, sorts and arguments), never by
   native ids, and never more than 4096 levels deep. The node charge does
   not count the bytes of declaration names; those comparisons are bounded
   by the leaf's own bytes (12 times on the order-free path).
   The Int factor permutation walks each side with at most 4096 pops and
   stops at the 65th factor; it reads a declaration's argument and domain
   lists only after its tags name a canonical product, and then at most 65
   elements of each (a longer candidate is refused). Both sides are
   shallow before any comparison, and the multiset check removes each left
   factor from the right list, so it makes at most 64 * 64 factor
   comparisons, together at most 64 times the charged size of the right
   side. As above, the node charge does not count declaration-name bytes
   or sort lists; those comparisons are bounded by the leaf's own bytes
   (64 times), not by the charge.
   The binder rules (elim-unused, der) admit at most 64 binders and, for der,
   at most 4096 literals; both sides must be shallow, so every recursive
   walk (occurrences, renumbering, substitution) descends at most 4096
   levels; argument lists are walked by tail-recursive loops; the
   occurrence marks cost one walk of the body per binder, and the final
   comparison is the kernel's structural equality of the recomputed and
   the given side.
   The other checks (existing Sorted-route code, not one of the loops above)
   are not themselves linear in the charge: the Int equivalence reads at
   most 256 nodes per side, and each of the (at most two) bounded
   propositional checks normalizes cut trees of at most the charged size
   and enumerates a truth table only up to 12 atoms (4096 rows of the
   simplified formula). This is the bounded form of the check the Sorted
   route already applies, uncharged, to a top-level step of the same size.
   An exhausted budget leaves the node PENDING. Premise ids that are not
   earlier entries (forward, self or negative references) make the
   certificate MALFORMED, which the Sorted route reports as a rejected
   proof entry, not as a pending obligation (for an NNF and a quant-intro
   root alike).

   Real leaves. `replay_with real` takes a Real gate from its caller:
   Z3SortedProof passes `Z3SortedReal.real_primitive` of its checked schema
   (Real is not a datatype sort there), and `replay` is `replay_with false`.
   Under the gate, a `rewrite` leaf the checks above refuse is replayed when
   `Z3SortedRealLinear.real_equivalent` decides it (at most 256 nodes per
   side): linear Real and Int-with-to_real renormalization, comparison
   orientation and strictness, binary Real product commutation, and Real
   equations (the same, opposite or proportional difference polynomial; an
   equation of constants decided as true or false). Its lemma
   requires `real ==> Z3SortedReal.real_model` of the same Sorted
   interpretation (which contains the gate), so the flag alone proves
   nothing. The ITE laws do not read the gate.
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
module AR = Z3SortedArithmetic
module DT = Z3SortedDatatype
module RL = Z3SortedReal
module LIN = Z3SortedRealLinear
module SI = Z3SortedInteger
module LA = Z3LinearArithmeticAst
module RW = Z3ArithmeticRewrite
module LP = FStar.List.Tot.Properties
module BRW = Z3BooleanRewrite

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

let rec prepend (xs acc:list expr) : Tot (list expr) (decreases xs) =
  match xs with [] -> acc | x :: rest -> prepend rest (x :: acc)

(* The operands of the nested canonical connective `op` (and, or) at the top
   of an expression, left to right. An application whose operator classifies
   as `op` (T.classify: the name, a Boolean domain and range, the
   interpretation and no parameters) is opened; every other expression (an
   atom, a negation, a quantifier, a look-alike `or` with another
   declaration, the other connective) is an operand, compared later by exact
   identity. A loop over an explicit stack: an opened argument list is pushed
   reversed, so the operands are reached right to left and consed onto `acc`
   in order. At most `fuel` pops; a longer walk is refused (None). *)
let rec operands_within (op:B.nary_op) (fuel:nat) (pending acc:list expr)
  : Tot (option (list expr)) (decreases fuel) =
  match pending with
  | [] -> Some acc
  | e :: rest ->
    if fuel = 0 then None
    else match e with
      | App f args ->
        if T.classify f = T.Nary op then operands_within op (fuel - 1) (prepend args rest) acc
        else operands_within op (fuel - 1) rest (e :: acc)
      | _ -> operands_within op (fuel - 1) rest (e :: acc)

let operands (op:B.nary_op) (e:expr) : option (list expr) = operands_within op 4096 [e] []

let rec at_most (n:nat) (xs:list expr) : Tot bool (decreases xs) =
  match xs with
  | [] -> true
  | _ :: rest -> if n = 0 then false else at_most (n - 1) rest

(* Every element of xs is an element of ys (exact identity). *)
let rec included (xs ys:list expr) : Tot bool (decreases xs) =
  match xs with
  | [] -> true
  | x :: rest -> if L.mem x ys then included rest ys else false

let rec depths_at (d:nat) (xs:list expr) (acc:list (expr & nat)) : Tot (list (expr & nat)) (decreases xs) =
  match xs with [] -> acc | x :: rest -> depths_at d rest ((x, d) :: acc)

(* Every node of the pending expressions lies at most `limit` levels below
   its root, found within at most `fuel` pops (otherwise false); a loop
   over an explicit stack. The regrouping admits only sides of depth at
   most 4096 (and at most 2^20 tree nodes), so the structural comparisons
   of its operands (recursive in the generated C equality, iterative in
   OCaml) never descend more than 4096 levels, also for distinct deep
   operands that pointer equality cannot short-circuit; deeper or larger
   sides are refused. *)
let rec shallow_within (limit fuel:nat) (pending:list (expr & nat)) : Tot bool (decreases fuel) =
  match pending with
  | [] -> true
  | (e, d) :: rest ->
    if fuel = 0 || d > limit then false
    else match e with
      | App _ args -> shallow_within limit (fuel - 1) (depths_at (d + 1) args rest)
      | Quantifier _ _ _ b -> shallow_within limit (fuel - 1) ((b, d + 1) :: rest)
      | Var _ _ -> shallow_within limit (fuel - 1) rest

let shallow (e:expr) : bool = shallow_within 4096 1048576 [(e, 0)]

(* `lhs` and `rhs` are the same nested `op` over the same operands up to
   grouping (associativity): equal operand lists; and, for at most 12
   operands per side (the truth-table bound), up to order and repetition
   (commutativity, idempotence): each operand list included in the other.
   Both sides must be shallow (above). *)
let regrouped_by (op:B.nary_op) (lhs rhs:expr) : bool =
  match operands op lhs, operands op rhs with
  | Some xs, Some ys ->
    shallow lhs && shallow rhs &&
    (xs = ys || (at_most 12 xs && at_most 12 ys && included xs ys && included ys xs))
  | _, _ -> false

let regrouped (lhs rhs:expr) : bool = regrouped_by B.Or lhs rhs || regrouped_by B.And lhs rhs

(* The operands of a canonical `op` application, one level; any other
   expression is its own single operand. *)
let junctands (op:B.nary_op) (e:expr) : list expr =
  match e with
  | App f args -> if T.classify f = T.Nary op then args else [e]
  | _ -> [e]

(* `c` is the canonical `op` (and, or) of c1 and c2: the binary application
   (op c1 c2), or one application over the operands of c1 followed by those
   of c2, each opened one level (bool_rewriter's flattening mk_and). *)
let joined (op:B.nary_op) (c c1 c2:expr) : bool =
  match c with
  | App f args -> T.classify f = T.Nary op && (args = [c1; c2] || args = L.append (junctands op c1) (junctands op c2))
  | _ -> false

(* The ITE laws of bool_rewriter::mk_ite_core on (ite c x y) ~ (ite c' x' y')
   with one canonical ite declaration f: the negated condition with swapped
   branches (either side carries the negation), and the merge of a nested
   (ite c2 ..) of the same f into the then branch (by `or`) or into the else
   branch (by `and`). *)
let ite_swapped (c x y c' x' y':expr) : bool =
  x' = y && y' = x && (negation_of c' c || negation_of c c')

let ite_merged_then (f:func_decl) (c x y c' x' y':expr) : bool =
  match y with
  | App g [c2; x2; y2] -> g = f && x2 = x && x' = x && y' = y2 && joined B.Or c' c c2
  | _ -> false

let ite_merged_else (f:func_decl) (c x y c' x' y':expr) : bool =
  match x with
  | App g [c2; x2; y2] -> g = f && y2 = y && y' = y && x' = x2 && joined B.And c' c c2
  | _ -> false

(* Both sides apply the same declaration f with T.classify f = Choice s
   (exactly T.ite_decl s, so every branch and the result have sort s) and
   are shallow (as for the regrouping, which bounds the structural
   comparisons below), and one law relates them. *)
let ite_rewritten (lhs rhs:expr) : bool =
  match lhs, rhs with
  | App f [c; x; y], App g [c'; x'; y'] ->
    if f = g && T.Choice? (T.classify f) && shallow lhs && shallow rhs
    then ite_swapped c x y c' x' y' || ite_merged_then f c x y c' x' y' || ite_merged_else f c x y c' x' y'
    else false
  | _, _ -> false

(* Int product factor permutation. A node is opened only when its
   declaration is a canonical Int multiplication (SI.classify = Calculate
   Mul: exactly `*` over an Int domain with Int range, op_arith_mul, or
   op_mul with two arguments, no parameters); every other expression, a
   numeral, an opaque Int application or a look-alike `*`, is one factor.
   A loop over an explicit stack: at most `fuel` pops and at most `room`
   factors, otherwise None. Admission is bounded before any list is read:
   the declaration's tags (name, range, parameters, interpretation) decide
   whether it can be a product at all; a candidate's argument and domain
   lists are then read only up to `room + 1` elements (a longer one is
   refused), so neither SI.classify nor the push of the arguments ever
   walks more than `room` elements. *)
let product_tags (f:func_decl) : bool =
  f.decl_name = "*" && f.range = LA.int_s && f.int_params = [] &&
  (f.interp = Some Z3ValueTheory.op_arith_mul || f.interp = Some Z3ValueTheory.op_mul)

let rec length_within (#a:Type) (n:nat) (xs:list a) : Tot bool (decreases xs) =
  match xs with [] -> true | _ :: rest -> if n = 0 then false else length_within (n - 1) rest

let rec factors_within (fuel room:nat) (pending acc:list expr)
  : Tot (option (list expr)) (decreases fuel) =
  match pending with
  | [] -> Some acc
  | e :: rest ->
    if fuel = 0 then None
    else match e with
      | App f args ->
        if product_tags f then
          (if length_within room args && length_within room f.domain then
             (if SI.classify f = SI.Calculate LA.Mul then factors_within (fuel - 1) room (prepend args rest) acc
              else if room = 0 then None
              else factors_within (fuel - 1) (room - 1) rest (e :: acc))
           else None)
        else if room = 0 then None
        else factors_within (fuel - 1) (room - 1) rest (e :: acc)
      | _ -> if room = 0 then None else factors_within (fuel - 1) (room - 1) rest (e :: acc)

let int_factors (e:expr) : option (list expr) = factors_within 4096 64 [e] []

(* Both sides are Int, shallow (bounding the structural comparisons, as for
   the ITE laws), and their factors are the same multiset: each left factor
   is removed from the right list by exact identity (multiplicity counts,
   so x*x and x*y differ, and so do numerals that differ in value or sign).
   `if`, not `&&`: a normalized check of a non-Int leaf reads no factors. *)
let product_permuted (lhs rhs:expr) : bool =
  if get_sort lhs = LA.int_s && get_sort rhs = LA.int_s then
    (match int_factors lhs, int_factors rhs with
     | Some xs, Some ys -> if shallow lhs && shallow rhs then RW.factor_permutation xs ys else false
     | _, _ -> false)
  else false

(* elim-unused (z3 elim_unused_vars; ast_manager::mk_elim_unused_vars
   exports iff(q, e)): q = (Q bs. body) with Q forall or exists and e the
   same quantifier over the binders the body uses, in order, with the body
   renumbered (removed binders gone, free indices lowered), or the bare
   renumbered body when no binder is used. The check recomputes e from q
   and compares by exact identity; nothing is read from the rule name. A
   binder position j of the block that starts at depth d occurs in e: *)
let rec occurs (j d:nat) (e:expr) : Tot bool (decreases e) =
  match e with
  | Var i _ -> i = d + j
  | App _ args -> occurs_args j d args
  | Quantifier _ bs _ b -> occurs j (d + L.length bs) b

and occurs_args (j d:nat) (args:list expr) : Tot bool (decreases args) =
  match args with
  | [] -> false
  | a :: rest -> if occurs j d a then true else occurs_args j d rest

let rec marks_below (k:nat) (body:expr) (acc:list bool) : Tot (list bool) (decreases k) =
  if k = 0 then acc else marks_below (k - 1) body (occurs (k - 1) 0 body :: acc)

(* The used binders of a block of n, innermost (Var 0) first. *)
let binder_marks (n:nat) (body:expr) : list bool = marks_below n body []

let rec count_kept (marks:list bool) : Tot nat (decreases marks) =
  match marks with [] -> 0 | m :: rest -> (if m then 1 else 0) + count_kept rest

let rec kept_items (#a:Type) (marks:list bool) (xs:list a) : Tot (list a) (decreases marks) =
  match marks, xs with
  | m :: rest, x :: tail -> if m then x :: kept_items rest tail else kept_items rest tail
  | _, _ -> []

(* The rank among the kept binders of position j, plus acc. *)
let rec rank_from (marks:list bool) (j acc:nat) : Tot (option nat) (decreases marks) =
  match marks with
  | [] -> None
  | m :: rest ->
    if j = 0 then (if m then Some acc else None)
    else rank_from rest (j - 1) (if m then acc + 1 else acc)

(* The new position of scope position p below a block of n binders of which
   `kept` stay. *)
let moved (marks:list bool) (n kept p:nat) : option nat =
  if p < n then rank_from marks p 0 else Some (p - n + kept)

(* The body renumbered (None if a removed binder occurs); the argument list
   is a loop with an accumulator. *)
let rec thin (marks:list bool) (n kept d:nat) (e:expr) : Tot (option expr) (decreases e) =
  match e with
  | Var i s ->
    if i < d then Some e
    else (match moved marks n kept (i - d) with Some j -> Some (Var (d + j) s) | None -> None)
  | App f args ->
    (match thin_args marks n kept d args [] with Some xs -> Some (App f xs) | None -> None)
  | Quantifier k bs s b ->
    (match thin marks n kept (d + L.length bs) b with Some b' -> Some (Quantifier k bs s b') | None -> None)

and thin_args (marks:list bool) (n kept d:nat) (args:list expr) (acc:list expr)
  : Tot (option (list expr)) (decreases args) =
  match args with
  | [] -> Some (L.rev acc)
  | a :: rest ->
    (match thin marks n kept d a with
     | Some b -> thin_args marks n kept d rest (b :: acc)
     | None -> None)

let eliminated (q:expr) : option expr =
  match q with
  | Quantifier k bs s body ->
    if (k = Forall_k || k = Exists_k) && s = bool_sort then
      let n = L.length bs in
      let marks = binder_marks n body in
      let kept = count_kept marks in
      if kept = n then None
      else (match thin marks n kept 0 body with
            | Some b -> Some (if kept = 0 then b else Quantifier k (L.rev (kept_items marks (L.rev bs))) bool_sort b)
            | None -> None)
    else None
  | _ -> None

(* At most 64 binders (the occurrence walks cost one body walk per binder),
   both sides shallow (bounding every walk and the final comparison). *)
let unused_eliminated (q e:expr) : bool =
  match q with
  | Quantifier _ bs _ _ ->
    if length_within 64 bs && shallow q && shallow e then
      (match eliminated q with Some r -> r = e | None -> false)
    else false
  | _ -> false

(* der (z3 der.cpp reduce1; ast_manager::mk_der exports iff(q, e)) for one
   eliminated variable of a universal over a disjunction. Var j (of the block
   that starts at depth d) is replaced by t lifted over the d binders above
   it; every other variable is kept. *)
let rec subst_var (j:nat) (t:expr) (d:nat) (e:expr) : Tot (option expr) (decreases e) =
  match e with
  | Var i s ->
    if i = d + j then (if get_sort t = s then thin [] 0 d 0 t else None) else Some e
  | App f args ->
    (match subst_args j t d args [] with Some xs -> Some (App f xs) | None -> None)
  | Quantifier k bs s b ->
    (match subst_var j t (d + L.length bs) b with Some b' -> Some (Quantifier k bs s b') | None -> None)

and subst_args (j:nat) (t:expr) (d:nat) (args:list expr) (acc:list expr)
  : Tot (option (list expr)) (decreases args) =
  match args with
  | [] -> Some (L.rev acc)
  | a :: rest ->
    (match subst_var j t d a with
     | Some b -> subst_args j t d rest (b :: acc)
     | None -> None)

(* A binder of the block of n (not a free variable). *)
let bound_var (n:nat) (e:expr) : option nat =
  match e with Var i _ -> if i < n then Some i else None | _ -> None

(* (not (= x t)) or (not (= t x)) with x = Var j a binder of the block (the
   left side preferred when it is one, as der::is_var_diseq) and t free of
   Var j. *)
let diseq_def (n:nat) (lit:expr) : option (nat & expr) =
  match lit with
  | App ng [App eqd [a; b]] ->
    if T.classify ng = T.Negation && T.classify eqd = T.Equality (get_sort a) then
      (match bound_var n a with
       | Some i -> if occurs i 0 b then None else Some (i, b)
       | None ->
         (match bound_var n b with
          | Some k -> if occurs k 0 a then None else Some (k, a)
          | None -> None))
    else None
  | _ -> None

let rec first_def (n:nat) (lits:list expr) (i:nat) : Tot (option (nat & nat & expr)) (decreases lits) =
  match lits with
  | [] -> None
  | l :: rest -> (match diseq_def n l with Some (j, t) -> Some (i, j, t) | None -> first_def n rest (i + 1))

let rec remove_at (i:nat) (xs:list expr) : Tot (list expr) (decreases xs) =
  match xs with [] -> [] | x :: rest -> if i = 0 then rest else x :: remove_at (i - 1) rest

(* ast_util mk_or: false, the single operand, or the canonical `or`. *)
let or_of (args:list expr) : expr =
  match args with
  | [] -> R.false_expr
  | [a] -> a
  | _ -> App (BRW.connective_decl BRW.Disjunction args) args

(* The literal order of z3's flatten_or (ast_util.cpp), which der::reduce1
   applies to the body, on a disjunction none of whose literals it opens:
   the last literal takes the place of the `or`, the others follow in
   order. *)
let rec split_last (x:expr) (rest:list expr) : Tot (expr & list expr) (decreases rest) =
  match rest with
  | [] -> (x, [])
  | y :: tail -> let (l, ys) = split_last y tail in (l, x :: ys)

let flat_order (lits:list expr) : list expr =
  match lits with
  | [] -> []
  | x :: rest -> let (l, ys) = split_last x rest in l :: ys

(* The first defining disequality of lits removed, the rest substituted. *)
let der_order (n:nat) (lits:list expr) (body':expr) : bool =
  match first_def n lits 0 with
  | Some (i, j, t) -> subst_var j t 0 (or_of (remove_at i lits)) = Some body'
  | None -> false

(* der (one eliminated variable, forall over an `or` of at most 4096
   literals, so that the literal removal and the rebuilt `or` read at most
   that many): the literals in z3's flatten_or order or in source order,
   the first defining disequality removed, the rest substituted, the
   binder list kept. *)
let der_body (n:nat) (lits:list expr) (body':expr) : bool =
  der_order n (flat_order lits) body' || der_order n lits body'

let der_step (q e:expr) : bool =
  match q, e with
  | Quantifier Forall_k bs s body, Quantifier Forall_k bs' s' body' ->
    if bs = bs' && s = bool_sort && s' = bool_sort && length_within 64 bs && shallow q && shallow e then
      (match body with
       | App f lits -> T.classify f = T.Nary B.Or && length_within 4096 lits && der_body (L.length bs) lits body'
       | _ -> false)
    else false
  | _, _ -> false

(* pull-quant (pull_quant.cpp pull_quant1_core; ast_manager::mk_pull_quant
   exports iff(e, q)). *)
let binder_quantifier (e:expr) : bool =
  match e with Quantifier k _ _ _ -> k = Forall_k || k = Exists_k | _ -> false

(* The position of the only forall/exists child, if exactly one. *)
let rec single_quantified (cs:list expr) (i:nat) (found:option nat) : Tot (option nat) (decreases cs) =
  match cs with
  | [] -> found
  | c :: rest ->
    if binder_quantifier c then (if Some? found then None else single_quantified rest (i + 1) (Some i))
    else single_quantified rest (i + 1) found

(* The children after pulling the quantified child at position p: its body
   in its place, every other child lifted over the n pulled binders. *)
let rec pulled_children (n p:nat) (b:expr) (cs:list expr) (i:nat) (acc:list expr)
  : Tot (option (list expr)) (decreases cs) =
  match cs with
  | [] -> Some (L.rev acc)
  | c :: rest ->
    if i = p then pulled_children n p b rest (i + 1) (b :: acc)
    else (match thin [] 0 n 0 c with
          | Some c' -> pulled_children n p b rest (i + 1) (c' :: acc)
          | None -> None)

(* The child at position p (a loop; FStar.List.Tot.nth has no native
   counterpart in the OCaml runtime). *)
let rec child_at (cs:list expr) (p:nat) : Tot (option expr) (decreases cs) =
  match cs with [] -> None | c :: rest -> if p = 0 then Some c else child_at rest (p - 1)

(* pull_quant (iff(e, q)) for one quantified child of a canonical and/or:
   (op c1 .. (Q bs. b) .. cn) ~ (Q bs. (op c1' .. b .. cn')), ci' lifted
   over bs (pull_quant::pull_quant1_core with one nested quantifier: its
   body shifts by 0). *)
let pulled (e q:expr) : bool =
  match e, q with
  | App f cs, Quantifier k bs s (App g cs') ->
    if (T.classify f = T.Nary B.Or || T.classify f = T.Nary B.And) && g = f && s = bool_sort &&
       length_within 64 bs && shallow e && shallow q then
      (match single_quantified cs 0 None with
       | Some p ->
         (match child_at cs p with
          | Some (Quantifier k' bs' s' b) ->
            k' = k && bs' = bs && s' = bool_sort && pulled_children (L.length bs) p b cs 0 [] = Some cs'
          | _ -> false)
       | None -> false)
    else false
  | _, _ -> false

(* One quantified child of a canonical and/or pulled out (pulled), or a
   nested forall flattened (Z3SortedQuantifier.flatten); both sides
   shallow before any comparison. *)
let pull_ok (e q:expr) : bool =
  if pulled e q then true else shallow e && shallow q && Q.flatten e q

(* A scoped rewrite leaf `lhs ~ rhs` (quant-intro roots only): the typed Int
   equivalence; an ITE law at any result sort (the term-ITE leaves of
   Pulse.Checker.Base-1 q1, e.g. node 3010 at sort Term); an Int product
   factor permutation (the nonlinear Int leaves, e.g. FStar.Math.Euclid
   p1 * p0 ~ p0 * p1); or, for Boolean
   sides, a regrouping of nested canonical and/or over the same operands
   (the n-ary re-association leaves of
   Pulse.Checker.Base-1, e.g. (or d1 d2 d3 d4) = (or (or d1 d2) (or d3 d4))
   with 80-94 KB operands), or the propositional equivalence of the Boolean
   cuts, first at depth 64 and otherwise at depth 2 (the same check over the
   coarser abstraction whose atoms are the subterms below the top two
   Boolean levels: an iff/negation normalization of wide conjunctions such
   as `(= a (not o)) = (not (= o a))` exceeds the truth-table bound at depth
   64 but has two atoms at depth 2). Every check is syntactic in the atoms
   and operands, so it holds at every typed environment of every scope at
   which both sides are typed (lemma_rewrite_at). *)
let propositional_at (fuel:nat) (lhs rhs:expr) : bool =
  DT.bounded_propositional (B.Eq (T.cut fuel lhs) (T.cut fuel rhs))

(* `if`, not `||`: F*'s normalizer reduces both operands of `||`, so a
   normalized check of a regrouped leaf would also run the propositional
   checks; the executable result is the same. *)
let rewrite_ok (lhs rhs:expr) : bool =
  AR.equivalent lhs rhs ||
  (if ite_rewritten lhs rhs then true
   else if product_permuted lhs rhs then true
   else get_sort lhs = bool_sort && get_sort rhs = bool_sort &&
        (if regrouped lhs rhs then true else propositional_at 64 lhs rhs || propositional_at 2 lhs rhs))

(* `real`: the caller's schema-derived Real gate (Z3SortedProof passes
   Z3SortedReal.real_primitive of its checked schema). Under it, a leaf the
   Real normal forms decide (Z3SortedRealLinear.real_equivalent: Real and
   Int-with-to_real linear renormalization, comparison orientation and
   strictness, binary Real product commutation, Real equations by their
   difference polynomials) is replayed too, after every check above. *)
let real_rewrite_ok (real:bool) (lhs rhs:expr) : bool =
  if rewrite_ok lhs rhs then true else real && LIN.real_equivalent lhs rhs

(* `scoped`: the certificate has a quant-intro root, whose body proofs may
   use quant-intro congruences and rewrite leaves; an NNF certificate
   (scoped = false) is replayed by exactly the previous rules. *)
let entry_ok (real:bool) (scoped:bool) (assertions:list expr) (e:U.binder_entry) (j:U.judgment)
             (facts:list U.judgment) : bool =
  match edge j with
  | None -> false
  | Some (lhs, rhs) ->
    let name = e.U.binder_name in
    if name = "nnf-neg" then
      (match lhs with
       | App n [src] -> T.classify n = T.Negation && nnf_ok false e.U.binder_sorts src rhs facts
       | _ -> false)
    else if name = "nnf-pos" then nnf_ok true e.U.binder_sorts lhs rhs facts
    else if name = "quant-intro" then
      scoped &&
      (match e.U.binder_sorts with
       | Some bs -> quantifier_ok true bs lhs rhs facts
       | None -> false)
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
    else if name = "rewrite" then scoped && Nil? facts && real_rewrite_ok real lhs rhs
    else if name = "elim-unused" then scoped && Nil? facts && unused_eliminated lhs rhs
    else if name = "der" then scoped && Nil? facts && der_step lhs rhs
    else if name = "pull-quant" then scoped && Nil? facts && pull_ok lhs rhs
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
let rec steps_ok (real:bool) (scoped:bool) (assertions:list expr) (count:nat) (t:U.scope_demands)
                 (cache:I.index_tree U.judgment)
                 (sizes:I.index_tree nat) (k:nat) (entries:list U.binder_entry) (work:nat)
  : Tot bool (decreases entries) =
  match entries with
  | [] -> true
  | e :: rest ->
    if Nil? (U.scope_demanded t k) then steps_ok real scoped assertions count t cache sizes (k + 1) rest work
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
            if entry_ok real scoped assertions e j facts && skolem_scopes_ok e j (U.scope_demanded t k)
            then steps_ok real scoped assertions count t cache (I.index_put sizes k size) (k + 1) rest w
            else false
          | _, _, _ -> false))

let rec entry_at (entries:list U.binder_entry) (n:nat) : Tot (option U.binder_entry) (decreases entries) =
  match entries with
  | [] -> None
  | e :: rest -> if n = 0 then Some e else entry_at rest (n - 1)

(* The certificates this replay consumes: an nnf-neg or nnf-pos root (NNF),
   or a quant-intro root (scoped rewrites). *)
let nnf_root (c:U.binder_certificate) : bool =
  0 <= c.U.binder_root &&
  (match entry_at c.U.binder_entries c.U.binder_root with
   | Some e -> e.U.binder_name = "nnf-neg" || e.U.binder_name = "nnf-pos"
   | None -> false)

let quant_intro_root (c:U.binder_certificate) : bool =
  0 <= c.U.binder_root &&
  (match entry_at c.U.binder_entries c.U.binder_root with
   | Some e -> e.U.binder_name = "quant-intro"
   | None -> false)

let consumed_root (c:U.binder_certificate) : bool = nnf_root c || quant_intro_root c

type verdict =
  | Replayed     (* every used entry replayed: the node is checked *)
  | Unreplayed   (* not a consumed certificate, outside the calculus, or over budget: PENDING *)
  | Malformed    (* a premise id is not an earlier entry: a rejected proof entry *)

let replay_with (real:bool) (assertions:list expr) (c:U.binder_certificate) (concl:U.judgment) : verdict =
  if not (consumed_root c) then Unreplayed
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
           steps_ok real (quant_intro_root c) assertions (U.count_cells 0 assertions) t cache I.Empty 0
             c.U.binder_entries (U.binder_work_limit n)
        then Replayed else Unreplayed

(* The replay without the Real gate (every previous caller). *)
let replay (assertions:list expr) (c:U.binder_certificate) (concl:U.judgment) : verdict =
  replay_with false assertions c concl

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

let lemma_all_hold_four (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                        (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                        (scope:list sort) (rho:V.environment base (S.signature s) scope)
                        (j1 j2 j3 j4:U.judgment)
  : Lemma (requires all_hold s bc eq other scope rho [j1; j2; j3; j4])
          (ensures holds_at s bc eq other scope rho j1 /\ holds_at s bc eq other scope rho j2 /\
                   holds_at s bc eq other scope rho j3 /\ holds_at s bc eq other scope rho j4) =
  assert (all_hold s bc eq other scope rho [j2; j3; j4]);
  assert (all_hold s bc eq other scope rho [j3; j4]);
  assert (all_hold s bc eq other scope rho [j4])

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
    lemma_all_hold_four s bc eq other scope rho jc jn jx jy;
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
    lemma_all_hold_four s bc eq other scope rho ja jna jb jnb;
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

(* The propositional check at any cut depth, at ANY scope where both sides
   are typed Booleans and ANY typed environment of it: read through the
   scoped cut (T.lemma_cut_with_boundaries_at holds for every fuel) and the
   ghost-valuation soundness of the bounded propositional check. *)
let lemma_propositional_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                           (scope:list sort) (rho:V.environment base (S.signature s) scope) (fuel:nat) (lhs rhs:expr)
  : Lemma (requires propositional_at fuel lhs rhs /\ D.scoped scope lhs /\ D.scoped scope rhs /\
                    get_sort lhs == bool_sort /\ get_sort rhs == bool_sort)
          (ensures same_at s bc eq other scope rho lhs rhs) =
  T.lemma_cut_with_boundaries_at s bc eq other scope rho [] fuel lhs;
  T.lemma_cut_with_boundaries_at s bc eq other scope rho [] fuel rhs;
  DT.lemma_bounded_propositional_g (T.truth_at s bc eq other scope rho) (B.Eq (T.cut fuel lhs) (T.cut fuel rhs));
  lemma_same_truth s bc eq other scope rho lhs rhs

(* Regrouped connectives. The fold of `op` over the truths of operands
   (B.geval_args over their atoms). *)
let rec fold_truth (t:expr -> GTot bool) (op:B.nary_op) (xs:list expr) : GTot bool (decreases xs) =
  match xs with
  | [] -> B.neutral op
  | x :: rest -> B.combine op (t x) (fold_truth t op rest)

let rec lemma_fold_atoms (t:expr -> GTot bool) (op:B.nary_op) (xs:list expr)
  : Lemma (ensures B.geval_args t op (L.map B.Atom xs) == fold_truth t op xs) (decreases xs) =
  match xs with
  | [] -> ()
  | _ :: rest -> lemma_fold_atoms t op rest

(* and, or and xor are associative and commutative with a neutral element,
   so a reversed push onto the stack keeps the fold. *)
let rec lemma_fold_prepend (t:expr -> GTot bool) (op:B.nary_op) (xs acc:list expr)
  : Lemma (ensures fold_truth t op (prepend xs acc) == B.combine op (fold_truth t op xs) (fold_truth t op acc))
          (decreases xs) =
  match xs with
  | [] -> ()
  | x :: rest -> lemma_fold_prepend t op rest (x :: acc)

let rec lemma_prepend_scoped (scope:list sort) (xs acc:list expr)
  : Lemma (requires D.scoped_args scope xs /\ D.scoped_args scope acc)
          (ensures D.scoped_args scope (prepend xs acc)) (decreases xs) =
  match xs with
  | [] -> ()
  | x :: rest -> lemma_prepend_scoped scope rest (x :: acc)

(* The operand loop at a scope where the pending expressions are typed: the
   fold of the collected operands is the fold of the pending expressions
   combined with the fold of acc. An opened application of the canonical
   `op` has the fold of its arguments as its truth (lemma_truth_nary). *)
let rec lemma_operands_within (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                              (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                              (scope:list sort) (rho:V.environment base (S.signature s) scope)
                              (op:B.nary_op) (fuel:nat) (pending acc out:list expr)
  : Lemma (requires operands_within op fuel pending acc == Some out /\ D.scoped_args scope pending)
          (ensures fold_truth (T.truth_at s bc eq other scope rho) op out ==
                   B.combine op (fold_truth (T.truth_at s bc eq other scope rho) op pending)
                                (fold_truth (T.truth_at s bc eq other scope rho) op acc))
          (decreases fuel) =
  match pending with
  | [] -> ()
  | e :: rest ->
    if fuel = 0 then ()
    else match e with
      | App f args ->
        if T.classify f = T.Nary op then (
          lemma_truth_nary s bc eq other scope rho f args op;
          lemma_fold_atoms (T.truth_at s bc eq other scope rho) op args;
          lemma_prepend_scoped scope args rest;
          lemma_fold_prepend (T.truth_at s bc eq other scope rho) op args rest;
          lemma_operands_within s bc eq other scope rho op (fuel - 1) (prepend args rest) acc out)
        else lemma_operands_within s bc eq other scope rho op (fuel - 1) rest (e :: acc) out
      | _ -> lemma_operands_within s bc eq other scope rho op (fuel - 1) rest (e :: acc) out

let lemma_operands (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                   (scope:list sort) (rho:V.environment base (S.signature s) scope)
                   (op:B.nary_op) (e:expr) (out:list expr)
  : Lemma (requires operands op e == Some out /\ D.scoped scope e)
          (ensures fold_truth (T.truth_at s bc eq other scope rho) op out == T.truth_at s bc eq other scope rho e) =
  lemma_operands_within s bc eq other scope rho op 4096 [e] [] out

(* Membership: an operand of a true disjunction's list makes it true, and a
   true conjunction makes each of its operands true. *)
let rec lemma_member_or (t:expr -> GTot bool) (x:expr) (ys:list expr)
  : Lemma (requires L.mem x ys /\ t x) (ensures fold_truth t B.Or ys) (decreases ys) =
  match ys with
  | [] -> ()
  | y :: rest -> if y = x then () else lemma_member_or t x rest

let rec lemma_member_and (t:expr -> GTot bool) (x:expr) (ys:list expr)
  : Lemma (requires L.mem x ys /\ fold_truth t B.And ys) (ensures t x) (decreases ys) =
  match ys with
  | [] -> ()
  | y :: rest -> if y = x then () else lemma_member_and t x rest

let rec lemma_included (t:expr -> GTot bool) (xs ys:list expr)
  : Lemma (requires included xs ys)
          (ensures (fold_truth t B.Or xs ==> fold_truth t B.Or ys) /\
                   (fold_truth t B.And ys ==> fold_truth t B.And xs))
          (decreases xs) =
  match xs with
  | [] -> ()
  | x :: rest ->
    FStar.Classical.move_requires (lemma_member_or t x) ys;
    FStar.Classical.move_requires (lemma_member_and t x) ys;
    lemma_included t rest ys

(* A regrouping by canonical or / and has equal truth on both sides at ANY
   scope where both sides are typed, at ANY typed environment of it: equal
   operand lists have equal folds, and lists included in each other have
   equal disjunctions and equal conjunctions. *)
let lemma_regrouped_by (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (scope:list sort) (rho:V.environment base (S.signature s) scope)
                       (op:B.nary_op) (lhs rhs:expr)
  : Lemma (requires regrouped_by op lhs rhs /\ (op == B.Or \/ op == B.And) /\
                    D.scoped scope lhs /\ D.scoped scope rhs)
          (ensures T.truth_at s bc eq other scope rho lhs == T.truth_at s bc eq other scope rho rhs) =
  match operands op lhs, operands op rhs with
  | Some xs, Some ys ->
    lemma_operands s bc eq other scope rho op lhs xs;
    lemma_operands s bc eq other scope rho op rhs ys;
    if xs = ys then ()
    else (
      lemma_included (T.truth_at s bc eq other scope rho) xs ys;
      lemma_included (T.truth_at s bc eq other scope rho) ys xs)
  | _, _ -> ()

let lemma_regrouped_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (scope:list sort) (rho:V.environment base (S.signature s) scope) (lhs rhs:expr)
  : Lemma (requires regrouped lhs rhs /\ D.scoped scope lhs /\ D.scoped scope rhs /\
                    get_sort lhs == bool_sort /\ get_sort rhs == bool_sort)
          (ensures same_at s bc eq other scope rho lhs rhs) =
  if regrouped_by B.Or lhs rhs then lemma_regrouped_by s bc eq other scope rho B.Or lhs rhs
  else lemma_regrouped_by s bc eq other scope rho B.And lhs rhs;
  lemma_same_truth s bc eq other scope rho lhs rhs

(* ITE laws. The value of a canonical ite at ANY sort, at ANY scope where it
   is typed and ANY typed environment of it, is the value of the branch its
   condition chooses (T.application, `Choice`): the interpretation the
   Sorted semantics already gives every ite, no Real or other theory law. *)
let choose (#base:sort -> Type0) (b:bool) (v w:V.tree base) : V.tree base = if b then v else w

let lemma_value_ite (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                    (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                    (scope:list sort) (rho:V.environment base (S.signature s) scope)
                    (f:func_decl) (c x y:expr)
  : Lemma (requires D.scoped scope (App f [c; x; y]) /\ T.Choice? (T.classify f))
          (ensures D.scoped scope c /\ D.scoped scope x /\ D.scoped scope y /\
                   get_sort c == bool_sort /\ get_sort x == f.range /\ get_sort y == f.range /\
                   T.evaluate_at s bc eq other scope rho (App f [c; x; y]) ==
                   choose (T.truth_at s bc eq other scope rho c)
                     (T.evaluate_at s bc eq other scope rho x) (T.evaluate_at s bc eq other scope rho y)) =
  let r = T.Choice?._0 (T.classify f) in
  assert (f == T.ite_decl r);
  V.lemma_sort_eq (get_sort c) bool_sort;
  V.lemma_sort_eq (get_sort x) r;
  V.lemma_sort_eq (get_sort y) r;
  T.lemma_evaluate_core_at s bc eq other scope rho f [c; x; y];
  assert_norm (T.evaluate_arguments_at s bc eq other scope rho [c; x; y] [bool_sort; r; r] ==
               [T.evaluate_at s bc eq other scope rho c; T.evaluate_at s bc eq other scope rho x;
                T.evaluate_at s bc eq other scope rho y])

let rec lemma_fold_append (t:expr -> GTot bool) (op:B.nary_op) (xs ys:list expr)
  : Lemma (ensures fold_truth t op (L.append xs ys) == B.combine op (fold_truth t op xs) (fold_truth t op ys))
          (decreases xs) =
  match xs with
  | [] -> ()
  | _ :: rest -> lemma_fold_append t op rest ys

(* The one-level operands of a typed Boolean term fold to its truth. *)
let lemma_junctands (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                    (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                    (scope:list sort) (rho:V.environment base (S.signature s) scope)
                    (op:B.nary_op) (e:expr)
  : Lemma (requires D.scoped scope e /\ get_sort e == bool_sort)
          (ensures fold_truth (T.truth_at s bc eq other scope rho) op (junctands op e) ==
                   T.truth_at s bc eq other scope rho e) =
  match e with
  | App f args ->
    if T.classify f = T.Nary op then (
      lemma_truth_nary s bc eq other scope rho f args op;
      lemma_fold_atoms (T.truth_at s bc eq other scope rho) op args)
  | _ -> ()

(* A joined condition is the `op` of the truths of c1 and c2. *)
let lemma_joined (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                 (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                 (scope:list sort) (rho:V.environment base (S.signature s) scope)
                 (op:B.nary_op) (c c1 c2:expr)
  : Lemma (requires joined op c c1 c2 /\ D.scoped scope c /\ D.scoped scope c1 /\ D.scoped scope c2 /\
                    get_sort c1 == bool_sort /\ get_sort c2 == bool_sort)
          (ensures T.truth_at s bc eq other scope rho c ==
                   B.combine op (T.truth_at s bc eq other scope rho c1) (T.truth_at s bc eq other scope rho c2)) =
  match c with
  | App f args ->
    let t = T.truth_at s bc eq other scope rho in
    lemma_truth_nary s bc eq other scope rho f args op;
    lemma_fold_atoms t op args;
    if args = [c1; c2] then ()
    else (
      lemma_fold_append t op (junctands op c1) (junctands op c2);
      lemma_junctands s bc eq other scope rho op c1;
      lemma_junctands s bc eq other scope rho op c2)
  | _ -> ()

(* Each ITE law has one value on both sides at ANY scope where both sides
   are typed, at ANY typed environment of it: every side is the choice of
   its condition (lemma_value_ite); a negated condition swaps the choice
   (lemma_truth_not), and a joined condition chooses the then branch of
   (ite c1 x (ite c2 x y)) exactly when c1 or c2 holds, and the then
   branch of (ite c1 (ite c2 x y) y) exactly when c1 and c2 hold
   (lemma_joined). *)
let lemma_ite_swapped_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                         (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                         (scope:list sort) (rho:V.environment base (S.signature s) scope)
                         (f:func_decl) (c x y c' x' y':expr)
  : Lemma (requires T.Choice? (T.classify f) /\ D.scoped scope (App f [c; x; y]) /\
                    D.scoped scope (App f [c'; x'; y']) /\ ite_swapped c x y c' x' y')
          (ensures same_at s bc eq other scope rho (App f [c; x; y]) (App f [c'; x'; y'])) =
  lemma_value_ite s bc eq other scope rho f c x y;
  lemma_value_ite s bc eq other scope rho f c' x' y';
  (match c with
   | App n [a] -> if T.classify n = T.Negation then lemma_truth_not s bc eq other scope rho n a
   | _ -> ());
  (match c' with
   | App n [a] -> if T.classify n = T.Negation then lemma_truth_not s bc eq other scope rho n a
   | _ -> ());
  lemma_same_at s bc eq other scope rho (App f [c; x; y]) (App f [c'; x'; y'])

let lemma_ite_merged_then_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                             (scope:list sort) (rho:V.environment base (S.signature s) scope)
                             (f:func_decl) (c x y c' x' y':expr)
  : Lemma (requires T.Choice? (T.classify f) /\ D.scoped scope (App f [c; x; y]) /\
                    D.scoped scope (App f [c'; x'; y']) /\ ite_merged_then f c x y c' x' y')
          (ensures same_at s bc eq other scope rho (App f [c; x; y]) (App f [c'; x'; y'])) =
  lemma_value_ite s bc eq other scope rho f c x y;
  lemma_value_ite s bc eq other scope rho f c' x' y';
  (match y with
   | App h [c2; x2; y2] ->
     lemma_value_ite s bc eq other scope rho h c2 x2 y2;
     lemma_joined s bc eq other scope rho B.Or c' c c2
   | _ -> ());
  lemma_same_at s bc eq other scope rho (App f [c; x; y]) (App f [c'; x'; y'])

let lemma_ite_merged_else_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                             (scope:list sort) (rho:V.environment base (S.signature s) scope)
                             (f:func_decl) (c x y c' x' y':expr)
  : Lemma (requires T.Choice? (T.classify f) /\ D.scoped scope (App f [c; x; y]) /\
                    D.scoped scope (App f [c'; x'; y']) /\ ite_merged_else f c x y c' x' y')
          (ensures same_at s bc eq other scope rho (App f [c; x; y]) (App f [c'; x'; y'])) =
  lemma_value_ite s bc eq other scope rho f c x y;
  lemma_value_ite s bc eq other scope rho f c' x' y';
  (match x with
   | App h [c2; x2; y2] ->
     lemma_value_ite s bc eq other scope rho h c2 x2 y2;
     lemma_joined s bc eq other scope rho B.And c' c c2
   | _ -> ());
  lemma_same_at s bc eq other scope rho (App f [c; x; y]) (App f [c'; x'; y'])

let lemma_ite_rewritten_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                           (scope:list sort) (rho:V.environment base (S.signature s) scope) (lhs rhs:expr)
  : Lemma (requires ite_rewritten lhs rhs /\ D.scoped scope lhs /\ D.scoped scope rhs)
          (ensures same_at s bc eq other scope rho lhs rhs) =
  match lhs, rhs with
  | App f [c; x; y], App _ [c'; x'; y'] ->
    if ite_swapped c x y c' x' y' then lemma_ite_swapped_at s bc eq other scope rho f c x y c' x' y'
    else if ite_merged_then f c x y c' x' y' then lemma_ite_merged_then_at s bc eq other scope rho f c x y c' x' y'
    else lemma_ite_merged_else_at s bc eq other scope rho f c x y c' x' y'
  | _, _ -> ()

(* Int product factor permutation. The value of a canonical Int product at
   ANY scope where it is typed, at ANY typed environment of it, is the
   integer product of the values of its factors (the `Calculate Mul` case
   of Z3SortedInteger.application, read back through the Int carrier of
   the same scalar model); equal factor multisets have equal products.
   No Real or other theory law is read. *)
let rec gproduct (v:expr -> GTot int) (xs:list expr) : GTot int (decreases xs) =
  match xs with [] -> 1 | x :: rest -> v x * gproduct v rest

let lemma_mul_swap (a b c:int) : Lemma (a * (b * c) == b * (a * c)) =
  FStar.Math.Lemmas.paren_mul_right a b c;
  FStar.Math.Lemmas.swap_mul a b;
  FStar.Math.Lemmas.paren_mul_right b a c

let lemma_mul_rotate (a b c:int) : Lemma (a * (b * c) == (b * a) * c) =
  lemma_mul_swap a b c;
  FStar.Math.Lemmas.paren_mul_right b a c

let rec lemma_remove_product (v:expr -> GTot int) (x:expr) (xs ys:list expr)
  : Lemma (requires RW.remove_factor x xs == Some ys)
          (ensures gproduct v xs == v x * gproduct v ys)
          (decreases xs) =
  match xs with
  | [] -> ()
  | y :: rest ->
    if x <> y then (
      let tail = Some?.v (RW.remove_factor x rest) in
      lemma_remove_product v x rest tail;
      lemma_mul_swap (v y) (v x) (gproduct v tail))

let rec lemma_permuted_product (v:expr -> GTot int) (xs ys:list expr)
  : Lemma (requires RW.factor_permutation xs ys)
          (ensures gproduct v xs == gproduct v ys)
          (decreases xs) =
  match xs with
  | [] -> ()
  | x :: rest ->
    let tail = Some?.v (RW.remove_factor x ys) in
    lemma_remove_product v x ys tail;
    lemma_permuted_product v rest tail

let rec lemma_prepend_product (v:expr -> GTot int) (scope:list sort) (xs acc:list expr)
  : Lemma (ensures gproduct v (prepend xs acc) == gproduct v xs * gproduct v acc /\
                   ((D.scoped_args scope xs /\ D.scoped_args scope acc) ==> D.scoped_args scope (prepend xs acc)) /\
                   ((LA.same_sort LA.int_s xs /\ LA.same_sort LA.int_s acc) ==> LA.same_sort LA.int_s (prepend xs acc)))
          (decreases xs) =
  match xs with
  | [] -> ()
  | x :: rest ->
    lemma_prepend_product v scope rest (x :: acc);
    lemma_mul_rotate (gproduct v rest) (v x) (gproduct v acc)

let rec lemma_numbers_product (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                              (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                              (scope:list sort) (rho:V.environment base (S.signature s) scope)
                              (args:list expr) (ss:list sort)
  : Lemma (requires D.scoped_args scope args /\ sorts_match args ss /\ SI.integer_sorts ss)
          (ensures SI.product (SI.numbers s eq.T.integers ss (T.evaluate_arguments_at s bc eq other scope rho args ss)) ==
                   gproduct (AR.integer s bc eq other scope rho) args)
          (decreases args) =
  match args, ss with
  | a :: rest, t :: tail ->
    V.lemma_sort_eq (get_sort a) t;
    lemma_numbers_product s bc eq other scope rho rest tail
  | _, _ -> ()

let lemma_product_node (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (scope:list sort) (rho:V.environment base (S.signature s) scope)
                       (f:func_decl) (args:list expr)
  : Lemma (requires D.scoped scope (App f args) /\ SI.classify f == SI.Calculate LA.Mul)
          (ensures D.scoped_args scope args /\ LA.same_sort LA.int_s args /\
                   AR.integer s bc eq other scope rho (App f args) ==
                   gproduct (AR.integer s bc eq other scope rho) args) =
  SI.lemma_argument_sorts args f.domain;
  AR.lemma_application s bc eq other scope rho f args;
  lemma_numbers_product s bc eq other scope rho args f.domain

let rec lemma_factors_within (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                             (scope:list sort) (rho:V.environment base (S.signature s) scope)
                             (fuel room:nat) (pending acc fs:list expr)
  : Lemma (requires D.scoped_args scope pending /\ LA.same_sort LA.int_s pending /\
                    factors_within fuel room pending acc == Some fs)
          (ensures gproduct (AR.integer s bc eq other scope rho) fs ==
                   gproduct (AR.integer s bc eq other scope rho) pending *
                   gproduct (AR.integer s bc eq other scope rho) acc)
          (decreases fuel) =
  let v = AR.integer s bc eq other scope rho in
  match pending with
  | [] -> ()
  | e :: rest ->
    match e with
    | App f args ->
      if product_tags f && length_within room args && length_within room f.domain &&
         SI.classify f = SI.Calculate LA.Mul then (
        lemma_product_node s bc eq other scope rho f args;
        lemma_prepend_product v scope args rest;
        lemma_factors_within s bc eq other scope rho (fuel - 1) room (prepend args rest) acc fs)
      else (
        lemma_factors_within s bc eq other scope rho (fuel - 1) (room - 1) rest (e :: acc) fs;
        lemma_mul_rotate (gproduct v rest) (v e) (gproduct v acc))
    | _ ->
      lemma_factors_within s bc eq other scope rho (fuel - 1) (room - 1) rest (e :: acc) fs;
      lemma_mul_rotate (gproduct v rest) (v e) (gproduct v acc)

let lemma_single_product (v:expr -> GTot int) (e:expr)
  : Lemma (gproduct v [e] * gproduct v [] == v e) =
  assert (gproduct v [] == 1);
  assert (gproduct v [e] == v e * 1)

let lemma_product_permuted_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                              (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                              (scope:list sort) (rho:V.environment base (S.signature s) scope) (lhs rhs:expr)
  : Lemma (requires product_permuted lhs rhs /\ D.scoped scope lhs /\ D.scoped scope rhs)
          (ensures same_at s bc eq other scope rho lhs rhs) =
  let v = AR.integer s bc eq other scope rho in
  let xs = Some?.v (int_factors lhs) in
  let ys = Some?.v (int_factors rhs) in
  lemma_factors_within s bc eq other scope rho 4096 64 [lhs] [] xs;
  lemma_factors_within s bc eq other scope rho 4096 64 [rhs] [] ys;
  lemma_single_product v lhs;
  lemma_single_product v rhs;
  lemma_permuted_product v xs ys;
  assert (v lhs == v rhs);
  AR.lemma_integer_equality s bc eq other scope rho lhs rhs;
  lemma_same_at s bc eq other scope rho lhs rhs

(* ---------------------------------------------------------------------- *)
(* elim-unused: thinning, typed tuples and the law                         *)
(* ---------------------------------------------------------------------- *)


let rec lemma_marks_below (k:nat) (body:expr) (acc:list bool)
  : Lemma (ensures L.length (marks_below k body acc) == k + L.length acc) (decreases k) =
  if k > 0 then lemma_marks_below (k - 1) body (occurs (k - 1) 0 body :: acc)

let rec lemma_kept_length (#a:Type) (marks:list bool) (xs:list a)
  : Lemma (requires L.length marks == L.length xs)
          (ensures L.length (kept_items marks xs) == count_kept marks) (decreases marks) =
  match marks, xs with
  | _ :: rest, _ :: tail -> lemma_kept_length rest tail
  | _, _ -> ()

let rec lemma_count_kept (marks:list bool)
  : Lemma (ensures count_kept marks <= L.length marks) (decreases marks) =
  match marks with [] -> () | _ :: rest -> lemma_count_kept rest

let rec lemma_none_kept (marks:list bool) (j acc:nat)
  : Lemma (requires count_kept marks == 0) (ensures rank_from marks j acc == None) (decreases marks) =
  match marks with
  | [] -> ()
  | _ :: rest -> if j > 0 then lemma_none_kept rest (j - 1) acc

let rec lemma_none_kept_items (#a:Type) (marks:list bool) (xs:list a)
  : Lemma (requires count_kept marks == 0) (ensures kept_items marks xs == []) (decreases marks) =
  match marks, xs with
  | _ :: rest, _ :: tail -> lemma_none_kept_items rest tail
  | _, _ -> ()

let rec lemma_rank_bound (marks:list bool) (j acc q:nat)
  : Lemma (requires rank_from marks j acc == Some q)
          (ensures acc <= q /\ q - acc < count_kept marks /\ j < L.length marks) (decreases marks) =
  match marks with
  | m :: rest -> if j > 0 then lemma_rank_bound rest (j - 1) (if m then acc + 1 else acc) q

(* ---------------------------------------------------------------------- *)
(* Typed tuples: projection onto the kept binders and completion            *)
(* ---------------------------------------------------------------------- *)

let rec project (#base:sort -> Type0) (sigma:V.signature) (marks:list bool) (ss:list sort)
                (vs:V.arguments base sigma ss)
  : Tot (V.arguments base sigma (kept_items marks ss)) (decreases marks) =
  match marks, ss, vs with
  | m :: rest, _ :: srest, v :: vrest ->
    if m then v :: project sigma rest srest vrest else project sigma rest srest vrest
  | _, _, _ -> []

let rec merge (#base:sort -> Type0) (sigma:V.signature) (fill:(t:sort -> GTot (V.value base sigma t)))
              (marks:list bool) (ss:list sort) (ws:V.arguments base sigma (kept_items marks ss))
  : GTot (V.arguments base sigma ss) (decreases ss) =
  match ss with
  | [] -> []
  | t :: srest ->
    (match marks with
     | [] -> fill t :: merge sigma fill [] srest []
     | m :: mrest ->
       if m then (match ws with
                  | w :: wrest -> w :: merge sigma fill mrest srest wrest
                  | [] -> FStar.Pervasives.false_elim ())
       else fill t :: merge sigma fill mrest srest ws)

let rec lemma_project_at (#base:sort -> Type0) (sigma:V.signature) (marks:list bool) (ss:list sort)
                         (vs:V.arguments base sigma ss) (p acc q:nat)
  : Lemma (requires L.length marks == L.length ss /\ rank_from marks p acc == Some q)
          (ensures p < L.length ss /\ acc <= q /\ q - acc < L.length (kept_items marks ss) /\
                   (E.tuple_at sigma (kept_items marks ss) (project sigma marks ss vs) (q - acc) <: V.tree base) ==
                   (E.tuple_at sigma ss vs p <: V.tree base))
          (decreases marks) =
  lemma_rank_bound marks p acc q;
  lemma_kept_length marks ss;
  match marks, ss, vs with
  | m :: rest, _ :: srest, _ :: vrest ->
    if p > 0 then lemma_project_at sigma rest srest vrest (p - 1) (if m then acc + 1 else acc) q
  | _, _, _ -> ()

let rec lemma_merge_at (#base:sort -> Type0) (sigma:V.signature) (fill:(t:sort -> GTot (V.value base sigma t)))
                       (marks:list bool) (ss:list sort) (ws:V.arguments base sigma (kept_items marks ss)) (p acc q:nat)
  : Lemma (requires L.length marks == L.length ss /\ rank_from marks p acc == Some q)
          (ensures p < L.length ss /\ acc <= q /\ q - acc < L.length (kept_items marks ss) /\
                   (E.tuple_at sigma ss (merge sigma fill marks ss ws) p <: V.tree base) ==
                   (E.tuple_at sigma (kept_items marks ss) ws (q - acc) <: V.tree base))
          (decreases ss) =
  lemma_rank_bound marks p acc q;
  lemma_kept_length marks ss;
  match ss, marks with
  | _ :: srest, m :: mrest ->
    if m then (match ws with
               | _ :: wrest -> if p > 0 then lemma_merge_at sigma fill mrest srest wrest (p - 1) (acc + 1) q
               | [] -> ())
    else if p > 0 then lemma_merge_at sigma fill mrest srest ws (p - 1) acc q
  | _, _ -> ()

(* ---------------------------------------------------------------------- *)
(* Thinning preserves values between related environments                   *)
(* ---------------------------------------------------------------------- *)

let related_at (#base:sort -> Type0) (sigma:V.signature) (marks:list bool) (n kept d:nat)
               (a b:list sort) (rho:V.environment base sigma a) (eta:V.environment base sigma b)
               (p:nat{p < L.length a}) : prop =
  (p < d ==> p < L.length b /\ (rho p <: V.tree base) == (eta p <: V.tree base)) /\
  (p >= d ==> (match moved marks n kept (p - d) with
               | Some q -> d + q < L.length b /\ (rho p <: V.tree base) == (eta (d + q) <: V.tree base)
               | None -> True))

let related (#base:sort -> Type0) (sigma:V.signature) (marks:list bool) (n kept d:nat)
            (a b:list sort) (rho:V.environment base sigma a) (eta:V.environment base sigma b) : prop =
  forall (p:nat{p < L.length a}). related_at sigma marks n kept d a b rho eta p

let lemma_related_extend (#base:sort -> Type0) (sigma:V.signature) (marks:list bool) (n kept d:nat)
                         (a b bound:list sort) (vs:V.arguments base sigma bound)
                         (rho:V.environment base sigma a) (eta:V.environment base sigma b)
  : Lemma (requires related sigma marks n kept d a b rho eta)
          (ensures related sigma marks n kept (d + L.length bound) (bound @ a) (bound @ b)
                     (V.extend sigma a bound vs rho) (V.extend sigma b bound vs eta)) =
  LP.append_length bound a;
  LP.append_length bound b;
  let m = L.length bound in
  let at (p:nat{p < L.length (bound @ a)})
    : Lemma (related_at sigma marks n kept (d + m) (bound @ a) (bound @ b)
               (V.extend sigma a bound vs rho) (V.extend sigma b bound vs eta) p) =
    DS.lemma_extend_index sigma a bound vs rho p;
    if p < m then DS.lemma_extend_index sigma b bound vs eta p
    else if p < d + m then (
      DS.lemma_extend_index sigma b bound vs eta p;
      assert (related_at sigma marks n kept d a b rho eta (p - m)))
    else (
      assert (related_at sigma marks n kept d a b rho eta (p - m));
      match moved marks n kept (p - (d + m)) with
      | Some q -> DS.lemma_extend_index sigma b bound vs eta (d + m + q)
      | None -> ()) in
  FStar.Classical.forall_intro at

let lemma_thin_sort (marks:list bool) (n kept d:nat) (e e':expr)
  : Lemma (requires thin marks n kept d e == Some e') (ensures get_sort e' == get_sort e) =
  match e with
  | Var _ _ -> ()
  | App f args -> ()
  | Quantifier k bs s b -> ()

(* The argument list of thin_args, without the accumulator. *)
let rec thin_list (marks:list bool) (n kept d:nat) (args:list expr) : Tot (option (list expr)) (decreases args) =
  match args with
  | [] -> Some []
  | a :: rest ->
    (match thin marks n kept d a, thin_list marks n kept d rest with
     | Some b, Some bs -> Some (b :: bs)
     | _, _ -> None)

let rec lemma_thin_args (marks:list bool) (n kept d:nat) (args acc:list expr)
  : Lemma (ensures thin_args marks n kept d args acc ==
                   (match thin_list marks n kept d args with Some ys -> Some (L.rev acc @ ys) | None -> None))
          (decreases args) =
  match args with
  | [] -> LP.append_l_nil (L.rev acc)
  | a :: rest ->
    (match thin marks n kept d a with
     | Some b ->
       lemma_thin_args marks n kept d rest (b :: acc);
       LP.rev_append [b] acc;
       (match thin_list marks n kept d rest with
        | Some ys -> LP.append_assoc (L.rev acc) [b] ys
        | None -> ())
     | None -> ())

let rec lemma_thin_eval (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                        (marks:list bool) (n kept d:nat) (a b:list sort)
                        (rho:V.environment base sigma a) (eta:V.environment base sigma b) (e e':expr)
  : Lemma (requires D.scoped a e /\ D.scoped b e' /\ thin marks n kept d e == Some e' /\
                    related sigma marks n kept d a b rho eta)
          (ensures (V.evaluate sigma i a rho e <: V.tree base) == (V.evaluate sigma i b eta e' <: V.tree base))
          (decreases e) =
  match e with
  | Var p _ ->
    assert (related_at sigma marks n kept d a b rho eta p);
    if p < d then assert (e' == e)
    else (match moved marks n kept (p - d) with
          | Some q -> assert (e' == Var (d + q) (get_sort e))
          | None -> ())
  | App f args ->
    lemma_thin_args marks n kept d args [];
    let ys = Some?.v (thin_list marks n kept d args) in
    lemma_thin_list_eval sigma i marks n kept d a b rho eta args ys f.domain
  | Quantifier k bound t body ->
    let body' = Some?.v (thin marks n kept (d + L.length bound) body) in
    lemma_thin_sort marks n kept (d + L.length bound) body body';
    let pointwise (vs:V.arguments base sigma (L.rev bound))
      : Lemma (V.evaluate sigma i (L.rev bound @ a) (V.extend sigma a (L.rev bound) vs rho) body ==
               V.evaluate sigma i (L.rev bound @ b) (V.extend sigma b (L.rev bound) vs eta) body') =
      LP.rev_length bound;
      lemma_related_extend sigma marks n kept d a b (L.rev bound) vs rho eta;
      lemma_thin_eval sigma i marks n kept (d + L.length bound) (L.rev bound @ a) (L.rev bound @ b)
        (V.extend sigma a (L.rev bound) vs rho) (V.extend sigma b (L.rev bound) vs eta) body body' in
    FStar.Classical.forall_intro pointwise;
    V.lemma_quantifier_environments sigma i a b rho eta k bound (get_sort body) body body'

and lemma_thin_list_eval (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                         (marks:list bool) (n kept d:nat) (a b:list sort)
                         (rho:V.environment base sigma a) (eta:V.environment base sigma b)
                         (args ys:list expr) (ss:list sort)
  : Lemma (requires D.scoped_args a args /\ D.scoped_args b ys /\ sorts_match args ss /\ sorts_match ys ss /\
                    thin_list marks n kept d args == Some ys /\ related sigma marks n kept d a b rho eta)
          (ensures V.evaluate_args sigma i a rho args ss == V.evaluate_args sigma i b eta ys ss)
          (decreases args) =
  match args, ys, ss with
  | x :: rest, y :: tail, _ :: stail ->
    lemma_thin_eval sigma i marks n kept d a b rho eta x y;
    lemma_thin_list_eval sigma i marks n kept d a b rho eta rest tail stail
  | _, _, _ -> ()

(* ---------------------------------------------------------------------- *)
(* The elim-unused law                                                      *)
(* ---------------------------------------------------------------------- *)

let lemma_marks (n:nat) (body:expr) : Lemma (L.length (binder_marks n body) == n) =
  lemma_marks_below n body []

(* A value of every sort, from the interpretation itself: every carrier of
   a Sorted interpretation is inhabited by its constants (a ghost value,
   never executed). *)
let inhabitant_of (#base:sort -> Type0) (s:S.checked_schema) (other:V.interpretation base (S.signature s))
         (t:sort) : GTot (V.value base (S.signature s) t) =
  other.V.application (inhabitant_decl t) []

(* Two binder tuples that agree on every kept position give the body and
   its thinned copy one value. *)
let lemma_bodies (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                 (marks:list bool) (n kept:nat) (scope ss ss':list sort) (rho:V.environment base sigma scope)
                 (body body':expr) (vs:V.arguments base sigma ss) (ws:V.arguments base sigma ss')
  : Lemma (requires L.length marks == n /\ L.length ss == n /\ L.length ss' == kept /\
                    thin marks n kept 0 body == Some body' /\
                    D.scoped (ss @ scope) body /\ D.scoped (ss' @ scope) body' /\
                    (forall (p q:nat). rank_from marks p 0 == Some q ==>
                       p < n /\ q < kept /\
                       (E.tuple_at sigma ss vs p <: V.tree base) == (E.tuple_at sigma ss' ws q <: V.tree base)))
          (ensures (V.evaluate sigma i (ss @ scope) (V.extend sigma scope ss vs rho) body <: V.tree base) ==
                   (V.evaluate sigma i (ss' @ scope) (V.extend sigma scope ss' ws rho) body' <: V.tree base)) =
  LP.append_length ss scope;
  LP.append_length ss' scope;
  let at (p:nat{p < L.length (ss @ scope)})
    : Lemma (related_at sigma marks n kept 0 (ss @ scope) (ss' @ scope)
               (V.extend sigma scope ss vs rho) (V.extend sigma scope ss' ws rho) p) =
    DS.lemma_extend_index sigma scope ss vs rho p;
    if p < n then
      (match rank_from marks p 0 with
       | Some q ->
         assert (q < kept /\ (E.tuple_at sigma ss vs p <: V.tree base) == (E.tuple_at sigma ss' ws q <: V.tree base));
         DS.lemma_extend_index sigma scope ss' ws rho q
       | None -> ())
    else DS.lemma_extend_index sigma scope ss' ws rho (p - n + kept) in
  FStar.Classical.forall_intro at;
  lemma_thin_eval sigma i marks n kept 0 (ss @ scope) (ss' @ scope)
    (V.extend sigma scope ss vs rho) (V.extend sigma scope ss' ws rho) body body'

let lemma_projected (#base:sort -> Type0) (sigma:V.signature) (marks:list bool) (ss:list sort)
                    (vs:V.arguments base sigma ss)
  : Lemma (requires L.length marks == L.length ss)
          (ensures forall (p q:nat). rank_from marks p 0 == Some q ==>
                    p < L.length ss /\ q < L.length (kept_items marks ss) /\
                     (E.tuple_at sigma ss vs p <: V.tree base) ==
                     (E.tuple_at sigma (kept_items marks ss) (project sigma marks ss vs) q <: V.tree base)) =
  lemma_kept_length marks ss;
  let at (p q:nat) : Lemma (rank_from marks p 0 == Some q ==>
                             p < L.length ss /\ q < L.length (kept_items marks ss) /\
                              (E.tuple_at sigma ss vs p <: V.tree base) ==
                              (E.tuple_at sigma (kept_items marks ss) (project sigma marks ss vs) q <: V.tree base)) =
    if rank_from marks p 0 = Some q then lemma_project_at sigma marks ss vs p 0 q in
  FStar.Classical.forall_intro_2 at

let lemma_merged (#base:sort -> Type0) (sigma:V.signature) (fill:(t:sort -> GTot (V.value base sigma t)))
                 (marks:list bool) (ss:list sort) (ws:V.arguments base sigma (kept_items marks ss))
  : Lemma (requires L.length marks == L.length ss)
          (ensures forall (p q:nat). rank_from marks p 0 == Some q ==>
                    p < L.length ss /\ q < L.length (kept_items marks ss) /\
                     (E.tuple_at sigma ss (merge sigma fill marks ss ws) p <: V.tree base) ==
                     (E.tuple_at sigma (kept_items marks ss) ws q <: V.tree base)) =
  lemma_kept_length marks ss;
  let at (p q:nat) : Lemma (rank_from marks p 0 == Some q ==>
                             p < L.length ss /\ q < L.length (kept_items marks ss) /\
                              (E.tuple_at sigma ss (merge sigma fill marks ss ws) p <: V.tree base) ==
                              (E.tuple_at sigma (kept_items marks ss) ws q <: V.tree base)) =
    if rank_from marks p 0 = Some q then lemma_merge_at sigma fill marks ss ws p 0 q in
  FStar.Classical.forall_intro_2 at

(* elim-unused at ANY scope where both sides are typed, at ANY typed
   environment: (Q bs. body) and its reduced form have one truth. The
   removed binders range over carriers inhabited by the interpretation
   (fill); the universal and existential laws are those of the root model. *)
let lemma_eliminated_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                        (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                        (scope:list sort) (rho:V.environment base (S.signature s) scope) (q e:expr)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    eliminated q == Some e /\ D.scoped scope q /\ D.scoped scope e)
          (ensures same_at s bc eq other scope rho q e) =
  match q with
  | Quantifier k bs _ body ->
    let sigma = S.signature s in
    let i = T.interpretation s bc eq other in
    let n = L.length bs in
    let marks = binder_marks n body in
    let kept = count_kept marks in
    let body' = Some?.v (thin marks n kept 0 body) in
    let ss = L.rev bs in
    let ss' = kept_items marks ss in
    lemma_marks n body;
    LP.rev_length bs;
    lemma_kept_length marks ss;
    LP.rev_involutive ss';
    let filler = inhabitant_of s other in
    let tq (vs:V.arguments base sigma ss) : GTot bool =
      T.truth_at s bc eq other (ss @ scope) (V.extend sigma scope ss vs rho) body in
    let te (ws:V.arguments base sigma ss') : GTot bool =
      T.truth_at s bc eq other (ss' @ scope) (V.extend sigma scope ss' ws rho) body' in
    assert (D.scoped (ss @ scope) body);
    if kept = 0 then (
      lemma_none_kept_items marks ss;
      assert (e == body');
      assert (D.scoped (ss' @ scope) body')
    ) else (
      assert (e == Quantifier k (L.rev ss') bool_sort body');
      assert (D.scoped (ss' @ scope) body')
    );
    let down (vs:V.arguments base sigma ss) : Lemma (tq vs == te (project sigma marks ss vs)) =
      lemma_projected sigma marks ss vs;
      lemma_bodies sigma i marks n kept scope ss ss' rho body body' vs (project sigma marks ss vs) in
    let up (ws:V.arguments base sigma ss') : Lemma (te ws == tq (merge sigma filler marks ss ws)) =
      lemma_merged sigma filler marks ss ws;
      lemma_bodies sigma i marks n kept scope ss ss' rho body body' (merge sigma filler marks ss ws) ws in
    FStar.Classical.forall_intro down;
    FStar.Classical.forall_intro up;
    (match k with
     | Forall_k -> Q.lemma_forall_truth s bc eq other scope rho bs body
     | _ -> lemma_exists_truth s bc eq other scope rho bs body);
    if kept = 0 then (
      let w0 : V.arguments base sigma ss' = [] in
      up w0;
      assert (V.extend sigma scope ss' w0 rho == rho);
      assert (te w0 == T.truth_at s bc eq other scope rho e)
    ) else (
      match k with
      | Forall_k -> Q.lemma_forall_truth s bc eq other scope rho (L.rev ss') body'
      | _ -> lemma_exists_truth s bc eq other scope rho (L.rev ss') body'
    );
    lemma_same_truth s bc eq other scope rho q e
  | _ -> ()

(* An elim-unused entry at ANY scope where both sides are typed, at ANY
   typed environment of it (the check reads no environment). *)
let lemma_unused_eliminated_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                               (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                               (scope:list sort) (rho:V.environment base (S.signature s) scope) (q e:expr)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    unused_eliminated q e /\ D.scoped scope q /\ D.scoped scope e)
          (ensures same_at s bc eq other scope rho q e) =
  lemma_eliminated_at s bc eq other scope rho q e

(* ---------------------------------------------------------------------- *)
(* Lifting, substitution and avoidance at typed environments                *)
(* ---------------------------------------------------------------------- *)

(* t lifted over d binders (thin with no removed binder) has, at an
   environment whose positions from d on are those of eta0, t's value. *)
let lemma_lift_eval (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                    (d:nat) (s0 a:list sort) (eta0:V.environment base sigma s0) (eta:V.environment base sigma a)
                    (t t':expr)
  : Lemma (requires D.scoped s0 t /\ D.scoped a t' /\ thin [] 0 d 0 t == Some t' /\
                    (forall (p:nat{p < L.length s0}). p + d < L.length a /\
                       (eta0 p <: V.tree base) == (eta (p + d) <: V.tree base)))
          (ensures (V.evaluate sigma i s0 eta0 t <: V.tree base) == (V.evaluate sigma i a eta t' <: V.tree base)) =
  let at (p:nat{p < L.length s0}) : Lemma (related_at sigma [] 0 d 0 s0 a eta0 eta p) = () in
  FStar.Classical.forall_intro at;
  lemma_thin_eval sigma i [] 0 d 0 s0 a eta0 eta t t'

let subst_rel_at (#base:sort -> Type0) (sigma:V.signature) (j d:nat) (s0 a:list sort)
                 (eta0:V.environment base sigma s0) (tv:V.tree base)
                 (rho eta:V.environment base sigma a) (p:nat{p < L.length a}) : prop =
  (p <> d + j ==> (rho p <: V.tree base) == (eta p <: V.tree base)) /\
  (p == d + j ==> (rho p <: V.tree base) == tv) /\
  (p >= d ==> p - d < L.length s0 /\ (eta p <: V.tree base) == (eta0 (p - d) <: V.tree base))

let subst_rel (#base:sort -> Type0) (sigma:V.signature) (j d:nat) (s0 a:list sort)
              (eta0:V.environment base sigma s0) (tv:V.tree base)
              (rho eta:V.environment base sigma a) : prop =
  L.length a == d + L.length s0 /\
  (forall (p:nat{p < L.length a}). subst_rel_at sigma j d s0 a eta0 tv rho eta p)

let lemma_subst_extend (#base:sort -> Type0) (sigma:V.signature) (j d:nat) (s0 a bound:list sort)
                       (eta0:V.environment base sigma s0) (tv:V.tree base)
                       (vs:V.arguments base sigma bound) (rho eta:V.environment base sigma a)
  : Lemma (requires subst_rel sigma j d s0 a eta0 tv rho eta)
          (ensures subst_rel sigma j (d + L.length bound) s0 (bound @ a) eta0 tv
                     (V.extend sigma a bound vs rho) (V.extend sigma a bound vs eta)) =
  LP.append_length bound a;
  let m = L.length bound in
  let at (p:nat{p < L.length (bound @ a)})
    : Lemma (subst_rel_at sigma j (d + m) s0 (bound @ a) eta0 tv
               (V.extend sigma a bound vs rho) (V.extend sigma a bound vs eta) p) =
    DS.lemma_extend_index sigma a bound vs rho p;
    DS.lemma_extend_index sigma a bound vs eta p;
    if p >= m then assert (subst_rel_at sigma j d s0 a eta0 tv rho eta (p - m)) in
  FStar.Classical.forall_intro at

let rec subst_list (j:nat) (t:expr) (d:nat) (args:list expr) : Tot (option (list expr)) (decreases args) =
  match args with
  | [] -> Some []
  | a :: rest ->
    (match subst_var j t d a, subst_list j t d rest with
     | Some b, Some bs -> Some (b :: bs)
     | _, _ -> None)

let rec lemma_subst_args (j:nat) (t:expr) (d:nat) (args acc:list expr)
  : Lemma (ensures subst_args j t d args acc ==
                   (match subst_list j t d args with Some ys -> Some (L.rev acc @ ys) | None -> None))
          (decreases args) =
  match args with
  | [] -> LP.append_l_nil (L.rev acc)
  | a :: rest ->
    (match subst_var j t d a with
     | Some b ->
       lemma_subst_args j t d rest (b :: acc);
       LP.rev_append [b] acc;
       (match subst_list j t d rest with
        | Some ys -> LP.append_assoc (L.rev acc) [b] ys
        | None -> ())
     | None -> ())

let rec lemma_subst_eval (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                         (j:nat) (t:expr) (d:nat) (s0 a:list sort) (eta0:V.environment base sigma s0)
                         (rho eta:V.environment base sigma a) (e e':expr)
  : Lemma (requires D.scoped s0 t /\ D.scoped a e /\ D.scoped a e' /\ subst_var j t d e == Some e' /\
                    subst_rel sigma j d s0 a eta0 (V.evaluate sigma i s0 eta0 t) rho eta)
          (ensures (V.evaluate sigma i a rho e <: V.tree base) == (V.evaluate sigma i a eta e' <: V.tree base))
          (decreases e) =
  match e with
  | Var p _ ->
    assert (subst_rel_at sigma j d s0 a eta0 (V.evaluate sigma i s0 eta0 t) rho eta p);
    if p = d + j then (
      let at (q:nat{q < L.length s0})
        : Lemma (q + d < L.length a /\ (eta0 q <: V.tree base) == (eta (q + d) <: V.tree base)) =
        assert (subst_rel_at sigma j d s0 a eta0 (V.evaluate sigma i s0 eta0 t) rho eta (q + d)) in
      FStar.Classical.forall_intro at;
      lemma_lift_eval sigma i d s0 a eta0 eta t e')
  | App f args ->
    lemma_subst_args j t d args [];
    let ys = Some?.v (subst_list j t d args) in
    lemma_subst_list_eval sigma i j t d s0 a eta0 rho eta args ys f.domain
  | Quantifier k bound _ body ->
    let body' = Some?.v (subst_var j t (d + L.length bound) body) in
    let pointwise (vs:V.arguments base sigma (L.rev bound))
      : Lemma (V.evaluate sigma i (L.rev bound @ a) (V.extend sigma a (L.rev bound) vs rho) body ==
               V.evaluate sigma i (L.rev bound @ a) (V.extend sigma a (L.rev bound) vs eta) body') =
      LP.rev_length bound;
      lemma_subst_extend sigma j d s0 a (L.rev bound) eta0 (V.evaluate sigma i s0 eta0 t) vs rho eta;
      lemma_subst_eval sigma i j t (d + L.length bound) s0 (L.rev bound @ a) eta0
        (V.extend sigma a (L.rev bound) vs rho) (V.extend sigma a (L.rev bound) vs eta) body body' in
    FStar.Classical.forall_intro pointwise;
    V.lemma_quantifier_environments sigma i a a rho eta k bound (get_sort body) body body'

and lemma_subst_list_eval (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                          (j:nat) (t:expr) (d:nat) (s0 a:list sort) (eta0:V.environment base sigma s0)
                          (rho eta:V.environment base sigma a) (args ys:list expr) (ss:list sort)
  : Lemma (requires D.scoped s0 t /\ D.scoped_args a args /\ D.scoped_args a ys /\
                    sorts_match args ss /\ sorts_match ys ss /\ subst_list j t d args == Some ys /\
                    subst_rel sigma j d s0 a eta0 (V.evaluate sigma i s0 eta0 t) rho eta)
          (ensures V.evaluate_args sigma i a rho args ss == V.evaluate_args sigma i a eta ys ss)
          (decreases args) =
  match args, ys, ss with
  | x :: rest, y :: tail, _ :: stail ->
    lemma_subst_eval sigma i j t d s0 a eta0 rho eta x y;
    lemma_subst_list_eval sigma i j t d s0 a eta0 rho eta rest tail stail
  | _, _, _ -> ()

let agree_at (#base:sort -> Type0) (sigma:V.signature) (j d:nat) (a:list sort)
             (rho rho':V.environment base sigma a) (p:nat{p < L.length a}) : prop =
  p <> d + j ==> (rho p <: V.tree base) == (rho' p <: V.tree base)

let lemma_agree_subst_rel_at (#base:sort -> Type0) (sigma:V.signature) (j:nat) (s0:list sort)
                             (rho rho':V.environment base sigma s0) (tv:V.tree base)
                             (p:nat{p < L.length s0})
  : Lemma (requires agree_at sigma j 0 s0 rho' rho p /\
                    (p == j ==> (rho' p <: V.tree base) == tv))
          (ensures subst_rel_at sigma j 0 s0 s0 rho tv rho' rho p) = ()

let agree (#base:sort -> Type0) (sigma:V.signature) (j d:nat) (a:list sort)
          (rho rho':V.environment base sigma a) : prop =
  forall (p:nat{p < L.length a}). agree_at sigma j d a rho rho' p

(* A term that does not mention Var j has one value at two environments
   that differ only there. *)
let rec lemma_avoid (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                    (j d:nat) (a:list sort) (rho rho':V.environment base sigma a) (e:expr)
  : Lemma (requires D.scoped a e /\ not (occurs j d e) /\ agree sigma j d a rho rho')
          (ensures (V.evaluate sigma i a rho e <: V.tree base) == (V.evaluate sigma i a rho' e <: V.tree base))
          (decreases e) =
  match e with
  | Var p _ -> assert (agree_at sigma j d a rho rho' p)
  | App f args -> lemma_avoid_args sigma i j d a rho rho' args f.domain
  | Quantifier k bound _ body ->
    let pointwise (vs:V.arguments base sigma (L.rev bound))
      : Lemma (V.evaluate sigma i (L.rev bound @ a) (V.extend sigma a (L.rev bound) vs rho) body ==
               V.evaluate sigma i (L.rev bound @ a) (V.extend sigma a (L.rev bound) vs rho') body) =
      LP.rev_length bound;
      LP.append_length (L.rev bound) a;
      let at (p:nat{p < L.length (L.rev bound @ a)})
        : Lemma (agree_at sigma j (d + L.length bound) (L.rev bound @ a)
                   (V.extend sigma a (L.rev bound) vs rho) (V.extend sigma a (L.rev bound) vs rho') p) =
        DS.lemma_extend_index sigma a (L.rev bound) vs rho p;
        DS.lemma_extend_index sigma a (L.rev bound) vs rho' p;
        if p >= L.length bound then assert (agree_at sigma j d a rho rho' (p - L.length bound)) in
      FStar.Classical.forall_intro at;
      lemma_avoid sigma i j (d + L.length bound) (L.rev bound @ a)
        (V.extend sigma a (L.rev bound) vs rho) (V.extend sigma a (L.rev bound) vs rho') body in
    FStar.Classical.forall_intro pointwise;
    V.lemma_quantifier_environments sigma i a a rho rho' k bound (get_sort body) body body

and lemma_avoid_args (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                     (j d:nat) (a:list sort) (rho rho':V.environment base sigma a) (args:list expr) (ss:list sort)
  : Lemma (requires D.scoped_args a args /\ sorts_match args ss /\ not (occurs_args j d args) /\
                    agree sigma j d a rho rho')
          (ensures V.evaluate_args sigma i a rho args ss == V.evaluate_args sigma i a rho' args ss)
          (decreases args) =
  match args, ss with
  | x :: rest, _ :: tail ->
    lemma_avoid sigma i j d a rho rho' x;
    lemma_avoid_args sigma i j d a rho rho' rest tail
  | _, _ -> ()

(* ---------------------------------------------------------------------- *)
(* Typed tuples with one position replaced                                  *)
(* ---------------------------------------------------------------------- *)

let rec replace (#base:sort -> Type0) (sigma:V.signature) (ss:list sort) (vs:V.arguments base sigma ss)
                (j:nat{j < L.length ss}) (v:V.value base sigma (L.index ss j))
  : Tot (V.arguments base sigma ss) (decreases ss) =
  match ss, vs with
  | _ :: srest, w :: wrest -> if j = 0 then v :: wrest else w :: replace sigma srest wrest (j - 1) v
  | _, _ -> FStar.Pervasives.false_elim ()

let rec lemma_replace_at (#base:sort -> Type0) (sigma:V.signature) (ss:list sort) (vs:V.arguments base sigma ss)
                         (j:nat{j < L.length ss}) (v:V.value base sigma (L.index ss j)) (p:nat{p < L.length ss})
  : Lemma (ensures (E.tuple_at sigma ss (replace sigma ss vs j v) p <: V.tree base) ==
                   (if p = j then (v <: V.tree base) else (E.tuple_at sigma ss vs p <: V.tree base)))
          (decreases ss) =
  match ss, vs with
  | _ :: srest, _ :: wrest -> if j > 0 && p > 0 then lemma_replace_at sigma srest wrest (j - 1) v (p - 1)
  | _, _ -> ()

let rec lemma_replace_same (#base:sort -> Type0) (sigma:V.signature) (ss:list sort) (vs:V.arguments base sigma ss)
                           (j:nat{j < L.length ss}) (v:V.value base sigma (L.index ss j))
  : Lemma (requires (v <: V.tree base) == (E.tuple_at sigma ss vs j <: V.tree base))
          (ensures replace sigma ss vs j v == vs)
          (decreases ss) =
  match ss, vs with
  | _ :: srest, _ :: wrest -> if j > 0 then lemma_replace_same sigma srest wrest (j - 1) v
  | _, _ -> ()

(* ---------------------------------------------------------------------- *)
(* Disjunctions                                                             *)
(* ---------------------------------------------------------------------- *)

let rec lemma_fold_remove (t:expr -> GTot bool) (xs:list expr) (k:nat{k < L.length xs})
  : Lemma (ensures fold_truth t B.Or xs == (t (L.index xs k) || fold_truth t B.Or (remove_at k xs)))
          (decreases xs) =
  match xs with
  | _ :: rest -> if k > 0 then lemma_fold_remove t rest (k - 1)

(* z3's flatten_or order keeps the disjunction: or is associative and
   commutative. *)
let rec lemma_split_last (t:expr -> GTot bool) (x:expr) (rest:list expr)
  : Lemma (ensures fold_truth t B.Or (fst (split_last x rest) :: snd (split_last x rest)) ==
                   fold_truth t B.Or (x :: rest))
          (decreases rest) =
  match rest with
  | [] -> ()
  | y :: tail -> lemma_split_last t y tail

let lemma_flat_order (t:expr -> GTot bool) (lits:list expr)
  : Lemma (ensures fold_truth t B.Or (flat_order lits) == fold_truth t B.Or lits) =
  match lits with
  | [] -> ()
  | x :: rest -> lemma_split_last t x rest

let rec lemma_split_last_scoped (scope:list sort) (x:expr) (rest:list expr)
  : Lemma (requires D.scoped_args scope (x :: rest) /\ T.boolean_sorts (L.map get_sort (x :: rest)))
          (ensures D.scoped_args scope (fst (split_last x rest) :: snd (split_last x rest)) /\
                   T.boolean_sorts (L.map get_sort (fst (split_last x rest) :: snd (split_last x rest))))
          (decreases rest) =
  match rest with
  | [] -> ()
  | y :: tail -> lemma_split_last_scoped scope y tail

let lemma_flat_order_scoped (scope:list sort) (lits:list expr)
  : Lemma (requires D.scoped_args scope lits /\ T.boolean_sorts (L.map get_sort lits))
          (ensures D.scoped_args scope (flat_order lits) /\ T.boolean_sorts (L.map get_sort (flat_order lits))) =
  match lits with
  | [] -> ()
  | x :: rest -> lemma_split_last_scoped scope x rest

let rec lemma_remove_scoped (scope:list sort) (xs:list expr) (k:nat)
  : Lemma (requires D.scoped_args scope xs /\ T.boolean_sorts (L.map get_sort xs))
          (ensures D.scoped_args scope (remove_at k xs) /\ T.boolean_sorts (L.map get_sort (remove_at k xs)))
          (decreases xs) =
  match xs with
  | [] -> ()
  | _ :: rest -> if k > 0 then lemma_remove_scoped scope rest (k - 1)

let rec lemma_boolean_domain (xs:list expr)
  : Lemma (requires T.boolean_sorts (L.map get_sort xs))
          (ensures sorts_match xs (BRW.boolean_domain xs) /\ T.boolean_sorts (BRW.boolean_domain xs))
          (decreases xs) =
  match xs with [] -> () | _ :: rest -> lemma_boolean_domain rest

let rec lemma_sorts_bool (xs:list expr) (ss:list sort)
  : Lemma (requires sorts_match xs ss /\ T.boolean_sorts ss) (ensures T.boolean_sorts (L.map get_sort xs))
          (decreases xs) =
  match xs, ss with
  | _ :: rest, t :: tail -> V.lemma_sort_eq (get_sort (L.hd xs)) t; lemma_sorts_bool rest tail
  | _, _ -> ()

let lemma_or_of (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                (scope:list sort) (rho:V.environment base (S.signature s) scope) (xs:list expr)
  : Lemma (requires D.scoped_args scope xs /\ T.boolean_sorts (L.map get_sort xs))
          (ensures D.scoped scope (or_of xs) /\ get_sort (or_of xs) == bool_sort /\
                   T.truth_at s bc eq other scope rho (or_of xs) ==
                   fold_truth (T.truth_at s bc eq other scope rho) B.Or xs) =
  match xs with
  | [] -> lemma_truth_constant s bc eq other scope rho R.false_expr false
  | [a] -> ()
  | _ ->
    lemma_boolean_domain xs;
    let f = BRW.connective_decl BRW.Disjunction xs in
    assert (T.classify f == T.Nary B.Or);
    lemma_truth_nary s bc eq other scope rho f xs B.Or;
    lemma_fold_atoms (T.truth_at s bc eq other scope rho) B.Or xs

(* ---------------------------------------------------------------------- *)
(* The defining disequality                                                  *)
(* ---------------------------------------------------------------------- *)

let rec lemma_first_def (n:nat) (lits:list expr) (i k j:nat) (t:expr)
  : Lemma (requires first_def n lits i == Some (k, j, t))
          (ensures i <= k /\ k - i < L.length lits /\ diseq_def n (L.index lits (k - i)) == Some (j, t))
          (decreases lits) =
  match lits with
  | l :: rest -> (match diseq_def n l with Some _ -> () | None -> lemma_first_def n rest (i + 1) k j t)

(* The literal's truth at a scope where it is typed: the binder's value
   differs from t's. *)
let lemma_diseq (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                (scope:list sort) (rho:V.environment base (S.signature s) scope) (n:nat) (lit t:expr) (j:nat)
  : Lemma (requires D.scoped scope lit /\ diseq_def n lit == Some (j, t))
          (ensures j < n /\ not (occurs j 0 t) /\ D.scoped scope t /\ j < L.length scope /\
                   get_sort t == L.index scope j /\ get_sort lit == bool_sort /\
                   (T.truth_at s bc eq other scope rho lit <==>
                    ~((rho j <: V.tree base) == (T.evaluate_at s bc eq other scope rho t <: V.tree base)))) =
  match lit with
  | App ng [App eqd [a; b]] ->
    lemma_truth_not s bc eq other scope rho ng (App eqd [a; b]);
    assert (eqd == R.eq_decl (get_sort a));
    assert (D.scoped_args scope [a; b]);
    assert (D.scoped_args scope [b]);
    V.lemma_sort_eq (get_sort b) (get_sort a);
    assert (App eqd [a; b] == R.mk_eq_expr a b);
    T.lemma_equality_at s bc eq other scope rho a b
  | _ -> ()

let rec lemma_index_scoped (scope:list sort) (xs:list expr) (k:nat{k < L.length xs})
  : Lemma (requires D.scoped_args scope xs) (ensures D.scoped scope (L.index xs k)) (decreases xs) =
  match xs with _ :: rest -> if k > 0 then lemma_index_scoped scope rest (k - 1)

(* ---------------------------------------------------------------------- *)
(* The der law                                                               *)
(* ---------------------------------------------------------------------- *)

(* Either literal order der_body reads has the truth of the source
   disjunction. *)
let lemma_order_fold (t:expr -> GTot bool) (lits ord:list expr)
  : Lemma (requires ord == flat_order lits \/ ord == lits)
          (ensures fold_truth t B.Or ord == fold_truth t B.Or lits) =
  lemma_flat_order t lits

(* der at ANY scope where both sides are typed, at ANY typed environment:
   (forall bs. (or l1 .. ln)) and (forall bs. (or ord without li)[x := t])
   have one truth when li = (not (= x t)), x a binder of bs not in t, and
   ord is the source literal list or z3's flatten_or order of it. *)
let lemma_der_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                 (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                 (scope:list sort) (rho:V.environment base (S.signature s) scope) (q e:expr)
  : Lemma (requires Q.forall_model s bc other /\ der_step q e /\ D.scoped scope q /\ D.scoped scope e)
          (ensures same_at s bc eq other scope rho q e) =
  match q, e with
  | Quantifier _ bs _ (App f lits), Quantifier _ _ _ body' ->
    let sigma = S.signature s in
    let i = T.interpretation s bc eq other in
    let n = L.length bs in
    let ss = L.rev bs in
    let s0 = ss @ scope in
    let ord = if der_order n (flat_order lits) body' then flat_order lits else lits in
    assert (der_order n ord body' /\ (ord == flat_order lits \/ ord == lits));
    let (k, j, t) = Some?.v (first_def n ord 0) in
    lemma_first_def n ord 0 k j t;
    let lit = L.index ord k in
    let rem = remove_at k ord in
    LP.rev_length bs;
    LP.append_length ss scope;
    assert (D.scoped s0 (App f lits) /\ D.scoped s0 body');
    assert (T.classify f == T.Nary B.Or);
    lemma_sorts_bool lits f.domain;
    lemma_flat_order_scoped s0 lits;
    assert (D.scoped_args s0 ord /\ T.boolean_sorts (L.map get_sort ord));
    lemma_remove_scoped s0 ord k;
    lemma_index_scoped s0 ord k;
    let ext (vs:V.arguments base sigma ss) : V.environment base sigma s0 = V.extend sigma scope ss vs rho in
    let tq (vs:V.arguments base sigma ss) : GTot bool = T.truth_at s bc eq other s0 (ext vs) (App f lits) in
    let te (vs:V.arguments base sigma ss) : GTot bool = T.truth_at s bc eq other s0 (ext vs) body' in
    let tl (vs:V.arguments base sigma ss) : GTot bool = T.truth_at s bc eq other s0 (ext vs) lit in
    let step (vs:V.arguments base sigma ss)
      : Lemma ((exists (ws:V.arguments base sigma ss). te vs == tq ws) /\ (tq vs == (tl vs || te vs))) =
      let rho_v = ext vs in
      lemma_diseq s bc eq other s0 rho_v n lit t j;
      DS.lemma_index_split ss scope j;
      let tv = T.evaluate_at s bc eq other s0 rho_v t in
      let v : V.value base sigma (L.index ss j) = tv in
      let vs' = replace sigma ss vs j v in
      let rho' = ext vs' in
      let at (p:nat{p < L.length s0})
        : Lemma (agree_at sigma j 0 s0 rho_v rho' p /\ agree_at sigma j 0 s0 rho' rho_v p /\
                 (p == j ==> (rho' p <: V.tree base) == (tv <: V.tree base))) =
        DS.lemma_extend_index sigma scope ss vs rho p;
        DS.lemma_extend_index sigma scope ss vs' rho p;
        if p < n then lemma_replace_at sigma ss vs j v p in
      FStar.Classical.forall_intro at;
      lemma_avoid sigma i j 0 s0 rho_v rho' t;
      lemma_or_of s bc eq other s0 rho' rem;
      let at2 (p:nat{p < L.length s0}) : Lemma (subst_rel_at sigma j 0 s0 s0 rho_v tv rho' rho_v p) =
        at p;
        lemma_agree_subst_rel_at sigma j s0 rho_v rho' tv p in
      FStar.Classical.forall_intro at2;
      lemma_subst_eval sigma i j t 0 s0 s0 rho_v rho' rho_v (or_of rem) body';
      T.lemma_boolean s bc (T.evaluate_at s bc eq other s0 rho' (or_of rem));
      T.lemma_boolean s bc (T.evaluate_at s bc eq other s0 rho_v body');
      lemma_truth_nary s bc eq other s0 rho' f lits B.Or;
      lemma_fold_atoms (T.truth_at s bc eq other s0 rho') B.Or lits;
      lemma_order_fold (T.truth_at s bc eq other s0 rho') lits ord;
      lemma_fold_remove (T.truth_at s bc eq other s0 rho') ord k;
      lemma_diseq s bc eq other s0 rho' n lit t j;
      assert (tq vs' == te vs);
      lemma_truth_nary s bc eq other s0 rho_v f lits B.Or;
      lemma_fold_atoms (T.truth_at s bc eq other s0 rho_v) B.Or lits;
      lemma_order_fold (T.truth_at s bc eq other s0 rho_v) lits ord;
      lemma_fold_remove (T.truth_at s bc eq other s0 rho_v) ord k;
      lemma_or_of s bc eq other s0 rho_v rem;
      if not (tl vs) then (
        DS.lemma_extend_index sigma scope ss vs rho j;
        lemma_replace_same sigma ss vs j v)
    in
    FStar.Classical.forall_intro step;
    Q.lemma_forall_truth s bc eq other scope rho bs (App f lits);
    Q.lemma_forall_truth s bc eq other scope rho bs body';
    lemma_same_truth s bc eq other scope rho q e
  | _, _ -> ()


(* pulled_children without the accumulator. *)
let rec pulled_list (n p:nat) (b:expr) (cs:list expr) (i:nat) : Tot (option (list expr)) (decreases cs) =
  match cs with
  | [] -> Some []
  | c :: rest ->
    if i = p then (match pulled_list n p b rest (i + 1) with Some ys -> Some (b :: ys) | None -> None)
    else (match thin [] 0 n 0 c, pulled_list n p b rest (i + 1) with
          | Some c', Some ys -> Some (c' :: ys)
          | _, _ -> None)

let rec lemma_pulled_children (n p:nat) (b:expr) (cs:list expr) (i:nat) (acc:list expr)
  : Lemma (ensures pulled_children n p b cs i acc ==
                   (match pulled_list n p b cs i with Some ys -> Some (L.rev acc @ ys) | None -> None))
          (decreases cs) =
  match cs with
  | [] -> LP.append_l_nil (L.rev acc)
  | c :: rest ->
    let step (x:expr) : Lemma (L.rev (x :: acc) == L.rev acc @ [x]) = LP.rev_append [x] acc in
    if i = p then (
      lemma_pulled_children n p b rest (i + 1) (b :: acc);
      step b;
      match pulled_list n p b rest (i + 1) with
      | Some ys -> LP.append_assoc (L.rev acc) [b] ys
      | None -> ())
    else (match thin [] 0 n 0 c with
          | Some c' ->
            lemma_pulled_children n p b rest (i + 1) (c' :: acc);
            step c';
            (match pulled_list n p b rest (i + 1) with
             | Some ys -> LP.append_assoc (L.rev acc) [c'] ys
             | None -> ())
          | None -> ())

let rec lemma_fold_remove_op (t:expr -> GTot bool) (op:B.nary_op{op = B.And \/ op = B.Or}) (xs:list expr)
                          (k:nat{k < L.length xs})
  : Lemma (ensures fold_truth t op xs == B.combine op (t (L.index xs k)) (fold_truth t op (remove_at k xs)))
          (decreases xs) =
  match xs with
  | _ :: rest -> if k > 0 then lemma_fold_remove_op t op rest (k - 1)

(* The value of a child lifted over the pulled binders, at an extension of
   the environment, is its value at the environment. *)
let lemma_lifted (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                 (scope ss:list sort) (rho:V.environment base sigma scope) (vs:V.arguments base sigma ss)
                 (c c':expr)
  : Lemma (requires D.scoped scope c /\ D.scoped (ss @ scope) c' /\ thin [] 0 (L.length ss) 0 c == Some c')
          (ensures (V.evaluate sigma i scope rho c <: V.tree base) ==
                   (V.evaluate sigma i (ss @ scope) (V.extend sigma scope ss vs rho) c' <: V.tree base)) =
  LP.append_length ss scope;
  let at (p:nat{p < L.length scope})
    : Lemma (related_at sigma [] 0 (L.length ss) 0 scope (ss @ scope) rho (V.extend sigma scope ss vs rho) p) =
    DS.lemma_extend_index sigma scope ss vs rho (p + L.length ss) in
  FStar.Classical.forall_intro at;
  lemma_thin_eval sigma i [] 0 (L.length ss) 0 scope (ss @ scope) rho (V.extend sigma scope ss vs rho) c c'

(* The folded truth of the pulled children at an extension: the pulled body
   combined with the other children at the environment. *)
let rec lemma_fold_pulled (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                          (scope ss:list sort) (rho:V.environment base (S.signature s) scope)
                          (vs:V.arguments base (S.signature s) ss)
                          (op:B.nary_op{op = B.And \/ op = B.Or}) (p:nat) (b:expr) (cs cs':list expr) (i:nat)
  : Lemma (requires i <= p /\ p - i < L.length cs /\
                    D.scoped_args scope (remove_at (p - i) cs) /\ D.scoped_args (ss @ scope) cs' /\
                    pulled_list (L.length ss) p b cs i == Some cs')
          (ensures fold_truth (T.truth_at s bc eq other (ss @ scope) (V.extend (S.signature s) scope ss vs rho)) op cs' ==
                   B.combine op (T.truth_at s bc eq other (ss @ scope) (V.extend (S.signature s) scope ss vs rho) b)
                     (fold_truth (T.truth_at s bc eq other scope rho) op (remove_at (p - i) cs)))
          (decreases cs) =
  match cs, cs' with
  | c :: rest, c' :: rest' ->
    if i = p then lemma_fold_lifted s bc eq other scope ss rho vs op p b rest rest' (i + 1)
    else (
      lemma_lifted (S.signature s) (T.interpretation s bc eq other) scope ss rho vs c c';
      lemma_fold_pulled s bc eq other scope ss rho vs op p b rest rest' (i + 1))
  | _, _ -> ()

and lemma_fold_lifted (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                      (scope ss:list sort) (rho:V.environment base (S.signature s) scope)
                      (vs:V.arguments base (S.signature s) ss)
                      (op:B.nary_op{op = B.And \/ op = B.Or}) (p:nat) (b:expr) (cs cs':list expr) (i:nat)
  : Lemma (requires D.scoped_args scope cs /\ D.scoped_args (ss @ scope) cs' /\
                    pulled_list (L.length ss) p b cs i == Some cs' /\ p < i)
          (ensures fold_truth (T.truth_at s bc eq other (ss @ scope) (V.extend (S.signature s) scope ss vs rho)) op cs' ==
                   fold_truth (T.truth_at s bc eq other scope rho) op cs)
          (decreases cs) =
  match cs, cs' with
  | c :: rest, c' :: rest' ->
    lemma_lifted (S.signature s) (T.interpretation s bc eq other) scope ss rho vs c c';
    lemma_fold_lifted s bc eq other scope ss rho vs op p b rest rest' (i + 1)
  | _, _ -> ()

let rec lemma_remove_scoped_args (scope:list sort) (xs:list expr) (k:nat)
  : Lemma (requires D.scoped_args scope xs) (ensures D.scoped_args scope (remove_at k xs)) (decreases xs) =
  match xs with [] -> () | _ :: rest -> if k > 0 then lemma_remove_scoped_args scope rest (k - 1)

let rec lemma_child_at (xs:list expr) (p:nat) (x:expr)
  : Lemma (requires child_at xs p == Some x) (ensures p < L.length xs /\ L.index xs p == x) (decreases xs) =
  match xs with _ :: rest -> if p > 0 then lemma_child_at rest (p - 1) x

(* pull-quant at ANY scope where both sides are typed, at ANY typed
   environment: (op c1 .. (Q bs. b) .. cn) and (Q bs. (op c1' .. b .. cn'))
   have one truth. For forall under `and` and exists under `or` the pulled
   binders range over carriers the interpretation inhabits. *)
let lemma_pulled_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                    (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                    (scope:list sort) (rho:V.environment base (S.signature s) scope) (e q:expr)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    pulled e q /\ D.scoped scope e /\ D.scoped scope q)
          (ensures same_at s bc eq other scope rho e q) =
  match e, q with
  | App f cs, Quantifier k bs _ (App _ cs') ->
    let sigma = S.signature s in
    let op : (op:B.nary_op{op = B.And \/ op = B.Or}) = if T.classify f = T.Nary B.Or then B.Or else B.And in
    let p = Some?.v (single_quantified cs 0 None) in
    let child = Some?.v (child_at cs p) in
    lemma_child_at cs p child;
    let b = Quantifier?.body child in
    let ss = L.rev bs in
    let n = L.length bs in
    LP.rev_length bs;
    lemma_pulled_children n p b cs 0 [];
    assert (pulled_list n p b cs 0 == Some cs');
    assert (D.scoped_args scope cs);
    lemma_remove_scoped_args scope cs p;
    lemma_index_scoped scope cs p;
    assert (D.scoped (ss @ scope) b);
    assert (D.scoped (ss @ scope) (App f cs'));
    lemma_truth_nary s bc eq other scope rho f cs op;
    lemma_fold_atoms (T.truth_at s bc eq other scope rho) op cs;
    lemma_fold_remove_op (T.truth_at s bc eq other scope rho) op cs p;
    let r = fold_truth (T.truth_at s bc eq other scope rho) op (remove_at p cs) in
    let ext (vs:V.arguments base sigma ss) : V.environment base sigma (ss @ scope) = V.extend sigma scope ss vs rho in
    let pointwise (vs:V.arguments base sigma ss)
      : Lemma (T.truth_at s bc eq other (ss @ scope) (ext vs) (App f cs') ==
               B.combine op (T.truth_at s bc eq other (ss @ scope) (ext vs) b) r) =
      lemma_truth_nary s bc eq other (ss @ scope) (ext vs) f cs' op;
      lemma_fold_atoms (T.truth_at s bc eq other (ss @ scope) (ext vs)) op cs';
      lemma_fold_pulled s bc eq other scope ss rho vs op p b cs cs' 0 in
    FStar.Classical.forall_intro pointwise;
    let vs0 = merge sigma (inhabitant_of s other) [] ss [] in
    pointwise vs0;
    (match k with
     | Forall_k ->
       Q.lemma_forall_truth s bc eq other scope rho bs b;
       Q.lemma_forall_truth s bc eq other scope rho bs (App f cs')
     | _ ->
       lemma_exists_truth s bc eq other scope rho bs b;
       lemma_exists_truth s bc eq other scope rho bs (App f cs'));
    lemma_same_truth s bc eq other scope rho e q
  | _, _ -> ()

(* The nested forall flattened (pull_quant::pull_quant1_core over a forall
   body; Z3SortedQuantifier.flatten) at ANY scope and ANY typed environment:
   Z3SortedQuantifier.lemma_flatten at the scope [] generalized. *)
let lemma_flatten_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                     (scope:list sort) (rho:V.environment base (S.signature s) scope) (a b:expr)
  : Lemma (requires Q.forall_model s bc other /\ D.scoped scope a /\ D.scoped scope b /\ Q.flatten a b)
          (ensures same_at s bc eq other scope rho a b) =
  match a, b with
  | Quantifier Forall_k outer _ (Quantifier Forall_k inner _ body),
    Quantifier Forall_k _ _ _ ->
    let sigma = S.signature s in
    let xs = L.rev inner in
    let ys = L.rev outer in
    LP.rev_append outer inner;
    LP.append_assoc xs ys scope;
    Q.lemma_forall_truth s bc eq other scope rho outer (Quantifier Forall_k inner bool_sort body);
    Q.lemma_forall_truth s bc eq other scope rho (outer @ inner) body;
    let outside (ws:V.arguments base sigma ys)
      : Lemma (T.truth_at s bc eq other (ys @ scope) (V.extend sigma scope ys ws rho)
                 (Quantifier Forall_k inner bool_sort body) <==>
               (forall (vs:V.arguments base sigma xs).
                 T.truth_at s bc eq other ((xs @ ys) @ scope)
                   (V.extend sigma scope (xs @ ys) (Q.append_arguments sigma xs ys vs ws) rho) body)) =
      Q.lemma_forall_truth s bc eq other (ys @ scope) (V.extend sigma scope ys ws rho) inner body;
      let inside (vs:V.arguments base sigma xs)
        : Lemma (T.truth_at s bc eq other ((xs @ ys) @ scope)
                   (V.extend sigma scope (xs @ ys) (Q.append_arguments sigma xs ys vs ws) rho) body ==
                 T.truth_at s bc eq other (xs @ (ys @ scope))
                   (V.extend sigma (ys @ scope) xs vs (V.extend sigma scope ys ws rho)) body) =
        let indices (n:nat{n < L.length ((xs @ ys) @ scope)})
          : Lemma (V.extend sigma scope (xs @ ys) (Q.append_arguments sigma xs ys vs ws) rho n ==
                   V.extend sigma (ys @ scope) xs vs (V.extend sigma scope ys ws rho) n) =
          Q.lemma_extend_append sigma scope xs ys vs ws rho n in
        FStar.Classical.forall_intro indices;
        Q.lemma_free_environments sigma (T.interpretation s bc eq other) ((xs @ ys) @ scope)
          (V.extend sigma scope (xs @ ys) (Q.append_arguments sigma xs ys vs ws) rho)
          (V.extend sigma (ys @ scope) xs vs (V.extend sigma scope ys ws rho)) body in
      FStar.Classical.forall_intro inside in
    FStar.Classical.forall_intro outside;
    let forward (_:squash (T.truth_at s bc eq other scope rho a))
      : Lemma (T.truth_at s bc eq other scope rho b) =
      let combined (vs:V.arguments base sigma (xs @ ys))
        : Lemma (T.truth_at s bc eq other ((xs @ ys) @ scope) (V.extend sigma scope (xs @ ys) vs rho) body) =
        let left, right = Q.split_arguments sigma xs ys vs in
        outside right in
      FStar.Classical.forall_intro combined in
    FStar.Classical.impl_intro forward;
    let backward (_:squash (T.truth_at s bc eq other scope rho b))
      : Lemma (T.truth_at s bc eq other scope rho a) =
      let outside' (ws:V.arguments base sigma ys)
        : Lemma (T.truth_at s bc eq other (ys @ scope) (V.extend sigma scope ys ws rho)
                   (Quantifier Forall_k inner bool_sort body)) =
        let inside' (vs:V.arguments base sigma xs)
          : Lemma (T.truth_at s bc eq other ((xs @ ys) @ scope)
                     (V.extend sigma scope (xs @ ys) (Q.append_arguments sigma xs ys vs ws) rho) body) =
          () in
        FStar.Classical.forall_intro inside';
        outside ws in
      FStar.Classical.forall_intro outside' in
    FStar.Classical.impl_intro backward;
    lemma_same_truth s bc eq other scope rho a b
  | _, _ -> ()

(* A pull-quant entry at ANY scope where both sides are typed, at ANY typed
   environment of it. *)
let lemma_pull_ok_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                     (scope:list sort) (rho:V.environment base (S.signature s) scope) (e q:expr)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    pull_ok e q /\ D.scoped scope e /\ D.scoped scope q)
          (ensures same_at s bc eq other scope rho e q) =
  if pulled e q then lemma_pulled_at s bc eq other scope rho e q
  else lemma_flatten_at s bc eq other scope rho e q

(* A rewrite leaf at ANY scope where both sides are typed, at ANY typed
   environment of it: rewrite_ok reads no environment. The Int equivalence
   is Z3SortedArithmetic.lemma_equivalent at that scope; the ITE laws are
   lemma_ite_rewritten_at; the Int factor permutation is
   lemma_product_permuted_at; the regrouping is lemma_regrouped_at; the
   propositional equivalences are lemma_propositional_at. *)
let lemma_rewrite_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                     (scope:list sort) (rho:V.environment base (S.signature s) scope) (lhs rhs:expr)
  : Lemma (requires rewrite_ok lhs rhs /\ D.scoped scope lhs /\ D.scoped scope rhs)
          (ensures same_at s bc eq other scope rho lhs rhs) =
  if AR.equivalent lhs rhs then (
    AR.lemma_equivalent s bc eq other scope rho lhs rhs;
    lemma_same_at s bc eq other scope rho lhs rhs)
  else if ite_rewritten lhs rhs then lemma_ite_rewritten_at s bc eq other scope rho lhs rhs
  else if product_permuted lhs rhs then lemma_product_permuted_at s bc eq other scope rho lhs rhs
  else if regrouped lhs rhs then lemma_regrouped_at s bc eq other scope rho lhs rhs
  else if propositional_at 64 lhs rhs then lemma_propositional_at s bc eq other scope rho 64 lhs rhs
  else lemma_propositional_at s bc eq other scope rho 2 lhs rhs

(* A gated Real leaf: both sides have one value at every typed environment of
   every Sorted model that satisfies the Real laws (RL.real_model, which
   contains the schema gate RL.real_primitive itself). The flag alone proves
   nothing: with real = true the hypothesis is the Real laws. *)
let lemma_real_rewrite_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                          (real:bool) (scope:list sort) (rho:V.environment base (S.signature s) scope)
                          (lhs rhs:expr)
  : Lemma (requires real_rewrite_ok real lhs rhs /\ (real ==> RL.real_model s bc eq other) /\
                    D.scoped scope lhs /\ D.scoped scope rhs)
          (ensures same_at s bc eq other scope rho lhs rhs) =
  if rewrite_ok lhs rhs then lemma_rewrite_at s bc eq other scope rho lhs rhs
  else (
    FStar.Classical.exists_elim
      (T.evaluate_at s bc eq other scope rho lhs == T.evaluate_at s bc eq other scope rho rhs)
      #(RL.carrier base) #(fun reals -> RL.real_laws s bc eq other reals) ()
      (fun reals -> LIN.lemma_real_equivalent s bc eq other reals scope rho lhs rhs);
    lemma_same_at s bc eq other scope rho lhs rhs)

(* ---------------------------------------------------------------------- *)
(* 6. One entry at one assigned scope                                       *)
(* ---------------------------------------------------------------------- *)

let lemma_entry_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                   (real:bool) (scoped:bool) (assertions:list expr) (e:U.binder_entry) (j:U.judgment)
                   (facts:list U.judgment)
                   (scope:list sort) (rho:V.environment base (S.signature s) scope)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    (real ==> RL.real_model s bc eq other) /\
                    T.truths s bc eq other assertions /\
                    entry_ok real scoped assertions e j facts /\ BS.binder_judgment_scoped scope j /\
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
    else if name = "quant-intro" then (
      match e.U.binder_sorts with
      | Some bs -> lemma_quantifier_ok s bc eq other scope rho true bs lhs rhs facts
      | None -> ())
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
      else if name = "rewrite" then lemma_real_rewrite_at s bc eq other real scope rho lhs rhs
      else if name = "elim-unused" then lemma_unused_eliminated_at s bc eq other scope rho lhs rhs
      else if name = "der" then lemma_der_at s bc eq other scope rho lhs rhs
      else if name = "pull-quant" then lemma_pull_ok_at s bc eq other scope rho lhs rhs
      else if L.mem (R.mk_eq_expr lhs rhs) assertions then
        lemma_assertion_edge s bc eq other assertions scope rho lhs rhs
      else (
        let cb = Some?.v (find_closure lhs rhs assertions) in
        lemma_find_closure lhs rhs assertions cb;
        lemma_closure_edge s bc eq other assertions scope rho lhs rhs cb))

let lemma_entry_valid (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                      (real:bool) (scoped:bool) (assertions:list expr) (e:U.binder_entry) (j:U.judgment)
                      (facts:list U.judgment)
                      (scope:list sort)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    (real ==> RL.real_model s bc eq other) /\
                    T.truths s bc eq other assertions /\
                    entry_ok real scoped assertions e j facts /\ BS.binder_judgment_scoped scope j /\
                    all_valid s bc eq other (BS.premise_scope_of e scope) facts)
          (ensures valid s bc eq other scope j) =
  let at (rho:V.environment base (S.signature s) scope) : Lemma (holds_at s bc eq other scope rho j) =
    lemma_entry_at s bc eq other real scoped assertions e j facts scope rho in
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
               (real:bool) (scoped:bool) (assertions:list expr) (t:U.scope_demands)
               (cache:I.index_tree U.judgment)
               (k:nat) (e:U.binder_entry) (j:U.judgment) (facts:list U.judgment)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    (real ==> RL.real_model s bc eq other) /\
                    T.truths s bc eq other assertions /\
                    I.index_find cache k == Some j /\
                    I.opt_map (I.index_find cache) e.U.binder_premises == Some facts /\
                    entry_ok real scoped assertions e j facts /\
                    BS.entry_scoped t k e j (U.scope_demanded t k) /\
                    prefix_valid s bc eq other t cache k)
          (ensures entry_valid s bc eq other t cache k) =
  let here (sc:list sort)
    : Lemma (requires L.memP sc (U.scope_demanded t k))
            (ensures valid s bc eq other sc j) =
    BS.lemma_entry_scoped t k e j (U.scope_demanded t k) sc;
    lemma_premises s bc eq other t cache k e.U.binder_premises facts (BS.premise_scope_of e sc);
    lemma_entry_valid s bc eq other real scoped assertions e j facts sc in
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
                    (real:bool) (scoped:bool) (assertions:list expr) (count:nat) (t:U.scope_demands)
                    (cache:I.index_tree U.judgment)
                    (sizes:I.index_tree nat) (k:nat) (entries:list U.binder_entry) (work:nat)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    (real ==> RL.real_model s bc eq other) /\
                    T.truths s bc eq other assertions /\
                    steps_ok real scoped assertions count t cache sizes k entries work /\
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
      lemma_steps s bc eq other real scoped assertions count t cache sizes (k + 1) rest work)
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
            lemma_step s bc eq other real scoped assertions t cache k e j facts;
            lemma_prefix_extend s bc eq other t cache k;
            lemma_steps s bc eq other real scoped assertions count t cache (I.index_put sizes k size) (k + 1) rest w
          | _, _, _ -> ()))

(* ---------------------------------------------------------------------- *)
(* 8. The theorem                                                           *)
(* ---------------------------------------------------------------------- *)

(* A replayed certificate's conclusion is scoped at `[]` and holds in the
   Sorted model `other` over (bc, eq), given the universal and existential
   quantifier laws of `other` and the truth of the assertions it reads
   (only `sk` steps read them). For an NNF and a quant-intro root alike:
   every used entry, at every scope the guard assigns it, holds at every
   typed environment of that scope (prefix_valid), derived from its local
   check and its premises at their own assigned scopes only. *)
let lemma_replay_with (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                      (real:bool) (assertions:list expr) (c:U.binder_certificate) (concl:U.judgment)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    (real ==> RL.real_model s bc eq other) /\
                    T.truths s bc eq other assertions /\ replay_with real assertions c concl == Replayed)
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
       lemma_steps s bc eq other real (quant_intro_root c) assertions (U.count_cells 0 assertions) t cache I.Empty 0
         entries (U.binder_work_limit n);
       let key : nat = root in
       assert (entry_valid s bc eq other t cache key);
       lemma_entry_valid_def s bc eq other t cache key;
       BS.lemma_scoped_at t cache entries key [])

(* The ungated replay: the quantifier laws alone. *)
let lemma_replay (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                 (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                 (assertions:list expr) (c:U.binder_certificate) (concl:U.judgment)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    T.truths s bc eq other assertions /\ replay assertions c concl == Replayed)
          (ensures BS.binder_judgment_scoped [] concl /\
                   holds_at s bc eq other [] (T.empty_environment (S.signature s)) concl) =
  lemma_replay_with s bc eq other false assertions c concl
