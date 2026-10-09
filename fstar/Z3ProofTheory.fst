(*
   Z3ProofTheory.fst

   F* formalization of the core equality-proof calculus used by
   src/ast/ast.h / src/ast/ast.cpp's proof-term constructors, and in
   particular of the fragment of that calculus actually exercised by
   src/ast/rewriter/rewriter_def.h (the generic bottom-up rewriting
   engine shared by every Z3 rewriter: `bool_rewriter`, `arith_rewriter`,
   `bv_rewriter`, `seq_rewriter`, `th_rewriter`, etc.).

   Ground truth / correspondence:

     - Proof *kinds*: `src/ast/ast.h`'s `basic_op_kind` enum (`PR_*`
       constants). This file models exactly the five kinds that
       `rewriter_def.h` ever constructs: `PR_REFLEXIVITY`,
       `PR_SYMMETRY`, `PR_TRANSITIVITY`, `PR_MONOTONICITY` (always
       reached here via the `mk_congruence` wrapper around
       `mk_monotonicity` with `R = (= : s -> s -> Bool)`), and
       `PR_REWRITE` (the "trusted leaf": every individual
       rewriter-plugin's `reduce_app`/`BR_DONE` callback is required
       to supply either its own proof object or fall back to
       `m().mk_rewrite(t0, m_r)`, so every leaf ultimately bottoms out
       at a `PR_REWRITE` node whose soundness is established
       separately, by each plugin's own rewrite-correctness audit --
       e.g. `BOOL_REWRITER_REPORT.md`, `ARITH_REWRITER_REPORT.md`,
       `BV_REWRITER_REPORT.md`, `SEQ_REWRITE_REPORT.md`, etc.), plus a
       sixth, compound shape, `QuantIntro`, modeling `PR_BIND`
       composed with `PR_QUANT_INTRO` exactly as
       `rewriter_tpl::process_quantifier` builds them together
       (`mk_quant_intro(q, new_q, mk_bind_proof(q, m_pr))`) for
       rewrites that fire underneath a binder. Z3's own
       `proof_checker::check1_basic` accepts this real (lambda-
       wrapped) shape *unconditionally*, as a second, distinct kind of
       trusted leaf alongside `PR_REWRITE` (see `QuantIntro`'s
       docstring below); this file instead *derives* its soundness
       from the wrapped child proof's own soundness, rather than
       trusting it blindly.

     - *Well-formedness semantics* for each kind: `src/ast/proofs/
       proof_checker.cpp`'s `proof_checker::check1_basic`, the
       authoritative executable specification of what makes a
       `PR_REFLEXIVITY`/`PR_SYMMETRY`/`PR_TRANSITIVITY`/
       `PR_MONOTONICITY`/`PR_REWRITE` node well-formed (this is Z3's
       own internal proof checker, used to self-validate generated
       proofs; it is not merely documentation but the ground-truth
       oracle this file's `fact`/`wf` judgment is designed to agree
       with). In particular `PR_MONOTONICITY`'s case there
       (`terms1.size() == terms2.size()` and, for every index `i`
       where `term1 <> term2`, a premise proof of exactly `term1 =
       term2` must be found *somewhere* among the supplied premises,
       not necessarily at position `i`) is mirrored exactly by this
       file's `congr_matched`/`find_matching_proof`.

     - The *smart constructors* `ast_manager::mk_reflexivity`/
       `mk_symmetry`/`mk_transitivity`/`mk_congruence`
       (`mk_monotonicity`)/`mk_rewrite` in `src/ast/ast.cpp`: these
       are the only way `rewriter_def.h` ever builds a `proof*`, and
       this file's `mk_refl`/`mk_sym`/`mk_trans`/`mk_congr`/
       `mk_rewrite_leaf` reproduce their exact logic (including
       `mk_transitivity`'s double-negation "fixup" special case and
       `mk_symmetry`'s reflexivity/symmetry-of-symmetry
       short-circuits), so that proving these smart constructors
       always produce a well-formed result directly transfers to
       every call site in `rewriter_def.h` (which never constructs a
       raw `PR_*` node itself).

   Terms (`expr`) and their denotational semantics (`interpretation`/
   `eval`) are reused unchanged from `Z3AstTheory.fst`; this file adds
   only proof terms and their well-formedness/soundness on top.
*)
module Z3ProofTheory

open Z3AstTheory

(* ----------------------------------------------------------------- *)
(* The `not` connective, recognized structurally                      *)
(* ----------------------------------------------------------------- *)

(* `mk_transitivity`'s double-negation fixup (see below) needs to
   recognize `(not (not e))`; `not` itself is just an ordinary
   (always-interpreted) unary `func_decl`, identified here by its
   `decl_name` exactly as `ast_manager::is_not` identifies it by
   `m_basic_fid`/`OP_NOT` in the real code (both are "look at the
   declaration's identity", just with a cheaper stand-in for identity
   here, consistent with `Z3AstTheory.fst`'s own `sort_eq`/name-based
   style). *)
let is_not (e:expr) : option expr =
  match e with
  | App f [a] -> if f.decl_name = "not" then Some a else None
  | _ -> None

let is_not_not (e:expr) : option expr =
  match is_not e with
  | Some a -> is_not a
  | None -> None

(* ----------------------------------------------------------------- *)
(* Proof terms: the fragment of `basic_op_kind` built by               *)
(* rewriter_def.h                                                      *)
(* ----------------------------------------------------------------- *)

(* A `proof` always concludes an equation between two `expr`s (every
   fact `rewriter_def.h` ever builds is an `eq`, via `ast_manager::
   mk_eq`; the `oeq`-flavored smart constructors `mk_oeq_*` are never
   called from `rewriter_def.h`, only their plain `eq` counterparts,
   so `oeq` is out of scope for this file -- see
   PROOF_REWRITER_REPORT.md). *)
(* `QuantIntro qk bound_sorts p` models the compound shape
   `rewriter_tpl::process_quantifier` actually builds --
   `mk_quant_intro(q1, q2, mk_bind_proof(q1, p))` -- as a single
   constructor rather than two (see "PR_BIND/PR_QUANT_INTRO" below for
   why `PR_BIND`'s own lambda-reification wrapper needs no separate
   node here). `p`'s fact is the equation between the two quantifiers'
   literal (still-bound, de-Bruijn-indexed) *bodies*; `QuantIntro`'s
   own fact is the corresponding equation between the two whole
   quantifiers, same `qk`/`bound_sorts` on both sides (exactly what
   `rewriter_def.h` ever constructs: `q`/`new_q` always agree on kind
   and bound sorts, differing only in body/patterns). *)
type proof =
  | Refl    : e:expr -> proof
  | Sym     : p:proof -> proof
  | Trans   : p1:proof -> p2:proof -> proof
  | Congr   : f:func_decl -> args1:list expr -> args2:list expr -> prfs:list proof -> proof
  | Rewrite : s:expr -> t:expr -> proof
  | QuantIntro : qk:quantifier_kind -> bound_sorts:list sort -> p:proof -> proof

(* ----------------------------------------------------------------- *)
(* `fact`: well-formedness + conclusion extraction, mirroring          *)
(* `proof_checker::check1_basic`                                       *)
(* ----------------------------------------------------------------- *)

(* `fact p = Some (a, b)` means `p` is well-formed (`check1_basic`
   would accept it) and its conclusion is the equation `a = b`;
   `fact p = None` means `p` is ill-formed (not producible by any of
   this file's smart constructors from well-formed inputs -- see the
   soundness theorems below).

   The only genuinely mutually-recursive pair here is `fact`/
   `facts_of` (exactly the same "function on a node, function on a
   list of children" shape as `Z3AstTheory.fst`'s `eval`/`eval_args`);
   `facts_of` precomputes the list of (optional) facts of a `Congr`
   node's premises once, so that the position-independent search
   `congr_matched`/`find_matching_fact` (defined first, below, since
   `fact` calls them) can be plain, non-mutual recursion over that
   already-computed `list (option (expr & expr))` -- avoiding a 3-way
   mutual-recursion cycle across unrelated list-length metrics
   (`list expr` vs. `list proof`) that F*'s termination checker cannot
   relate automatically. *)

(* `PR_MONOTONICITY`'s acceptance condition: pointwise, either the two
   argument lists already agree at this position (no premise needed --
   the semantic counterpart of `rewriter_core::elim_reflex_prs`
   dropping implicit-reflexivity child proofs before `mk_congruence`
   is ever called), or *some* supplied premise proves exactly this
   position's equation (found by content, not by position -- matching
   `check1_basic`'s own linear search `for (proof* pr : proofs) found
   |= ...`). Both operate on an already-computed
   `list (option (expr & expr))` (the facts of a `Congr` node's
   premises, see `facts_of` below), so neither needs to call back into
   `fact` and both are plain (non-mutual) structural recursions. *)
let rec find_matching_fact (a1 a2:expr) (fs:list (option (expr & expr))) : bool =
  match fs with
  | [] -> false
  | Some (x, y) :: fs' -> (x = a1 && y = a2) || find_matching_fact a1 a2 fs'
  | None :: fs' -> find_matching_fact a1 a2 fs'

let rec congr_matched (args1 args2:list expr) (fs:list (option (expr & expr))) : bool =
  match args1, args2 with
  | [], [] -> true
  | a1 :: args1', a2 :: args2' ->
    (a1 = a2 || find_matching_fact a1 a2 fs) && congr_matched args1' args2' fs
  | _, _ -> false

let rec fact (p:proof) : Tot (option (expr & expr)) (decreases p) =
  match p with
  | Refl e -> Some (e, e)
  | Sym p1 ->
    (match fact p1 with
     | Some (a, b) -> Some (b, a)
     | None -> None)
  | Trans p1 p2 ->
    (match fact p1, fact p2 with
     | Some (a, b), Some (c, d) -> if b = c then Some (a, d) else None
     | _, _ -> None)
  | Congr f args1 args2 prfs ->
    if List.Tot.length args1 = List.Tot.length args2
       && congr_matched args1 args2 (facts_of prfs)
    then Some (App f args1, App f args2)
    else None
  | Rewrite s t -> Some (s, t)
  | QuantIntro qk bound_sorts p1 ->
    (match fact p1 with
     | Some (body1, body2) -> Some (Quantifier qk bound_sorts body1, Quantifier qk bound_sorts body2)
     | None -> None)

and facts_of (prfs:list proof) : Tot (list (option (expr & expr))) (decreases prfs) =
  match prfs with
  | [] -> []
  | p :: prfs' -> fact p :: facts_of prfs'

(* ----------------------------------------------------------------- *)
(* Smart constructors, mirroring `ast_manager::mk_*` in ast.cpp         *)
(* ----------------------------------------------------------------- *)

(* `ast_manager::mk_reflexivity`: always well-formed, by construction. *)
let mk_refl (e:expr) : proof = Refl e

(* `ast_manager::mk_symmetry`. The real code short-circuits two cases
   (`is_reflexivity(p)` returns `p` unchanged; `is_symmetry(p)` unwraps
   to the original parent) purely as allocation-saving optimizations:
   both results are semantically identical to always wrapping in
   `PR_SYMMETRY`, since `Refl e`'s symmetric fact is itself
   (`lemma_mk_sym_refl` below) and `Sym`'s own symmetric fact is its
   argument's original fact (`lemma_mk_sym_sym` below). This file
   models the always-wrap behavior (`Sym p`); the two optimized paths
   are proved equivalent corollaries rather than separate constructor
   cases, since `rewriter_def.h` only ever consumes the *fact*
   `mk_symmetry` establishes, never its internal shape. *)
let mk_sym (p:proof) : proof = Sym p

(* `ast_manager::mk_transitivity` (two-proof form), including the
   double-negation "fixup": when the two middle terms are not
   literally equal but are related by `b = not(not(c))` (or
   symmetrically `c = not(not(b))`), the real code bridges the gap
   with an extra `mk_rewrite(b, c)` step before chaining -- this is
   exactly one more `PR_REWRITE` leaf, whose soundness (double-negation
   elimination is a valid rewrite under any Boolean interpretation) is
   discharged the same way every other `PR_REWRITE` leaf is: by the
   caller-side `all_leaves_sound` hypothesis in the soundness theorem
   below, not by an unconditional axiom in this file. If neither the
   terms match nor the double-negation bridge applies, the real code's
   `SASSERT(fact1->get_arg(1) == fact2->get_arg(0))` would fail --
   modeled here by returning a `Trans` node whose `fact` degrades to
   `None` (ill-formed), never asserted/relied upon by the soundness
   theorem. *)
let mk_trans (p1 p2:proof) : proof =
  match fact p1, fact p2 with
  | Some (_, b), Some (c, _) ->
    if b = c then Trans p1 p2
    else if is_not_not b = Some c then Trans (Trans p1 (Rewrite b c)) p2
    else if is_not_not c = Some b then Trans (Trans p1 (Rewrite b c)) p2
    else Trans p1 p2
  | _, _ -> Trans p1 p2

(* `ast_manager::mk_congruence`/`mk_monotonicity`, specialized to the
   `R = eq` case (the only one `rewriter_def.h` ever calls: always
   `mk_congruence`, never `mk_oeq_congruence`). `f1`/`f2` are
   `App f args1`/`App f args2` by construction at every call site (the
   rewriter only ever rebuilds an application with the same head
   symbol `f` and arity, per `process_children`'s `new_t = m().mk_app
   (f, ...)`), so this smart constructor is parameterized directly by
   `f`, `args1`, `args2` rather than by two already-built `App` nodes. *)
let mk_congr (f:func_decl) (args1 args2:list expr) (prfs:list proof) : proof =
  Congr f args1 args2 prfs

(* `ast_manager::mk_rewrite`: always well-formed, by construction; its
   soundness (`eval i s rho == eval i t rho`) is exactly what every
   rewriter plugin's own correctness report (`BOOL_REWRITER_REPORT.md`,
   `SEQ_REWRITE_REPORT.md`, `BV_REWRITER_REPORT.md`, ...) separately
   establishes for the specific `(s, t)` pairs its `reduce_app`
   produces -- out of scope for this file, which only verifies the
   *proof-calculus* layer on top. *)
let mk_rewrite_leaf (s t:expr) : proof = Rewrite s t

(* `ast_manager::mk_bind_proof` + `ast_manager::mk_quant_intro`, taken
   together as the one compound shape `process_quantifier` ever
   builds. `mk_bind_proof(q, p)` itself constructs no new *semantic*
   content -- it only re-expresses `p` as a term (`mk_lambda(decls,
   p)`) so that `mk_quant_intro` can later be given a single `proof*`
   that packages "a proof, for each assignment of the bound
   variables" (this file does not model that intermediate
   lambda-term representation explicitly; see `QuantIntro`'s own
   docstring above for why one constructor suffices). `mk_quant_intro`
   itself only has a real `SASSERT` precondition
   (`q1->get_num_decls() == q2->get_num_decls()`, i.e. same arity/
   bound sorts), always satisfied at this call site since `q`/`new_q`
   are built by `update_quantifier` from the same `q`, never changing
   its bound-variable declarations -- modeled here by `bound_sorts`
   simply being shared between both sides of `fact`'s conclusion,
   rather than separately parameterized and equality-checked. *)
let mk_quant_intro (qk:quantifier_kind) (bound_sorts:list sort) (p:proof) : proof =
  QuantIntro qk bound_sorts p

(* ----------------------------------------------------------------- *)
(* Smart constructors are well-formed by construction                  *)
(* ----------------------------------------------------------------- *)

let lemma_mk_refl_wf (e:expr)
  : Lemma (fact (mk_refl e) == Some (e, e))
  = ()

let lemma_mk_sym_wf (p:proof) (a b:expr)
  : Lemma (requires fact p == Some (a, b))
          (ensures fact (mk_sym p) == Some (b, a))
  = ()

(* The two optimizations `ast_manager::mk_symmetry` actually performs
   (short-circuiting on `is_reflexivity`/`is_symmetry`) are sound:
   reflexivity is its own symmetric fact, and double-symmetry recovers
   the original fact, exactly the conclusions `mk_sym` would also
   reach via the general `Sym` wrapping (just via a different, more
   compact, proof shape). *)
let lemma_mk_sym_refl (e:expr)
  : Lemma (fact (mk_refl e) == fact (mk_sym (mk_refl e)))
  = ()

let lemma_mk_sym_sym (p:proof) (a b:expr)
  : Lemma (requires fact p == Some (a, b))
          (ensures fact (mk_sym (mk_sym p)) == Some (a, b))
  = ()

(* `mk_trans`'s direct case (no double-negation bridge needed). *)
let lemma_mk_trans_wf_direct (p1 p2:proof) (a b d:expr)
  : Lemma (requires fact p1 == Some (a, b) /\ fact p2 == Some (b, d))
          (ensures fact (mk_trans p1 p2) == Some (a, d))
  = ()

(* `mk_trans`'s double-negation-bridge case, first orientation
   (`b = not(not c)`). *)
let lemma_mk_trans_wf_bridge1 (p1 p2:proof) (a b c d:expr)
  : Lemma (requires fact p1 == Some (a, b) /\ fact p2 == Some (c, d) /\
                    ~(b == c) /\ is_not_not b == Some c)
          (ensures fact (mk_trans p1 p2) == Some (a, d))
  = ()

(* Second orientation (`c = not(not b)`). *)
let lemma_mk_trans_wf_bridge2 (p1 p2:proof) (a b c d:expr)
  : Lemma (requires fact p1 == Some (a, b) /\ fact p2 == Some (c, d) /\
                    ~(b == c) /\ None? (is_not_not b) /\ is_not_not c == Some b)
          (ensures fact (mk_trans p1 p2) == Some (a, d))
  = ()

(* `mk_congr`'s well-formedness is exactly `congr_matched`, spelled out
   as a reusable side condition (so call sites just need to discharge
   this one predicate, matching how `rewriter_def.h` always supplies
   premises for exactly the positions it changed and relies on
   `elim_reflex_prs`/positional unconcern for the rest). *)
let lemma_mk_congr_wf (f:func_decl) (args1 args2:list expr) (prfs:list proof)
  : Lemma (requires List.Tot.length args1 = List.Tot.length args2 /\
                    congr_matched args1 args2 (facts_of prfs))
          (ensures fact (mk_congr f args1 args2 prfs) == Some (App f args1, App f args2))
  = ()

let lemma_mk_rewrite_wf (s t:expr)
  : Lemma (fact (mk_rewrite_leaf s t) == Some (s, t))
  = ()

let lemma_mk_quant_intro_wf (qk:quantifier_kind) (bound_sorts:list sort) (p:proof) (body1 body2:expr)
  : Lemma (requires fact p == Some (body1, body2))
          (ensures fact (mk_quant_intro qk bound_sorts p) ==
                   Some (Quantifier qk bound_sorts body1, Quantifier qk bound_sorts body2))
  = ()

(* ----------------------------------------------------------------- *)
(* Semantics and soundness                                             *)
(* ----------------------------------------------------------------- *)

(* `all_leaves_sound i p` holds iff every `Rewrite` leaf reachable
   inside `p` denotes a semantically true equation under interpretation
   `i`, for every variable environment. This is exactly, and only, the
   obligation each rewriter plugin's own correctness report discharges
   for the specific `(s, t)` pairs it ever hands to `mk_rewrite`/
   `mk_rewrite_leaf` (this file does not re-derive those facts, it
   only shows that *if* every leaf is sound, the whole constructed
   proof tree's conclusion is too). *)
let rec all_leaves_sound (#value:Type) (i:interpretation value) (p:proof) : Tot prop (decreases p) =
  match p with
  | Refl _ -> True
  | Sym p1 -> all_leaves_sound i p1
  | Trans p1 p2 -> all_leaves_sound i p1 /\ all_leaves_sound i p2
  | Congr _ _ _ prfs -> all_leaves_sound_list i prfs
  | Rewrite s t -> (forall (rho:env value). eval i s rho == eval i t rho)
  | QuantIntro _ _ p1 -> all_leaves_sound i p1

and all_leaves_sound_list (#value:Type) (i:interpretation value) (prfs:list proof) : Tot prop (decreases prfs) =
  match prfs with
  | [] -> True
  | p :: prfs' -> all_leaves_sound i p /\ all_leaves_sound_list i prfs'

(* Size metrics used purely to justify termination of the mutually
   recursive soundness lemmas below (`lemma_proof_sound`/
   `lemma_congr_args_sound`/`lemma_find_matching_sound`): the true
   "descent" in that cycle is `lemma_find_matching_sound` locating a
   proof `p` strictly inside `prfs` and invoking `lemma_proof_sound`
   on it, which is strictly smaller by `proof_size` than the `Congr`
   node `prfs` came from; `congr_matched`/`find_matching_fact`'s own
   looping over `args1`/`prfs` in between does not itself shrink any
   proof, so plain structural `decreases p` is not expressive enough
   for the whole cycle and an explicit lexicographic measure is used
   instead (see the three lemmas' `decreases %[...]` clauses). *)
let rec proof_size (p:proof) : nat =
  match p with
  | Refl _ -> 1
  | Sym p1 -> 1 + proof_size p1
  | Trans p1 p2 -> 1 + proof_size p1 + proof_size p2
  | Congr _ _ _ prfs -> 1 + proof_list_size prfs
  | Rewrite _ _ -> 1
  | QuantIntro _ _ p1 -> 1 + proof_size p1

and proof_list_size (prfs:list proof) : nat =
  match prfs with
  | [] -> 0
  | p :: prfs' -> 1 + proof_size p + proof_list_size prfs'

(* The central soundness theorem: a well-formed proof tree all of
   whose `Rewrite` leaves are semantically sound denotes a true
   equation, for every variable environment. This is the F*
   counterpart of "the rewriter's `proof*` output, when it passes
   `proof_checker::check`, is a correct derivation" -- restricted to
   exactly the `PR_REFLEXIVITY`/`PR_SYMMETRY`/`PR_TRANSITIVITY`/
   `PR_MONOTONICITY`/`PR_REWRITE` fragment `rewriter_def.h` uses. *)
let rec lemma_proof_sound (#value:Type) (i:interpretation value) (p:proof) (rho:env value)
  : Lemma (requires Some? (fact p) /\ all_leaves_sound i p /\ quant_extensional i)
          (ensures (let Some (a, b) = fact p in eval i a rho == eval i b rho))
          (decreases %[proof_size p; 0])
  = match p with
    | Refl _ -> ()
    | Sym p1 -> lemma_proof_sound i p1 rho
    | Trans p1 p2 -> lemma_proof_sound i p1 rho; lemma_proof_sound i p2 rho
    | Congr f args1 args2 prfs -> lemma_congr_args_sound i args1 args2 prfs rho
    | Rewrite _ _ -> ()
    | QuantIntro qk bound_sorts p1 ->
      (* `p1`'s fact (recovered under `Some? (fact p)`'s refinement on
         `QuantIntro`, i.e. `fact p1 = Some (body1, body2)`) relates
         the two quantifiers' literal, still-bound bodies. Unlike the
         other cases, the obligation isn't "evaluate at `rho`" but
         "evaluate at every `rho` extended by an assignment of the
         bound variables" -- exactly `lemma_pr_quant_intro`'s premise
         in `Z3PreprocessingProofTheory.fst`, and discharged the same
         way: invoke `lemma_proof_sound` on `p1` itself, once per
         extended environment (sound to do, since `all_leaves_sound`
         is a property of the proof tree alone, not of which
         environment it's instantiated at), then close the
         `Quantifier` case of `eval` via `quant_extensional i`. *)
      let (body1, body2) = (match fact p1 with Some (b1, b2) -> (b1, b2)) in
      let aux (vs:list value{List.Tot.length vs = List.Tot.length bound_sorts})
        : Lemma (eval i body1 (shift vs rho) == eval i body2 (shift vs rho))
        = lemma_proof_sound i p1 (shift vs rho)
      in
      FStar.Classical.forall_intro aux

(* If `find_matching_fact` succeeds against `facts_of prfs`, the
   premise that established that fact is reachable inside `prfs` and
   (by `all_leaves_sound_list`, which holds of every proof reachable
   inside `prfs`) sound -- so the queried equation holds
   semantically. Unlike `find_matching_fact` itself (which only
   inspects the already-computed facts, not the proofs), this lemma
   needs to walk `prfs` and `facts_of prfs` in lockstep to recover
   *which* proof justified the match and invoke its own soundness. *)
and lemma_find_matching_sound (#value:Type) (i:interpretation value) (a1 a2:expr) (prfs:list proof) (rho:env value)
  : Lemma (requires find_matching_fact a1 a2 (facts_of prfs) /\ all_leaves_sound_list i prfs /\ quant_extensional i)
          (ensures eval i a1 rho == eval i a2 rho)
          (decreases %[proof_list_size prfs; 0])
  = match prfs with
    | [] -> ()
    | p :: prfs' ->
      (match fact p with
       | Some (x, y) ->
         if x = a1 && y = a2 then lemma_proof_sound i p rho
         else lemma_find_matching_sound i a1 a2 prfs' rho
       | None -> lemma_find_matching_sound i a1 a2 prfs' rho)

(* Pointwise lifting: if `congr_matched` holds (against `facts_of
   prfs`), every corresponding pair of arguments denotes the same
   value (either literally the same `expr`, or bridged by a sound
   matching premise), hence so does the whole list of per-argument
   denotations -- directly what `Congr`'s `fact` case of
   `lemma_proof_sound` needs, since `eval` of an `App` depends on its
   arguments' list of denotations only. *)
and lemma_congr_args_sound (#value:Type) (i:interpretation value) (args1 args2:list expr) (prfs:list proof) (rho:env value)
  : Lemma (requires congr_matched args1 args2 (facts_of prfs) /\ all_leaves_sound_list i prfs /\ quant_extensional i)
          (ensures eval_args i args1 rho == eval_args i args2 rho)
          (decreases %[proof_list_size prfs; List.Tot.length args1])
  = match args1, args2 with
    | [], [] -> ()
    | a1 :: args1', a2 :: args2' ->
      (if a1 = a2 then () else lemma_find_matching_sound i a1 a2 prfs rho);
      lemma_congr_args_sound i args1' args2' prfs rho

