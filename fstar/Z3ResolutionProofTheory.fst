(*
   Z3ResolutionProofTheory.fst

   A resolution/clausal proof-step layer sitting *above* the
   equational rewrite calculus already modeled by
   `Z3ProofTheory.fst`/`Z3PatternMatchedProofChecker.fst`. See
   `RESOLUTION_CHECKER_SCOPE.md` for the full rule inventory and
   tiering rationale.

   Ground truth for every rule's acceptance condition:
   `src/ast/proofs/proof_checker.cpp::check1_basic`'s
   `PR_UNIT_RESOLUTION` / `PR_AND_ELIM` / `PR_NOT_OR_ELIM` /
   `PR_MODUS_PONENS` / `PR_COMMUTATIVITY` / `PR_IFF_TRUE` /
   `PR_IFF_FALSE` cases.

   Two layers are provided:

   1. Standalone semantic lemmas (`lemma_clause_shrink`,
      `lemma_unit_resolution_sound`, `lemma_and_elim_sound`,
      `lemma_not_or_elim_sound`, `lemma_array_ext_sound`, ...): these
      state and prove the soundness of each rule directly in terms of
      `clause_holds`/`conj_holds`/`lit_true`, independent of any
      concrete proof-term data structure. They are the reusable
      mathematical content.

   2. `rproof`, a proof-term data structure (one level up from
      `Z3ProofTheory.proof`, the same way `Congr`/`Rewrite` sit above
      bare `interpretation`) with its own `rfact`/`all_rtrusted_sound`/
      `lemma_rproof_sound`, mirroring `Z3ProofTheory.fst`'s
      `fact`/`all_leaves_sound`/`lemma_proof_sound` exactly. This
      currently covers `PR_MODUS_PONENS`, `PR_AND_ELIM`,
      `PR_COMMUTATIVITY`, `PR_IFF_TRUE`/`PR_IFF_FALSE`, the equational
      calculus re-exposed as a Boolean `=`-fact (`REq`), unit
      resolution, hypothesis discharge, and explicit `Trusted` leaves.
*)
module Z3ResolutionProofTheory

open Z3AstTheory
open Z3ValueTheory
open Z3ProofTheory

(* ----------------------------------------------------------------- *)
(* Literals and clauses                                                *)
(* ----------------------------------------------------------------- *)

type literal = expr
type clause = list literal

let lit_true (i:interpretation value) (rho:env value) (l:literal) : prop =
  eval i l rho == VBool true

let lit_is_false (i:interpretation value) (rho:env value) (l:literal) : prop =
  eval i l rho == VBool false

let rec clause_holds (i:interpretation value) (rho:env value) (c:clause) : Tot prop (decreases c) =
  match c with
  | [] -> False
  | l :: c' -> lit_true i rho l \/ clause_holds i rho c'

let rec conj_holds (i:interpretation value) (rho:env value) (c:list expr) : Tot prop (decreases c) =
  match c with
  | [] -> True
  | l :: c' -> lit_true i rho l /\ conj_holds i rho c'

(* `src/ast/proofs/proof_checker.cpp`'s `m.is_complement`. *)
let complementary (l1 l2:literal) : bool =
  is_not l1 = Some l2 || is_not l2 = Some l1

(* ----------------------------------------------------------------- *)
(* Connective soundness hypotheses, explicit on `i` (same style as     *)
(* `Z3ProofTheory.fst`'s `quant_extensional`): these state that `i`     *)
(* interprets any func_decl literally named "not"/"and"/"or"/          *)
(* "implies"/"=" the standard way. Kept explicit rather than baked     *)
(* into `interpretation` so this file stays theory/wiring-agnostic.    *)
(* ----------------------------------------------------------------- *)

let not_sound (i:interpretation value) : prop =
  forall (f:func_decl) (a:expr) (rho:env value).
    {:pattern (eval i (App f [a]) rho)}
    f.decl_name == "not" ==>
    ((eval i (App f [a]) rho == VBool true) == (eval i a rho == VBool false))

let and_sound (i:interpretation value) : prop =
  forall (f:func_decl) (args:list expr) (rho:env value).
    {:pattern (eval i (App f args) rho)}
    f.decl_name == "and" ==>
    (eval i (App f args) rho == VBool true <==> conj_holds i rho args)

let or_sound (i:interpretation value) : prop =
  forall (f:func_decl) (args:list expr) (rho:env value).
    {:pattern (eval i (App f args) rho)}
    f.decl_name == "or" ==>
    (eval i (App f args) rho == VBool true <==> clause_holds i rho args)

let implies_sound (i:interpretation value) : prop =
  forall (f:func_decl) (a b:expr) (rho:env value).
    {:pattern (eval i (App f [a; b]) rho)}
    (f.decl_name == "implies" \/ f.decl_name == "=>") ==>
    (eval i (App f [a; b]) rho == VBool true <==> (lit_true i rho a ==> lit_true i rho b))

let eq_sound (i:interpretation value) : prop =
  forall (f:func_decl) (a b:expr) (rho:env value).
    {:pattern (eval i (App f [a; b]) rho)}
    f.decl_name == "=" ==>
    (eval i (App f [a; b]) rho == VBool true <==> eval i a rho == eval i b rho)

(* The nullary constants `true`/`false` (`op_true`/`op_false`, per
   `Z3InterpretedProofChecker.fst`'s `interp_true`/`interp_false`). *)
let true_sound (i:interpretation value) : prop =
  forall (f:func_decl) (rho:env value).
    {:pattern (eval i (App f []) rho)}
    f.decl_name == "true" ==> eval i (App f []) rho == VBool true

let false_sound (i:interpretation value) : prop =
  forall (f:func_decl) (rho:env value).
    {:pattern (eval i (App f []) rho)}
    f.decl_name == "false" ==> eval i (App f []) rho == VBool false

(* `not_sound`, specialized to a single `f`/`a`: instantiated with
   `a`'s own (known-`VBool`) value, it relates `(not a)`'s truth to
   `a`'s falsity in both directions (the forward direction is exactly
   `not_sound`'s own statement; the reverse follows since `VBool` is
   an injective constructor and `bool` has only two values, both
   decided automatically by Z3's native datatype theory). *)
let lemma_not_relates (i:interpretation value) (rho:env value) (f:func_decl) (a:expr)
  : Lemma (requires not_sound i /\ f.decl_name == "not" /\ VBool? (eval i a rho))
          (ensures (eval i (App f [a]) rho == VBool true) == (eval i a rho == VBool false))
  = ()

(* If two literals are complementary and one is true, the other is
   false -- provided `l2` is itself Bool-valued (`VBool? (eval i l2
   rho)`), the semantic counterpart of `l2` being a well-sorted
   literal (always the case for every real disjunct of a clause; kept
   as an explicit hypothesis here, same style as `wf`/`closed` are
   explicit side conditions elsewhere in this project, rather than
   baked into `interpretation` itself). *)
let lemma_complementary_sound (i:interpretation value) (rho:env value) (l1 l2:literal)
  : Lemma (requires not_sound i /\ complementary l1 l2 /\ lit_true i rho l1 /\
                    VBool? (eval i l2 rho))
          (ensures lit_is_false i rho l2)
  = match l1 with
    | App f [a] ->
      if f.decl_name = "not" && a = l2 then lemma_not_relates i rho f a
      else
        (match l2 with
         | App g [b] ->
           if g.decl_name = "not" && b = l1 then
             (lemma_not_relates i rho g b;
              match eval i l2 rho with
              | VBool c -> ())
           else ()
         | _ -> ())
    | _ ->
      (match l2 with
       | App g [b] ->
         if g.decl_name = "not" && b = l1 then
           (lemma_not_relates i rho g b;
            match eval i l2 rho with
            | VBool c -> ())
         else ()
       | _ -> ())

(* ----------------------------------------------------------------- *)
(* PR_UNIT_RESOLUTION's core step and n-ary fold.                      *)
(* ----------------------------------------------------------------- *)

let rec remove_first (c:clause) (l:literal) : Tot clause (decreases c) =
  match c with
  | [] -> []
  | l0 :: c' -> if l0 = l then c' else l0 :: remove_first c' l

(* Well-sortedness: every literal of `c` is Boolean-valued under `i`,
   `rho` -- the semantic side condition every real clause disjunct
   satisfies, required by `lemma_complementary_sound`. *)
let wf_clause (i:interpretation value) (rho:env value) (c:clause) : prop =
  forall (l:literal). List.Tot.memP l c ==> VBool? (eval i l rho)

let rec lemma_remove_first_wf (i:interpretation value) (rho:env value) (c:clause) (l:literal)
  : Lemma (requires wf_clause i rho c)
          (ensures wf_clause i rho (remove_first c l))
          (decreases c)
  = match c with
    | [] -> ()
    | l0 :: c' -> if l0 = l then () else lemma_remove_first_wf i rho c' l

let rec lemma_clause_shrink (i:interpretation value) (rho:env value) (c:clause) (l:literal)
  : Lemma (requires clause_holds i rho c /\ lit_is_false i rho l)
          (ensures clause_holds i rho (remove_first c l))
          (decreases c)
  = match c with
    | [] -> ()
    | l0 :: c' ->
      if l0 = l then ()
      else
        (FStar.Classical.excluded_middle (lit_true i rho l0);
         let goal () : prop = clause_holds i rho (remove_first c l) in
         FStar.Classical.or_elim #(lit_true i rho l0) #(~ (lit_true i rho l0)) #goal
           (fun _ -> ())
           (fun _ -> lemma_clause_shrink i rho c' l))

let rec find_complement (c:clause) (f:literal) : Tot (option literal) (decreases c) =
  match c with
  | [] -> None
  | l0 :: c' -> if complementary l0 f then Some l0 else find_complement c' f

(* `complementary` is a symmetric predicate (it is an `||` of two
   mirror-image `is_not` checks), so a `complementary l0 f` witness
   also certifies `complementary f l0`. *)
let lemma_complementary_sym (l1 l2:literal)
  : Lemma (complementary l1 l2 == complementary l2 l1)
  = ()

let rec lemma_find_complement_mem (c:clause) (f:literal)
  : Lemma (requires Some? (find_complement c f))
          (ensures List.Tot.memP (Some?.v (find_complement c f)) c /\
                   complementary f (Some?.v (find_complement c f)))
          (decreases c)
  = match c with
    | [] -> ()
    | l0 :: c' ->
      if complementary l0 f then lemma_complementary_sym l0 f
      else lemma_find_complement_mem c' f

let rec unit_resolve (c:clause) (fmls:list literal) : Tot clause (decreases fmls) =
  match fmls with
  | [] -> c
  | f :: fmls' ->
    (match find_complement c f with
     | Some l0 -> unit_resolve (remove_first c l0) fmls'
     | None -> unit_resolve c fmls')

let rec lemma_unit_resolve_sound (i:interpretation value) (rho:env value) (c:clause) (fmls:list literal)
  : Lemma (requires clause_holds i rho c /\ not_sound i /\ wf_clause i rho c /\
                    (forall (f:literal). List.Tot.memP f fmls ==> lit_true i rho f))
          (ensures clause_holds i rho (unit_resolve c fmls))
          (decreases fmls)
  = match fmls with
    | [] -> ()
    | f :: fmls' ->
      (match find_complement c f with
       | Some l0 ->
         lemma_find_complement_mem c f;
         lemma_complementary_sound i rho f l0;
         lemma_clause_shrink i rho c l0;
         lemma_remove_first_wf i rho c l0;
         lemma_unit_resolve_sound i rho (remove_first c l0) fmls'
       | None -> lemma_unit_resolve_sound i rho c fmls')

(* The full `PR_UNIT_RESOLUTION` soundness statement: a true clause,
   resolved against a list of proven-true resolvent facts, remains a
   true clause. (If the real proof's conclusion is `False`, i.e. the
   resolvent clause becomes empty, then this lemma's hypothesis
   `clause_holds i rho c` together with `clause_holds i rho []`'s
   literal falsity means the premises were contradictory under `rho`
   -- exactly the semantic content of a refutation.) *)
let lemma_unit_resolution_sound (i:interpretation value) (rho:env value) (c:clause) (fmls:list literal)
  : Lemma (requires clause_holds i rho c /\ not_sound i /\ wf_clause i rho c /\
                    (forall (f:literal). List.Tot.memP f fmls ==> lit_true i rho f))
          (ensures clause_holds i rho (unit_resolve c fmls))
  = lemma_unit_resolve_sound i rho c fmls

(* ----------------------------------------------------------------- *)
(* PR_AND_ELIM / PR_NOT_OR_ELIM                                        *)
(* ----------------------------------------------------------------- *)

let rec lemma_and_elim_sound (i:interpretation value) (rho:env value) (c:list expr) (t:expr)
  : Lemma (requires conj_holds i rho c /\ List.Tot.memP t c)
          (ensures lit_true i rho t)
          (decreases c)
  = match c with
    | [] -> ()
    | l0 :: c' -> if l0 = t then () else lemma_and_elim_sound i rho c' t

let rec lemma_not_or_elim_sound (i:interpretation value) (rho:env value) (c:clause) (t:expr)
  : Lemma (requires ~(clause_holds i rho c) /\ List.Tot.memP t c /\ VBool? (eval i t rho))
          (ensures lit_is_false i rho t)
          (decreases c)
  = match c with
    | [] -> ()
    | l0 :: c' -> if l0 = t then () else lemma_not_or_elim_sound i rho c' t

(* ----------------------------------------------------------------- *)
(* PR_MODUS_PONENS / PR_MODUS_PONENS_OEQ                                *)
(* ----------------------------------------------------------------- *)

let lemma_mp_sound (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (requires lit_true i rho a /\ (lit_true i rho a ==> lit_true i rho b))
          (ensures lit_true i rho b)
  = ()

(* ----------------------------------------------------------------- *)
(* PR_COMMUTATIVITY                                                     *)
(* ----------------------------------------------------------------- *)

let lemma_commutativity_sound (i:interpretation value) (rho:env value) (f:func_decl) (s t:expr)
  : Lemma (requires Some? f.interp /\ (forall (x y:value). i.interp_app f [x; y] == i.interp_app f [y; x]))
          (ensures eval i (App f [s; t]) rho == eval i (App f [t; s]) rho)
  = ()

(* ----------------------------------------------------------------- *)
(* PR_IFF_TRUE / PR_IFF_FALSE                                           *)
(* ----------------------------------------------------------------- *)

let eq_decl (s0:sort) : func_decl =
  { decl_name = "="; domain = [s0; s0]; range = bool_sort; interp = Some op_eq; int_params = [] }

let mk_eq_expr (s t:expr) : expr = App (eq_decl (get_sort s)) [s; t]

let mk_iff_expr (a b:expr) : expr = App (eq_decl bool_sort) [a; b]

let true_expr : expr = App ({ decl_name = "true"; domain = []; range = bool_sort; interp = Some op_true; int_params = [] }) []
let false_expr : expr = App ({ decl_name = "false"; domain = []; range = bool_sort; interp = Some op_false; int_params = [] }) []

let formula_clause (e:expr) : clause =
  match e with
  | App f args ->
    if f.decl_name = "or" then args
    else if f.decl_name = "false" && args = [] then []
    else [e]
  | _ -> [e]

let consequence_covers (concl lit:expr) : bool =
  lit = concl ||
  (match concl with
   | App f args -> f.decl_name = "or" && List.Tot.mem lit args
   | _ -> false)

let rec clause_consequence (residual:clause) (concl:expr) : Tot bool (decreases residual) =
  match residual with
  | [] -> true
  | l :: rest -> consequence_covers concl l && clause_consequence rest concl

let resolution_residual (c:expr) (units:list literal) : clause =
  match units with
  | [u] ->
    if complementary c u then []
    else unit_resolve (formula_clause c) units
  | _ -> unit_resolve (formula_clause c) units

let rec lemma_clause_member (i:interpretation value) (rho:env value) (c:clause) (l:expr)
  : Lemma (requires List.Tot.memP l c /\ lit_true i rho l)
          (ensures clause_holds i rho c)
          (decreases c)
  = match c with
    | [] -> ()
    | h :: rest -> if h = l then () else lemma_clause_member i rho rest l

let lemma_formula_clause (i:interpretation value) (rho:env value) (e:expr)
  : Lemma (requires lit_true i rho e /\ or_sound i /\ false_sound i)
          (ensures clause_holds i rho (formula_clause e))
  = match e with
    | App f args -> ()
    | _ -> ()

let lemma_consequence_covers (i:interpretation value) (rho:env value) (concl lit:expr)
  : Lemma (requires consequence_covers concl lit /\ lit_true i rho lit /\ or_sound i)
          (ensures lit_true i rho concl)
  = if lit = concl then ()
    else match concl with
         | App f args ->
           FStar.List.Tot.Properties.mem_memP lit args;
           lemma_clause_member i rho args lit
         | _ -> ()

let rec lemma_clause_consequence (i:interpretation value) (rho:env value) (c:clause) (concl:expr)
  : Lemma (requires clause_holds i rho c /\ clause_consequence c concl /\ or_sound i)
          (ensures lit_true i rho concl)
          (decreases c)
  = match c with
    | [] -> ()
    | l :: rest ->
      FStar.Classical.excluded_middle (lit_true i rho l);
      FStar.Classical.or_elim #(lit_true i rho l) #(~(lit_true i rho l))
        #(fun () -> lit_true i rho concl)
        (fun _ -> lemma_consequence_covers i rho concl l)
        (fun _ -> lemma_clause_consequence i rho rest concl)

let lemma_resolution_residual_sound (i:interpretation value) (rho:env value)
                                    (c:expr) (units:list literal)
  : Lemma (requires lit_true i rho c /\ not_sound i /\ or_sound i /\ false_sound i /\
                    wf_clause i rho (formula_clause c) /\
                    (forall (u:literal). List.Tot.memP u units ==> lit_true i rho u))
          (ensures clause_holds i rho (resolution_residual c units))
  = match units with
    | [u] ->
      if complementary c u then
        (lemma_complementary_sym c u;
         lemma_complementary_sound i rho u c)
      else
        (lemma_formula_clause i rho c;
         lemma_unit_resolution_sound i rho (formula_clause c) units)
    | _ ->
      lemma_formula_clause i rho c;
      lemma_unit_resolution_sound i rho (formula_clause c) units

let lemma_iff_true_sound (i:interpretation value) (rho:env value) (a:expr)
  : Lemma (requires lit_true i rho a /\ eq_sound i /\ true_sound i)
          (ensures eval i (mk_iff_expr a true_expr) rho == VBool true)
  = ()

let lemma_iff_false_sound (i:interpretation value) (rho:env value) (a:expr)
  : Lemma (requires lit_is_false i rho a /\ eq_sound i /\ false_sound i)
          (ensures eval i (mk_iff_expr a false_expr) rho == VBool true)
  = ()

(* ----------------------------------------------------------------- *)
(* Array extensionality ("array-ext"). Not reachable via               *)
(* `check1_basic`'s `basic`-family switch at all --                     *)
(* `proof_checker::check1` only dispatches `get_basic_family_id()`      *)
(* proofs, so this theory-plugin proof rule is outside what Z3's own    *)
(* in-tree checker verifies. `Z3ArrayTheory.lemma_array_extensionality`  *)
(* already proves the exact semantic content for the abstract `arr idx  *)
(* v` model, so this is a genuine Tier-1 mechanized rule. *)
let lemma_array_ext_sound (#idx:eqtype) (#v:Type) (a b:Z3ArrayTheory.arr idx v)
  : Lemma (requires forall (k:idx). Z3ArrayTheory.select a k == Z3ArrayTheory.select b k)
          (ensures a == b)
  = Z3ArrayTheory.lemma_array_extensionality a b

(* ----------------------------------------------------------------- *)
(* `rproof`: a proof-term data structure, mirroring                    *)
(* `Z3ProofTheory.proof`/`fact`/`all_leaves_sound` one layer up.        *)
(*                                                                      *)
(* Round 2 (see RESOLUTION_CHECKER_SCOPE.md / RESOLUTION_CHECKER_REPORT.md): *)
(* promotes `unit_resolve`/`and_elim`/`not_or_elim` from standalone      *)
(* lemmas into first-class `rproof` constructors (`RUnitRes`,           *)
(* `RNotOrElim`; `RAndElim` was already first-class since round 1), so   *)
(* a single `rproof` term can represent an entire resolution            *)
(* refutation end-to-end, not just the propositional glue around one    *)
(* equational-rewrite island. Also adds `PR_HYPOTHESIS`/`PR_LEMMA`       *)
(* (`Hyp`/`Lemma`) with explicit hypothesis-closure bookkeeping          *)
(* (`hyps_closed`): every `Hyp a` leaf reachable in a proof must be a    *)
(* member of the ambient hypothesis list `lemma_rproof_sound_hyps` is    *)
(* given, *except* inside a `RLemma fact_ pf_false` node, which           *)
(* discharges its own, locally-scoped hypothesis `(not fact_)` and is    *)
(* unconditionally sound regardless of the ambient hypotheses -- this    *)
(* closes exactly the gap `proof_checker.cpp` itself leaves as a         *)
(* comment ("TBD all branches with hypotheses must be closed by a        *)
(* later lemma"). The original no-open-hypotheses top-level theorem is   *)
(* recovered as `lemma_rproof_sound := lemma_rproof_sound_hyps ... []`.   *)
(* ----------------------------------------------------------------- *)

noeq
type rproof =
  (* The equational calculus, re-exposed as the Boolean fact `s = t`. *)
  | REq         : s:expr -> t:expr -> p:proof -> rproof
  (* `conj`'s conjunction holds (established by `premise`, whose own
     conclusion must be literally `(and conj)`) `=>` `t` holds,
     `t` a member of `conj`. *)
  | RAndElim    : and_f:func_decl -> conj:list expr -> t:expr -> premise:rproof -> rproof
  (* `pf_a : a`, `pf_imp : (implies a b)` or `(= a b)` (iff) `=> b`. *)
  | RModusPonens : a:expr -> b:expr -> imp_f:func_decl -> pf_a:rproof -> pf_imp:rproof -> rproof
  (* `f` commutative (asserted, not derived -- a syntactic property of
     the declaration) `=> f(s,t) = f(t,s)`. *)
  | RCommute    : f:func_decl{Some? f.interp} -> s:expr -> t:expr -> rproof
  | RIffTrue    : a:expr -> premise:rproof -> rproof
  | RIffFalse   : a:expr -> premise:rproof -> rproof
  (* Tier-2 trusted leaf: `concl` must hold under every `rho`
     (discharged by the caller, never silently assumed) -- it is both
     the side-condition obligation *and* the conclusion in one, since
     nothing downstream needs them distinguished. Matches
     `check1_basic`'s own `side_conditions.push_back` pattern for
     `PR_HYPER_RESOLVE`/`PR_REWRITE_STAR`/`PR_DISTRIBUTIVITY`, and its
     unconditional-trust pattern for `PR_DEF_AXIOM`/`PR_TH_LEMMA`/
     `PR_QUANT_INST`. *)
  | Trusted     : tag:string -> concl:expr -> rproof
  (* The stated consequence must contain every surviving literal.
     In particular, [C] may conclude C (even when C is itself an or),
     and an empty residual may conclude false. *)
  | RUnitRes    : concl:expr -> clause_pf:rproof -> units:list (expr & rproof) -> rproof
  (* `PR_NOT_OR_ELIM`: `premise` proves `(not (or disj))` (`disj`
     recovered structurally from `premise`'s own fact, not stored as a
     separate field -- same minimal style as `RIffFalse`); `t` is any
     member of `disj`; conclusion is `(not t)`. *)
  | RNotOrElim  : t:expr -> premise:rproof -> rproof
  (* `PR_HYPOTHESIS`: assumes `a` outright, licensed only when `a` is a
     member of the ambient hypothesis list threaded through
     `lemma_rproof_sound_hyps` (`hyps_closed`). *)
  | Hyp         : a:expr -> rproof
  (* `PR_LEMMA`: `pf_false` must prove `False` (`= false_expr`) under
     exactly the single local hypothesis `(not fact_)`
     (`hyps_closed pf_false [mk_not_expr fact_]`, checked inside
     `all_rtrusted_sound`, *not* against the ambient `hyps` the
     `Lemma` node itself is embedded under -- it is a self-contained,
     locally-closed sub-derivation); the conclusion is `fact_`,
     unconditionally -- classical proof by contradiction. *)
  | RLemma      : fact_:expr -> pf_false:rproof -> rproof

(* `not`, as a canonical `func_decl` (only its `decl_name`/`interp`
   matter to `not_sound`/`eval`, never object identity -- see
   `Z3ProofTheory.is_not`, which is likewise purely name-driven). *)
let not_decl : func_decl =
  { decl_name = "not"; domain = [bool_sort]; range = bool_sort; interp = Some op_not; int_params = [] }
let mk_not_expr (a:expr) : expr = App not_decl [a]

let rec rfact (p:rproof) : Tot (option expr) (decreases p) =
  match p with
  | REq s t p1 -> if fact p1 = Some (s, t) then Some (mk_eq_expr s t) else None
  | RAndElim and_f conj t premise ->
    (match rfact premise with
     | Some (App f args) ->
       if f = and_f && f.decl_name = "and" && args = conj && List.Tot.mem t conj
       then Some t else None
     | _ -> None)
  | RModusPonens a b imp_f pf_a pf_imp ->
    (match rfact pf_a, rfact pf_imp with
     | Some a', Some (App f [a2; b2]) ->
       if a' = a && a2 = a && b2 = b && f = imp_f &&
          (imp_f.decl_name = "implies" || imp_f.decl_name = "=>" || imp_f.decl_name = "=")
       then Some b else None
     | _, _ -> None)
  | RCommute f s t -> Some (mk_eq_expr (App f [s; t]) (App f [t; s]))
  | RIffTrue a premise ->
    (match rfact premise with
     | Some a' -> if a' = a then Some (mk_iff_expr a true_expr) else None
     | None -> None)
  | RIffFalse a premise ->
    (match rfact premise with
     | Some a' ->
       (match is_not a' with
        | Some a0 -> if a0 = a then Some (mk_iff_expr a false_expr) else None
        | None -> None)
     | None -> None)
  | Trusted tag concl -> Some concl
  | RUnitRes concl clause_pf units ->
    (match rfact clause_pf with
     | Some c ->
       if rfacts_match units &&
          clause_consequence (resolution_residual c (lits_of units)) concl
       then Some concl
       else None
     | _ -> None)
  | RNotOrElim t premise ->
    (match rfact premise with
     | Some (App f [App orf args]) ->
       if f.decl_name = "not" && orf.decl_name = "or" && List.Tot.mem t args
       then Some (App f [t]) else None
     | _ -> None)
  | Hyp a -> Some a
  | RLemma fact_ pf_false ->
    if rfact pf_false = Some false_expr then Some fact_ else None

(* `facts_of`-style companions for `RUnitRes`'s `units` list: whether
   every `(lit, pf)` pair's `pf` actually establishes exactly `lit`
   (`rfacts_match`), and the flattened list of resolvent literals
   itself (`lits_of`, the argument `unit_resolve` is folded over). *)
and rfacts_match (units:list (expr & rproof)) : Tot bool (decreases units) =
  match units with
  | [] -> true
  | (lit, pf) :: rest -> (rfact pf = Some lit) && rfacts_match rest

and lits_of (units:list (expr & rproof)) : Tot (list expr) (decreases units) =
  match units with
  | [] -> []
  | (lit, _) :: rest -> lit :: lits_of rest

let rec all_rtrusted_sound (i:interpretation value) (p:rproof) : Tot prop (decreases p) =
  match p with
  | REq _ _ p1 -> all_leaves_sound i p1
  | RAndElim _ _ _ premise -> all_rtrusted_sound i premise
  | RModusPonens _ _ _ pf_a pf_imp -> all_rtrusted_sound i pf_a /\ all_rtrusted_sound i pf_imp
  | RCommute f _ _ -> (forall (x y:value). i.interp_app f [x; y] == i.interp_app f [y; x])
  | RIffTrue _ premise -> all_rtrusted_sound i premise
  | RIffFalse _ premise -> all_rtrusted_sound i premise
  | Trusted _ concl -> (forall (rho:env value). eval i concl rho == VBool true)
  (* `wf_clause` is the semantic well-sortedness side condition
     `lemma_unit_resolution_sound` needs on its initial clause -- see
     that lemma's own precondition -- recorded here exactly like
     `RCommute`'s commutativity obligation, as an explicit, caller-
     discharged fact rather than something silently assumed. *)
  | RUnitRes _ clause_pf units ->
    all_rtrusted_sound i clause_pf /\ all_rtrusted_sound_units i units /\
    (forall (rho:env value).
       match rfact clause_pf with
       | Some c -> wf_clause i rho (formula_clause c)
       | None -> False)
  | RNotOrElim t premise ->
    all_rtrusted_sound i premise /\ (forall (rho:env value). VBool? (eval i t rho))
  | Hyp _ -> True
  | RLemma fact_ pf_false ->
    all_rtrusted_sound i pf_false /\ hyps_closed pf_false [mk_not_expr fact_] /\
    (forall (rho:env value). VBool? (eval i fact_ rho))

and all_rtrusted_sound_units (i:interpretation value) (units:list (expr & rproof)) : Tot prop (decreases units) =
  match units with
  | [] -> True
  | (_, pf) :: rest -> all_rtrusted_sound i pf /\ all_rtrusted_sound_units i rest

(* `hyps_closed p hyps`: every `Hyp a` leaf reachable in `p` (other
   than inside a `Lemma` node's own locally-closed sub-derivation,
   which is self-contained and checked separately via
   `all_rtrusted_sound`'s `Lemma` case) has its assumed fact `a` as a
   member of the ambient `hyps` list -- i.e. no proof is accepted with
   a dangling, un-discharged hypothesis. *)
and hyps_closed (p:rproof) (hyps:list expr) : Tot prop (decreases p) =
  match p with
  | REq _ _ _ -> True
  | RAndElim _ _ _ premise -> hyps_closed premise hyps
  | RModusPonens _ _ _ pf_a pf_imp -> hyps_closed pf_a hyps /\ hyps_closed pf_imp hyps
  | RCommute _ _ _ -> True
  | RIffTrue _ premise -> hyps_closed premise hyps
  | RIffFalse _ premise -> hyps_closed premise hyps
  | Trusted _ _ -> True
  | RUnitRes _ clause_pf units -> hyps_closed clause_pf hyps /\ hyps_closed_units units hyps
  | RNotOrElim _ premise -> hyps_closed premise hyps
  | Hyp a -> List.Tot.memP a hyps
  | RLemma _ _ -> True

and hyps_closed_units (units:list (expr & rproof)) (hyps:list expr) : Tot prop (decreases units) =
  match units with
  | [] -> True
  | (_, pf) :: rest -> hyps_closed pf hyps /\ hyps_closed_units rest hyps

(* Pure size metrics, purely to justify termination of the mutually
   recursive soundness lemmas below -- same role as `Z3ProofTheory.
   fst`'s `proof_size`/`proof_list_size`. *)
let rec rproof_size (p:rproof) : nat =
  match p with
  | REq _ _ _ -> 1
  | RAndElim _ _ _ premise -> 1 + rproof_size premise
  | RModusPonens _ _ _ pf_a pf_imp -> 1 + rproof_size pf_a + rproof_size pf_imp
  | RCommute _ _ _ -> 1
  | RIffTrue _ premise -> 1 + rproof_size premise
  | RIffFalse _ premise -> 1 + rproof_size premise
  | Trusted _ _ -> 1
  | RUnitRes _ clause_pf units -> 1 + rproof_size clause_pf + runits_size units
  | RNotOrElim _ premise -> 1 + rproof_size premise
  | Hyp _ -> 1
  | RLemma _ pf_false -> 1 + rproof_size pf_false

and runits_size (units:list (expr & rproof)) : nat =
  match units with
  | [] -> 0
  | (_, pf) :: rest -> 1 + rproof_size pf + runits_size rest

(* `PR_LEMMA`'s classical proof-by-contradiction step, factored out of
   the main mutual-recursion group since it needs no further recursion
   into `rproof` itself -- just the *already established* fact that
   `pf_false` is sound under the single hypothesis `(not fact_)`
   (`hyp_implies_false`, supplied by the caller, `lemma_rproof_sound_hyps`'s
   own `Lemma` case, exactly where that fact is available). Classically
   case-splits on whether `(not fact_)` actually holds at `rho`: if it
   does, `hyp_implies_false` forces `false_expr` true, contradicting
   `false_sound`; if it doesn't, `not_sound` plus the `VBool?`
   well-sortedness side condition forces `fact_` itself true. *)
let lemma_lemma_sound (i:interpretation value) (rho:env value) (fact_:expr)
                       (hyp_implies_false:squash (conj_holds i rho [mk_not_expr fact_] ==> lit_true i rho false_expr))
  : Lemma (requires false_sound i /\ not_sound i /\ VBool? (eval i fact_ rho))
          (ensures lit_true i rho fact_)
  = let goal () : prop = lit_true i rho fact_ in
    FStar.Classical.excluded_middle (conj_holds i rho [mk_not_expr fact_]);
    FStar.Classical.or_elim #(conj_holds i rho [mk_not_expr fact_])
                            #(~(conj_holds i rho [mk_not_expr fact_])) #goal
      (fun (_:squash (conj_holds i rho [mk_not_expr fact_])) ->
         (* `false_expr` ends up true, contradicting `false_sound`. *)
         match eval i false_expr rho with
         | VBool b -> ()
         | _ -> ())
      (fun (_:squash (~(conj_holds i rho [mk_not_expr fact_]))) ->
         (* `~(not fact_)`, so by `not_sound`, `eval i fact_ rho =!=
            VBool false`; combined with `VBool?`, it must be `VBool
            true`. *)
         match eval i fact_ rho with
         | VBool b -> ()
         | _ -> ())

(* `a`'s membership in `hyps` plus `hyps`'s conjunction holding
   directly yields `a` itself -- the semantic content `Hyp` licenses. *)
let rec lemma_conj_mem (i:interpretation value) (rho:env value) (hyps:list expr) (a:expr)
  : Lemma (requires List.Tot.memP a hyps)
          (ensures conj_holds i rho hyps ==> lit_true i rho a)
          (decreases hyps)
  = match hyps with
    | [] -> ()
    | h :: hyps' -> if h = a then () else lemma_conj_mem i rho hyps' a

(* The composed soundness theorem, relative to an explicit ambient
   hypothesis list `hyps` (every `Hyp` leaf not under a `Lemma` must be
   licensed by membership in `hyps`, `hyps_closed`): a well-formed
   `rproof` (`Some? (rfact p)`), all of whose non-hypothesis leaves are
   sound (`all_rtrusted_sound`), under an interpretation that
   interprets `not`/`and`/`or`/`implies`/`=` the standard way and
   respects quantifier-extensionality, denotes a true fact *whenever
   its ambient hypotheses do* -- for every environment. The original,
   no-open-hypotheses theorem is `lemma_rproof_sound := 
   lemma_rproof_sound_hyps ... []` below. *)
let rec lemma_rproof_sound_hyps (i:interpretation value) (p:rproof) (rho:env value) (hyps:list expr)
  : Lemma (requires Some? (rfact p) /\ all_rtrusted_sound i p /\ hyps_closed p hyps /\
                    not_sound i /\ and_sound i /\ or_sound i /\ implies_sound i /\
                    eq_sound i /\ true_sound i /\ false_sound i /\
                    quant_extensional i)
          (ensures conj_holds i rho hyps ==> lit_true i rho (Some?.v (rfact p)))
          (decreases rproof_size p)
  = match p with
    | REq s t p1 ->
      lemma_proof_sound i p1 rho;
      let aux (_:squash (conj_holds i rho hyps)) : Lemma (lit_true i rho (mk_eq_expr s t)) = () in
      FStar.Classical.impl_intro aux
    | RAndElim and_f conj t premise ->
      lemma_rproof_sound_hyps i premise rho hyps;
      (match rfact premise with
       | Some (App f args) ->
         FStar.List.Tot.Properties.mem_memP t conj;
         let aux (_:squash (conj_holds i rho hyps)) : Lemma (lit_true i rho t) =
           lemma_and_elim_sound i rho conj t
         in FStar.Classical.impl_intro aux
       | _ -> ())
    | RModusPonens a b imp_f pf_a pf_imp ->
      lemma_rproof_sound_hyps i pf_a rho hyps;
      lemma_rproof_sound_hyps i pf_imp rho hyps;
      (match rfact pf_a, rfact pf_imp with
       | Some a', Some (App f [a2; b2]) ->
         let aux (_:squash (conj_holds i rho hyps)) : Lemma (lit_true i rho b) =
           lemma_mp_sound i rho a b
         in FStar.Classical.impl_intro aux
       | _, _ -> ())
    | RCommute f s t ->
      let aux (_:squash (conj_holds i rho hyps)) : Lemma (lit_true i rho (mk_eq_expr (App f [s; t]) (App f [t; s]))) = () in
      FStar.Classical.impl_intro aux
    | RIffTrue a premise ->
      lemma_rproof_sound_hyps i premise rho hyps;
      (match rfact premise with
       | Some a' ->
         let aux (_:squash (conj_holds i rho hyps)) : Lemma (lit_true i rho (mk_iff_expr a true_expr)) =
           lemma_iff_true_sound i rho a
         in FStar.Classical.impl_intro aux
       | None -> ())
    | RIffFalse a premise ->
      lemma_rproof_sound_hyps i premise rho hyps;
      (match rfact premise with
       | Some a' ->
         (match a' with
          | App f [a0] ->
            if f.decl_name = "not" then
              let aux (_:squash (conj_holds i rho hyps)) : Lemma (lit_true i rho (mk_iff_expr a false_expr)) =
                lemma_iff_false_sound i rho a
              in FStar.Classical.impl_intro aux
            else ()
          | _ -> ())
       | None -> ())
    | Trusted _ concl ->
      let aux (_:squash (conj_holds i rho hyps)) : Lemma (lit_true i rho concl) = () in
      FStar.Classical.impl_intro aux
    | RUnitRes concl clause_pf units ->
      lemma_rproof_sound_hyps i clause_pf rho hyps;
      (match rfact clause_pf with
       | Some c ->
        let aux (_:squash (conj_holds i rho hyps)) : Lemma (lit_true i rho concl) =
           let fmls_aux (q:literal)
             : Lemma (requires List.Tot.memP q (lits_of units)) (ensures lit_true i rho q)
             = lemma_units_sound_hyps i rho hyps units q
           in
           FStar.Classical.forall_intro (FStar.Classical.move_requires fmls_aux);
           lemma_resolution_residual_sound i rho c (lits_of units);
           lemma_clause_consequence i rho (resolution_residual c (lits_of units)) concl
         in FStar.Classical.impl_intro aux
       | _ -> ())
    | RNotOrElim t premise ->
      lemma_rproof_sound_hyps i premise rho hyps;
      (match rfact premise with
       | Some (App f [App orf args]) ->
         FStar.List.Tot.Properties.mem_memP t args;
         let aux (_:squash (conj_holds i rho hyps)) : Lemma (lit_true i rho (App f [t])) =
           lemma_not_or_elim_sound i rho args t
         in FStar.Classical.impl_intro aux
       | _ -> ())
    | Hyp a ->
      let aux (_:squash (conj_holds i rho hyps)) : Lemma (lit_true i rho a) =
        lemma_conj_mem i rho hyps a
      in FStar.Classical.impl_intro aux
    | RLemma fact_ pf_false ->
      lemma_rproof_sound_hyps i pf_false rho [mk_not_expr fact_];
      let aux (_:squash (conj_holds i rho hyps)) : Lemma (lit_true i rho fact_) =
        lemma_lemma_sound i rho fact_ ()
      in FStar.Classical.impl_intro aux

(* `RUnitRes`'s per-literal lookup into `units`: if `q` is (the fact
   of) some pair in `units`, and `units` is itself well-formed
   (`rfacts_match`) and sound (`all_rtrusted_sound_units`,
   `hyps_closed_units`), then `q` holds whenever the ambient `hyps`
   do -- found by walking `units` and delegating to that pair's own
   `rproof`'s soundness via `lemma_rproof_sound_hyps` once the matching
   element is found. *)
and lemma_units_sound_hyps (i:interpretation value) (rho:env value) (hyps:list expr)
                            (units:list (expr & rproof)) (q:expr)
  : Lemma (requires rfacts_match units /\ all_rtrusted_sound_units i units /\
                    hyps_closed_units units hyps /\ List.Tot.memP q (lits_of units) /\
                    not_sound i /\ and_sound i /\ or_sound i /\ implies_sound i /\
                    eq_sound i /\ true_sound i /\ false_sound i /\
                    quant_extensional i)
          (ensures conj_holds i rho hyps ==> lit_true i rho q)
          (decreases runits_size units)
  = match units with
    | [] -> ()
    | (lit, pf) :: rest ->
      if lit = q then lemma_rproof_sound_hyps i pf rho hyps
      else lemma_units_sound_hyps i rho hyps rest q

(* The original, no-open-hypotheses top-level theorem (round 1's
   signature, preserved as a convenience corollary): a well-formed,
   fully self-contained `rproof` (no `Hyp` leaves outside of
   `Lemma`-closed sub-derivations) denotes a true fact, unconditionally. *)
let lemma_rproof_sound (i:interpretation value) (p:rproof) (rho:env value)
  : Lemma (requires Some? (rfact p) /\ all_rtrusted_sound i p /\ hyps_closed p [] /\
                    not_sound i /\ and_sound i /\ or_sound i /\ implies_sound i /\
                    eq_sound i /\ true_sound i /\ false_sound i /\
                    quant_extensional i)
          (ensures lit_true i rho (Some?.v (rfact p)))
  = lemma_rproof_sound_hyps i p rho []
