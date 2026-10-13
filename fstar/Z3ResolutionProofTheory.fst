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
      calculus re-exposed as a Boolean `=`-fact (`REq`), and Tier-2
      `Trusted` leaves. `PR_UNIT_RESOLUTION`/`PR_NOT_OR_ELIM`/
      `PR_HYPOTHESIS`/`PR_LEMMA` are proved as standalone lemmas above
      but not yet wired into the `rproof` constructor set -- see
      "Status after round 1" in `RESOLUTION_CHECKER_SCOPE.md`.
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
    f.decl_name == "implies" ==>
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
          (imp_f.decl_name = "implies" || imp_f.decl_name = "=")
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

let rec all_rtrusted_sound (i:interpretation value) (p:rproof) : Tot prop (decreases p) =
  match p with
  | REq _ _ p1 -> all_leaves_sound i p1
  | RAndElim _ _ _ premise -> all_rtrusted_sound i premise
  | RModusPonens _ _ _ pf_a pf_imp -> all_rtrusted_sound i pf_a /\ all_rtrusted_sound i pf_imp
  | RCommute f _ _ -> (forall (x y:value). i.interp_app f [x; y] == i.interp_app f [y; x])
  | RIffTrue _ premise -> all_rtrusted_sound i premise
  | RIffFalse _ premise -> all_rtrusted_sound i premise
  | Trusted _ concl -> (forall (rho:env value). eval i concl rho == VBool true)

(* The composed soundness theorem: a well-formed `rproof` (`Some? (rfact
   p)`), all of whose leaves are sound (`all_rtrusted_sound`), under an
   interpretation that interprets `not`/`and`/`implies`/`=` the
   standard way and respects quantifier-extensionality, denotes a true
   fact, for every environment. *)
let rec lemma_rproof_sound (i:interpretation value) (p:rproof) (rho:env value)
  : Lemma (requires Some? (rfact p) /\ all_rtrusted_sound i p /\
                    not_sound i /\ and_sound i /\ implies_sound i /\
                    eq_sound i /\ true_sound i /\ false_sound i /\
                    quant_extensional i)
          (ensures lit_true i rho (Some?.v (rfact p)))
          (decreases p)
  = match p with
    | REq s t p1 -> lemma_proof_sound i p1 rho
    | RAndElim and_f conj t premise ->
      lemma_rproof_sound i premise rho;
      (match rfact premise with
       | Some (App f args) ->
         FStar.List.Tot.Properties.mem_memP t conj;
         lemma_and_elim_sound i rho conj t
       | _ -> ())
    | RModusPonens a b imp_f pf_a pf_imp ->
      lemma_rproof_sound i pf_a rho;
      lemma_rproof_sound i pf_imp rho;
      (match rfact pf_a, rfact pf_imp with
       | Some a', Some (App f [a2; b2]) ->
         lemma_mp_sound i rho a b
       | _, _ -> ())
    | RCommute f s t -> ()
    | RIffTrue a premise ->
      lemma_rproof_sound i premise rho;
      (match rfact premise with
       | Some a' -> lemma_iff_true_sound i rho a
       | None -> ())
    | RIffFalse a premise ->
      lemma_rproof_sound i premise rho;
      (match rfact premise with
       | Some a' ->
         (match a' with
          | App f [a0] ->
            if f.decl_name = "not" then lemma_iff_false_sound i rho a
            else ()
          | _ -> ())
       | None -> ())
    | Trusted _ _ -> ()
