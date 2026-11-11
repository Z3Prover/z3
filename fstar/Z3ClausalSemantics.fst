module Z3ClausalSemantics

open Z3AstTheory
module C = Z3CanonicalOps
module P = Z3ProofTheory
module L = FStar.List.Tot

(* A proof-only valuation works for both unindexed interpretations and
   sort-indexed carriers, including ghost function-space arrays. *)
type valuation = expr -> GTot bool
type literal = expr
type clause = list literal

let rec clause_holds (rho:valuation) (c:clause) : GTot bool (decreases c) =
  match c with
  | [] -> false
  | l :: rest -> rho l || clause_holds rho rest

let rec conj_holds (rho:valuation) (c:clause) : GTot bool (decreases c) =
  match c with
  | [] -> true
  | l :: rest -> rho l && conj_holds rho rest

let complementary (a b:literal) : bool =
  P.is_not a = Some b || P.is_not b = Some a ||
  (match a, b with
   | App f [], App g [] ->
     (C.canonical_true f && C.canonical_false g) ||
     (C.canonical_false f && C.canonical_true g)
   | _, _ -> false)

let complement_model (rho:valuation) : prop =
  forall (a b:literal). complementary a b /\ rho a ==> not (rho b)

let rec remove_first (c:clause) (l:literal) : Tot clause (decreases c) =
  match c with
  | [] -> []
  | x :: rest -> if x = l then rest else x :: remove_first rest l

let rec remove_complements (c:clause) (l:literal) : Tot clause (decreases c) =
  match c with
  | [] -> []
  | x :: rest ->
    if complementary x l then remove_complements rest l
    else x :: remove_complements rest l

let rec unit_resolve (c:clause) (units:list literal) : Tot clause (decreases units) =
  match units with
  | [] -> c
  | l :: rest -> unit_resolve (remove_complements c l) rest

let lemma_complementary_sym (a b:literal)
  : Lemma (complementary a b == complementary b a)
  = ()

let rec lemma_clause_member (rho:valuation) (c:clause) (l:literal)
  : Lemma (requires L.memP l c /\ rho l)
          (ensures clause_holds rho c)
          (decreases c)
  = match c with
    | [] -> ()
    | x :: rest -> if x <> l then lemma_clause_member rho rest l

let rec lemma_conj_member (rho:valuation) (c:clause) (l:literal)
  : Lemma (requires conj_holds rho c /\ L.memP l c)
          (ensures rho l)
          (decreases c)
  = match c with
    | [] -> ()
    | x :: rest -> if x <> l then lemma_conj_member rho rest l

let rec lemma_clause_false_member (rho:valuation) (c:clause) (l:literal)
  : Lemma (requires not (clause_holds rho c) /\ L.memP l c)
          (ensures not (rho l))
          (decreases c)
  = match c with
    | [] -> ()
    | x :: rest -> if x <> l then lemma_clause_false_member rho rest l

let rec lemma_clause_shrink (rho:valuation) (c:clause) (l:literal)
  : Lemma (requires clause_holds rho c /\ not (rho l))
          (ensures clause_holds rho (remove_first c l))
          (decreases c)
  = match c with
    | [] -> ()
    | x :: rest -> if x <> l && not (rho x) then lemma_clause_shrink rho rest l

let rec lemma_remove_complements (rho:valuation) (c:clause) (l:literal)
  : Lemma (requires complement_model rho /\ clause_holds rho c /\ rho l)
          (ensures clause_holds rho (remove_complements c l))
          (decreases c)
  = match c with
    | [] -> ()
    | x :: rest ->
      if complementary x l then (
        lemma_complementary_sym x l;
        lemma_remove_complements rho rest l)
      else if not (rho x) then lemma_remove_complements rho rest l

let rec lemma_unit_resolution (rho:valuation) (c:clause) (units:list literal)
  : Lemma (requires complement_model rho /\ clause_holds rho c /\ conj_holds rho units)
          (ensures clause_holds rho (unit_resolve c units))
          (decreases units)
  = match units with
    | [] -> ()
    | l :: rest ->
      lemma_remove_complements rho c l;
      lemma_unit_resolution rho (remove_complements c l) rest

let rec lemma_conj_intro (rho:valuation) (c:clause)
  : Lemma (requires forall (l:literal). L.memP l c ==> rho l)
          (ensures conj_holds rho c)
          (decreases c)
  = match c with
    | [] -> ()
    | _ :: rest -> lemma_conj_intro rho rest

(* Resolution implementations can supply their own elimination/coverage
   test; the disjunction argument does not depend on that syntax. *)
let rec lemma_clause_consequence (rho:valuation) (c:clause) (conclusion:expr)
  : Lemma (requires clause_holds rho c /\
                    (forall (l:literal). L.memP l c /\ rho l ==> rho conclusion))
          (ensures rho conclusion)
          (decreases c)
  = match c with
    | [] -> ()
    | l :: rest -> if not (rho l) then lemma_clause_consequence rho rest conclusion
