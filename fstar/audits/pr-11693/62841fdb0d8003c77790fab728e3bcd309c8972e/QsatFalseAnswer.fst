module QsatFalseAnswer
(* Model of the PR change in qsat.cpp (qsat_qe branch, l_false case).
   Answer conjuncts are Boolean values under a fixed assignment; quantifier
   rebinding over a nonempty domain D is modelled by predicates over D. *)
open FStar.List.Tot

let conj (l:list bool) : bool = fold_right (fun a b -> a && b) l true

(* PR: fml = mk_and(m_answer); if some a is false then fml = false *)
let pr_fml (l:list bool) : bool = if mem false l then false else conj l

(* O1: the PR formula equals the conjunction semantically (no change in meaning) *)
let rec conj_false (l:list bool) : Lemma (mem false l ==> conj l = false) =
  match l with [] -> () | _::t -> conj_false t
let o1 (l:list bool) : Lemma (pr_fml l = conj l) = conj_false l

(* O2: rebinding with exists/forall over a nonempty domain of a constant-false body is false *)
let ex_over (#a:Type) (d:a) (p:a -> bool) : prop = exists (x:a). p x == true
let fa_over (#a:Type) (p:a -> bool) : prop = forall (x:a). p x == true
let o2_exists (#a:Type) (d:a) : Lemma (~(ex_over d (fun _ -> false))) = ()
let o2_forall (#a:Type) (d:a) : Lemma (~(fa_over (fun (_:a) -> false))) =
  let _ = fa_over (fun (_:a) -> false) in ()

(* O3: the old behaviour (forall over d of body-with-false-conjunct) is also
   semantically false, so the PR changes representation, not meaning *)
let o3 (#a:Type) (d:a) (l:list bool) : Lemma
  (requires mem false l)
  (ensures ~(fa_over #a (fun _ -> conj l))) = conj_false l
