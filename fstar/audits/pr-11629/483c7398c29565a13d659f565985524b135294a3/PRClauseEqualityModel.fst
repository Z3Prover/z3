module PRClauseEqualityModel
module L = FStar.List.Tot

(* Abstract model of the PR's clause-equality replay: v is the truth valuation,
   lits the clause literals, e the selected equality literal. *)
let clause_true (v:int -> bool) (lits:list int) : prop = exists (t:int). L.mem t lits /\ v t
let complements_except_false (v:int -> bool) (lits:list int) (e:int) : prop =
  forall (t:int). L.mem t (L.filter (fun x -> x <> e) lits) ==> ~(v t)

(* If the clause is false, every literal other than e is false, so the complements
   facts ++ not(l) for l<>e hold; soundness of the equality check then gives e. *)
let clause_equality_sound (v:int -> bool) (lits:list int) (e:int) (facts_hold:prop)
  : Lemma (requires L.mem e lits /\ facts_hold /\
                    (complements_except_false v lits e ==> v e))
          (ensures clause_true v lits) =
  let aux (t:int) : Lemma (L.mem t (L.filter (fun x -> x <> e) lits) ==> L.mem t lits /\ t <> e) =
    L.mem_filter (fun x -> x <> e) lits t in
  FStar.Classical.forall_intro aux

(* Duplicates of e are removed along with e, and only e-equal literals are removed. *)
let filter_excludes_only_e (lits:list int) (e:int) (t:int)
  : Lemma (L.mem t (L.filter (fun x -> x <> e) lits) ==> (L.mem t lits /\ t <> e)) =
  L.mem_filter (fun x -> x <> e) lits t

let budget_ok (nf nl:nat) : bool = not (nf > 29) && not (nf + nl > 30)
let budget_bound (nf nl:nat) : Lemma (requires budget_ok nf nl) (ensures nf + nl <= 30) = ()
