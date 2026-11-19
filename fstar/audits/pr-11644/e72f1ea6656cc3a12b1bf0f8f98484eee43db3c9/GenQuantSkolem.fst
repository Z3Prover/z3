module GenQuantSkolem
(* Semantic model of the PR's addition to context::internalize_quantifier
   (src/smt/smt_internalizer.cpp @ e72f1ea): for forall q marked skolemid "generated",
   add the clause  q \/ ~body[sk].  Sorts assumed non-empty; not C++ execution. *)

let q (#a:Type) (body: a -> prop) : prop = forall (x:a). body x

(* O3: negative polarity: ~q ==> some witness falsifies the body. *)
let neg_polarity_witness (#a:Type) (body: a -> prop)
  : Lemma (requires ~(q body)) (ensures exists (sk:a). ~(body sk))
  = let aux () : Lemma (requires ~(exists (sk:a). ~(body sk))) (ensures q body) =
      let f (x:a) : Lemma (body x) =
        FStar.Classical.excluded_middle (body x) in
      FStar.Classical.forall_intro f
    in
    FStar.Classical.move_requires aux ()

(* O1: the clause is satisfiable for some interpretation of the fresh constant. *)
let clause_satisfiable (#a:Type) (d:a) (body: a -> prop)
  : Lemma (exists (sk:a). q body \/ ~(body sk))
  = FStar.Classical.excluded_middle (q body);
    FStar.Classical.move_requires (neg_polarity_witness #a) body;
    ()

(* O2: if q holds, the clause holds for every interpretation of the skolems. *)
let clause_when_q (#a:Type) (body: a -> prop) (sk:a)
  : Lemma (requires q body) (ensures q body \/ ~(body sk)) = ()

(* O4: var_subst std_order maps (VAR j) to args[n-1-j]; decl i is (VAR n-1-i);
   skolems pushed in decl order, so decl i receives skolems[i]. *)
let subst_order (n:nat) (i:nat{i<n})
  : Lemma (n - 1 - (n - 1 - i) == i) = ()
