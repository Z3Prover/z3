module Z3RegexCertificate

module A = Z3PredicateAlgebra
module T = Z3TransitionTerm
module R = Z3RegexTheory

noeq type system (p:Type) (s:eqtype) = {
  nullable : s -> bool;
  derivative : s -> T.term p s
}

(* These are the semantic obligations for the supplied state implementation,
   not assumptions about a producer, a union-find, or an accepted certificate. *)
let system_sound (#p:Type) (#a #s:eqtype) (alg:A.algebra p a)
    (sys:system p s) (language:s -> R.lang a) : prop =
  (forall q. R.mem [] (language q) <==> sys.nullable q) /\
  (forall q x w. R.mem (x :: w) (language q) <==>
    R.mem w (language (T.eval alg.holds (sys.derivative q) x)))

type row (s:Type) = {
  state : s;
  label : nat
}

type certificate (s:Type) = list (row s)

let rec class_of (#s:eqtype) (cert:certificate s) (q:s)
  : Tot (option nat) (decreases cert) =
  match cert with
  | [] -> None
  | e :: rest -> if q = e.state then Some e.label else class_of rest q

let rec representative (#s:Type) (cert:certificate s) (label:nat)
  : Tot (option s) (decreases cert) =
  match cert with
  | [] -> None
  | e :: rest -> if label = e.label then Some e.state else representative rest label

(* Equality needs no certificate entry. Missing nonidentical successors fail. *)
let related (#s:eqtype) (cert:certificate s) (q r:s) : bool =
  q = r ||
  (match class_of cert q, class_of cert r with
   | Some i, Some j -> i = j
   | _ -> false)

let lemma_related_symm (#s:eqtype) (cert:certificate s) (q r:s)
  : Lemma (related cert q r == related cert r q) = ()

let lemma_related_trans (#s:eqtype) (cert:certificate s) (q r t:s)
  : Lemma (requires related cert q r /\ related cert r t)
          (ensures related cert q t) = ()

let transitions_agree (#p #a:Type) (#s:eqtype) (alg:A.algebra p a)
    (is_empty:p -> bool) (sys:system p s) (cert:certificate s) (q r:s) : bool =
  T.check alg is_empty (fun pair -> related cert (fst pair) (snd pair)) alg.top
    (T.lift_binary (fun l r -> (l, r)) (sys.derivative q) (sys.derivative r))

let lemma_transitions_agree (#p #a:Type) (#s:eqtype) (alg:A.algebra p a)
    (is_empty:p -> bool) (sys:system p s) (cert:certificate s) (q r:s) (x:a)
  : Lemma (requires A.valid alg /\ A.empty_sound alg is_empty /\
                   transitions_agree alg is_empty sys cert q r)
          (ensures related cert (T.eval alg.holds (sys.derivative q) x)
                                (T.eval alg.holds (sys.derivative r) x)) =
  A.lemma_top alg x;
  T.lemma_check_sound alg is_empty
    (fun pair -> related cert (fst pair) (snd pair)) alg.top
    (T.lift_binary (fun l r -> (l, r)) (sys.derivative q) (sys.derivative r)) x;
  T.lemma_eval_lift_binary alg.holds (fun l r -> (l, r))
    (sys.derivative q) (sys.derivative r) x

let check_state (#p #a:Type) (#s:eqtype) (alg:A.algebra p a)
    (is_empty:p -> bool) (sys:system p s) (cert:certificate s)
    (label:nat) (q:s) : bool =
  class_of cert q = Some label &&
  (match representative cert label with
   | None -> false
   | Some r ->
     sys.nullable q = sys.nullable r &&
     transitions_agree alg is_empty sys cert q r)

let rec check_rows (#p #a:Type) (#s:eqtype) (alg:A.algebra p a)
    (is_empty:p -> bool) (sys:system p s) (cert rows:certificate s)
  : Tot bool (decreases rows) =
  match rows with
  | [] -> true
  | e :: rest ->
    check_state alg is_empty sys cert e.label e.state &&
    check_rows alg is_empty sys cert rest

(* false rejects this certificate; it is not an inequivalence judgment. *)
let check_equivalence (#p #a:Type) (#s:eqtype) (alg:A.algebra p a)
    (is_empty:p -> bool) (sys:system p s) (q r:s) (cert:certificate s) : bool =
  related cert q r && check_rows alg is_empty sys cert cert

let rec lemma_checked_lookup (#p #a:Type) (#s:eqtype) (alg:A.algebra p a)
    (is_empty:p -> bool) (sys:system p s) (cert rows:certificate s) (q:s) (k:nat)
  : Lemma (requires check_rows alg is_empty sys cert rows /\ class_of rows q == Some k)
          (ensures check_state alg is_empty sys cert k q)
          (decreases rows) =
  match rows with
  | [] -> ()
  | e :: rest ->
    if q = e.state then ()
    else lemma_checked_lookup alg is_empty sys cert rest q k

let lemma_checked_progress (#p #a:Type) (#s:eqtype) (alg:A.algebra p a)
    (is_empty:p -> bool) (sys:system p s) (cert:certificate s) (q r:s) (x:a)
  : Lemma (requires A.valid alg /\ A.empty_sound alg is_empty /\
                   check_rows alg is_empty sys cert cert /\ related cert q r)
          (ensures sys.nullable q == sys.nullable r /\
                   related cert (T.eval alg.holds (sys.derivative q) x)
                                (T.eval alg.holds (sys.derivative r) x)) =
  if q = r then ()
  else match class_of cert q, class_of cert r with
  | Some k, Some _ ->
    lemma_checked_lookup alg is_empty sys cert cert q k;
    lemma_checked_lookup alg is_empty sys cert cert r k;
    (match representative cert k with
     | None -> ()
     | Some t ->
       lemma_transitions_agree alg is_empty sys cert q t x;
       lemma_transitions_agree alg is_empty sys cert r t x;
       lemma_related_symm cert (T.eval alg.holds (sys.derivative r) x)
                               (T.eval alg.holds (sys.derivative t) x);
       lemma_related_trans cert (T.eval alg.holds (sys.derivative q) x)
                                (T.eval alg.holds (sys.derivative t) x)
                                (T.eval alg.holds (sys.derivative r) x))
  | _ -> ()

let lemma_checked_null (#p #a:Type) (#s:eqtype) (alg:A.algebra p a)
    (is_empty:p -> bool) (sys:system p s) (cert:certificate s) (q r:s)
  : Lemma (requires check_rows alg is_empty sys cert cert /\ related cert q r)
          (ensures sys.nullable q == sys.nullable r) =
  if q = r then ()
  else match class_of cert q, class_of cert r with
  | Some k, Some _ ->
    lemma_checked_lookup alg is_empty sys cert cert q k;
    lemma_checked_lookup alg is_empty sys cert cert r k
  | _ -> ()

let rec lemma_related_language (#p:Type) (#a #s:eqtype) (alg:A.algebra p a)
    (is_empty:p -> bool) (sys:system p s) (language:s -> R.lang a)
    (cert:certificate s) (q r:s) (w:list a)
  : Lemma (requires A.valid alg /\ A.empty_sound alg is_empty /\
                   system_sound alg sys language /\
                   check_rows alg is_empty sys cert cert /\ related cert q r)
          (ensures R.mem w (language q) <==> R.mem w (language r))
          (decreases w) =
  match w with
  | [] -> lemma_checked_null alg is_empty sys cert q r
  | x :: rest ->
    lemma_checked_progress alg is_empty sys cert q r x;
    lemma_related_language alg is_empty sys language cert
      (T.eval alg.holds (sys.derivative q) x)
      (T.eval alg.holds (sys.derivative r) x) rest

let lemma_check_equivalence_sound (#p:Type) (#a #s:eqtype) (alg:A.algebra p a)
    (is_empty:p -> bool) (sys:system p s) (language:s -> R.lang a)
    (q r:s) (cert:certificate s)
  : Lemma (requires A.valid alg /\ A.empty_sound alg is_empty /\
                   system_sound alg sys language /\
                   check_equivalence alg is_empty sys q r cert)
          (ensures R.equiv (language q) (language r)) =
  FStar.Classical.forall_intro
    (fun w -> lemma_related_language alg is_empty sys language cert q r w)
