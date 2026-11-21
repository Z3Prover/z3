module Z3RelationalReachability

open Z3AstTheory
open Z3UnifiedProofSyntax
module L = FStar.List.Tot

type relation_semantics = expr -> expr -> prop

let symmetric (rel:relation_semantics) : prop =
  forall (a b:expr). rel a b ==> rel b a

let transitive (rel:relation_semantics) : prop =
  forall (a b c:expr). rel a b /\ rel b c ==> rel a c

let reflexive (rel:relation_semantics) : prop =
  forall (a:expr). rel a a

let rec edges_hold (rel:relation_semantics) (r:relation) (js:list judgment)
  : Tot prop (decreases js) =
  match js with
  | [] -> True
  | j :: rest ->
    (match edge r j with Some (a, b) -> rel a b | None -> True) /\
    edges_hold rel r rest

let rec lemma_matching (rel:relation_semantics) (r:relation)
                       (a b:expr) (js:list judgment)
  : Lemma (requires edges_hold rel r js /\ matching r a b js)
          (ensures rel a b)
          (decreases js) =
  match js with
  | [] -> ()
  | j :: rest ->
    if edge r j <> Some (a, b) then lemma_matching rel r a b rest

let rec arguments_related (rel:relation_semantics) (xs ys:list expr)
  : Tot prop (decreases xs) =
  match xs, ys with
  | [], [] -> True
  | x :: rest, y :: tail -> rel x y /\ arguments_related rel rest tail
  | _, _ -> False

let rec lemma_arguments (rel:relation_semantics) (r:relation)
                        (xs ys:list expr) (js:list judgment)
  : Lemma (requires reflexive rel /\ edges_hold rel r js /\ arguments_match r xs ys js)
          (ensures arguments_related rel xs ys)
          (decreases xs) =
  match xs, ys with
  | [], [] -> ()
  | x :: rest, y :: tail ->
    (if x <> y then lemma_matching rel r x y js);
    lemma_arguments rel r rest tail js
  | _, _ -> ()

let reachable_sound (rel:relation_semantics) (start:expr) (known:list expr) : prop =
  forall (e:expr). L.memP e known ==> rel start e

let lemma_extend (rel:relation_semantics) (start a b:expr) (known:list expr)
  : Lemma (requires transitive rel /\ reachable_sound rel start known /\
                    L.mem a known /\ rel a b)
          (ensures reachable_sound rel start (b :: known)) =
  FStar.List.Tot.Properties.mem_memP a known

let rec lemma_extend_reachable (rel:relation_semantics) (r:relation) (start:expr)
                               (js:list judgment) (known:list expr)
  : Lemma (requires symmetric rel /\ transitive rel /\ edges_hold rel r js /\
                    reachable_sound rel start known)
          (ensures reachable_sound rel start (extend_reachable r js known))
          (decreases js) =
  match js with
  | [] -> ()
  | j :: rest ->
    (match edge r j with
     | Some (a, b) ->
       if L.mem a known then (
         lemma_extend rel start a b known;
         lemma_extend_reachable rel r start rest (b :: known))
       else if L.mem b known then (
         lemma_extend rel start b a known;
         lemma_extend_reachable rel r start rest (a :: known))
       else lemma_extend_reachable rel r start rest known
     | None -> lemma_extend_reachable rel r start rest known)

let rec lemma_reachable (rel:relation_semantics) (r:relation) (start:expr)
                        (js:list judgment) (known:list expr) (fuel:nat)
  : Lemma (requires symmetric rel /\ transitive rel /\ edges_hold rel r js /\
                    reachable_sound rel start known)
          (ensures reachable_sound rel start (reachable fuel r js known))
          (decreases fuel) =
  if fuel > 0 then (
    lemma_extend_reachable rel r start js known;
    lemma_reachable rel r start js (extend_reachable r js known) (fuel - 1))
