module Z3ArrayIndexDependencies

open FStar.FunctionalExtensionality
open Z3ArrayTheory
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module C = FStar.Classical

let rec deps_hold (#term:eqtype) (#idx:eqtype) (eval:term -> idx)
                 (eqs:list (term & term)) : bool =
  match eqs with
  | [] -> true
  | (t, r) :: rest -> eval t = eval r && deps_hold eval rest

let rec find_index (#term:eqtype) (same:term -> term -> bool)
                   (t:term) (reps:list term)
  : Tot (r:option term{match r with None -> True | Some r -> L.mem r reps}) =
  match reps with
  | [] -> None
  | r :: rest -> if same t r then Some r else find_index same t rest

(* Store indices are visited outermost first, along both reachability paths.
   The equality list is logically unordered; representatives retain scan order. *)
let rec collect (#term:eqtype) (same:term -> term -> bool)
                (terms reps:list term) : list term & list (term & term) =
  match terms with
  | [] -> reps, []
  | t :: rest ->
    match find_index same t reps with
    | None -> collect same rest (L.append reps [t])
    | Some r ->
      let out, eqs = collect same rest reps in
      out, (t, r) :: eqs

let rec lemma_map_mem (#term #idx:eqtype) (eval:term -> idx)
                      (terms:list term) (t:term)
  : Lemma (requires L.mem t terms)
          (ensures L.mem (eval t) (L.map eval terms)) =
  match terms with
  | [] -> ()
  | h :: rest -> if t = h then () else lemma_map_mem eval rest t

let rec lemma_collect_covers (#term #idx:eqtype)
                            (same:term -> term -> bool) (eval:term -> idx)
                            (terms reps:list term) (t:term)
  : Lemma (requires deps_hold eval (snd (collect same terms reps)))
          (ensures (L.mem t terms \/ L.mem t reps) ==>
                   L.mem (eval t) (L.map eval (fst (collect same terms reps))))
          (decreases terms) =
  match terms with
  | [] -> if L.mem t reps then lemma_map_mem eval reps t
  | h :: rest ->
    match find_index same h reps with
    | None ->
      LP.append_mem reps [h] t;
      lemma_collect_covers same eval rest (L.append reps [h]) t
    | Some r ->
      lemma_collect_covers same eval rest reps t;
      if t = h then lemma_collect_covers same eval rest reps r

(* C++ records each non-identical coordinate, not just one component of
   a multi-index store. Identical enodes need no explicit antecedent. *)
let rec coordinate_eqs (#term:eqtype) (xs ys:list term) : list (term & term) =
  match xs, ys with
  | x :: xt, y :: yt ->
    let rest = coordinate_eqs xt yt in
    if x = y then rest else (x, y) :: rest
  | _ -> []

let rec lemma_coordinate_eqs (#term #idx:eqtype) (eval:term -> idx)
                             (xs ys:list term)
  : Lemma (requires L.length xs = L.length ys /\
                    deps_hold eval (coordinate_eqs xs ys))
          (ensures L.map eval xs == L.map eval ys)
          (decreases xs) =
  match xs, ys with
  | x :: xt, y :: yt -> lemma_coordinate_eqs eval xt yt
  | _ -> ()

let rec lemma_deps_append (#term #idx:eqtype) (eval:term -> idx)
                          (xs ys:list (term & term))
  : Lemma (deps_hold eval (L.append xs ys) =
           (deps_hold eval xs && deps_hold eval ys)) =
  match xs with
  | [] -> ()
  | _ :: rest -> lemma_deps_append eval rest ys

let rec matching_arities (#term:eqtype) (pairs:list (list term & list term)) : bool =
  match pairs with
  | [] -> true
  | (xs, ys) :: rest -> L.length xs = L.length ys && matching_arities rest

let rec coordinate_dependencies (#term:eqtype)
                                 (pairs:list (list term & list term))
  : list (term & term) =
  match pairs with
  | [] -> []
  | (xs, ys) :: rest ->
    L.append (coordinate_eqs xs ys) (coordinate_dependencies rest)

let rec lemma_tuple_dependencies (#term #idx:eqtype) (eval:term -> idx)
                                 (pairs:list (list term & list term))
  : Lemma (requires matching_arities pairs /\
                    deps_hold eval (coordinate_dependencies pairs))
          (ensures deps_hold (L.map eval) pairs) =
  match pairs with
  | [] -> ()
  | (xs, ys) :: rest ->
    lemma_deps_append eval (coordinate_eqs xs ys) (coordinate_dependencies rest);
    lemma_coordinate_eqs eval xs ys;
    lemma_tuple_dependencies eval rest

let rec distinct (#idx:eqtype) (xs:list idx) : bool =
  match xs with
  | [] -> true
  | x :: rest -> not (L.mem x rest) && distinct rest

let rec remove_one (#idx:eqtype) (x:idx) (xs:list idx) : list idx =
  match xs with
  | [] -> []
  | h :: rest -> if x = h then rest else h :: remove_one x rest

let rec lemma_remove_length (#idx:eqtype) (x:idx) (xs:list idx)
  : Lemma (requires L.mem x xs)
          (ensures L.length (remove_one x xs) + 1 = L.length xs) =
  match xs with
  | [] -> ()
  | h :: rest -> if x = h then () else lemma_remove_length x rest

let rec lemma_remove_other (#idx:eqtype) (x y:idx) (xs:list idx)
  : Lemma (requires x <> y)
          (ensures L.mem y (remove_one x xs) = L.mem y xs) =
  match xs with
  | [] -> ()
  | h :: rest -> if x = h then () else lemma_remove_other x y rest

let rec lemma_covered_size (#idx:eqtype) (domain reps:list idx)
  : Lemma (requires distinct domain /\
                    (forall k. L.mem k domain ==> L.mem k reps))
          (ensures L.length domain <= L.length reps)
          (decreases domain) =
  match domain with
  | [] -> ()
  | h :: rest ->
    lemma_remove_length h reps;
    let covered (k:idx) : Lemma (L.mem k rest ==> L.mem k (remove_one h reps)) =
      if L.mem k rest then lemma_remove_other h k reps
    in
    C.forall_intro covered;
    lemma_covered_size rest (remove_one h reps)

let lemma_uncovered (#idx:eqtype) (domain reps:list idx)
  : Lemma (requires distinct domain /\ L.length reps < L.length domain)
          (ensures exists k. L.mem k domain /\ not (L.mem k reps)) =
  C.excluded_middle (exists k. L.mem k domain /\ not (L.mem k reps));
  if not (exists k. L.mem k domain /\ not (L.mem k reps)) then
    lemma_covered_size domain reps

let rec chain (#term #idx:eqtype) (#v:Type) (eval:term -> idx)
              (base:v) (updates:list (term & v)) : arr idx v =
  match updates with
  | [] -> const_arr base
  | (t, value) :: rest -> store (chain eval base rest) (eval t) value

let rec keys (#term:eqtype) (#v:Type) (updates:list (term & v)) : list term =
  match updates with
  | [] -> []
  | (t, _) :: rest -> t :: keys rest

let rec lemma_chain_uncovered (#term #idx:eqtype) (#v:Type)
                               (eval:term -> idx) (base:v)
                               (updates:list (term & v)) (reps:list idx) (k:idx)
  : Lemma (requires not (L.mem k reps) /\
                    (forall t. L.mem t (keys updates) ==> L.mem (eval t) reps))
          (ensures select (chain eval base updates) k == base)
          (decreases updates) =
  match updates with
  | [] -> ()
  | (t, value) :: rest ->
    lemma_chain_uncovered eval base rest reps k;
    lemma_select_store_diff (chain eval base rest) (eval t) k value

let rec lemma_map_length (#term #idx:eqtype) (eval:term -> idx) (xs:list term)
  : Lemma (L.length (L.map eval xs) = L.length xs) =
  match xs with
  | [] -> ()
  | _ :: rest -> lemma_map_length eval rest

(* Finite-domain form of the propagation rule. No uniqueness of the
   representative values is required: their list length is an upper bound. *)
let lemma_fixed_propagation (#term #idx:eqtype) (#v:Type)
                            (same:term -> term -> bool) (eval:term -> idx)
                            (domain:list idx) (base1 base2:v)
                            (us1 us2:list (term & v))
  : Lemma
      (requires
        distinct domain /\
        L.length (fst (collect same (L.append (keys us1) (keys us2)) [])) <
          L.length domain /\
        deps_hold eval (snd (collect same (L.append (keys us1) (keys us2)) [])) /\
        chain eval base1 us1 == chain eval base2 us2)
      (ensures base1 == base2) =
  let terms = L.append (keys us1) (keys us2) in
  let reps = fst (collect same terms []) in
  let values = L.map eval reps in
  let covered (t:term) : Lemma (L.mem t terms ==> L.mem (eval t) values) =
    lemma_collect_covers same eval terms [] t
  in
  C.forall_intro covered;
  let covered1 (t:term) : Lemma (L.mem t (keys us1) ==> L.mem (eval t) values) =
    LP.append_mem (keys us1) (keys us2) t
  in
  let covered2 (t:term) : Lemma (L.mem t (keys us2) ==> L.mem (eval t) values) =
    LP.append_mem (keys us1) (keys us2) t
  in
  C.forall_intro covered1;
  C.forall_intro covered2;
  lemma_map_length eval reps;
  lemma_uncovered domain values;
  let at_uncovered (k:idx)
    : Lemma ((L.mem k domain /\ not (L.mem k values)) ==> base1 == base2) =
    if L.mem k domain && not (L.mem k values) then begin
      lemma_chain_uncovered eval base1 us1 values k;
      lemma_chain_uncovered eval base2 us2 values k
    end
  in
  C.forall_to_exists at_uncovered

type d = | A | B | Cc
type term = | Ta | Tb | Tx

let eval_at (x:d) (t:term) : d =
  match t with Ta -> A | Tb -> B | Tx -> x

let branch_root (t:term) : nat = if t = Tb then 1 else 0
let same_root (t r:term) : bool = branch_root t = branch_root r
let issue_updates : list (term & bool) = [(Tx, false); (Tb, false); (Ta, false)]

(* The old explanation permits this countermodel, although it was generated
   while Tx and Ta shared an egraph root. The new explanation excludes it. *)
let lemma_old_omission_countermodel ()
  : Lemma
      (feq (chain (eval_at Cc) true issue_updates) (const_arr #d false) /\
       true <> false /\
       L.length (fst (collect same_root (keys issue_updates) [])) = 2 /\
       not (deps_hold (eval_at Cc) (snd (collect same_root (keys issue_updates) [])))) =
  let pointwise (k:d)
    : Lemma (select (chain (eval_at Cc) true issue_updates) k == false) =
    match k with A -> () | B -> () | Cc -> ()
  in
  C.forall_intro pointwise

let lemma_duplicate_branch_is_conflicting (x:d)
  : Lemma (requires x = A \/ x = B)
          (ensures select (chain (eval_at x) true issue_updates) Cc == true)
  = ()

let lemma_each_tuple_component_is_needed ()
  : Lemma
      (fst (A, false) = fst (A, true) /\ (A, false) <> (A, true) /\
       snd (A, false) = snd (B, false) /\ (A, false) <> (B, false))
  = ()
