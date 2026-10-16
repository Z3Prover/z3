module Z3BooleanNormalForm

open FStar.List.Tot
module B = Z3BoundedBoolEquiv
type formula = B.skeleton

let dual (op:B.nary_op) : B.nary_op =
  match op with B.And -> B.Or | B.Or -> B.And | B.Xor -> B.Xor

let rec join (op:B.nary_op) (xs:list formula) : Tot (list formula) (decreases xs) =
  match xs with
  | [] -> []
  | B.Nary other args :: rest ->
    if op = other then args @ join op rest
    else B.Nary other args :: join op rest
  | x :: rest -> x :: join op rest

let rec common_member (xs ys:list formula) : Tot (option formula) (decreases xs) =
  match xs with
  | [] -> None
  | x :: rest -> if mem x ys then Some x else common_member rest ys

let complementary (x y:formula) : bool =
  match x, y with
  | B.Not a, _ -> a = y
  | _, B.Not b -> x = b
  | _, _ -> false

let rec has_complement (x:formula) (ys:list formula) : Tot bool (decreases ys) =
  match ys with
  | [] -> false
  | y :: rest -> complementary x y || has_complement x rest

let absorbed (op:B.nary_op) (x:formula) (ys:list formula) : bool =
  match x with
  | B.Nary other args -> other = dual op && Some? (common_member args ys)
  | _ -> false

let rec prune_absorbed (op:B.nary_op) (x:formula) (ys:list formula)
  : Tot (list formula) (decreases ys) =
  match ys with
  | [] -> []
  | y :: rest ->
    if absorbed op y [x] then prune_absorbed op x rest
    else y :: prune_absorbed op x rest

let insert (op:B.nary_op) (x:formula) (ys:list formula) : list formula =
  let unit = B.Bool (B.neutral op) in
  let zero = B.Bool (not (B.neutral op)) in
  if x = unit then ys
  else if x = zero || ys = [zero] || has_complement x ys then [zero]
  else if mem x ys || absorbed op x ys then ys
  else x :: prune_absorbed op x ys

let rec reduce_args (op:B.nary_op) (xs:list formula)
  : Tot (list formula) (decreases xs) =
  match xs with
  | [] -> []
  | x :: rest -> insert op x (reduce_args op rest)

let make_nary (op:B.nary_op) (xs:list formula) : formula =
  match reduce_args op (join op xs) with
  | [] -> B.Bool (B.neutral op)
  | [x] -> x
  | ys -> B.Nary op ys

let rec normalize (negative:bool) (s:formula) : Tot formula (decreases s) =
  match s with
  | B.Atom _ -> if negative then B.Not s else s
  | B.Bool b -> B.Bool (if negative then not b else b)
  | B.Not a -> normalize (not negative) a
  | B.Nary op args ->
    if op = B.Xor then
      let result = B.Nary op (normalize_args false args) in
      if negative then B.Not result else result
    else
      let next = if negative then dual op else op in
      make_nary next (normalize_args negative args)
  | B.Implies a b ->
    let next = if negative then B.And else B.Or in
    make_nary next [normalize (not negative) a; normalize negative b]
  | B.Eq a b ->
    let result = B.Eq (normalize false a) (normalize false b) in
    if negative then B.Not result else result

and normalize_args (negative:bool) (args:list formula)
  : Tot (list formula) (decreases args) =
  match args with
  | [] -> []
  | a :: rest -> normalize negative a :: normalize_args negative rest

let rec lemma_eval_append (rho:Z3AstTheory.expr -> bool) (op:B.nary_op)
                          (xs ys:list formula)
  : Lemma (B.eval_args rho op (xs @ ys) ==
           B.combine op (B.eval_args rho op xs) (B.eval_args rho op ys))
          (decreases xs) =
  match xs with [] -> () | _ :: rest -> lemma_eval_append rho op rest ys

let rec lemma_join_sound (rho:Z3AstTheory.expr -> bool) (op:B.nary_op)
                         (xs:list formula)
  : Lemma (B.eval_args rho op (join op xs) == B.eval_args rho op xs)
          (decreases xs) =
  match xs with
  | [] -> ()
  | B.Nary other args :: rest ->
    lemma_join_sound rho op rest;
    if op = other then lemma_eval_append rho op args (join op rest)
  | _ :: rest -> lemma_join_sound rho op rest

let rec lemma_member_eval (rho:Z3AstTheory.expr -> bool) (x:formula) (ys:list formula)
  : Lemma (requires mem x ys)
          (ensures (B.eval_args rho B.And ys ==> B.eval rho x) /\
                   (B.eval rho x ==> B.eval_args rho B.Or ys))
          (decreases ys) =
  match ys with
  | [] -> ()
  | y :: rest -> if x <> y then lemma_member_eval rho x rest

let rec lemma_common_member (xs ys:list formula)
  : Lemma (requires Some? (common_member xs ys))
          (ensures mem (Some?.v (common_member xs ys)) xs /\
                   mem (Some?.v (common_member xs ys)) ys)
          (decreases xs) =
  match xs with
  | [] -> ()
  | x :: rest -> if not (mem x ys) then lemma_common_member rest ys

let rec lemma_complement_sound (rho:Z3AstTheory.expr -> bool)
                               (x:formula) (ys:list formula)
  : Lemma (requires has_complement x ys)
          (ensures not (B.eval_args rho B.And (x :: ys)) /\
                   B.eval_args rho B.Or (x :: ys))
          (decreases ys) =
  match ys with
  | [] -> ()
  | y :: rest ->
    if complementary x y then (match x, y with B.Not _, _ | _, B.Not _ -> () | _, _ -> ())
    else lemma_complement_sound rho x rest

let lemma_absorbed_sound (rho:Z3AstTheory.expr -> bool) (op:B.nary_op)
                        (x:formula) (ys:list formula)
  : Lemma (requires op <> B.Xor /\ absorbed op x ys)
          (ensures B.eval_args rho op (x :: ys) == B.eval_args rho op ys) =
  match x with
  | B.Nary other args ->
    lemma_common_member args ys;
    let a = Some?.v (common_member args ys) in
    lemma_member_eval rho a args;
    lemma_member_eval rho a ys;
    (match op with B.And | B.Or | B.Xor -> ())
  | _ -> ()

let rec lemma_prune_absorbed_sound (rho:Z3AstTheory.expr -> bool) (op:B.nary_op)
                                  (x:formula) (ys:list formula)
  : Lemma (requires op <> B.Xor /\ B.eval rho x == B.neutral op)
          (ensures B.eval_args rho op (prune_absorbed op x ys) == B.eval_args rho op ys)
          (decreases ys) =
  match ys with
  | [] -> ()
  | y :: rest ->
    lemma_prune_absorbed_sound rho op x rest;
    if absorbed op y [x] then (
      lemma_absorbed_sound rho op y [x];
      match op with B.And | B.Or | B.Xor -> ())

let lemma_insert_sound (rho:Z3AstTheory.expr -> bool) (op:B.nary_op)
                       (x:formula) (ys:list formula)
  : Lemma (requires op <> B.Xor)
          (ensures B.eval_args rho op (insert op x ys) == B.eval_args rho op (x :: ys)) =
  let unit = B.Bool (B.neutral op) in
  let zero = B.Bool (not (B.neutral op)) in
  if x = unit || x = zero || ys = [zero] then ()
  else if has_complement x ys then (
    lemma_complement_sound rho x ys;
    match op with B.And | B.Or | B.Xor -> ())
  else if mem x ys then (
    lemma_member_eval rho x ys;
    match op with B.And | B.Or | B.Xor -> ())
  else if absorbed op x ys then lemma_absorbed_sound rho op x ys
  else if B.eval rho x = B.neutral op then lemma_prune_absorbed_sound rho op x ys
  else (match op with B.And | B.Or | B.Xor -> ())

let rec lemma_reduce_args_sound (rho:Z3AstTheory.expr -> bool) (op:B.nary_op)
                               (xs:list formula)
  : Lemma (requires op <> B.Xor)
          (ensures B.eval_args rho op (reduce_args op xs) == B.eval_args rho op xs)
          (decreases xs) =
  match xs with
  | [] -> ()
  | x :: rest ->
    lemma_reduce_args_sound rho op rest;
    lemma_insert_sound rho op x (reduce_args op rest)

let lemma_make_nary_sound (rho:Z3AstTheory.expr -> bool) (op:B.nary_op) (xs:list formula)
  : Lemma (requires op <> B.Xor)
          (ensures B.eval rho (make_nary op xs) == B.eval_args rho op xs) =
  lemma_join_sound rho op xs;
  lemma_reduce_args_sound rho op (join op xs);
  match reduce_args op (join op xs) with [] | [_] -> () | _ -> ()

let rec lemma_normalize_sound (rho:Z3AstTheory.expr -> bool) (negative:bool) (s:formula)
  : Lemma (B.eval rho (normalize negative s) ==
           (if negative then not (B.eval rho s) else B.eval rho s))
          (decreases s) =
  match s with
  | B.Atom _ | B.Bool _ -> ()
  | B.Not a -> lemma_normalize_sound rho (not negative) a
  | B.Nary op args ->
    if op = B.Xor then lemma_normalize_args_sound rho false op args
    else (
      lemma_normalize_args_sound rho negative op args;
      lemma_make_nary_sound rho (if negative then dual op else op) (normalize_args negative args))
  | B.Implies a b ->
    lemma_normalize_sound rho (not negative) a;
    lemma_normalize_sound rho negative b;
    lemma_make_nary_sound rho (if negative then B.And else B.Or)
      [normalize (not negative) a; normalize negative b]
  | B.Eq a b ->
    lemma_normalize_sound rho false a;
    lemma_normalize_sound rho false b

and lemma_normalize_args_sound (rho:Z3AstTheory.expr -> bool) (negative:bool)
                               (op:B.nary_op) (args:list formula)
  : Lemma (requires not negative \/ op <> B.Xor)
          (ensures
            B.eval_args rho (if negative then dual op else op) (normalize_args negative args) ==
            (if negative then not (B.eval_args rho op args) else B.eval_args rho op args))
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_normalize_sound rho negative a;
    lemma_normalize_args_sound rho negative op rest

(* Set matching proves associativity/commutativity/idempotence without
   enumerating assignments. Fuel bounds recursive contextual comparison. *)
let rec shape_equal (fuel:nat) (s t:formula)
  : Tot bool (decreases %[fuel; 0]) =
  if s = t then true
  else if fuel = 0 then false
  else match s, t with
  | B.Not a, B.Not b -> shape_equal (fuel - 1) a b
  | B.Eq a b, B.Eq c d ->
    (shape_equal (fuel - 1) a c && shape_equal (fuel - 1) b d) ||
    (shape_equal (fuel - 1) a d && shape_equal (fuel - 1) b c)
  | B.Nary op xs, B.Nary other ys ->
    op = other && op <> B.Xor &&
    shape_included (fuel - 1) xs ys && shape_included (fuel - 1) ys xs
  | _, _ -> false

and shape_included (fuel:nat) (xs ys:list formula)
  : Tot bool (decreases %[fuel; length xs + length ys + 1]) =
  match xs with
  | [] -> true
  | x :: rest -> shape_member fuel x ys && shape_included fuel rest ys

and shape_member (fuel:nat) (x:formula) (ys:list formula)
  : Tot bool (decreases %[fuel; length ys]) =
  match ys with
  | [] -> false
  | y :: rest ->
    (fuel > 0 && shape_equal (fuel - 1) x y) || shape_member fuel x rest

let rec lemma_shape_equal_sound (rho:Z3AstTheory.expr -> bool)
                               (fuel:nat) (s t:formula)
  : Lemma (requires shape_equal fuel s t)
          (ensures B.eval rho s == B.eval rho t)
          (decreases %[fuel; 0]) =
  if s = t || fuel = 0 then ()
  else match s, t with
  | B.Not a, B.Not b -> lemma_shape_equal_sound rho (fuel - 1) a b
  | B.Eq a b, B.Eq c d ->
    if shape_equal (fuel - 1) a c && shape_equal (fuel - 1) b d then (
      lemma_shape_equal_sound rho (fuel - 1) a c;
      lemma_shape_equal_sound rho (fuel - 1) b d)
    else (
      lemma_shape_equal_sound rho (fuel - 1) a d;
      lemma_shape_equal_sound rho (fuel - 1) b c)
  | B.Nary op xs, B.Nary other ys ->
    lemma_shape_included_sound rho (fuel - 1) xs ys;
    lemma_shape_included_sound rho (fuel - 1) ys xs;
    (match op with B.And | B.Or | B.Xor -> ())
  | _, _ -> ()

and lemma_shape_included_sound (rho:Z3AstTheory.expr -> bool)
                              (fuel:nat) (xs ys:list formula)
  : Lemma (requires shape_included fuel xs ys)
          (ensures
            (B.eval_args rho B.And ys ==> B.eval_args rho B.And xs) /\
            (B.eval_args rho B.Or xs ==> B.eval_args rho B.Or ys))
          (decreases %[fuel; length xs + length ys + 1]) =
  match xs with
  | [] -> ()
  | x :: rest ->
    lemma_shape_member_sound rho fuel x ys;
    lemma_shape_included_sound rho fuel rest ys

and lemma_shape_member_sound (rho:Z3AstTheory.expr -> bool)
                            (fuel:nat) (x:formula) (ys:list formula)
  : Lemma (requires shape_member fuel x ys)
          (ensures
            (B.eval_args rho B.And ys ==> B.eval rho x) /\
            (B.eval rho x ==> B.eval_args rho B.Or ys))
          (decreases %[fuel; length ys]) =
  match ys with
  | [] -> ()
  | y :: rest ->
    if fuel > 0 && shape_equal (fuel - 1) x y
    then lemma_shape_equal_sound rho (fuel - 1) x y
    else lemma_shape_member_sound rho fuel x rest

let equivalent (s t:formula) : bool =
  shape_equal 32 (normalize false s) (normalize false t)

let lemma_equivalent_sound (rho:Z3AstTheory.expr -> bool) (s t:formula)
  : Lemma (requires equivalent s t)
          (ensures B.eval rho s == B.eval rho t) =
  lemma_normalize_sound rho false s;
  lemma_normalize_sound rho false t;
  lemma_shape_equal_sound rho 32 (normalize false s) (normalize false t)

(* Propagate the assumption that every disjunct is false. Unlike a truth
   table, this handles an arbitrarily wide Tseitin gate without branching. *)
let rec forced (negative:list formula) (s:formula) (truth:bool)
  : Tot bool (decreases s) =
  (if truth then has_complement s negative else mem s negative) ||
  (match s with
   | B.Atom _ -> false
   | B.Bool b -> b = truth
   | B.Not a -> forced negative a (not truth)
   | B.Nary B.And args ->
     if truth then forced_all negative true args else forced_any negative false args
   | B.Nary B.Or args ->
     if truth then forced_any negative true args else forced_all negative false args
   | B.Nary B.Xor [a; b] ->
     (forced negative a true && forced negative b (not truth)) ||
     (forced negative a false && forced negative b truth)
   | B.Nary B.Xor _ -> false
   | B.Implies a b ->
     if truth then forced negative a false || forced negative b true
     else forced negative a true && forced negative b false
   | B.Eq a b ->
     (forced negative a true && forced negative b truth) ||
     (forced negative a false && forced negative b (not truth)))

and forced_all (negative:list formula) (truth:bool) (args:list formula)
  : Tot bool (decreases args) =
  match args with
  | [] -> true
  | a :: rest -> forced negative a truth && forced_all negative truth rest

and forced_any (negative:list formula) (truth:bool) (args:list formula)
  : Tot bool (decreases args) =
  match args with
  | [] -> false
  | a :: rest -> forced negative a truth || forced_any negative truth rest

let rec lemma_forced_sound (rho:Z3AstTheory.expr -> bool)
                           (negative:list formula) (s:formula) (truth:bool)
  : Lemma (requires not (B.eval_args rho B.Or negative) /\ forced negative s truth)
          (ensures B.eval rho s == truth)
          (decreases s) =
  if truth && has_complement s negative then lemma_complement_sound rho s negative
  else if not truth && mem s negative then lemma_member_eval rho s negative
  else match s with
  | B.Atom _ | B.Bool _ -> ()
  | B.Not a -> lemma_forced_sound rho negative a (not truth)
  | B.Nary B.And args ->
    if truth then lemma_forced_all_sound rho negative true args
    else lemma_forced_any_sound rho negative false args
  | B.Nary B.Or args ->
    if truth then lemma_forced_any_sound rho negative true args
    else lemma_forced_all_sound rho negative false args
  | B.Nary B.Xor [a; b] ->
    if forced negative a true && forced negative b (not truth) then (
      lemma_forced_sound rho negative a true;
      lemma_forced_sound rho negative b (not truth))
    else (
      lemma_forced_sound rho negative a false;
      lemma_forced_sound rho negative b truth)
  | B.Nary B.Xor _ -> ()
  | B.Implies a b ->
    if truth then (
      if forced negative a false then lemma_forced_sound rho negative a false
      else lemma_forced_sound rho negative b true)
    else (
      lemma_forced_sound rho negative a true;
      lemma_forced_sound rho negative b false)
  | B.Eq a b ->
    if forced negative a true && forced negative b truth then (
      lemma_forced_sound rho negative a true;
      lemma_forced_sound rho negative b truth)
    else (
      lemma_forced_sound rho negative a false;
      lemma_forced_sound rho negative b (not truth))

and lemma_forced_all_sound (rho:Z3AstTheory.expr -> bool)
                          (negative:list formula) (truth:bool) (args:list formula)
  : Lemma (requires not (B.eval_args rho B.Or negative) /\ forced_all negative truth args)
          (ensures (if truth then B.eval_args rho B.And args
                    else not (B.eval_args rho B.Or args)))
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_forced_sound rho negative a truth;
    lemma_forced_all_sound rho negative truth rest

and lemma_forced_any_sound (rho:Z3AstTheory.expr -> bool)
                          (negative:list formula) (truth:bool) (args:list formula)
  : Lemma (requires not (B.eval_args rho B.Or negative) /\ forced_any negative truth args)
          (ensures (if truth then B.eval_args rho B.Or args
                    else not (B.eval_args rho B.And args)))
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    if forced negative a truth then lemma_forced_sound rho negative a truth
    else lemma_forced_any_sound rho negative truth rest

let disjuncts (s:formula) : list formula =
  match s with B.Nary B.Or args -> args | _ -> [s]

let clause_tautology (s:formula) : bool =
  forced (disjuncts s) s true

let lemma_clause_tautology_sound (rho:Z3AstTheory.expr -> bool) (s:formula)
  : Lemma (requires clause_tautology s)
          (ensures B.eval rho s) =
  FStar.Classical.excluded_middle (B.eval rho s);
  if not (B.eval rho s) then (
    (match s with B.Nary B.Or _ -> () | _ -> ());
    lemma_forced_sound rho (disjuncts s) s true)
