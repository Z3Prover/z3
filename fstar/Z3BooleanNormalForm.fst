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

let make_not (s:formula) : formula =
  match s with B.Bool b -> B.Bool (not b) | B.Not a -> a | _ -> B.Not s

let make_eq (s t:formula) : formula =
  if s = t then B.Bool true
  else match s, t with
  | B.Bool b, _ -> if b then t else make_not t
  | _, B.Bool b -> if b then s else make_not s
  | B.Not a, B.Not b -> B.Eq a b
  | B.Not a, _ -> B.Not (B.Eq a t)
  | _, B.Not b -> B.Not (B.Eq s b)
  | _, _ -> B.Eq s t

let lemma_make_not_sound (rho:Z3AstTheory.expr -> bool) (s:formula)
  : Lemma (B.eval rho (make_not s) == not (B.eval rho s)) =
  match s with B.Bool _ | B.Not _ -> () | _ -> ()

let lemma_make_eq_sound (rho:Z3AstTheory.expr -> bool) (s t:formula)
  : Lemma (B.eval rho (make_eq s t) == (B.eval rho s = B.eval rho t)) =
  if s = t then ()
  else match s, t with
  | B.Bool _, _ -> lemma_make_not_sound rho t
  | _, B.Bool _ -> lemma_make_not_sound rho s
  | _, _ -> ()

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
    let result = make_eq (normalize false a) (normalize false b) in
    if negative then make_not result else result

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
    lemma_normalize_sound rho false b;
    lemma_make_eq_sound rho (normalize false a) (normalize false b);
    if negative then lemma_make_not_sound rho (make_eq (normalize false a) (normalize false b))

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
let rec shape_equal_by (same:Z3AstTheory.expr -> Z3AstTheory.expr -> Tot bool)
                      (fuel:nat) (s t:formula)
  : Tot bool (decreases %[fuel; 0]) =
  if s = t then true
  else if fuel = 0 then false
  else match s, t with
  | B.Atom a, B.Atom b -> same a b
  | B.Not a, B.Not b -> shape_equal_by same (fuel - 1) a b
  | B.Eq a b, B.Eq c d ->
    (shape_equal_by same (fuel - 1) a c && shape_equal_by same (fuel - 1) b d) ||
    (shape_equal_by same (fuel - 1) a d && shape_equal_by same (fuel - 1) b c)
  | B.Nary op xs, B.Nary other ys ->
    op = other && op <> B.Xor &&
    shape_included_by same (fuel - 1) xs ys && shape_included_by same (fuel - 1) ys xs
  | _, _ -> false

and shape_included_by (same:Z3AstTheory.expr -> Z3AstTheory.expr -> Tot bool)
                      (fuel:nat) (xs ys:list formula)
  : Tot bool (decreases %[fuel; length xs + length ys + 1]) =
  match xs with
  | [] -> true
  | x :: rest -> shape_member_by same fuel x ys && shape_included_by same fuel rest ys

and shape_member_by (same:Z3AstTheory.expr -> Z3AstTheory.expr -> Tot bool)
                    (fuel:nat) (x:formula) (ys:list formula)
  : Tot bool (decreases %[fuel; length ys]) =
  match ys with
  | [] -> false
  | y :: rest ->
    (fuel > 0 && shape_equal_by same (fuel - 1) x y) || shape_member_by same fuel x rest

let rec lemma_shape_equal_by_sound (rho:Z3AstTheory.expr -> bool)
                                  (same:Z3AstTheory.expr -> Z3AstTheory.expr -> Tot bool)
                                  (fuel:nat) (s t:formula)
  : Lemma (requires shape_equal_by same fuel s t /\
                    (forall (a b:Z3AstTheory.expr). same a b ==> rho a == rho b))
          (ensures B.eval rho s == B.eval rho t)
          (decreases %[fuel; 0]) =
  if s = t || fuel = 0 then ()
  else match s, t with
  | B.Atom _, B.Atom _ -> ()
  | B.Not a, B.Not b -> lemma_shape_equal_by_sound rho same (fuel - 1) a b
  | B.Eq a b, B.Eq c d ->
    if shape_equal_by same (fuel - 1) a c && shape_equal_by same (fuel - 1) b d then (
      lemma_shape_equal_by_sound rho same (fuel - 1) a c;
      lemma_shape_equal_by_sound rho same (fuel - 1) b d)
    else (
      lemma_shape_equal_by_sound rho same (fuel - 1) a d;
      lemma_shape_equal_by_sound rho same (fuel - 1) b c)
  | B.Nary op xs, B.Nary other ys ->
    lemma_shape_included_by_sound rho same (fuel - 1) xs ys;
    lemma_shape_included_by_sound rho same (fuel - 1) ys xs;
    (match op with B.And | B.Or | B.Xor -> ())
  | _, _ -> ()

and lemma_shape_included_by_sound (rho:Z3AstTheory.expr -> bool)
                                 (same:Z3AstTheory.expr -> Z3AstTheory.expr -> Tot bool)
                                 (fuel:nat) (xs ys:list formula)
  : Lemma (requires shape_included_by same fuel xs ys /\
                    (forall (a b:Z3AstTheory.expr). same a b ==> rho a == rho b))
          (ensures
            (B.eval_args rho B.And ys ==> B.eval_args rho B.And xs) /\
            (B.eval_args rho B.Or xs ==> B.eval_args rho B.Or ys))
          (decreases %[fuel; length xs + length ys + 1]) =
  match xs with
  | [] -> ()
  | x :: rest ->
    lemma_shape_member_by_sound rho same fuel x ys;
    lemma_shape_included_by_sound rho same fuel rest ys

and lemma_shape_member_by_sound (rho:Z3AstTheory.expr -> bool)
                               (same:Z3AstTheory.expr -> Z3AstTheory.expr -> Tot bool)
                               (fuel:nat) (x:formula) (ys:list formula)
  : Lemma (requires shape_member_by same fuel x ys /\
                    (forall (a b:Z3AstTheory.expr). same a b ==> rho a == rho b))
          (ensures
            (B.eval_args rho B.And ys ==> B.eval rho x) /\
            (B.eval rho x ==> B.eval_args rho B.Or ys))
          (decreases %[fuel; length ys]) =
  match ys with
  | [] -> ()
  | y :: rest ->
    if fuel > 0 && shape_equal_by same (fuel - 1) x y
    then lemma_shape_equal_by_sound rho same (fuel - 1) x y
    else lemma_shape_member_by_sound rho same fuel x rest

let shape_equal (fuel:nat) (s t:formula) : bool =
  shape_equal_by (fun a b -> a = b) fuel s t

let shape_included (fuel:nat) (xs ys:list formula) : bool =
  shape_included_by (fun a b -> a = b) fuel xs ys

let shape_member (fuel:nat) (x:formula) (ys:list formula) : bool =
  shape_member_by (fun a b -> a = b) fuel x ys

let lemma_shape_equal_sound (rho:Z3AstTheory.expr -> bool) (fuel:nat) (s t:formula)
  : Lemma (requires shape_equal fuel s t)
          (ensures B.eval rho s == B.eval rho t) =
  lemma_shape_equal_by_sound rho (fun a b -> a = b) fuel s t

let lemma_shape_included_sound (rho:Z3AstTheory.expr -> bool)
                              (fuel:nat) (xs ys:list formula)
  : Lemma (requires shape_included fuel xs ys)
          (ensures
            (B.eval_args rho B.And ys ==> B.eval_args rho B.And xs) /\
            (B.eval_args rho B.Or xs ==> B.eval_args rho B.Or ys)) =
  lemma_shape_included_by_sound rho (fun a b -> a = b) fuel xs ys

let lemma_shape_member_sound (rho:Z3AstTheory.expr -> bool)
                            (fuel:nat) (x:formula) (ys:list formula)
  : Lemma (requires shape_member fuel x ys)
          (ensures
            (B.eval_args rho B.And ys ==> B.eval rho x) /\
            (B.eval rho x ==> B.eval_args rho B.Or ys)) =
  lemma_shape_member_by_sound rho (fun a b -> a = b) fuel x ys

let normal_equivalent (s t:formula) : bool =
  shape_equal 32 (normalize false s) (normalize false t)

let lemma_normal_equivalent_sound (rho:Z3AstTheory.expr -> bool) (s t:formula)
  : Lemma (requires normal_equivalent s t)
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

(* Compute both polarities once; separate recursive queries duplicate nested equalities. *)
let rec forced_pair (negative:list formula) (s:formula)
  : Tot (bool & bool) (decreases s) =
  let positive, negative_result =
    match s with
    | B.Atom _ -> false, false
    | B.Bool b -> b, not b
    | B.Not a ->
      let p, n = forced_pair negative a in n, p
    | B.Nary B.Xor [a; b] ->
      let ap, an = forced_pair negative a in
      let bp, bn = forced_pair negative b in
      (ap && bn) || (an && bp), (ap && bp) || (an && bn)
    | B.Nary op args ->
      if op = B.Xor then false, false else forced_pair_args negative op args
    | B.Implies a b ->
      let ap, an = forced_pair negative a in
      let bp, bn = forced_pair negative b in
      an || bp, ap && bn
    | B.Eq a b ->
      let ap, an = forced_pair negative a in
      let bp, bn = forced_pair negative b in
      (ap && bp) || (an && bn), (ap && bn) || (an && bp) in
  has_complement s negative || positive, mem s negative || negative_result

and forced_pair_args (negative:list formula) (op:B.nary_op{op <> B.Xor}) (args:list formula)
  : Tot (bool & bool) (decreases args) =
  match args with
  | [] -> B.neutral op, not (B.neutral op)
  | a :: rest ->
    let ap, an = forced_pair negative a in
    let bp, bn = forced_pair_args negative op rest in
    if op = B.And then ap && bp, an || bn else ap || bp, an && bn

let rec lemma_forced_pair (negative:list formula) (s:formula)
  : Lemma (
      let p, n = forced_pair negative s in
      p == forced negative s true /\ n == forced negative s false)
      (decreases s) =
  match s with
  | B.Atom _ | B.Bool _ -> ()
  | B.Not a -> lemma_forced_pair negative a
  | B.Nary B.Xor [a; b] ->
    lemma_forced_pair negative a;
    lemma_forced_pair negative b
  | B.Nary op args ->
    if op <> B.Xor then lemma_forced_pair_args negative op args
  | B.Implies a b | B.Eq a b ->
    lemma_forced_pair negative a;
    lemma_forced_pair negative b

and lemma_forced_pair_args (negative:list formula) (op:B.nary_op{op <> B.Xor})
                           (args:list formula)
  : Lemma (
      let p, n = forced_pair_args negative op args in
      p == (if op = B.And then forced_all negative true args else forced_any negative true args) /\
      n == (if op = B.And then forced_any negative false args else forced_all negative false args))
      (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_forced_pair negative a;
    lemma_forced_pair_args negative op rest

(* Retain single-polarity short circuits outside equality and XOR. *)
let rec forced_polarity (negative:list formula) (s:formula) (truth:bool)
  : Tot bool (decreases s) =
  (if truth then has_complement s negative else mem s negative) ||
  (match s with
   | B.Atom _ -> false
   | B.Bool b -> b = truth
   | B.Not a -> forced_polarity negative a (not truth)
   | B.Nary B.And args ->
     if truth then forced_polarity_all negative true args else forced_polarity_any negative false args
   | B.Nary B.Or args ->
     if truth then forced_polarity_any negative true args else forced_polarity_all negative false args
   | B.Nary B.Xor [a; b] ->
     let ap, an = forced_pair negative a in
     if not (ap || an) then false else
     let bp, bn = forced_pair negative b in
     if truth then (ap && bn) || (an && bp) else (ap && bp) || (an && bn)
   | B.Nary B.Xor _ -> false
   | B.Implies a b ->
     if truth then forced_polarity negative a false || forced_polarity negative b true
     else forced_polarity negative a true && forced_polarity negative b false
   | B.Eq a b ->
     let ap, an = forced_pair negative a in
     if not (ap || an) then false else
     let bp, bn = forced_pair negative b in
     if truth then (ap && bp) || (an && bn) else (ap && bn) || (an && bp))

and forced_polarity_all (negative:list formula) (truth:bool) (args:list formula)
  : Tot bool (decreases args) =
  match args with
  | [] -> true
  | a :: rest -> forced_polarity negative a truth && forced_polarity_all negative truth rest

and forced_polarity_any (negative:list formula) (truth:bool) (args:list formula)
  : Tot bool (decreases args) =
  match args with
  | [] -> false
  | a :: rest -> forced_polarity negative a truth || forced_polarity_any negative truth rest

let rec lemma_forced_polarity (negative:list formula) (s:formula) (truth:bool)
  : Lemma (forced_polarity negative s truth == forced negative s truth)
          (decreases s) =
  match s with
  | B.Atom _ | B.Bool _ -> ()
  | B.Not a -> lemma_forced_polarity negative a (not truth)
  | B.Nary B.And args ->
    if truth then lemma_forced_polarity_all negative true args
    else lemma_forced_polarity_any negative false args
  | B.Nary B.Or args ->
    if truth then lemma_forced_polarity_any negative true args
    else lemma_forced_polarity_all negative false args
  | B.Nary B.Xor [a; b] | B.Eq a b ->
    lemma_forced_pair negative a;
    lemma_forced_pair negative b
  | B.Nary B.Xor _ -> ()
  | B.Implies a b ->
    lemma_forced_polarity negative a (not truth);
    lemma_forced_polarity negative b truth

and lemma_forced_polarity_all (negative:list formula) (truth:bool) (args:list formula)
  : Lemma (forced_polarity_all negative truth args == forced_all negative truth args)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_forced_polarity negative a truth;
    lemma_forced_polarity_all negative truth rest

and lemma_forced_polarity_any (negative:list formula) (truth:bool) (args:list formula)
  : Lemma (forced_polarity_any negative truth args == forced_any negative truth args)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_forced_polarity negative a truth;
    lemma_forced_polarity_any negative truth rest

let disjuncts (s:formula) : list formula =
  match s with B.Nary B.Or args -> args | _ -> [s]

let clause_tautology (s:formula) : bool =
  forced_polarity (disjuncts s) s true

let lemma_clause_tautology_sound (rho:Z3AstTheory.expr -> bool) (s:formula)
  : Lemma (requires clause_tautology s)
          (ensures B.eval rho s) =
  FStar.Classical.excluded_middle (B.eval rho s);
  lemma_forced_polarity (disjuncts s) s true;
  if not (B.eval rho s) then (
    (match s with B.Nary B.Or _ -> () | _ -> ());
    lemma_forced_sound rho (disjuncts s) s true)

let neutral_assumption (op:B.nary_op) (s:formula) : formula =
  if op = B.Or then s else make_not s

let lemma_neutral_assumption (rho:Z3AstTheory.expr -> bool) (op:B.nary_op) (s:formula)
  : Lemma (requires op <> B.Xor /\ B.eval rho s == B.neutral op)
          (ensures not (B.eval rho (neutral_assumption op s))) =
  lemma_make_not_sound rho s;
  match op with B.And | B.Or | B.Xor -> ()

(* Shared disjuncts may be assumed false when comparing the remaining
   formula. Keep negated compound terms intact to expose complements. *)
let rec specialize (negative:list formula) (s:formula)
  : Tot formula (decreases s) =
  if forced_polarity negative s true then B.Bool true
  else if forced_polarity negative s false then B.Bool false
  else match s with
  | B.Atom _ | B.Bool _ -> s
  | B.Not a -> make_not (specialize negative a)
  | B.Nary op args ->
    let xs = if op = B.Xor then specialize_args negative args
             else specialize_context_args negative op args in
    if op = B.Xor then B.Nary op xs else make_nary op (reduce_args op xs)
  | B.Implies a b ->
    make_nary B.Or [make_not (specialize negative a); specialize negative b]
  | B.Eq a b -> make_eq (specialize negative a) (specialize negative b)

and specialize_args (negative:list formula) (args:list formula)
  : Tot (list formula) (decreases args) =
  match args with
  | [] -> []
  | a :: rest -> specialize negative a :: specialize_args negative rest

and specialize_context_args (negative:list formula) (op:B.nary_op) (args:list formula)
  : Tot (list formula) (decreases args) =
  match args with
  | [] -> []
  | a :: rest ->
    let x = specialize negative a in
    if x = B.Bool (not (B.neutral op)) then [x]
    else if x = B.Bool (B.neutral op) then specialize_context_args negative op rest
    else x :: specialize_context_args (neutral_assumption op x :: negative) op rest

let rec lemma_specialize_sound (rho:Z3AstTheory.expr -> bool)
                               (negative:list formula) (s:formula)
  : Lemma (requires not (B.eval_args rho B.Or negative))
          (ensures B.eval rho (specialize negative s) == B.eval rho s)
          (decreases s) =
  lemma_forced_polarity negative s true;
  lemma_forced_polarity negative s false;
  if forced negative s true then lemma_forced_sound rho negative s true
  else if forced negative s false then lemma_forced_sound rho negative s false
  else match s with
  | B.Atom _ | B.Bool _ -> ()
  | B.Not a ->
    lemma_specialize_sound rho negative a;
    lemma_make_not_sound rho (specialize negative a)
  | B.Nary op args ->
    if op = B.Xor then lemma_specialize_args_sound rho negative op args
    else (
      lemma_specialize_context_args_sound rho negative op args;
      lemma_reduce_args_sound rho op (specialize_context_args negative op args);
      lemma_make_nary_sound rho op (reduce_args op (specialize_context_args negative op args)))
  | B.Implies a b ->
    lemma_specialize_sound rho negative a;
    lemma_specialize_sound rho negative b;
    lemma_make_not_sound rho (specialize negative a);
    lemma_make_nary_sound rho B.Or
      [make_not (specialize negative a); specialize negative b]
  | B.Eq a b ->
    lemma_specialize_sound rho negative a;
    lemma_specialize_sound rho negative b;
    lemma_make_eq_sound rho (specialize negative a) (specialize negative b)

and lemma_specialize_args_sound (rho:Z3AstTheory.expr -> bool)
                                (negative:list formula) (op:B.nary_op)
                                (args:list formula)
  : Lemma (requires not (B.eval_args rho B.Or negative))
          (ensures B.eval_args rho op (specialize_args negative args) ==
                   B.eval_args rho op args)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_specialize_sound rho negative a;
    lemma_specialize_args_sound rho negative op rest

and lemma_specialize_context_args_sound (rho:Z3AstTheory.expr -> bool)
                                        (negative:list formula) (op:B.nary_op)
                                        (args:list formula)
  : Lemma (requires not (B.eval_args rho B.Or negative) /\ op <> B.Xor)
          (ensures B.eval_args rho op (specialize_context_args negative op args) ==
                   B.eval_args rho op args)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_specialize_sound rho negative a;
    let x = specialize negative a in
    if x = B.Bool (not (B.neutral op)) then
      (match op with B.And | B.Or | B.Xor -> ())
    else if x = B.Bool (B.neutral op) then
      lemma_specialize_context_args_sound rho negative op rest
    else if B.eval rho x = B.neutral op then (
      lemma_neutral_assumption rho op x;
      lemma_specialize_context_args_sound rho (neutral_assumption op x :: negative) op rest)
    else (match op with B.And | B.Or | B.Xor -> ())

let rec lemma_intersect_disjunction (rho:Z3AstTheory.expr -> bool) (xs ys:list formula)
  : Lemma (B.eval_args rho B.Or (B.intersect xs ys) ==>
           B.eval_args rho B.Or xs /\ B.eval_args rho B.Or ys)
          (decreases xs) =
  match xs with
  | [] -> ()
  | x :: rest ->
    lemma_intersect_disjunction rho rest ys;
    if mem x ys then lemma_member_eval rho x ys

let direct_contextual_equivalent (s t:formula) : bool =
  let common = B.intersect (disjuncts s) (disjuncts t) in
  normal_equivalent (specialize common s) (specialize common t)

let lemma_direct_contextual_equivalent_sound (rho:Z3AstTheory.expr -> bool) (s t:formula)
  : Lemma (requires direct_contextual_equivalent s t)
          (ensures B.eval rho s == B.eval rho t) =
  let common = B.intersect (disjuncts s) (disjuncts t) in
  lemma_intersect_disjunction rho (disjuncts s) (disjuncts t);
  if B.eval_args rho B.Or common then (
    (match s with B.Nary B.Or _ -> () | _ -> ());
    (match t with B.Nary B.Or _ -> () | _ -> ()))
  else (
    lemma_specialize_sound rho common s;
    lemma_specialize_sound rho common t;
    lemma_normal_equivalent_sound rho (specialize common s) (specialize common t))

let rec reverse (s:formula) : Tot formula (decreases s) =
  match s with
  | B.Atom _ | B.Bool _ -> s
  | B.Not a -> B.Not (reverse a)
  | B.Nary op args -> B.Nary op (reverse_args args)
  | B.Implies a b -> B.Implies (reverse a) (reverse b)
  | B.Eq a b -> B.Eq (reverse a) (reverse b)

and reverse_args (args:list formula) : Tot (list formula) (decreases args) =
  match args with [] -> [] | a :: rest -> reverse_args rest @ [reverse a]

let rec lemma_reverse_sound (rho:Z3AstTheory.expr -> bool) (s:formula)
  : Lemma (B.eval rho (reverse s) == B.eval rho s) (decreases s) =
  match s with
  | B.Atom _ | B.Bool _ -> ()
  | B.Not a -> lemma_reverse_sound rho a
  | B.Nary op args -> lemma_reverse_args_sound rho op args
  | B.Implies a b | B.Eq a b -> lemma_reverse_sound rho a; lemma_reverse_sound rho b

and lemma_reverse_args_sound (rho:Z3AstTheory.expr -> bool) (op:B.nary_op) (args:list formula)
  : Lemma (B.eval_args rho op (reverse_args args) == B.eval_args rho op args)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_reverse_sound rho a;
    lemma_reverse_args_sound rho op rest;
    lemma_eval_append rho op (reverse_args rest) [reverse a];
    match op with B.And | B.Or | B.Xor -> ()

let contextual_equivalent (s t:formula) : bool =
  normal_equivalent s t || direct_contextual_equivalent s t ||
  direct_contextual_equivalent (normalize false s) (normalize false t) ||
  direct_contextual_equivalent (normalize true s) (normalize true t) ||
  direct_contextual_equivalent (reverse s) (reverse t) ||
  direct_contextual_equivalent (reverse (normalize false s)) (reverse (normalize false t))

let lemma_contextual_equivalent_sound (rho:Z3AstTheory.expr -> bool) (s t:formula)
  : Lemma (requires contextual_equivalent s t)
          (ensures B.eval rho s == B.eval rho t) =
  if normal_equivalent s t then lemma_normal_equivalent_sound rho s t
  else if direct_contextual_equivalent s t then lemma_direct_contextual_equivalent_sound rho s t
  else if direct_contextual_equivalent (normalize false s) (normalize false t) then (
    lemma_normalize_sound rho false s;
    lemma_normalize_sound rho false t;
    lemma_direct_contextual_equivalent_sound rho (normalize false s) (normalize false t))
  else if direct_contextual_equivalent (normalize true s) (normalize true t) then (
    lemma_normalize_sound rho true s;
    lemma_normalize_sound rho true t;
    lemma_direct_contextual_equivalent_sound rho (normalize true s) (normalize true t))
  else if direct_contextual_equivalent (reverse s) (reverse t) then (
    lemma_reverse_sound rho s;
    lemma_reverse_sound rho t;
    lemma_direct_contextual_equivalent_sound rho (reverse s) (reverse t))
  else (
    lemma_normalize_sound rho false s;
    lemma_normalize_sound rho false t;
    lemma_reverse_sound rho (normalize false s);
    lemma_reverse_sound rho (normalize false t);
    lemma_direct_contextual_equivalent_sound rho
      (reverse (normalize false s)) (reverse (normalize false t)))

let rec normalize_context (fuel:nat) (s:formula) : Tot formula (decreases fuel) =
  if fuel = 0 then s
  else
    let next = specialize [] (normalize false s) in
    if next = s then s else normalize_context (fuel - 1) next

let rec lemma_normalize_context_sound (rho:Z3AstTheory.expr -> bool) (fuel:nat) (s:formula)
  : Lemma (B.eval rho (normalize_context fuel s) == B.eval rho s) (decreases fuel) =
  if fuel > 0 then (
    lemma_normalize_sound rho false s;
    lemma_specialize_sound rho [] (normalize false s);
    let next = specialize [] (normalize false s) in
    if next <> s then lemma_normalize_context_sound rho (fuel - 1) next)

let equivalent (s t:formula) : bool =
  contextual_equivalent s t ||
  contextual_equivalent (normalize_context 2 s) (normalize_context 2 t)

let lemma_equivalent_sound (rho:Z3AstTheory.expr -> bool) (s t:formula)
  : Lemma (requires equivalent s t)
          (ensures B.eval rho s == B.eval rho t) =
  if contextual_equivalent s t then lemma_contextual_equivalent_sound rho s t
  else (
    lemma_normalize_context_sound rho 2 s;
    lemma_normalize_context_sound rho 2 t;
    lemma_contextual_equivalent_sound rho (normalize_context 2 s) (normalize_context 2 t))

(* The first atom of [B.support e] (lemma_first_atom), without building the support. *)
let rec first_atom (#a:Type) (e:B.formula a) : Tot (option a) (decreases e) =
  match e with
  | B.Atom x -> Some x
  | B.Bool _ -> None
  | B.Nary _ args -> first_atom_args args
  | B.Not x -> first_atom x
  | B.Implies x y | B.Eq x y -> (match first_atom x with None -> first_atom y | r -> r)
and first_atom_args (#a:Type) (args:list (B.formula a)) : Tot (option a) (decreases args) =
  match args with
  | [] -> None
  | x :: xs -> (match first_atom x with None -> first_atom_args xs | r -> r)

let first_of (#a:Type) (xs:list a) : option a = match xs with [] -> None | x :: _ -> Some x

let lemma_first_of_append (#a:Type) (xs ys:list a)
  : Lemma (first_of (xs @ ys) == (match first_of xs with None -> first_of ys | r -> r)) =
  match xs with [] -> () | _ -> ()

let rec lemma_first_atom (#a:Type) (e:B.formula a)
  : Lemma (ensures first_atom e == first_of (B.support e)) (decreases e) =
  match e with
  | B.Atom _ | B.Bool _ -> ()
  | B.Nary _ args -> lemma_first_atom_args args
  | B.Not x -> lemma_first_atom x
  | B.Implies x y | B.Eq x y ->
    lemma_first_atom x; lemma_first_atom y;
    lemma_first_of_append (B.support x) (B.support y)
and lemma_first_atom_args (#a:Type) (args:list (B.formula a))
  : Lemma (ensures first_atom_args args == first_of (B.support_args args)) (decreases args) =
  match args with
  | [] -> ()
  | x :: xs ->
    lemma_first_atom x; lemma_first_atom_args xs;
    lemma_first_of_append (B.support x) (B.support_args xs)

let rec shannon (fuel:nat) (s t:formula) : Tot bool (decreases fuel) =
  if normal_equivalent s t then true
  else if fuel = 0 then false
  else
    let _ = assert (fuel > 0) in
    match (match first_atom s with None -> first_atom t | atom -> atom) with
    | None -> false
    | Some atom ->
      shannon (fuel - 1) (specialize [B.Atom atom] s) (specialize [B.Atom atom] t) &&
      shannon (fuel - 1) (specialize [B.Not (B.Atom atom)] s)
                         (specialize [B.Not (B.Atom atom)] t)

let rec lemma_shannon_sound (rho:Z3AstTheory.expr -> bool) (fuel:nat) (s t:formula)
  : Lemma (requires shannon fuel s t)
          (ensures B.eval rho s == B.eval rho t)
          (decreases fuel) =
  if normal_equivalent s t then lemma_normal_equivalent_sound rho s t
  else if fuel > 0 then
    match (match first_atom s with None -> first_atom t | atom -> atom) with
    | None -> ()
    | Some atom ->
      let negative = if rho atom then [B.Not (B.Atom atom)] else [B.Atom atom] in
      lemma_specialize_sound rho negative s;
      lemma_specialize_sound rho negative t;
      lemma_shannon_sound rho (fuel - 1) (specialize negative s) (specialize negative t)
