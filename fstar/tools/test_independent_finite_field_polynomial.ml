module P = Z3IndependentFiniteFieldPolynomial
module M = Z3IndependentFiniteFieldMonomial

let zi = Z.of_int
let to_z q = List.map (fun (m, c) -> List.map zi m, zi c) q
let max_coefficient q = List.fold_left (fun n (_, c) -> max n (abs c)) 0 q
let max_degree q = List.fold_left (fun n (m, _) -> max n (List.length m)) 0 q

let rec reference_add a b =
  match a, b with
  | [], _ -> b
  | _, [] -> a
  | (m1, c1) :: ar, (m2, c2) :: br ->
    if m1 = m2 then (m1, c1 + c2) :: reference_add ar br
    else if compare m1 m2 < 0 then (m1, c1) :: reference_add ar b
    else (m2, c2) :: reference_add a br

let rec reference_split q =
  match q with
  | x :: y :: rest -> let a, b = reference_split rest in x :: a, y :: b
  | _ -> q, []

let rec reference_canon q =
  match q with
  | [] | [_] -> q
  | _ -> let a, b = reference_split q in reference_add (reference_canon a) (reference_canon b)

let reference_normalize p q =
  List.filter_map (fun (m, c) ->
    let c = ((c mod p) + p) mod p in
    if c = 0 then None else Some (m, c)) (reference_canon q)

let rec reference_terms_ordered = function
  | [] | [_] -> true
  | (a, _) :: ((b, _) :: _ as rest) ->
    compare a b < 0 && reference_terms_ordered rest

let check_terms_order q =
  if P.terms_ordered q <> reference_terms_ordered (P.expand q) then
    failwith "compact polynomial term order"

let check_terms_ordered_metered q =
  let bound = P.terms_order_bound q in
  if P.terms_ordered_metered Z.zero q <> None then failwith "zero term-order fuel";
  match P.terms_ordered_metered bound q with
  | None -> failwith "term-order guard exhausted sufficient bound"
  | Some (result, work) ->
    if result <> P.terms_ordered q || Z.leq work Z.zero || Z.gt work bound ||
       P.terms_ordered_metered (Z.pred work) q <> None ||
       P.terms_ordered_metered work q <> Some (result, work) ||
       P.terms_ordered_metered (Z.add bound (zi 1000)) q <> Some (result, work) then
      failwith "metered term-order guard";
    result, work

let check_guarded_normalize_metered p q =
  let ordered, gw = check_terms_ordered_metered q in
  let bound = P.guarded_normalize_bound q in
  if P.guarded_normalize_metered Z.zero p q <> None then
    failwith "zero guarded normalization fuel";
  match P.guarded_normalize_metered bound p q with
  | None -> failwith "guarded normalization exhausted sufficient bound"
  | Some (result, work) ->
    if result <> P.normalize p q || Z.leq work Z.zero || Z.gt work bound ||
       P.guarded_normalize_metered (Z.pred work) p q <> None ||
       P.guarded_normalize_metered work p q <> Some (result, work) ||
       P.guarded_normalize_metered (Z.add bound (zi 1000)) p q <> Some (result, work) then
      failwith "guarded normalization correctness or fuel boundary";
    let path =
      if ordered then P.reduce_metered bound p q else P.normalize_metered bound p q in
    (match path with
     | Some (expected, path_work) ->
       if result <> expected || not (Z.equal work (Z.add gw path_work)) then
         failwith "guarded normalization branch or shared work"
     | None -> failwith "guarded normalization reference path exhausted");
    if P.guarded_normalize_metered gw p q <> None then
      failwith "guarded normalization failed to charge reduction or fallback"

let check_guarded_arithmetic name p bound expected operation raw_operation =
  if operation Z.zero <> None then failwith (name ^ " accepted zero fuel");
  match operation bound with
  | None -> failwith (name ^ " exhausted sufficient bound")
  | Some (result, work) ->
    if result <> expected || Z.leq work Z.zero || Z.gt work bound ||
       operation (Z.pred work) <> None ||
       operation work <> Some (result, work) ||
       operation (Z.add bound (zi 1000)) <> Some (result, work) then
      failwith (name ^ " correctness or fuel boundary");
    (match raw_operation bound with
     | None -> failwith (name ^ " raw operation exhausted bound")
     | Some (raw, rw) ->
       if operation rw <> None then failwith (name ^ " did not share fuel");
       match P.guarded_normalize_metered (Z.sub bound rw) p raw with
       | Some (expected, nw) when expected = result && Z.equal work (Z.add rw nw) -> ()
       | _ -> failwith (name ^ " normalization work accounting"))

let check_add_guarded p a b =
  check_guarded_arithmetic "guarded addition" p (P.add_guarded_normalize_bound a b)
    (P.normalize p (P.add a b))
    (fun fuel -> P.add_guarded_normalize_metered fuel p a b)
    (fun fuel -> P.add_metered fuel a b)

let check_scale_guarded p m c q =
  check_guarded_arithmetic "guarded scaling" p (P.scale_guarded_normalize_bound m q)
    (P.normalize p (P.scale_mono m c q))
    (fun fuel -> P.scale_guarded_normalize_metered fuel p m c q)
    (fun fuel -> P.scale_metered fuel m c q)

let check_input_prepare_guarded p q =
  let bound = P.input_prepare_guarded_bound q in
  let expected =
    if P.sorted_monomials q then Some (P.normalize p (P.compress q)) else None in
  let operation fuel = P.input_prepare_guarded_metered fuel p q in
  if operation Z.zero <> None then failwith "guarded input accepted zero fuel";
  match operation bound with
  | None -> failwith "guarded input exhausted sufficient bound"
  | Some (result, work) ->
    if result <> expected || Z.leq work Z.zero || Z.gt work bound ||
       operation (Z.pred work) <> None ||
       operation work <> Some (result, work) ||
       operation (Z.add bound (zi 1000)) <> Some (result, work) then
      failwith "guarded input correctness or fuel boundary";
    (match P.sorted_monomials_metered bound q, result with
     | Some (false, sw), None ->
       if not (Z.equal work sw) then failwith "guarded input rejection charged extra work"
     | Some (true, sw), Some result ->
       (match P.compress_metered (Z.sub bound sw) q with
        | None -> failwith "guarded input compression exhausted bound"
        | Some (raw, cw) ->
          let preparation = Z.add sw cw in
          if operation preparation <> None then failwith "guarded input did not share fuel";
          match P.guarded_normalize_metered (Z.sub bound preparation) p raw with
          | Some (expected, nw) when expected = result &&
              Z.equal work (Z.add preparation nw) -> ()
          | _ -> failwith "guarded input normalization work accounting")
     | _ -> failwith "guarded input rejection mismatch")

let check_compress_metered q =
  let bound = zi (List.fold_left (fun total (m, _) -> total + List.length m + 2) 1 q) in
  if P.compress_metered Z.zero q <> None then failwith "zero polynomial compression fuel";
  match P.compress_metered bound q with
  | None -> failwith "metered polynomial compression exhausted exact fuel"
  | Some (result, work) ->
    if result <> P.compress q || not (Z.equal work bound) then
      failwith "metered polynomial compression correctness";
    if P.compress_metered (Z.pred work) q <> None ||
       P.compress_metered (Z.add bound (zi 1000)) q <> Some (result, work) then
      failwith "metered polynomial compression fuel boundary"

let check_sorted_metered q =
  let bound = zi (List.fold_left (fun total (m, _) -> total + List.length m + 2) 1 q) in
  if P.sorted_monomials_metered Z.zero q <> None then failwith "zero polynomial sortedness fuel";
  match P.sorted_monomials_metered bound q with
  | None -> failwith "metered polynomial sortedness exhausted conservative fuel"
  | Some (result, work) ->
    if result <> P.sorted_monomials q || Z.leq work Z.zero || Z.gt work bound then
      failwith "metered polynomial sortedness correctness";
    if P.sorted_monomials_metered (Z.pred work) q <> None ||
       P.sorted_monomials_metered work q <> Some (result, work) ||
       P.sorted_monomials_metered (Z.add bound (zi 1000)) q <> Some (result, work) then
      failwith "metered polynomial sortedness fuel boundary"

let check_input_prepare_metered p q =
  let bound = P.input_prepare_bound q in
  let expected =
    if P.sorted_monomials q then Some (P.normalize p (P.compress q)) else None in
  if P.input_prepare_metered Z.zero p q <> None then failwith "zero input preparation fuel";
  match P.input_prepare_metered bound p q with
  | None -> failwith "metered input preparation exhausted conservative fuel"
  | Some (result, work) ->
    if result <> expected || Z.leq work Z.zero || Z.gt work bound then
      failwith "metered input preparation correctness";
    if P.input_prepare_metered (Z.pred work) p q <> None ||
       P.input_prepare_metered work p q <> Some (result, work) ||
       P.input_prepare_metered (Z.add bound (zi 1000)) p q <> Some (result, work) then
      failwith "metered input preparation fuel boundary"

let check_split_metered q =
  let bound = zi (List.length q + 1) in
  if P.split_metered Z.zero q <> None then failwith "zero split fuel";
  match P.split_metered bound q with
  | None -> failwith "metered split exhausted conservative fuel"
  | Some (a, b, work) ->
    if (a, b) <> reference_split q ||
       not (Z.equal work (zi (1 + List.length q / 2))) ||
       Z.gt work bound then failwith "metered split correctness";
    if P.split_metered (Z.pred work) q <> None ||
       P.split_metered work q <> Some (a, b, work) then
      failwith "metered split fuel boundary"

let check_canon_metered q =
  let fuel = P.canon_work_bound (zi (List.length q)) (P.compact_weight q) in
  if P.canon_metered Z.zero q <> None then failwith "zero canon fuel";
  match P.canon_metered fuel q with
  | None -> failwith "metered canon exhausted test fuel"
  | Some (result, work) ->
    if result <> P.canon q || Z.leq work Z.zero || Z.gt work fuel then
      failwith "metered canon correctness";
    if P.canon_metered (Z.pred work) q <> None ||
       P.canon_metered work q <> Some (result, work) ||
       P.canon_metered (Z.add fuel (zi 1000)) q <> Some (result, work) then
      failwith "metered canon fuel boundary"

let check_reduce_metered p q =
  let fuel = zi (List.length q + 1) in
  if P.reduce_metered Z.zero p q <> None then failwith "zero reduction fuel";
  match P.reduce_metered fuel p q with
  | None -> failwith "metered reduction exhausted exact fuel"
  | Some (result, work) ->
    if result <> P.reduce p q || not (Z.equal work fuel) then
      failwith "metered reduction correctness";
    if P.reduce_metered (Z.pred work) p q <> None ||
       P.reduce_metered (Z.add fuel (zi 1000)) p q <> Some (result, work) then
      failwith "metered reduction fuel boundary"

let check_normalize_metered p q =
  let fuel = Z.add (P.canon_work_bound (zi (List.length q)) (P.compact_weight q))
    (zi (List.length q + 1)) in
  if P.normalize_metered Z.zero p q <> None then failwith "zero normalize fuel";
  match P.normalize_metered fuel p q with
  | None -> failwith "metered normalization exhausted conservative fuel"
  | Some (result, work) ->
    if result <> P.normalize p q || Z.leq work Z.zero || Z.gt work fuel then
      failwith "metered normalization correctness";
    if P.normalize_metered (Z.pred work) p q <> None ||
       P.normalize_metered work p q <> Some (result, work) ||
       P.normalize_metered (Z.add fuel (zi 1000)) p q <> Some (result, work) then
      failwith "metered normalization fuel boundary"

let check_scale_metered m c q =
  let bound = Z.succ (Z.add (P.compact_weight q)
    (Z.mul (zi (List.length q)) (zi (1 + List.length m)))) in
  if P.scale_metered Z.zero m c q <> None then failwith "zero scaling fuel";
  match P.scale_metered bound m c q with
  | None -> failwith "metered scaling exhausted conservative fuel"
  | Some (result, work) ->
    if result <> P.scale_mono m c q || Z.leq work Z.zero || Z.gt work bound then
      failwith "metered scaling correctness";
    if P.scale_metered (Z.pred work) m c q <> None ||
       P.scale_metered work m c q <> Some (result, work) ||
       P.scale_metered (Z.add bound (zi 1000)) m c q <> Some (result, work) then
      failwith "metered scaling fuel boundary"

let check_scale_normalize_metered p m c q =
  let bound = P.scale_normalize_bound m q in
  if P.scale_normalize_metered Z.zero p m c q <> None then
    failwith "zero normalized scaling fuel";
  match P.scale_normalize_metered bound p m c q with
  | None -> failwith "metered normalized scaling exhausted conservative fuel"
  | Some (result, work) ->
    if result <> P.normalize p (P.scale_mono m c q) ||
       Z.leq work Z.zero || Z.gt work bound then
      failwith "metered normalized scaling correctness";
    if P.scale_normalize_metered (Z.pred work) p m c q <> None ||
       P.scale_normalize_metered work p m c q <> Some (result, work) ||
       P.scale_normalize_metered (Z.add bound (zi 1000)) p m c q <> Some (result, work)
    then failwith "metered normalized scaling fuel boundary"

let check_add_normalize_metered p a b =
  let bound = P.add_normalize_bound a b in
  if P.add_normalize_metered Z.zero p a b <> None then
    failwith "zero normalized addition fuel";
  match P.add_normalize_metered bound p a b with
  | None -> failwith "metered normalized addition exhausted conservative fuel"
  | Some (result, work) ->
    if result <> P.normalize p (P.add a b) ||
       Z.leq work Z.zero || Z.gt work bound then
      failwith "metered normalized addition correctness";
    if P.add_normalize_metered (Z.pred work) p a b <> None ||
       P.add_normalize_metered work p a b <> Some (result, work) ||
       P.add_normalize_metered (Z.add bound (zi 1000)) p a b <> Some (result, work)
    then failwith "metered normalized addition fuel boundary"

let check_metered a b =
  let terms = List.length a + List.length b in
  let weight = Z.add (P.compact_weight a) (P.compact_weight b) in
  let fuel = Z.succ (Z.mul (zi terms) (Z.add (zi 3) (Z.mul (zi 2) weight))) in
  if P.add_metered Z.zero a b <> None then failwith "zero merge fuel";
  match P.add_metered fuel a b with
  | None -> failwith "metered merge exhausted conservative fuel"
  | Some (result, work) ->
    if result <> P.add a b || Z.leq work Z.zero || Z.gt work fuel then
      failwith "metered merge correctness";
    if P.add_metered (Z.pred work) a b <> None ||
       P.add_metered work a b <> Some (result, work) ||
       P.add_metered (Z.add fuel (zi 1000)) a b <> Some (result, work) then
      failwith "metered merge fuel boundary"

let check a b =
  let za = to_z a and zb = to_z b in
  check_compress_metered za;
  check_compress_metered zb;
  check_sorted_metered za;
  check_sorted_metered zb;
  check_input_prepare_metered (zi 7) za;
  check_input_prepare_metered (zi 7) zb;
  let ca = P.compress za and cb = P.compress zb in
  check_terms_order ca;
  check_terms_order cb;
  let ordered_a = P.canon ca and ordered_b = P.canon cb in
  if not (P.terms_ordered (P.add ordered_a ordered_b)) then
    failwith "ordered polynomial merge";
  if P.expand ca <> za || P.expand cb <> zb then failwith "polynomial round trip";
  if not (P.sorted_monomials za && P.sorted_monomials zb &&
          P.canonical_monomials ca && P.canonical_monomials cb &&
          P.canonical_monomials (P.add ca cb))
  then failwith "polynomial monomial canonicalization";
  let result = P.add ca cb in
  check_metered ca cb;
  check_add_normalize_metered (zi 7) ca cb;
  if P.expand result <> to_z (reference_add a b) then failwith "polynomial addition";
  if not (P.coefficients_bounded (zi (max_coefficient a + max_coefficient b)) result)
  then failwith "polynomial addition coefficient bound";
  if Z.gt (P.compact_weight result) (Z.add (P.compact_weight ca) (P.compact_weight cb)) ||
     List.length result > List.length a + List.length b ||
     not (P.degrees_bounded (zi (max (max_degree a) (max_degree b))) result)
  then failwith "polynomial addition structural bounds";
  List.iter (fun offset ->
    let valuation k = Z.sub k (zi offset) in
    if not (Z.equal (P.evaluate valuation result)
              (Z.add (P.evaluate valuation ca) (P.evaluate valuation cb)))
    then failwith "polynomial addition evaluation") [0; 1; 3]

let check_scale m c q =
  let factor = M.compress (List.map zi m) in
  let original = P.compress (to_z q) in
  check_scale_metered factor (zi c) original;
  check_scale_normalize_metered (zi 7) factor (zi c) original;
  let result = P.scale_mono factor (zi c) original in
  let expected = List.map (fun (n, k) -> List.sort compare (m @ n), c * k) q in
  if not (P.canonical_monomials result) || P.expand result <> to_z expected then
    failwith "compact polynomial scaling";
  if not (P.coefficients_bounded (zi (abs c * max_coefficient q)) result) then
    failwith "polynomial scaling coefficient bound";
  let weight_bound = Z.add (P.compact_weight original) (zi (List.length q * List.length factor)) in
  if Z.gt (P.compact_weight result) weight_bound || List.length result <> List.length q ||
     not (P.degrees_bounded (zi (List.length m + max_degree q)) result) then
    failwith "polynomial scaling structural bounds";
  List.iter (fun offset ->
    let valuation k = Z.sub k (zi offset) in
    let expected = Z.mul (Z.mul (zi c) (M.evaluate valuation factor))
      (P.evaluate valuation original) in
    if not (Z.equal (P.evaluate valuation result) expected) then
      failwith "compact polynomial scaling evaluation") [0; 1; 3]

let check_normalize p q =
  let original = P.compress (to_z q) in
  check_split_metered original;
  if p = 7 then check_canon_metered original;
  check_reduce_metered (zi p) original;
  check_normalize_metered (zi p) original;
  let canonical = P.canon original in
  let normalized = P.normalize (zi p) original in
  check_terms_order original;
  check_terms_order canonical;
  check_terms_order normalized;
  if not (P.terms_ordered canonical && P.terms_ordered normalized &&
          P.terms_ordered (P.reduce (zi p) canonical)) then
    failwith "canonical polynomial term order preservation";
  if P.terms_ordered original && P.canon original <> original then
    failwith "ordered canonicalization identity";
  if P.expand canonical <> to_z (reference_canon q) ||
     not (P.coefficients_bounded (zi (List.length q * max_coefficient q)) canonical) ||
     not (P.coefficients_bounded (zi (p - 1)) normalized) then
    failwith "canonicalization or reduction coefficient bound";
  if Z.gt (P.compact_weight canonical) (P.compact_weight original) ||
     Z.gt (P.compact_weight normalized) (P.compact_weight original) ||
     List.length canonical > List.length q || List.length normalized > List.length q ||
     not (P.degrees_bounded (zi (max_degree q)) canonical) ||
     not (P.degrees_bounded (zi (max_degree q)) normalized) then
    failwith "canonicalization or reduction structural bounds";
  if not (P.canonical_monomials normalized) ||
     P.expand normalized <> to_z (reference_normalize p q) then
    failwith "compact polynomial normalization";
  List.iter (fun offset ->
    let valuation k = Z.sub k (zi offset) in
    if not (Z.equal (Z.erem (P.evaluate valuation normalized) (zi p))
              (Z.erem (P.evaluate valuation original) (zi p))) then
      failwith "compact polynomial normalization evaluation") [0; 1; 3]

let () =
  check [] [];
  check [([], 2); ([1; 1], 3); ([2], -4)]
        [([], -2); ([1; 1], 5); ([3], 7)];
  check [([0; 0; 0], 1); ([0; 0], 2)] [([0; 0], -2)];
  check [([], -6); ([0], 6)] [([], -7); ([0], 7)];
  check_scale [] 0 [([], 2); ([1; 1], -3)];
  check_scale [0; 0; 1] (-3) [([], 2); ([0; 1; 1], -4)];
  check_scale [1; 1] 2 [];
  check_normalize 1 [([], 3)];
  check_normalize 7 [([2; 2], -8); ([], 7); ([2; 2], 8); ([1], -1)];
  check_normalize 17 (List.init 11 (fun _ -> [], -7));
  check_normalize 2 [];
  let huge = Z.shift_left Z.one 510 in
  check_compress_metered [[huge; Z.one; huge], Z.neg huge; [], Z.zero];
  check_sorted_metered [[huge; Z.one; huge], Z.neg huge; [], Z.zero];
  let early_unsorted = ([zi 2; Z.one], Z.zero) :: List.init 300 (fun _ -> [], Z.zero) in
  if P.sorted_monomials_metered (zi 2) early_unsorted <> Some (false, zi 2) then
    failwith "polynomial sortedness did not reject early";
  check_input_prepare_metered (zi 17) early_unsorted;
  if P.input_prepare_metered (zi 2) (zi 7) early_unsorted <> Some (None, zi 2) then
    failwith "input preparation did not reject early";
  let repeated = List.init 11 (fun _ -> [], Z.neg huge) in
  check_input_prepare_metered Z.one repeated;
  check_input_prepare_metered (zi 2) repeated;
  check_input_prepare_metered (zi 17) repeated;
  check_reduce_metered (zi 17) repeated;
  check_normalize_metered (zi 17) repeated;
  check_scale_normalize_metered Z.one [] Z.zero repeated;
  check_scale_normalize_metered (zi 2) [zi 1, Z.one] (Z.neg huge) repeated;
  check_add_normalize_metered Z.one repeated [];
  check_add_normalize_metered (zi 2) repeated repeated;
  let canonical = P.canon repeated in
  if canonical <> [[], Z.neg (Z.mul (zi 11) huge)] ||
     not (P.coefficients_bounded (Z.mul (zi 11) huge) canonical) ||
     P.coefficients_bounded (Z.pred (Z.mul (zi 11) huge)) canonical then
    failwith "large canonical coefficient bound";
  let malformed = [[zi 1, zi 1; zi 1, zi 1], zi 4] in
  if P.canonical_monomials malformed then failwith "duplicate compact runs accepted";
  if not (P.terms_ordered malformed) then
    failwith "term order confused with monomial run order";
  let duplicate_terms = [[], zi 3; [], zi (-3)] in
  if not (P.canonical_monomials duplicate_terms) ||
     P.terms_ordered duplicate_terms then
    failwith "duplicate polynomial terms accepted as strictly ordered";
  let guarded_cases = [
    []; [[], Z.zero]; duplicate_terms; malformed;
    [[], Z.one; [zi 1, Z.one; zi 1, Z.one], zi (-3); [zi 2, Z.one], zi 4];
    P.compress (to_z [([], 0); ([0], -2); ([0; 0], 3); ([1], 7)]);
    P.compress (to_z [([0; 0], 1); ([0], 2)])
  ] in
  List.iter (fun p -> List.iter (fun q ->
    check_guarded_normalize_metered (zi p) q;
    check_add_guarded (zi p) q q;
    check_scale_guarded (zi p) [Z.one, Z.one] (zi (-2)) q;
    check_input_prepare_guarded (zi p) (P.expand q)) guarded_cases) [1; 2; 7; 17];
  let descending_head =
    ([zi 2, Z.one], Z.one) :: ([zi 1, Z.one], Z.one) ::
    List.init 300 (fun _ -> [], Z.zero) in
  if P.terms_ordered_metered (zi 2) descending_head <> Some (false, zi 2) then
    failwith "term-order guard did not reject before scanning tail";
  let scale_source = P.compress (to_z [([], 1); ([0], 1)]) in
  let scale_reversed = P.scale_mono [zi 1, Z.one] Z.one scale_source in
  if not (P.terms_ordered scale_source) || P.terms_ordered scale_reversed then
    failwith "scaling order counterexample";
  check_guarded_normalize_metered (zi 7) scale_reversed;
  check_scale_guarded (zi 7) [Z.one, Z.one] Z.one scale_source;
  check_input_prepare_guarded (zi 7) (to_z [([2; 1], 1)]);
  check_input_prepare_guarded (zi 7) early_unsorted;
  if P.input_prepare_guarded_metered (zi 2) (zi 7) early_unsorted <>
     Some (None, zi 2) then failwith "guarded input did not reject early";
  check_add_guarded (zi 7) [[], Z.one] [[], Z.minus_one];
  check_terms_order (P.compress (to_z [([], 0); ([0], 0); ([0; 0], -2); ([1], 3)]));
  check_terms_order (P.compress (to_z [([0; 0], 1); ([0], 2)]));
  let huge_degree = Z.shift_left Z.one 200 in
  if not (P.terms_ordered [[zi 0, huge_degree], Z.zero;
                           [zi 0, Z.succ huge_degree], Z.one]) ||
     P.terms_ordered [[zi 0, Z.succ huge_degree], Z.one;
                      [zi 0, huge_degree], Z.zero] then
    failwith "huge compact exponents term order";
  check_guarded_normalize_metered (zi 17)
    [[zi 0, huge_degree], Z.neg huge; [zi 0, Z.succ huge_degree], huge];
  check_scale_guarded (zi 17) [zi 0, huge_degree] (Z.neg huge) malformed;
  let noncanonical = [[zi 2, huge_degree; zi 1, Z.one], zi 3;
                      [zi 2, huge_degree; zi 1, Z.one], zi (-3);
                      [zi 0, Z.one], zi 2] in
  check_split_metered noncanonical;
  check_canon_metered noncanonical;
  check_reduce_metered (zi 7) noncanonical;
  check_normalize_metered (zi 7) noncanonical;
  check_guarded_normalize_metered (zi 7) noncanonical;
  check_add_guarded (zi 17) noncanonical malformed;
  check_metered noncanonical malformed;
  check_add_normalize_metered (zi 17) noncanonical malformed;
  let nc_canonical = P.canon noncanonical in
  let nc_normal = P.normalize (zi 7) noncanonical in
  if Z.gt (P.compact_weight nc_canonical) (P.compact_weight noncanonical) ||
     Z.gt (P.compact_weight nc_normal) (P.compact_weight noncanonical) ||
     not (P.degrees_bounded (Z.succ huge_degree) nc_canonical) ||
     not (P.degrees_bounded (Z.succ huge_degree) nc_normal) then
    failwith "noncanonical normalization structural bounds";
  let unordered_factor = [zi 2, zi 2; zi 0, zi 1] in
  check_scale_guarded (zi 17) unordered_factor (Z.neg huge) noncanonical;
  check_scale_metered unordered_factor (Z.neg huge) noncanonical;
  check_scale_normalize_metered (zi 17) unordered_factor (Z.neg huge) noncanonical;
  let unordered_product = P.scale_mono unordered_factor Z.one malformed in
  if Z.gt (P.compact_weight unordered_product)
       (Z.add (P.compact_weight malformed) (zi (List.length unordered_factor))) ||
     not (P.degrees_bounded (zi 5) unordered_product) then
    failwith "unordered compact structural bounds";
  if P.sorted_monomials (to_z [([2; 1], 1)]) then failwith "unsorted input accepted";
  let rng = Random.State.make [| 619 |] in
  let random_poly () =
    List.init (Random.State.int rng 12) (fun _ ->
      let m = List.init (Random.State.int rng 10) (fun _ -> Random.State.int rng 5) in
      List.sort compare m, Random.State.int rng 13 - 6) in
  for case = 1 to 10000 do
    let a = random_poly () and b = random_poly () in
    if case <= 200 then (
      let raw = P.compress (to_z a) in
      check_guarded_normalize_metered (zi 7) raw;
      check_guarded_normalize_metered (zi 7) (P.canon raw);
      check_add_guarded (zi 7) raw (P.compress (to_z b));
      check_scale_guarded (zi 7) [Z.one, Z.one] (zi (-3)) raw;
      check_input_prepare_guarded (zi 7) (to_z a));
    check a b;
    List.iter (fun p -> check_normalize p a) [1; 2; 7; 17];
    let m = List.init (Random.State.int rng 10) (fun _ -> Random.State.int rng 5) in
    check_scale (List.sort compare m) (Random.State.int rng 13 - 6) a
  done;
  let ordered = List.init 256 (fun i -> [zi i, Z.one], zi (i - 127)) in
  check_guarded_normalize_metered (zi 17) ordered;
  let bound = P.guarded_normalize_bound ordered in
  (match P.guarded_normalize_metered bound (zi 17) ordered,
         P.normalize_metered bound (zi 17) ordered with
   | Some (fast, fw), Some (old, ow) ->
     if fast <> old || Z.geq fw ow then failwith "ordered normalization work reduction";
     Printf.printf "ordered 256-term normalization: guarded=%s original=%s abstract units\n"
       (Z.to_string fw) (Z.to_string ow)
   | _ -> failwith "ordered normalization comparison exhausted fuel");
  let even = List.init 128 (fun i -> [zi (2 * i), Z.one], zi (i - 63)) in
  let odd = List.init 128 (fun i -> [zi (2 * i + 1), Z.one], zi (i - 63)) in
  check_add_guarded (zi 17) even odd;
  let bound = P.add_guarded_normalize_bound even odd in
  (match P.add_guarded_normalize_metered bound (zi 17) even odd,
         P.add_normalize_metered bound (zi 17) even odd with
   | Some (fast, fw), Some (old, ow) ->
     if fast <> old || Z.geq fw ow then failwith "ordered addition work reduction";
     Printf.printf "ordered 128+128-term addition: guarded=%s original=%s abstract units\n"
       (Z.to_string fw) (Z.to_string ow)
   | _ -> failwith "ordered addition comparison exhausted fuel");
  print_endline "compact finite-field polynomial tests passed"
