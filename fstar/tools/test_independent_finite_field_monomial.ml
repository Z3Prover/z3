module M = Z3IndependentFiniteFieldMonomial

let zi = Z.of_int

let rec less_expanded a b =
  match a, b with
  | [], [] -> false
  | [], _ -> true
  | _, [] -> false
  | x :: xs, y :: ys ->
    if Z.lt x y then true else if Z.gt x y then false else less_expanded xs ys

let check_less a b =
  if M.less a b <> less_expanded (M.expand a) (M.expand b) then
    failwith "compact monomial comparison";
  let bound = 1 + List.length a + List.length b in
  for fuel = 0 to bound do
    (match M.equal_metered (zi fuel) a b with
     | None -> if fuel = bound then failwith "metered equality completeness"
     | Some (result, work) ->
       if result <> (a = b) || Z.gt work (zi fuel) ||
          Z.gt work (zi bound) || Z.leq work Z.zero then
         failwith "metered equality correctness");
    match M.less_metered (zi fuel) a b with
    | None -> if fuel = bound then failwith "metered comparison completeness"
    | Some (result, work) ->
      if result <> M.less a b || Z.gt work (zi fuel) ||
         Z.gt work (zi bound) || Z.leq work Z.zero then
        failwith "metered comparison correctness"
  done

let check_compress_metered m =
  let bound = zi (List.length m + 1) in
  if M.compress_metered Z.zero m <> None then failwith "zero compression fuel";
  match M.compress_metered bound m with
  | None -> failwith "metered compression exhausted exact fuel"
  | Some (result, work) ->
    if result <> M.compress m || not (Z.equal work bound) then
      failwith "metered compression correctness";
    if M.compress_metered (Z.pred work) m <> None ||
       M.compress_metered (Z.add bound (zi 1000)) m <> Some (result, work) then
      failwith "metered compression fuel boundary"

let check_sorted_metered m =
  let bound = zi (List.length m + 1) in
  if M.sorted_metered Z.zero m <> None then failwith "zero sortedness fuel";
  match M.sorted_metered bound m with
  | None -> failwith "metered sortedness exhausted conservative fuel"
  | Some (result, work) ->
    if result <> M.sorted m || Z.leq work Z.zero || Z.gt work bound then
      failwith "metered sortedness correctness";
    if M.sorted_metered (Z.pred work) m <> None ||
       M.sorted_metered work m <> Some (result, work) ||
       M.sorted_metered (Z.add bound (zi 1000)) m <> Some (result, work) then
      failwith "metered sortedness fuel boundary"

let check_ordered_metered m =
  let bound = zi (List.length m + 1) in
  if M.ordered_metered Z.zero m <> None then failwith "zero ordering fuel";
  match M.ordered_metered bound m with
  | None -> failwith "metered ordering exhausted conservative fuel"
  | Some (result, work) ->
    if result <> M.ordered m || Z.leq work Z.zero || Z.gt work bound then
      failwith "metered ordering correctness";
    if M.ordered_metered (Z.pred work) m <> None ||
       M.ordered_metered work m <> Some (result, work) ||
       M.ordered_metered (Z.add bound (zi 1000)) m <> Some (result, work) then
      failwith "metered ordering fuel boundary"

let check xs =
  let m = List.map zi xs in
  check_compress_metered m;
  check_sorted_metered m;
  let compact = M.compress m in
  check_ordered_metered compact;
  if M.expand compact <> m then failwith "monomial round trip";
  List.iter (fun offset ->
    let valuation k = Z.sub k (zi offset) in
    let expected = List.fold_left (fun acc k -> Z.mul acc (valuation k)) Z.one m in
    if not (Z.equal (M.evaluate valuation compact) expected) then
      failwith "compact monomial evaluation") [0; 1; 3]

let check_multiply_metered a b =
  let bound = zi (1 + List.length a + List.length b) in
  if M.multiply_metered Z.zero a b <> None then failwith "zero product fuel";
  match M.multiply_metered bound a b with
  | None -> failwith "metered product exhausted conservative fuel"
  | Some (result, work) ->
    if result <> M.multiply a b || Z.leq work Z.zero || Z.gt work bound then
      failwith "metered product correctness";
    if M.multiply_metered (Z.pred work) a b <> None ||
       M.multiply_metered work a b <> Some (result, work) ||
       M.multiply_metered (Z.add bound (zi 1000)) a b <> Some (result, work) then
      failwith "metered product fuel boundary"

let check_multiply ?(ordered=true) xs ys =
  let a = M.compress (List.map zi xs) in
  let b = M.compress (List.map zi ys) in
  check_multiply_metered a b;
  let product = M.multiply a b in
  let expected = List.map zi (List.sort compare (xs @ ys)) in
  if not (Z.equal (M.degree product) (Z.add (M.degree a) (M.degree b))) ||
     List.length product > List.length a + List.length b then
    failwith "compact monomial product size";
  if ordered && not (M.sorted (List.map zi xs) && M.sorted (List.map zi ys) &&
                     M.ordered a && M.ordered b && M.ordered product) then
    failwith "compact monomial ordering";
  if ordered && (M.compress (M.expand a) <> a || M.compress (M.expand product) <> product)
  then failwith "ordered monomial canonicalization";
  if ordered && M.expand product <> expected then failwith "compact monomial product";
  List.iter (fun offset ->
    let valuation k = Z.sub k (zi offset) in
    let expected = Z.mul (M.evaluate valuation a) (M.evaluate valuation b) in
    if not (Z.equal (M.evaluate valuation product) expected) then
      failwith "compact monomial product evaluation") [0; 1; 3]

let () =
  check [];
  check [1; 1; 2; 2; 1; 3; 3; 3];
  if M.compress (List.map zi [1; 1; 2; 2; 1; 3; 3; 3]) <>
     List.map (fun (x, n) -> zi x, zi n) [1, 2; 2, 2; 1, 1; 3, 3]
  then failwith "incorrect adjacent run compression";
  check (List.init 300 (fun _ -> 2));
  check_multiply [] [0; 0; 1];
  check_multiply [0; 0; 2; 4; 4] [0; 1; 2; 2; 5];
  check_multiply ~ordered:false [3; 1; 1; 0] [3; 0; 3; 2];
  check_multiply (List.init 300 (fun _ -> 2)) [2; 2; 2];
  let huge = Z.shift_left Z.one 200 in
  check_compress_metered [huge; huge; Z.one; huge];
  check_sorted_metered [huge; huge; Z.one; huge];
  if M.sorted_metered Z.one (zi 2 :: zi 1 :: List.init 300 (fun _ -> Z.zero)) <>
     Some (false, Z.one) then failwith "sortedness did not reject early";
  let product = M.multiply [zi 1, huge] [zi 1, huge; zi 2, Z.one] in
  check_multiply_metered [zi 1, huge] [zi 1, huge; zi 2, Z.one];
  if not (Z.equal (M.degree product) (Z.succ (Z.mul (zi 2) huge))) ||
     List.length product <> 2 then failwith "large compact product size";
  (match M.less_metered (zi 2) [zi 1, huge] [zi 1, Z.succ huge] with
   | Some (true, work) when Z.equal work (zi 2) -> ()
   | _ -> failwith "large compact metered comparison");
  (match M.equal_metered (zi 2) [zi 1, huge] [zi 1, huge] with
   | Some (true, work) when Z.equal work (zi 2) -> ()
   | _ -> failwith "large compact metered equality");
  let runs xs = List.map (fun (x, n) -> zi x, zi n) xs in
  check_ordered_metered [huge, huge; Z.one, Z.one];
  if M.ordered_metered Z.one (runs [2, 1; 1, 1] @
                              List.init 300 (fun _ -> Z.zero, Z.one)) <>
     Some (false, Z.one) then failwith "ordering did not reject early";
  List.iter (fun (a, b) -> check_less (runs a) (runs b))
    [([], []); ([], [0, 1]); ([0, 1], []); ([0, 1], [1, 1]);
     ([0, 2], [0, 3]); ([0, 3], [0, 2]);
     ([0, 2; 3, 1], [0, 3; 2, 1]);
     ([0, 2; 3, 1], [0, 2; 3, 1]);
     ([0, 2; 3, 1], [0, 2; 3, 2]);
     ([0, 1; 0, 2], [0, 3]); ([1, 2; 0, 1], [1, 1; 0, 2])];
  (match M.equal_metered (zi 2) (runs [0, 2; 3, 1]) (runs [0, 2; 3, 1]),
         M.equal_metered (zi 3) (runs [0, 2; 3, 1]) (runs [0, 2; 3, 1]) with
   | None, Some (true, work) when Z.equal work (zi 3) -> ()
   | _ -> failwith "metered equality fuel boundary");
  if M.sorted (List.map zi [1; 2; 1]) ||
     M.ordered (List.map (fun (x, n) -> zi x, zi n) [1, 2; 1, 1]) ||
     M.ordered (List.map (fun (x, n) -> zi x, zi n) [2, 1; 1, 1])
  then failwith "unordered monomial accepted";
  let rng = Random.State.make [| 2026 |] in
  for _ = 1 to 10000 do
    let random_mono () = List.init (Random.State.int rng 20)
      (fun _ -> Random.State.int rng 6) in
    let xs = random_mono () and ys = random_mono () in
    check xs;
    check_less (M.compress (List.map zi xs)) (M.compress (List.map zi ys));
    check_multiply ~ordered:false xs ys;
    check_multiply (List.sort compare xs) (List.sort compare ys)
  done;
  print_endline "compact finite-field monomial tests passed"
