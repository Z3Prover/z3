module B = Z3IndependentFiniteFieldBudget
module M = Z3IndependentFiniteFieldMonomial

let zi = Z.of_int

let check q weight degree coefficient =
  let compact = List.fold_left (fun total (m, _) -> total + 1 + List.length m) 0 q in
  let expanded = List.fold_left (fun total (m, _) ->
    total + 1 + List.fold_left (fun sum (_, n) -> sum + Z.to_int n) 0 m) 0 q in
  let bounded = List.for_all (fun (m, _) ->
    List.fold_left (fun sum (_, n) -> sum + Z.to_int n) 0 m <= degree) q in
  let coefficients = List.for_all (fun (_, c) -> Z.leq (Z.abs c) (zi coefficient)) q in
  if not (Z.equal (B.compact_weight q) (zi compact)) ||
     not (Z.equal (B.expanded_weight q) (zi expanded)) ||
     B.check (zi weight) (zi degree) q <> (compact <= weight && bounded) ||
     B.check_resources (zi weight) (zi degree) (zi coefficient) q <>
       (compact <= weight && bounded && coefficients)
  then failwith "compact budget accounting"

let () =
  check [] 0 0 0;
  let q = [[zi 0, zi 2; zi 1, zi 1], zi 3; [], zi (-2)] in
  List.iter (fun (w, d, c) -> check q w d c)
    [4, 3, 3; 4, 3, 2; 3, 3, 3; 4, 2, 3; 5, 4, 4; 4, 3, 0];
  let magnitude = Z.shift_left Z.one 512 in
  let coeffs = [[], magnitude; [], Z.neg magnitude] in
  if not (B.check_resources (zi 2) Z.zero magnitude coeffs) ||
     B.check_resources (zi 2) Z.zero (Z.pred magnitude) coeffs ||
     B.check_resources Z.one Z.zero magnitude coeffs then
    failwith "large signed coefficient bounds";
  let huge = Z.shift_left Z.one 200 in
  let q = [[zi 4, huge], zi 1] in
  if not (Z.equal (B.compact_weight q) (zi 2)) ||
     not (Z.equal (B.expanded_weight q) (Z.succ huge)) ||
     not (B.check (zi 2) huge q) || B.check (zi 2) (Z.pred huge) q ||
     B.check (zi 1) huge q then failwith "large compact degree";
  let rng = Random.State.make [| 1919 |] in
  for _ = 1 to 10000 do
    let q = List.init (Random.State.int rng 12) (fun _ ->
      let vars = List.init (Random.State.int rng 12) (fun _ -> zi (Random.State.int rng 5)) in
      M.compress vars, zi (Random.State.int rng 11 - 5)) in
    check q (Random.State.int rng 40) (Random.State.int rng 14) (Random.State.int rng 8)
  done;
  print_endline "compact finite-field budget tests passed"
