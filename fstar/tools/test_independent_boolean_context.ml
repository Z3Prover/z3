module N = Z3BooleanNormalForm
module B = Z3BoundedBoolEquiv
module A = Z3AstTheory

let reference s t =
  N.normal_equivalent s t || N.direct_contextual_equivalent s t ||
  N.direct_contextual_equivalent (N.normalize false s) (N.normalize false t) ||
  N.direct_contextual_equivalent (N.normalize true s) (N.normalize true t) ||
  N.direct_contextual_equivalent (N.reverse s) (N.reverse t) ||
  N.direct_contextual_equivalent (N.reverse (N.normalize false s)) (N.reverse (N.normalize false t))

let atom n = B.Atom (A.Var (Z.of_int n, A.bool_sort))

let () =
  let check a b =
    if N.contextual_equivalent a b <> reference a b then
      failwith "cached contextual equivalence changed" in
  let fixtures = [
    B.Bool true; B.Bool false; atom 0; B.Not (atom 0);
    B.Nary (B.Or, [atom 0; B.Not (atom 0)]);
    B.Nary (B.And, [atom 0; atom 1]);
    B.Implies (atom 0, atom 1); B.Eq (atom 0, atom 1);
    B.Nary (B.Xor, [atom 0; atom 1])
  ] in
  List.iter (fun a -> List.iter (check a) fixtures) fixtures;
  let rng = Random.State.make [| 2026; 11; 14 |] in
  let rec formula depth =
    if depth = 0 then atom (Random.State.int rng 4)
    else match Random.State.int rng 7 with
      | 0 -> B.Bool (Random.State.bool rng)
      | 1 -> B.Not (formula (depth - 1))
      | 2 -> B.Implies (formula (depth - 1), formula (depth - 1))
      | 3 -> B.Eq (formula (depth - 1), formula (depth - 1))
      | k ->
          let op = if k = 4 then B.And else if k = 5 then B.Or else B.Xor in
          B.Nary (op, [formula (depth - 1); formula (depth - 1)]) in
  for _ = 1 to 128 do check (formula 4) (formula 4) done;
  let rec shared depth =
    if depth = 0 then atom 0
    else let child = shared (depth - 1) in B.Nary (B.Or, [child; child]) in
  check (shared 8) (atom 0);
  print_endline "cached contextual equivalence tests passed"
