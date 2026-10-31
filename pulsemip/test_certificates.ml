module P = Z3LinearArithmeticTheory
module M = PulseMip_Model
module C = PulseMip_Certificate
module Q = PulseMip_Rational

let z = Z.of_int
let q num den : Q.rational = { num = z num; den = z den }
let poly cst mono : Z.t P.polynomial =
  { P.cst = z cst; denom = Z.one; mono = List.map (fun (a, v) -> z a, z v) mono }
let problem integers constraints objective : M.problem =
  { M.variables = Z.one; integers = List.map z integers; constraints; objective }

let check name expected actual =
  if actual <> expected then failwith name

let () =
  let p = problem [0] [poly 1 [(-1, 0)]] (poly 0 [(1, 0)]) in
  let good = C.Optimal ([q 1 1], C.LowerBound ([Z.one], Z.one)) in
  check "valid optimum" true (C.accepts p good);
  check "false optimum" false (C.accepts p (C.Optimal ([q 2 1], C.LowerBound ([Z.one], Z.one))));
  check "zero-scale fake optimality" false
    (C.accepts p (C.Optimal ([q 2 1], C.LowerBound ([Z.zero], Z.zero))));
  check "negative-scale fake optimality" false
    (C.accepts p (C.Optimal ([q 2 1], C.LowerBound ([Z.zero], z (-1)))));
  check "missing coefficient" false (C.accepts p (C.Infeasible (C.Contradiction [])));
  let trivial = problem [] [poly (-1) []] (poly 0 []) in
  check "negative Farkas weight" false (C.accepts trivial (C.Infeasible (C.Contradiction [z (-1)])));
  check "fractional integer" false (C.accepts p (C.Unknown (C.NodeLimit, Some [q 3 2])));
  check "zero denominator" false (C.accepts p (C.Unknown (C.NodeLimit, Some [q 1 0])));
  check "negative denominator" false (C.accepts p (C.Unknown (C.NodeLimit, Some [q (-1) (-1)])));
  check "wrong point dimension" false (C.accepts p (C.Unknown (C.NodeLimit, Some [])));
  let u = problem [0] [] (poly 0 [(-1, 0)]) in
  check "valid integer ray" true (C.accepts u (C.Unbounded ([q 0 1], [q 1 1])));
  check "zero direction" false (C.accepts u (C.Unbounded ([q 0 1], [q 0 1])));
  check "fractional integer ray" false (C.accepts u (C.Unbounded ([q 0 1], [q 1 2])));
  check "bad ray denominator" false (C.accepts u (C.Unbounded ([q 0 1], [q 1 0])));
  check "Euclidean negative floor" true (Z.equal (Q.floor (q (-3) 2)) (z (-2)));
  print_endline "PASS 15 exact-runtime and certificate-mutation checks"
