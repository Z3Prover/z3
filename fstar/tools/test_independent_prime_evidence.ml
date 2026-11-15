module Cert = Z3IndependentPrimeEvidence
module Factor = Z3IndependentFactorPrime

let zi = Z.of_int

let factors n =
  let rec loop n d acc =
    if n = 1 then List.rev acc
    else if n mod d = 0 then loop (n / d) d (zi d :: acc)
    else loop n (d + 1) acc in
  loop n 2 []

let prime n =
  n >= 2 &&
  let rec loop d = d * d > n || (n mod d <> 0 && loop (d + 1)) in
  loop 2

let reference n a fs =
  let n = zi n and a = zi a in
  let e = Z.pred n in
  Z.equal (Z.powm a e n) Z.one &&
  List.for_all (fun q ->
    Z.equal (Z.gcd (Z.pred (Z.powm a (Z.divexact e q) n)) n) Z.one) fs

let expect label expected n a fs =
  let actual = Cert.check n a fs in
  if actual <> expected then failwith (label ^ ": unexpected result")

let () =
  let check_factor n =
    if Factor.factor_prime (zi n) <> prime n then
      failwith (Printf.sprintf "incorrect factor primality for %d" n) in
  for n = 65520 to 65600 do check_factor n done;
  for n = 268435400 to 268435456 do check_factor n done;
  List.iter check_factor
    [2; 3; 11; 19; 10177; 906349; 2508409; 125527; 859267; 2529403;
     52437899; 254760293; 906349 * 3; 16381 * 16381];
  if Factor.factor_prime (zi 268435457) then failwith "oversized factor accepted";
  for n = 2 to 100 do
    let fs = factors (n - 1) in
    for a = 0 to n - 1 do
      expect (Printf.sprintf "n=%d a=%d" n a)
        (prime n && reference n a fs) (zi n) (zi a) fs
    done
  done;
  expect "prime 65537" true (zi 65537) (zi 3) (List.init 16 (fun _ -> zi 2));
  expect "prime 97" true (zi 97) (zi 5) (factors 96);
  expect "nonadjacent repeated factor" true (zi 97) (zi 5)
    (List.map zi [2; 3; 2; 2; 2; 2]);
  expect "repeated factor with invalid base" false (zi 17) (zi 4)
    (List.init 4 (fun _ -> zi 2));
  expect "too many repeated factors" false (zi 17) (zi 3)
    (List.init 5 (fun _ -> zi 2));
  expect "missing factor" false (zi 7) (zi 3) [zi 2];
  expect "extra factor" false (zi 7) (zi 3) [zi 2; zi 3; zi 2];
  expect "composite factor" false (zi 7) (zi 3) [zi 6];
  expect "zero factor" false (zi 7) (zi 3) [Z.zero; zi 2; zi 3];
  expect "unit factor" false (zi 7) (zi 3) [Z.one; zi 2; zi 3];
  expect "negative factor" false (zi 7) (zi 3) [zi (-2); zi 3];
  expect "oversized factor" false (zi 7) (zi 3) [zi 268435457];
  expect "too many factors" false (zi 7) (zi 3) (List.init 257 (fun _ -> zi 2));
  expect "Fermat pseudoprime" false (zi 15) (zi 4) [zi 2; zi 7];
  expect "negative base" false (zi 7) (zi (-1)) [zi 2; zi 3];
  expect "base out of range" false (zi 7) (zi 7) [zi 2; zi 3];
  expect "out of range modulus" false (Z.succ (Z.shift_left Z.one 256)) Z.one [];
  let p = Z.of_string
      "52435875175126190479447740508185965837690552500527637822603658699938581184513" in
  let artifact_factors =
    List.init 32 (fun _ -> zi 2) @
    List.map zi [3; 11; 19; 10177; 906349; 906349; 2508409; 125527;
                 859267; 2529403; 52437899; 254760293; 254760293] in
  expect "255-bit artifact modulus" true p (zi 7) artifact_factors;
  expect "255-bit incomplete factors" false p (zi 7) (List.tl artifact_factors);
  print_endline "bounded Lucas evidence tests passed"
