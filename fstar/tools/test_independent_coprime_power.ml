module Coprime = Z3IndependentCoprimePower

let check a e n =
  let actual = Coprime.coprime_power a e n in
  let expected = Z.equal (Z.gcd (Z.pred (Z.powm a e n)) n) Z.one in
  if actual <> expected then
    failwith (Printf.sprintf "coprimality mismatch: a=%s e=%s n=%s"
                (Z.to_string a) (Z.to_string e) (Z.to_string n))

let () =
  for a = -8 to 8 do
    for e = 0 to 15 do
      for n = 2 to 40 do
        check (Z.of_int a) (Z.of_int e) (Z.of_int n)
      done
    done
  done;
  let n = Z.of_string
      "52435875175126190479447740508185965837690552500527637822603658699938581184513" in
  check (Z.of_int 7) (Z.pred n) n;
  check (Z.of_int 7) (Z.divexact (Z.pred n) (Z.of_int 3)) n;
  check (Z.of_int 4) (Z.of_int 7) (Z.of_int 15);
  print_endline "modular-power coprimality tests passed"
