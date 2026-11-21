module Pow = Z3IndependentModPow

let check a e p =
  let actual = Pow.pow_mod a e p in
  let expected = Z.powm a e p in
  if not (Z.equal actual expected) then
    failwith (Printf.sprintf "modular power mismatch: a=%s e=%s p=%s"
                (Z.to_string a) (Z.to_string e) (Z.to_string p))

let () =
  for a = -12 to 12 do
    for e = 0 to 20 do
      for p = 1 to 25 do
        check (Z.of_int a) (Z.of_int e) (Z.of_int p)
      done
    done
  done;
  let p = Z.of_string
      "52435875175126190479447740508185965837690552500527637822603658699938581184513" in
  check (Z.of_int 7) (Z.pred p) p;
  check (Z.neg p) (Z.shift_left Z.one 255) p;
  check (Z.neg (Z.add p (Z.of_int 7))) (Z.pred p) p;
  print_endline "modular exponentiation tests passed"
