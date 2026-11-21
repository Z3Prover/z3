module Prime = Z3IndependentFiniteFieldPrime

let reference n =
  let rec check d =
    d * d > n || (n mod d <> 0 && check (d + 1)) in
  n >= 2 && check 2

let () =
  for n = -10 to 65536 do
    if Prime.small_prime (Z.of_int n) <> reference n then
      failwith (Printf.sprintf "incorrect primality result for %d" n)
  done;
  List.iter (fun n ->
    if Prime.small_prime n then failwith "oversized modulus was accepted")
    [Z.of_int 65537; Z.shift_left Z.one 255];
  print_endline "bounded finite-field primality tests passed"
