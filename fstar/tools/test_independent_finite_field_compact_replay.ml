module R = Z3IndependentFiniteFieldCompactReplay

let zi = Z.of_int
let some = function Some x -> x | None -> failwith "expected replay step"
let none = function None -> () | Some _ -> failwith "unexpected replay step"
let term vars coefficient = List.map zi vars, zi coefficient

let () =
  let p = zi 7 in
  let s0 = R.initial in
  none (R.add p s0 (zi 0) (zi 0));
  none (R.input p s0 [term [2; 1] 1]);
  let s1 = some (R.input p s0 [term [0; 0] 1; term [] (-1)]) in
  let s2 = some (R.input p s1 [term [0; 0] (-1); term [] 2]) in
  none (R.add p s2 (zi (-1)) (zi 0));
  none (R.add p s2 (zi 0) (zi 2));
  none (R.scale p s2 (zi 0) [zi 2, zi 1; zi 1, zi 1] (zi 3));
  let s3 = some (R.add p s2 (zi 0) (zi 1)) in
  if not (R.unit_root s3 (zi 2)) || R.unit_root s3 (zi 1) ||
     R.unit_root s3 (zi (-1)) || R.unit_root s3 (zi 3)
  then failwith "unit root";
  let s4 = some (R.scale p s3 (zi 0) [zi 2, zi 3] (zi 3)) in
  let expected = [[zi 0, zi 2; zi 2, zi 3], zi 3; [zi 2, zi 3], zi 4] in
  if R.earlier s4 (zi 3) <> Some expected || R.earlier s4 (zi 4) <> None ||
     R.earlier s1 (zi 1) <> None then failwith "scaled replay or state persistence";
  print_endline "compact finite-field replay state tests passed"
