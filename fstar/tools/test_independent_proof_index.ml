module I = Z3IndependentProofIndex
module T = Z3ProofIndex

let zi = Z.of_int

let check_get tree key expected =
  let bound = I.depth key in
  if I.get_metered Z.zero tree key <> None then failwith "zero lookup fuel";
  match I.get_metered bound tree key with
  | None -> failwith "lookup exhausted depth bound"
  | Some (result, work) ->
    if result <> expected || Z.leq work Z.zero || Z.gt work bound ||
       I.get_metered (Z.pred work) tree key <> None ||
       I.get_metered work tree key <> Some (result, work)
    then failwith "metered lookup"

let put tree key value =
  let bound = I.depth key in
  if I.put_metered (Z.pred bound) tree key value <> None then
    failwith "insertion accepted insufficient fuel";
  match I.put_metered bound tree key value with
  | None -> failwith "insertion exhausted depth bound"
  | Some (result, work) ->
    if not (Z.equal work bound) ||
       I.put_metered (Z.add bound (zi 100)) tree key value <> Some (result, work)
    then failwith "metered insertion";
    result

let () =
  let huge = Z.shift_left Z.one 200 in
  check_get T.Empty huge None;
  (match I.get_metered Z.one T.Empty huge with
   | Some (None, work) when Z.equal work Z.one -> ()
   | _ -> failwith "missing lookup did not terminate early");
  let keys = [Z.zero; Z.one; zi 2; zi 3; zi 127; huge; Z.succ huge] in
  let tree = List.fold_left (fun tree key -> put tree key key) T.Empty keys in
  List.iter (fun key -> check_get tree key (Some key)) keys;
  check_get tree (zi 128) None;
  let updated = put tree huge (zi 42) in
  check_get tree huge (Some huge);
  check_get updated huge (Some (zi 42));
  List.iter (fun key -> if not (Z.equal key huge) then check_get updated key (Some key)) keys;
  let rng = Random.State.make [| 2026 |] in
  let values = Hashtbl.create 300 in
  let state = ref T.Empty in
  for _ = 1 to 2000 do
    let key = zi (Random.State.int rng 500) in
    let value = zi (Random.State.int rng 10000) in
    state := put !state key value;
    Hashtbl.replace values key value;
    let query = zi (Random.State.int rng 500) in
    check_get !state query (Hashtbl.find_opt values query)
  done;
  print_endline "metered proof index tests passed"
