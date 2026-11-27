module M = Z3IndependentFiniteFieldCompactMetered
module R = Z3IndependentFiniteFieldCompactReplay
module I = Z3IndependentProofIndex
module T = Z3ProofIndex
module P = Z3IndependentFiniteFieldPolynomial
module N = Z3IndependentFiniteFieldMonomial

let zi = Z.of_int

let check_earlier s key =
  let bound = M.earlier_bound s key in
  if M.earlier_metered Z.zero s key <> None then failwith "zero lookup fuel";
  match M.earlier_metered bound s key with
  | None -> failwith "lookup exhausted bound"
  | Some (result, work) ->
    if result <> R.earlier s key || Z.leq work Z.zero || Z.gt work bound ||
       M.earlier_metered (Z.pred work) s key <> None ||
       M.earlier_metered work s key <> Some (result, work)
    then failwith "metered earlier"

let record s value =
  let bound = I.depth s.R.next in
  if M.record_metered (Z.pred bound) s value <> None then
    failwith "record accepted insufficient fuel";
  match M.record_metered bound s value with
  | None -> failwith "record exhausted bound"
  | Some (result, work) ->
    if not (Z.equal work bound) || not (Z.equal result.R.next (Z.succ s.R.next)) then
      failwith "metered record";
    result

let check_input p s q =
  let bound = M.input_bound s q in
  if M.input_metered Z.zero p s q <> None then failwith "zero input fuel";
  match M.input_metered bound p s q with
  | None -> failwith "input exhausted conservative bound"
  | Some (result, work) ->
    if result <> R.input p s q || Z.leq work Z.zero || Z.gt work bound ||
       M.input_metered (Z.pred work) p s q <> None ||
       M.input_metered work p s q <> Some (result, work)
    then failwith "metered input";
    (match P.input_prepare_guarded_metered bound p q, result with
     | Some (Some _, preparation_work), Some _ ->
       if not (Z.equal work (Z.add preparation_work (I.depth s.R.next))) then
         failwith "guarded input work accounting";
       if M.input_metered preparation_work p s q <> None then
         failwith "insertion did not consume remaining fuel"
     | Some (None, preparation_work), None ->
       if not (Z.equal preparation_work work) then failwith "rejected input work"
     | _ -> failwith "input preparation mismatch")

let check_add p s a b =
  let fuel = zi 1000000 in
  if M.add_metered Z.zero p s a b <> None then failwith "zero addition fuel";
  match M.add_metered fuel p s a b with
  | None -> failwith "addition exhausted test fuel"
  | Some (result, work) ->
    if result <> R.add p s a b || Z.leq work Z.zero || Z.gt work fuel ||
       M.add_metered (Z.pred work) p s a b <> None ||
       M.add_metered work p s a b <> Some (result, work)
    then failwith "metered addition";
    (match M.earlier_metered fuel s a with
     | Some (None, wa) ->
       if result <> None || not (Z.equal work wa) then failwith "first missing source"
     | Some (Some qa, wa) ->
       (match M.earlier_metered (Z.sub fuel wa) s b with
        | Some (None, wb) ->
          if result <> None || not (Z.equal work (Z.add wa wb)) then
            failwith "second missing source"
        | Some (Some qb, wb) ->
          (match P.add_guarded_normalize_metered fuel p qa qb with
           | Some (_, wp) ->
             let expected = Z.add (Z.add (Z.add wa wb) wp) (I.depth s.R.next) in
             if not (Z.equal work expected) then failwith "guarded addition work accounting";
             if M.add_metered (Z.add (Z.add wa wb) wp) p s a b <> None then
               failwith "addition insertion did not consume fuel"
           | None -> failwith "addition normalization exhausted test fuel")
        | None -> failwith "second lookup exhausted test fuel")
     | None -> failwith "first lookup exhausted test fuel")

let check_scale p s source m c =
  let fuel = zi 1000000 in
  if M.scale_metered Z.zero p s source m c <> None then failwith "zero scaling fuel";
  match M.scale_metered fuel p s source m c with
  | None -> failwith "scaling exhausted test fuel"
  | Some (result, work) ->
    if result <> R.scale p s source m c || Z.leq work Z.zero || Z.gt work fuel ||
       M.scale_metered (Z.pred work) p s source m c <> None ||
       M.scale_metered work p s source m c <> Some (result, work)
    then failwith "metered scaling";
    (match N.ordered_metered fuel m with
     | Some (false, wm) ->
       if result <> None || not (Z.equal work wm) then failwith "unordered factor"
     | Some (true, wm) ->
       (match M.earlier_metered (Z.sub fuel wm) s source with
        | Some (None, wq) ->
          if result <> None || not (Z.equal work (Z.add wm wq)) then
            failwith "missing scaling source"
        | Some (Some q, wq) ->
          (match P.scale_guarded_normalize_metered fuel p m c q with
           | Some (_, wp) ->
             let expected = Z.add (Z.add (Z.add wm wq) wp) (I.depth s.R.next) in
             if not (Z.equal work expected) then failwith "guarded scaling work accounting";
             if M.scale_metered (Z.add (Z.add wm wq) wp) p s source m c <> None then
               failwith "scaling insertion did not consume fuel"
           | None -> failwith "scaling normalization exhausted test fuel")
        | None -> failwith "scaling lookup exhausted test fuel")
     | None -> failwith "ordering exhausted test fuel")

let () =
  let s0 = R.initial in
  let hole = { R.values = T.Empty; next = zi 3 } in
  List.iter (check_earlier s0) [zi (-1); Z.zero; Z.one];
  check_earlier hole Z.zero;
  (match M.earlier_metered (zi 2) hole Z.zero with
   | Some (None, work) when Z.equal work (zi 2) -> ()
   | _ -> failwith "in-range missing reference");
  let s1 = record s0 [([], zi 7)] in
  check_earlier s0 Z.zero;
  check_earlier s1 Z.zero;
  let s = ref s1 in
  for i = 1 to 500 do
    let value = [([], zi i)] in
    let old = !s in
    s := record old value;
    check_earlier old (zi i);
    check_earlier !s (zi i);
    check_earlier !s (zi (i / 2));
    if R.earlier !s (zi i) <> Some value then failwith "recorded value"
  done;
  List.iter (check_earlier !s) [zi (-1); zi 501; Z.shift_left Z.one 200];
  let term xs c = List.map zi xs, zi c in
  List.iter (fun q -> check_input (zi 7) !s q)
    [[]; [term [] 0]; [term [0; 0; 2] 3; term [1; 3] (-4)];
     [term [2; 1] 7]; [term [0] 2; term [3; 1] 1]];
  (match M.input_metered (zi 2) (zi 7) !s [term [2; 1] 7] with
   | Some (None, work) when Z.equal work (zi 2) -> ()
   | _ -> failwith "unsorted input did not reject early");
  let rng = Random.State.make [| 2027 |] in
  for _ = 1 to 500 do
    let q = List.init (Random.State.int rng 5) (fun _ ->
      let variables = List.init (Random.State.int rng 6) (fun _ -> Random.State.int rng 5) in
      term variables (Random.State.int rng 15 - 7)) in
    List.iter (fun p -> check_input (zi p) !s q) [1; 2; 7]
  done;
  List.iter (fun (a, b) -> check_add (zi 7) !s (zi a) (zi b))
    [(-1, 0); (0, -1); (501, 0); (0, 501); (0, 0); (1, 250); (499, 500)];
  for _ = 1 to 500 do
    let a = zi (Random.State.int rng 505 - 2) in
    let b = zi (Random.State.int rng 505 - 2) in
    check_add (zi 7) !s a b
  done;
  let huge = Z.shift_left Z.one 200 in
  let large_state = record (record R.initial [([huge, Z.one], huge)])
      [([huge, Z.one], Z.neg huge)] in
  check_add (zi 7) large_state Z.zero Z.one;
  let ordered_state = record R.initial [[], Z.one; [Z.zero, Z.one], Z.one] in
  check_scale (zi 7) ordered_state Z.zero [Z.one, Z.one] Z.one;
  let even = List.init 128 (fun i -> [zi (2 * i), Z.one], zi (i - 63)) in
  let odd = List.init 128 (fun i -> [zi (2 * i + 1), Z.one], zi (i - 63)) in
  let ordered_pair = record (record R.initial even) odd in
  check_add (zi 17) ordered_pair Z.zero Z.one;
  List.iter (fun (source, runs, coefficient) ->
    check_scale (zi 7) !s (zi source)
      (List.map (fun (x, count) -> zi x, zi count) runs) (zi coefficient))
    [(-1, [], 1); (501, [0, 1], 0); (0, [], 0); (1, [0, 3; 2, 1], -3);
     (0, [2, 1; 1, 1], 1); (0, [1, 1; 1, 2], 1)];
  for _ = 1 to 500 do
    let runs = List.init (Random.State.int rng 5) (fun _ ->
      zi (Random.State.int rng 6), zi (1 + Random.State.int rng 3)) in
    check_scale (zi 7) !s (zi (Random.State.int rng 505 - 2)) runs
      (zi (Random.State.int rng 15 - 7))
  done;
  check_scale (zi 7) large_state Z.zero [huge, huge] (Z.neg huge);
  if M.scale_metered Z.one (zi 7) !s Z.zero [zi 2, Z.one; zi 1, Z.one] Z.one <>
     Some (None, Z.one) then failwith "unordered scaling factor did not reject early";
  if M.add_metered Z.one (zi 7) !s (zi (-1)) Z.zero <> Some (None, Z.one) then
    failwith "invalid first source did not reject early";
  print_endline "metered compact replay state tests passed"
