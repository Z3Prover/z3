module C = Z3FiniteFieldCertificate
module I = Z3ProofIndex
module R = Z3IndependentFiniteFieldCompactReplay
module P = Z3IndependentFiniteFieldCompactPac
module M = Z3IndependentFiniteFieldCompactPacMetered
module A = Z3AstTheory
module T = Z3OperatorTags
module W = Z3IndependentFiniteFieldWitness
module F = Z3SortedFiniteField
module CoreMetered = Z3IndependentFiniteFieldCompactMetered

let zi = Z.of_int
let some = function Some value -> value | None -> failwith "expected input"

let check_complement l lits =
  let bound = zi (List.length lits + 1) in
  if M.complementary_metered Z.zero l lits <> None then failwith "zero complement fuel";
  match M.complementary_metered bound l lits with
  | None -> failwith "complement exhausted list bound"
  | Some (result, work) ->
    if result <> W.complementary_in l lits || Z.leq work Z.zero || Z.gt work bound ||
       M.complementary_metered (Z.pred work) l lits <> None ||
       M.complementary_metered work l lits <> Some (result, work)
    then failwith "metered complementary scan"

let check p r a b =
  let fuel = zi 1000000 in
  let expected = P.step p Z.zero I.Empty I.Empty [] r (C.PacAdd (a, b)) in
  if M.add_step_metered Z.zero p r a b <> None then failwith "zero PAC addition fuel";
  match M.add_step_metered fuel p r a b with
  | None -> failwith "PAC addition exhausted test fuel"
  | Some (result, work) ->
    if result <> expected || Z.leq work Z.zero || Z.gt work fuel ||
       M.add_step_metered (Z.pred work) p r a b <> None ||
       M.add_step_metered work p r a b <> Some (result, work) then
      failwith "metered PAC addition";
    (match result with
     | None -> ()
     | Some output -> if output.P.used <> r.P.used then failwith "support changed")

let check_input p eqs sup lits r j =
  let fuel = zi 10000000 in
  let expected = P.step p (zi 2) eqs sup lits r (C.PacInput j) in
  if M.input_step_metered Z.zero p eqs sup lits r j <> None then
    failwith "zero PAC input fuel";
  match M.input_step_metered fuel p eqs sup lits r j with
  | None -> failwith "PAC input exhausted test fuel"
  | Some (result, work) ->
    if result <> expected || Z.leq work Z.zero || Z.gt work fuel ||
       M.input_step_metered (Z.pred work) p eqs sup lits r j <> None ||
       M.input_step_metered work p eqs sup lits r j <> Some (result, work)
    then failwith "metered PAC input"

let check_variables n previous fs =
  let bound = zi (List.length fs + 1) in
  if M.variables_metered Z.zero n previous fs <> None then failwith "zero variable fuel";
  match M.variables_metered bound n previous fs with
  | None -> failwith "variable conversion exhausted list bound"
  | Some (result, work) ->
    if result <> F.variables n previous fs || Z.leq work Z.zero || Z.gt work bound ||
       M.variables_metered (Z.pred work) n previous fs <> None ||
       M.variables_metered work n previous fs <> Some (result, work)
    then failwith "metered variable conversion"

let check_mul p nvars r source c fs =
  let fuel = zi 10000000 in
  let expected = P.step p nvars I.Empty I.Empty [] r (C.PacMul (source, c, fs)) in
  if M.mul_step_metered Z.zero p nvars r source c fs <> None then
    failwith "zero PAC multiplication fuel";
  match M.mul_step_metered fuel p nvars r source c fs with
  | None -> failwith "PAC multiplication exhausted test fuel"
  | Some (result, work) ->
    if result <> expected || Z.leq work Z.zero || Z.gt work fuel ||
       M.mul_step_metered (Z.pred work) p nvars r source c fs <> None ||
       M.mul_step_metered work p nvars r source c fs <> Some (result, work)
    then failwith "metered PAC multiplication";
    (match result with
     | None -> ()
     | Some output -> if output.P.used <> r.P.used then failwith "multiplication changed support")

let check_nodes p nvars eqs sup lits r nodes =
  let fuel = zi 10000000 in
  let expected = P.replay_nodes p nvars eqs sup lits r nodes in
  match M.replay_nodes_metered fuel p nvars eqs sup lits r nodes with
  | None -> failwith "PAC replay exhausted test fuel"
  | Some (result, work) ->
    if result <> expected || Z.lt work Z.zero || Z.gt work fuel ||
       M.replay_nodes_metered work p nvars eqs sup lits r nodes <> Some (result, work) ||
       (Z.gt work Z.zero &&
        M.replay_nodes_metered (Z.pred work) p nvars eqs sup lits r nodes <> None)
    then failwith "metered PAC replay";
    let rec run_steps fuel spent state = function
      | [] -> Some (Some state, spent)
      | node :: rest ->
        (match M.step_metered fuel p nvars eqs sup lits state node with
         | None -> None
         | Some (None, w) -> Some (None, Z.add spent w)
         | Some (Some next, w) -> run_steps (Z.sub fuel w) (Z.add spent w) next rest)
    in
    if run_steps fuel Z.zero r nodes <> Some (result, work) then
      failwith "PAC replay did not accumulate step fuel"

let check_metered_bool name expected run =
  if run Z.zero <> None || run (zi (-1)) <> None then
    failwith (name ^ ": nonpositive native fuel");
  match run (zi 1000000) with
  | None -> failwith (name ^ ": exhausted test fuel")
  | Some (result, work) ->
    if result <> expected || Z.leq work Z.zero || Z.gt work (zi 1000000) ||
       run work <> Some (result, work) || run (Z.pred work) <> None then
      failwith (name ^ ": result or exact fuel")

let check_finality r root support =
  check_metered_bool "unit root" (R.unit_root r.P.core root)
    (fun fuel -> M.unit_root_metered fuel r.P.core root);
  check_metered_bool "all support used" (F.all_used r.P.used support)
    (fun fuel -> M.all_used_metered fuel r.P.used support);
  check_metered_bool "combined finality"
    (R.unit_root r.P.core root && F.all_used r.P.used support)
    (fun fuel -> M.finalize_metered fuel r root support)

let () =
  let p = zi 7 in
  let atom name =
    A.App ({ A.decl_name = name; domain = []; range = A.bool_sort;
             interp = None; int_params = [] }, []) in
  let negate x =
    A.App ({ A.decl_name = "not"; domain = [A.bool_sort]; range = A.bool_sort;
             interp = Some T.op_not; int_params = [] }, [x]) in
  let lit = atom "p" in
  let other = atom "q" in
  let neg = negate lit in
  let numeral p k =
    A.App ({ A.decl_name = "num"; domain = []; range = F.ff_sort (zi p);
             interp = Some F.op_ff_num; int_params = [zi p; zi k] }, []) in
  List.iter (fun (l, lits) -> check_complement l lits)
    [(lit, []); (lit, [neg]); (neg, [lit]); (lit, [lit; other]);
     (lit, List.init 300 (fun _ -> other) @ [neg]);
     (neg, List.init 300 (fun _ -> other))];
  if M.complementary_metered Z.one lit (neg :: List.init 300 (fun _ -> other)) <>
     Some (true, Z.one) then failwith "complement did not match early";
  let first = some (R.input p R.initial [([zi 0], Z.one)]) in
  let second = some (R.input p first [([], Z.one); ([zi 0], Z.neg Z.one)]) in
  let used = I.index_put I.Empty (zi 99) true in
  let r = { P.core = second; used } in
  let even = List.init 128 (fun i -> [zi (2 * i), Z.one], zi (i - 63)) in
  let odd = List.init 128 (fun i -> [zi (2 * i + 1), Z.one], zi (i - 63)) in
  let ordered_core = {
    R.values = I.index_put (I.index_put I.Empty Z.zero even) Z.one odd;
    next = zi 2
  } in
  let ordered_replay = { P.core = ordered_core; used } in
  let ordered_nodes = [C.PacAdd (Z.zero, Z.one); C.PacAdd (zi 2, zi 2)] in
  check_nodes (zi 17) Z.zero I.Empty I.Empty [] ordered_replay ordered_nodes;
  (match CoreMetered.add_metered (zi 10000000) (zi 17) ordered_core Z.zero Z.one with
   | Some (Some next, first_work) ->
     (match CoreMetered.add_metered (zi 10000000) (zi 17) next (zi 2) (zi 2) with
      | Some (Some final, second_work) ->
        let total = Z.add first_work second_work in
        let expected = { P.core = final; used } in
        if M.replay_nodes_metered total (zi 17) Z.zero I.Empty I.Empty []
             ordered_replay ordered_nodes <> Some (Some expected, total) ||
           M.replay_nodes_metered (Z.pred total) (zi 17) Z.zero I.Empty I.Empty []
             ordered_replay ordered_nodes <> None then
          failwith "guarded ordered PAC cumulative fuel or support";
        Printf.printf "guarded ordered two-node PAC replay: %s abstract units\n"
          (Z.to_string total)
      | _ -> failwith "second guarded PAC reference step")
   | _ -> failwith "first guarded PAC reference step");
  let huge = Z.shift_left Z.one 200 in
  let eqs = I.Empty
    |> fun t -> I.index_put t Z.zero ([([Z.zero], Z.one)], F.Definition)
    |> fun t -> I.index_put t Z.one ([([], Z.one); ([Z.zero], Z.neg Z.one)], F.Premise (Z.zero, lit))
    |> fun t -> I.index_put t (zi 2) ([], F.Witness)
    |> fun t -> I.index_put t (zi 3) ([([Z.one; Z.zero], Z.one)], F.Definition)
    |> fun t -> I.index_put t (zi 4) ([([], Z.one)], F.Premise (huge, lit)) in
  let sup = I.index_put (I.index_put I.Empty Z.zero true) huge true in
  List.iter (fun j -> check_input p eqs sup [neg] r (zi j)) [-1; 0; 1; 2; 3; 4; 5];
  check_input p eqs I.Empty [neg] r Z.one;
  check_input p eqs (I.index_put I.Empty Z.zero false) [neg] r Z.one;
  check_input p eqs sup [lit] r Z.one;
  check_input p eqs sup (List.init 300 (fun _ -> other) @ [neg]) r Z.one;
  (match M.input_step_metered (zi 10000000) p eqs sup [neg] r (zi 4) with
   | Some (Some result, _) when I.index_get result.P.used huge = Some true &&
                               I.index_get result.P.used (zi 99) = Some true -> ()
   | _ -> failwith "premise support update");
  if M.input_step_metered Z.one p eqs sup [neg] r (zi (-1)) <> Some (None, Z.one) then
    failwith "negative PAC input did not reject early";
  List.iter (fun fs -> check_variables (zi 4) Z.zero (List.map zi fs))
    [[]; [0; 0; 1; 3]; [1; 0]; [-1]; [4]; List.init 300 (fun _ -> 1)];
  if M.variables_metered Z.one (zi 2) Z.zero (zi (-1) :: List.init 300 (fun _ -> Z.zero)) <>
     Some (None, Z.one) then failwith "invalid variable did not reject early";
  List.iter (fun (source, c, fs) ->
    check_mul p (zi 2) r (zi source) c (List.map zi fs))
    [(0, numeral 7 2, []); (0, numeral 7 2, [0; 0; 1]);
     (-1, numeral 7 2, [0]); (2, numeral 7 2, [0]);
     (0, numeral 5 2, [0]); (0, numeral 7 2, [1; 0]);
     (0, numeral 7 2, [2]); (0, lit, [0]); (0, numeral 7 7, [0])];
  check_mul p (Z.succ huge) r Z.zero (numeral 7 2) [huge; huge];
  if M.mul_step_metered Z.one p (zi 2) r Z.zero lit [Z.zero] <> Some (None, Z.one)
  then failwith "invalid numeral did not reject early";
  let nodes = [C.PacInput Z.zero; C.PacInput Z.one; C.PacAdd (zi 2, zi 3);
               C.PacMul (zi 4, numeral 7 2, [Z.zero])] in
  check_nodes p (zi 2) eqs sup [neg] r [];
  check_nodes p (zi 2) eqs sup [neg] r nodes;
  check_nodes p (zi 2) eqs sup [neg] r (nodes @ [C.PacInput (zi 2)]);
  check_nodes p (zi 2) eqs I.Empty [neg] r nodes;
  check_nodes p (zi 2) eqs sup [lit] r nodes;
  if M.replay_nodes_metered Z.zero p (zi 2) eqs sup [neg] r [] <> Some (Some r, Z.zero)
  then failwith "empty replay spent fuel";
  if M.replay_nodes_metered Z.zero p (zi 2) eqs sup [neg] r nodes <> None then
    failwith "nonempty replay accepted zero fuel";
  List.iter (fun (a, b) -> check p r (zi a) (zi b))
    [(-1, 0); (0, -1); (2, 0); (0, 2); (0, 0); (0, 1)];
  (match M.add_step_metered (zi 1000000) p r Z.zero Z.one with
   | Some (Some result, _) when R.unit_root result.P.core (zi 2) -> ()
   | _ -> failwith "PAC addition unit root");
  if M.add_step_metered Z.one p r (zi (-1)) Z.zero <> Some (None, Z.one) then
    failwith "invalid PAC source did not reject early";
  let rng = Random.State.make [| 2028 |] in
  for _ = 1 to 500 do
    check p r (zi (Random.State.int rng 6 - 2)) (zi (Random.State.int rng 6 - 2));
    check_input p eqs sup (if Random.State.bool rng then [lit] else [neg]) r
      (zi (Random.State.int rng 9 - 2));
    let candidates = [|lit; neg; other; negate other|] in
    let l = candidates.(Random.State.int rng 4) in
    let lits = List.init (Random.State.int rng 25)
      (fun _ -> candidates.(Random.State.int rng 4)) in
    check_complement l lits;
    let fs = List.init (Random.State.int rng 6) (fun _ -> zi (Random.State.int rng 5 - 1)) in
    check_variables (zi 2) Z.zero fs;
    check_mul p (zi 2) r (zi (Random.State.int rng 5 - 1))
      (if Random.State.bool rng then numeral 7 2 else numeral 5 1) fs;
    let nodes = List.init (Random.State.int rng 8) (fun _ ->
      match Random.State.int rng 3 with
      | 0 -> C.PacInput (zi (Random.State.int rng 8 - 1))
      | 1 -> C.PacAdd (zi (Random.State.int rng 5 - 1), zi (Random.State.int rng 5 - 1))
      | _ -> C.PacMul (zi (Random.State.int rng 5 - 1), numeral 7 2, fs)) in
    check_nodes p (zi 2) eqs sup [neg] r nodes
  done;
  check_nodes p (zi 2) eqs sup [neg] r
    (List.init 12000 (fun _ -> C.PacAdd (Z.zero, Z.zero)));
  let final_core = some (R.add p second Z.zero Z.one) in
  let final = { P.core = final_core; used = I.index_put I.Empty Z.zero true } in
  List.iter (fun root ->
    List.iter (fun support -> check_finality final root support)
      [[]; [Z.zero]; [Z.zero; Z.zero]; [Z.one]; [zi (-1)]; [huge]])
    [zi (-1); Z.zero; zi 2; zi 3; huge];
  check_finality { final with P.used = I.index_put I.Empty Z.zero false }
    (zi 2) [Z.zero];
  check_finality { P.core = { R.values = I.Empty; next = zi 3 }; used = I.Empty }
    (zi 2) [];
  List.iter (fun q ->
    let core = { R.values = I.index_put I.Empty Z.zero q; next = Z.one } in
    check_finality { P.core = core; used = I.Empty } Z.zero [])
    [[]; [([], zi 2)]; [([], Z.one); ([], Z.one)]; [([Z.zero, Z.one], Z.one)]];
  let huge_core = { R.values = I.index_put I.Empty huge [([], Z.one)]; next = Z.succ huge } in
  check_finality { P.core = huge_core; used = I.index_put I.Empty huge true } huge [huge];
  let support = List.init 12000 zi in
  let used = List.fold_left (fun tree key -> I.index_put tree key true) I.Empty support in
  check_finality { final with P.used = used } (zi 2) support;
  if M.finalize_metered Z.one final (zi (-1)) support <> Some (false, Z.one) ||
     M.all_used_metered Z.one used (Z.neg huge :: support) <> Some (false, Z.one) ||
     M.all_used_metered (zi 2) I.Empty (Z.zero :: support) <> Some (false, zi 2) then
    failwith "finality did not reject before scanning the unused tail";
  (match M.unit_root_metered (zi 1000000) final.P.core (zi 2),
         M.all_used_metered (zi 1000000) final.P.used [Z.zero] with
   | Some (true, root_work), Some (true, support_work) ->
     let total = Z.add root_work support_work in
     if M.finalize_metered total final (zi 2) [Z.zero] <> Some (true, total) ||
        M.finalize_metered (Z.pred total) final (zi 2) [Z.zero] <> None then
       failwith "finality did not share one fuel balance"
   | _ -> failwith "finality reference controls failed");
  print_endline "metered compact PAC step tests passed"
