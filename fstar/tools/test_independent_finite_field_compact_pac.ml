module A = Z3AstTheory
module T = Z3OperatorTags
module F = Z3SortedFiniteField
module C = Z3FiniteFieldCertificate
module I = Z3ProofIndex
module R = Z3IndependentFiniteFieldCompactReplay
module P = Z3IndependentFiniteFieldCompactPac

let zi = Z.of_int
let some = function Some x -> x | None -> failwith "expected PAC step"
let none = function None -> () | Some _ -> failwith "unexpected PAC step"
let term vars coefficient = List.map zi vars, zi coefficient

let numeral p k =
  A.App ({ A.decl_name = "num"; domain = []; range = F.ff_sort (zi p);
           interp = Some F.op_ff_num; int_params = [zi p; zi k] }, [])

let () =
  let lit = A.App ({ A.decl_name = "p"; domain = []; range = A.bool_sort;
                     interp = None; int_params = [] }, []) in
  let not_lit = A.App ({ A.decl_name = "not"; domain = [A.bool_sort];
                         range = A.bool_sort; interp = Some T.op_not; int_params = [] }, [lit]) in
  let eqs = I.Empty
    |> fun t -> I.index_put t (zi 0) ([term [0] 1], F.Definition)
    |> fun t -> I.index_put t (zi 1) ([term [] 1; term [0] (-1)], F.Premise (zi 0, lit))
    |> fun t -> I.index_put t (zi 2) ([], F.Witness)
    |> fun t -> I.index_put t (zi 3) ([term [1; 0] 1], F.Definition) in
  let sup = I.index_put I.Empty (zi 0) true in
  let run s n = P.step (zi 7) (zi 2) eqs sup [not_lit] s n in
  none (run P.initial (C.PacInput (zi (-1))));
  none (run P.initial (C.PacInput (zi 4)));
  none (run P.initial (C.PacInput (zi 2)));
  none (run P.initial (C.PacInput (zi 3)));
  none (P.step (zi 7) (zi 2) eqs I.Empty [not_lit] P.initial (C.PacInput (zi 1)));
  none (P.step (zi 7) (zi 2) eqs sup [lit] P.initial (C.PacInput (zi 1)));
  let nodes = [C.PacInput (zi 0); C.PacInput (zi 1); C.PacAdd (zi 0, zi 1)] in
  let result = some (P.replay_nodes (zi 7) (zi 2) eqs sup [not_lit] P.initial nodes) in
  if not (R.unit_root result.P.core (zi 2)) ||
     I.index_get result.P.used (zi 0) <> Some true then failwith "root or support";
  none (run result (C.PacAdd (zi 0, zi 3)));
  none (run result (C.PacMul (zi 0, numeral 5 2, [zi 0])));
  none (run result (C.PacMul (zi 0, numeral 7 2, [zi 1; zi 0])));
  none (run result (C.PacMul (zi 0, numeral 7 2, [zi 2])));
  none (run result (C.PacMul (zi 0, lit, [zi 0])));
  let scaled = some (run result (C.PacMul (zi 0, numeral 7 2, [zi 0; zi 1]))) in
  let expected = [[zi 0, zi 2; zi 1, zi 1], zi 2] in
  if R.earlier scaled.P.core (zi 3) <> Some expected ||
     I.index_get scaled.P.used (zi 0) <> Some true then failwith "multiply or support";
  print_endline "compact finite-field PAC node tests passed"
