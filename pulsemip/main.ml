module M = PulseMip_Model
module C = PulseMip_Certificate
module Q = PulseMip_Rational
module P = Z3LinearArithmeticTheory

let tokens () =
  String.split_on_char ' ' (String.trim (read_line ())) |> List.filter (fun s -> s <> "")

let natural s =
  let n = Z.of_string s in
  if Z.sign n < 0 then invalid_arg "negative dimension or search limit";
  n

let count s = Z.to_int (natural s)

let row n =
  match tokens () with
  | cst :: coefficients when List.length coefficients = n ->
      { P.cst = Z.of_string cst; denom = Z.one;
        mono = List.mapi (fun v a -> (Z.of_string a, Z.of_int v)) coefficients }
  | _ -> invalid_arg "wrong polynomial dimension"

let rational (q : Q.rational) =
  let g = Z.gcd q.num q.den in
  Z.to_string (Z.divexact q.num g) ^ "/" ^ Z.to_string (Z.divexact q.den g)

let point x = print_endline (String.concat " " (List.map rational x))

let strings xs =
  "[" ^ String.concat "," (List.map (fun n -> "\"" ^ Z.to_string n ^ "\"") xs) ^ "]"

let rec certificate = function
  | C.Contradiction weights ->
      "{\"kind\":\"infeasible\",\"weights\":" ^ strings weights ^ "}"
  | C.LowerBound (weights, scale) ->
      "{\"kind\":\"bound\",\"weights\":" ^ strings weights ^
      ",\"scale\":\"" ^ Z.to_string scale ^ "\"}"
  | C.Split (v, k, left, right) ->
      "{\"kind\":\"split\",\"variable\":" ^ Z.to_string v ^
      ",\"pivot\":\"" ^ Z.to_string k ^ "\",\"left\":" ^ certificate left ^
      ",\"right\":" ^ certificate right ^ "}"

let emit p = function
  | C.Optimal (x, t) ->
      print_endline "OPTIMAL"; point x; print_endline (rational (M.eval p.M.objective x));
      print_endline (certificate t)
  | C.Infeasible t -> print_endline "INFEASIBLE"; print_endline (certificate t)
  | C.Unbounded (x, d) -> print_endline "UNBOUNDED"; point x; point d
  | C.Unknown (reason, incumbent) ->
      let why = match reason with C.NodeLimit -> "NODE_LIMIT" | C.RowLimit -> "ROW_LIMIT" in
      (match incumbent with
       | None -> print_endline ("UNKNOWN " ^ why ^ " NONE")
       | Some x ->
           print_endline ("UNKNOWN " ^ why ^ " INCUMBENT"); point x;
           print_endline (rational (M.eval p.M.objective x)))
  | C.Error message -> print_endline ("ERROR " ^ message); exit 1

let main () =
  match tokens () with
  | [variables; integer_count; row_count; node_limit; row_limit] ->
      let n = count variables in
      let ni = count integer_count in
      let nr = count row_count in
      let nodes = natural node_limit in
      let rows = natural row_limit in
      let integers = List.map natural (tokens ()) in
      if List.length integers <> ni then invalid_arg "wrong integer variable count";
      let objective = row n in
      let constraints = List.init nr (fun _ -> row n) in
      let p = { M.variables = Z.of_int n; integers; objective; constraints } in
      emit p (PulseMip_Solver.solve p nodes rows)
  | _ -> invalid_arg "invalid solver protocol header"

let () =
  try main () with
  | Invalid_argument message | Failure message -> print_endline ("ERROR input: " ^ message); exit 1
  | End_of_file -> print_endline "ERROR input: incomplete problem"; exit 1
  | Z.Overflow -> print_endline "ERROR input: dimension exceeds host address space"; exit 1
