module A = Z3AstTheory
module D = Z3ExprScope

let original scope n s =
  Z.lt n (FStar_List_Tot_Base.length scope) &&
  FStar_List_Tot_Base.index scope n = s

let outcome action =
  try `Value (action ()) with error -> `Error (Printexc.to_string error)

let () =
  let b = A.bool_sort and i = Z3LinearArithmeticAst.int_s in
  let check scope n s =
    if outcome (fun () -> D.scoped scope (A.Var (n, s))) <>
       outcome (fun () -> original scope n s) then
      failwith "scope variable lookup changed" in
  List.iter (fun (scope, n, s) -> check scope n s) [
    [], Z.zero, b;
    [b; i; b], Z.zero, b;
    [b; i; b], Z.one, i;
    [b; i; b], Z.one, b;
    [b; i; b], Z.of_int 2, b;
    [b; i; b], Z.of_int 3, b;
    [b; i; b], Z.shift_left Z.one 256, b;
    [], Z.minus_one, b;
    [b; i; b], Z.minus_one, b;
    List.init 128 (fun n -> if n = 0 then b else i), Z.zero, b;
    List.init 128 (fun _ -> i), Z.of_int 127, i
  ];
  let quantified n =
    A.Quantifier (A.Forall_k, [b; i], b, A.Var (Z.of_int n, b)) in
  if not (D.scoped [] (quantified 1)) || D.scoped [] (quantified 0) then
    failwith "quantifier scope ordering changed";
  print_endline "scope lookup fast-path tests passed"
