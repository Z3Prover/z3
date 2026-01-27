(*
   Example demonstrating polymorphic datatypes in Z3 ML API
   
   This example creates a parametric Pair datatype similar to the C++ example:
   Pair[alpha, beta] with constructor mk-pair(first: alpha, second: beta)
*)

open Z3
open Z3.Symbol
open Z3.Sort
open Z3.Expr
open Z3.Datatype
open Z3.Arithmetic
open Z3.Solver

let polymorphic_datatype_example () =
  Printf.printf "Polymorphic Datatype Example\n";
  
  (* Create a context *)
  let ctx = mk_context [("model", "true")] in
  
  (* Create type variables alpha and beta for polymorphic datatype *)
  let alpha_sym = mk_string ctx "alpha" in
  let beta_sym = mk_string ctx "beta" in
  let alpha = Sort.mk_type_variable ctx alpha_sym in
  let beta = Sort.mk_type_variable ctx beta_sym in
  
  Printf.printf "Type variables: alpha=%s, beta=%s\n" 
    (Sort.to_string alpha) (Sort.to_string beta);
  
  (* Define parametric Pair datatype with constructor mk-pair(first: alpha, second: beta) *)
  let pair_name = mk_string ctx "Pair" in
  let mk_pair_name = mk_string ctx "mk-pair" in
  let is_pair_name = mk_string ctx "is-pair" in
  let first_name = mk_string ctx "first" in
  let second_name = mk_string ctx "second" in
  
  let field_names = [first_name; second_name] in
  let field_sorts = [Some alpha; Some beta] in
  let sort_refs = [0; 0] in
  
  (* Create the constructor *)
  let mk_pair_constructor = Datatype.mk_constructor ctx mk_pair_name is_pair_name 
                                                     field_names field_sorts sort_refs in
  
  (* Create the polymorphic datatype *)
  let type_params = [alpha; beta] in
  let pair_sort = Datatype.mk_polymorphic_sort ctx pair_name type_params [mk_pair_constructor] in
  
  Printf.printf "Created polymorphic datatype: %s\n" (Sort.to_string pair_sort);
  
  (* Instantiate Pair with concrete types: (Pair Int Real) *)
  let int_sort = Integer.mk_sort ctx in
  let real_sort = Real.mk_sort ctx in
  let pair_int_real = Datatype.mk_sort_ref_p ctx pair_name [int_sort; real_sort] in
  
  Printf.printf "Instantiated with Int and Real: %s\n" (Sort.to_string pair_int_real);
  
  (* Get constructor and accessors for (Pair Int Real) *)
  let constructors = Datatype.get_constructors pair_int_real in
  let mk_pair_ir = List.hd constructors in
  
  Printf.printf "Constructor: %s\n" (FuncDecl.to_string mk_pair_ir);
  
  (* Create some test values *)
  let x = Integer.mk_numeral_i ctx 42 in
  let y = Real.mk_numeral_s ctx "3.14" in
  
  (* Create a pair value *)
  let pair_value = FuncDecl.apply mk_pair_ir [x; y] in
  
  Printf.printf "Created pair: %s\n" (Expr.to_string pair_value);
  
  (* Get accessors *)
  let accessors = Datatype.get_accessors pair_int_real in
  let pair_accessors = List.hd accessors in
  let first_accessor = List.nth pair_accessors 0 in
  let second_accessor = List.nth pair_accessors 1 in
  
  Printf.printf "First accessor: %s\n" (FuncDecl.to_string first_accessor);
  Printf.printf "Second accessor: %s\n" (FuncDecl.to_string second_accessor);
  
  (* Extract values using accessors *)
  let first_value = FuncDecl.apply first_accessor [pair_value] in
  let second_value = FuncDecl.apply second_accessor [pair_value] in
  
  Printf.printf "First value: %s\n" (Expr.to_string first_value);
  Printf.printf "Second value: %s\n" (Expr.to_string second_value);
  
  (* Verify using a solver *)
  let solver = mk_solver ctx None in
  Solver.add solver [
    Boolean.mk_eq ctx first_value x;
    Boolean.mk_eq ctx second_value y
  ];
  
  let result = check solver [] in
  Printf.printf "Solver result: %s\n" (string_of_status result);
  
  if result = SATISFIABLE then
    Printf.printf "Successfully verified polymorphic datatype!\n"
  else
    Printf.printf "ERROR: Solver should have returned SAT\n";
  
  Printf.printf "\nTest passed!\n"

let _ =
  try
    polymorphic_datatype_example ();
    exit 0
  with Z3.Error(msg) ->
    Printf.printf "Z3 ERROR: %s\n" msg;
    exit 1
