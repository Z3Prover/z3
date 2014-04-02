(* 
   Copyright (C) 2012 Microsoft Corporation
   Author: CM Wintersteiger (cwinter) 2012-12-17
*)

open Z3
open Z3.Symbol
open Z3.Sort
open Z3.Expr
open Z3.Boolean
open Z3.FuncDecl
open Z3.Goal
open Z3.Tactic
open Z3.Tactic.ApplyResult
open Z3.Probe
open Z3.Solver
open Z3.Arithmetic
open Z3.Arithmetic.Integer
open Z3.Arithmetic.Real
open Z3.BitVector

exception TestFailedException of string

(**
   Model Converter test
*)
let  model_converter_test ( ctx : context ) =
  Printf.printf "ModelConverterTest\n";
  let xr = (Expr.mk_const ctx (Symbol.mk_string ctx "x") (Real.mk_sort ctx)) in
  let yr = (Expr.mk_const ctx (Symbol.mk_string ctx "y") (Real.mk_sort ctx)) in
  let g4 = (mk_goal ctx true false false ) in
  (Goal.add g4 [ (mk_gt ctx xr (Real.mk_numeral_nd ctx 10 1)) ]) ;
  (Goal.add g4 [ (mk_eq ctx 
			 yr
			 (Arithmetic.mk_add ctx [ xr; (Real.mk_numeral_nd ctx 1 1)  ])) ]) ;
  (Goal.add g4 [ (mk_gt ctx yr (Real.mk_numeral_nd ctx 1 1)) ]) ;
  (
    let  ar = (Tactic.apply (mk_tactic ctx "simplify") g4 None) in
    if ((get_num_subgoals ar) == 1 && 
	   ((is_decided_sat (get_subgoal ar 0)) ||  
	       (is_decided_unsat (get_subgoal ar 0)))) then
      raise (TestFailedException "")
    else
      Printf.printf "Test passed.\n"
  );
  (
    let ar = (Tactic.apply (and_then ctx (mk_tactic ctx ("simplify")) (mk_tactic ctx "solve-eqs") []) g4 None) in
    if ((get_num_subgoals ar) == 1 && 
	   ((is_decided_sat (get_subgoal ar 0)) ||  
	       (is_decided_unsat (get_subgoal ar 0)))) then
      raise (TestFailedException "")
    else
      Printf.printf "Test passed.\n"
    ;
    let solver = (mk_solver ctx None) in
    let f e = (Solver.add solver [ e ]) in
    ignore (List.map f (get_formulas (get_subgoal ar 0))) ;
    let q = (check solver []) in
    if q != SATISFIABLE then 
      raise (TestFailedException "")
    else
      let m = (get_model solver) in    
      match m with 
	| None -> raise (TestFailedException "")
	| Some (m) -> 
	  Printf.printf "Solver says: %s\n" (string_of_status q) ;
	  Printf.printf "Model: \n%s\n" (Model.to_string m) ;
	  Printf.printf "Converted Model: \n%s\n" (Model.to_string (convert_model ar 0 m))
  )

(**
 Some basic tests.
*)
let basic_tests ( ctx : context ) =
  Printf.printf "BasicTests\n" ;
(*  let qi = (mk_int ctx 1) in *)
  let fname = (mk_string ctx "f") in
  let x = (mk_string ctx "x") in
  let y = (mk_string ctx "y") in
  let bs = (Boolean.mk_sort ctx) in
  let domain = [ bs; bs ] in
  let f = (FuncDecl.mk_func_decl ctx fname domain bs) in
  let fapp = (mk_app ctx f 
		[ (Expr.mk_const ctx x bs); (Expr.mk_const ctx y bs) ]) in
  let fargs2 = [ (mk_fresh_const ctx "cp" bs) ] in
  let domain2 = [ bs ] in
  let fapp2 = (mk_app ctx (mk_fresh_func_decl ctx "fp" domain2 bs) fargs2) in
  let trivial_eq = (mk_eq ctx fapp fapp) in
  let nontrivial_eq = (mk_eq ctx fapp fapp2) in
  let g = (mk_goal ctx true false false) in
  (Goal.add g [ trivial_eq ]) ;
  (Goal.add g [ nontrivial_eq ]) ;
  Printf.printf "%s\n" ("Goal: " ^ (Goal.to_string g)) ;
  (
    let solver = (mk_solver ctx None) in
    (List.iter (fun a -> (Solver.add solver [ a ])) (get_formulas g)) ;
    if (check solver []) != SATISFIABLE then
      raise (TestFailedException "")
    else
      Printf.printf "Test passed.\n"
  );
  (
    let ar = (Tactic.apply (mk_tactic ctx "simplify") g None) in
    if ((get_num_subgoals ar) == 1 && 
	   ((is_decided_sat (get_subgoal ar 0)) ||  
	       (is_decided_unsat (get_subgoal ar 0)))) then
      raise (TestFailedException "")
    else
      Printf.printf "Test passed.\n"
  );
  (
    let ar = (Tactic.apply (mk_tactic ctx "smt") g None) in
    if ((get_num_subgoals ar) == 1 && 
	   (not (is_decided_sat (get_subgoal ar 0)))) then
      raise (TestFailedException "")
    else
      Printf.printf "Test passed.\n"
  );
  (Goal.add g [ (mk_eq ctx 
			(mk_numeral_int ctx 1 (BitVector.mk_sort ctx 32))
			(mk_numeral_int ctx 2 (BitVector.mk_sort ctx 32))) ] )
  ;
  (
    let ar = (Tactic.apply (mk_tactic ctx "smt") g None) in
    if ((get_num_subgoals ar) == 1 && 
	   (not (is_decided_unsat (get_subgoal ar 0)))) then
      raise (TestFailedException "")
    else 
      Printf.printf "Test passed.\n"
  );
  (
    let g2 = (mk_goal ctx true true false) in
    let ar = (Tactic.apply (mk_tactic ctx "smt") g2 None) in
    if ((get_num_subgoals ar) == 1 && 
	   (not (is_decided_sat (get_subgoal ar 0)))) then
      raise (TestFailedException "")
    else
      Printf.printf "Test passed.\n"
  );
  (
    let g2 = (mk_goal ctx true true false) in
    (Goal.add g2 [ (Boolean.mk_false ctx) ]) ;
    let ar = (Tactic.apply (mk_tactic ctx "smt") g2 None) in
    if ((get_num_subgoals ar) == 1 && 
	   (not (is_decided_unsat (get_subgoal ar 0)))) then
      raise (TestFailedException "")
    else 
      Printf.printf "Test passed.\n"
  );
  (
    let g3 = (mk_goal ctx true true false) in
    let xc = (Expr.mk_const ctx (Symbol.mk_string ctx "x") (Integer.mk_sort ctx)) in
    let yc = (Expr.mk_const ctx (Symbol.mk_string ctx "y") (Integer.mk_sort ctx)) in
    (Goal.add g3 [ (mk_eq ctx xc (mk_numeral_int ctx 1 (Integer.mk_sort ctx))) ]) ;
    (Goal.add g3 [ (mk_eq ctx yc (mk_numeral_int ctx 2 (Integer.mk_sort ctx))) ]) ;
    let constr = (mk_eq ctx xc yc) in
    (Goal.add g3 [ constr ] ) ;
    let ar = (Tactic.apply (mk_tactic ctx "smt") g3 None) in
    if ((get_num_subgoals ar) == 1 && 
	   (not (is_decided_unsat (get_subgoal ar 0)))) then
      raise (TestFailedException "")
    else 
      Printf.printf "Test passed.\n"
  ) ;
  model_converter_test ctx ;
  (* Real num/den test. *)
  let rn = Real.mk_numeral_nd ctx 42 43 in
  let inum = (get_numerator rn) in
  let iden = get_denominator rn in
  Printf.printf "Numerator: %s Denominator: %s\n" (Real.to_string inum) (Real.to_string iden) ;
  if ((Real.to_string inum) <> "42" or (Real.to_string iden) <> "43") then
    raise (TestFailedException "")
  else 
    Printf.printf "Test passed.\n"
  ;
  if ((to_decimal_string rn 3) <> "0.976?") then
    raise (TestFailedException "")
  else 
    Printf.printf "Test passed.\n"
  ;
  if (to_decimal_string (Real.mk_numeral_s ctx "-1231231232/234234333") 5 <> "-5.25640?") then
    raise (TestFailedException "")
  else if (to_decimal_string (Real.mk_numeral_s ctx "-123123234234234234231232/234234333") 5 <> "-525641278361333.28170?") then
    raise (TestFailedException "")
  else if (to_decimal_string (Real.mk_numeral_s ctx "-234234333") 5 <> "-234234333") then
    raise (TestFailedException "")
  else if (to_decimal_string (Real.mk_numeral_s ctx "234234333/2") 5 <> "117117166.5") then
    raise (TestFailedException "")
  ;
  (* Error handling test. *)
  try (
    let i = Integer.mk_numeral_s ctx "1/2" in
    raise (TestFailedException "") (* unreachable *)
  )
  with Z3native.Exception(_) -> (
    Printf.printf "Exception caught, OK.\n" 
  )

(**
   A basic example of how to use quantifiers.
**)
let  quantifierExample1 ( ctx : context ) =
  Printf.printf "QuantifierExample\n" ;
  let is = (Integer.mk_sort ctx) in
  let types = [ is; is; is ] in
  let names = [ (Symbol.mk_string ctx "x_0");
		(Symbol.mk_string ctx "x_1");
		(Symbol.mk_string ctx "x_2") ] in
  let vars = [ (Quantifier.mk_bound ctx 2 (List.nth types 0));
	       (Quantifier.mk_bound ctx 2 (List.nth types 1));
	       (Quantifier.mk_bound ctx 2 (List.nth types 2)) ] in
  let xs = [ (Integer.mk_const ctx (List.nth names 0));
	     (Integer.mk_const ctx (List.nth names 1));
	     (Integer.mk_const ctx (List.nth names 2)) ] in
  
  let body_vars = (Boolean.mk_and ctx 
		     [ (mk_eq ctx 
			  (Arithmetic.mk_add ctx [ (List.nth vars 0) ; (Integer.mk_numeral_i ctx 1)]) 
			  (Integer.mk_numeral_i ctx 2)) ;
		       (mk_eq ctx 
			  (Arithmetic.mk_add ctx [ (List.nth vars 1); (Integer.mk_numeral_i ctx 2)])
			  (Arithmetic.mk_add ctx [ (List.nth vars 2); (Integer.mk_numeral_i ctx 3)])) ]) in
  let body_const = (Boolean.mk_and ctx
		      [ (mk_eq ctx 
			   (Arithmetic.mk_add ctx [ (List.nth xs 0); (Integer.mk_numeral_i ctx 1)]) 
			   (Integer.mk_numeral_i ctx 2)) ;
			(mk_eq ctx 
			   (Arithmetic.mk_add ctx [ (List.nth xs 1); (Integer.mk_numeral_i ctx 2)])
			   (Arithmetic.mk_add ctx [ (List.nth xs 2); (Integer.mk_numeral_i ctx 3)])) ]) in
  
  let x = (Quantifier.mk_forall ctx types names body_vars (Some 1) [] [] (Some (Symbol.mk_string ctx "Q1")) (Some (Symbol.mk_string ctx "skid1"))) in
  Printf.printf "Quantifier X: %s\n" (Quantifier.to_string x) ;
  let y = (Quantifier.mk_forall_const ctx xs body_const (Some 1) [] [] (Some (Symbol.mk_string ctx "Q2")) (Some (Symbol.mk_string ctx "skid2"))) in
  Printf.printf "Quantifier Y: %s\n" (Quantifier.to_string y) ;
  if (is_true (Quantifier.expr_of_quantifier x)) then
    raise (TestFailedException "") (* unreachable *)
  else if (is_false (Quantifier.expr_of_quantifier x)) then
    raise (TestFailedException "") (* unreachable *)
  else if (is_const (Quantifier.expr_of_quantifier x)) then
    raise (TestFailedException "") (* unreachable *)

let _ = 
  try (
    if not (Log.open_ "z3.log") then
      raise (TestFailedException "Log couldn't be opened.")
    else
      (
	Printf.printf "Running Z3 version %s\n" Version.to_string ;
	let cfg = [("model", "true"); ("proof", "false")] in
	let ctx = (mk_context cfg) in
	let is = (Symbol.mk_int ctx 42) in
	let ss = (Symbol.mk_string ctx "mySymbol") in
	let bs = (Boolean.mk_sort ctx) in
	let ints = (Integer.mk_sort ctx) in
	let rs = (Real.mk_sort ctx) in
	Printf.printf "int symbol: %s\n" (Symbol.to_string is);
	Printf.printf "string symbol: %s\n" (Symbol.to_string ss);
	Printf.printf "bool sort: %s\n" (Sort.to_string bs);
	Printf.printf "int sort: %s\n" (Sort.to_string ints);
	Printf.printf "real sort: %s\n" (Sort.to_string rs);
	basic_tests ctx ;
	quantifierExample1 ctx ;
	Printf.printf "Disposing...\n";
	Gc.full_major ()
      );
    Printf.printf "Exiting.\n" ;
    exit 0
  ) with Z3native.Exception(msg) -> (
    Printf.printf "Z3 EXCEPTION: %s\n" msg ;
    exit 1
  )    
;;
