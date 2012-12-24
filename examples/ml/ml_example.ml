(* 
   Copyright (C) 2012 Microsoft Corporation
   Author: CM Wintersteiger (cwinter) 2012-12-17
*)

open Z3
open Z3.Symbol
open Z3.Sort
open Z3.Expr
open Z3.FuncDecl
open Z3.Goal
open Z3.Tactic
open Z3.Probe
open Z3.Solver
open Z3.Arithmetic

exception ExampleException of string


(**
 Some basic tests.
*)
let basic_tests ( ctx : context ) =
  Printf.printf "BasicTests\n" ;
  let qi = (mk_int ctx 1) in
  let fname = ((mk_string ctx "f") :> symbol) in
  let x = ((mk_string ctx "x") :> symbol) in
  let y = ((mk_string ctx "y") :> symbol) in
  let bs = (Sort.mk_bool ctx) in
  let domain = [| bs; bs |] in
  let f = (FuncDecl.mk_func_decl ctx fname domain bs) in
  let fapp = (mk_app ctx f 
		[| (mk_const ctx x bs); (mk_const ctx y bs) |]) in
  let fargs2 = [| (mk_fresh_const ctx "cp" bs) |] in
  let domain2 = [| bs |] in
  let fapp2 = (mk_app ctx (mk_fresh_func_decl ctx "fp" domain2 bs) fargs2) in
  let trivial_eq = (mk_eq ctx fapp fapp) in
  let nontrivial_eq = (mk_eq ctx fapp fapp2) in
  let g = (mk_goal ctx true false false) in
  (Goal.assert_ g [| trivial_eq |]) ;
  (Goal.assert_ g [| nontrivial_eq |]) ;
  Printf.printf "%s\n" ("Goal: " ^ (Goal.to_string g)) ;
  let solver = (mk_solver ctx None) in
  (Array.iter (fun a -> (Solver.assert_ solver [| a |])) (get_formulas g)) ;
  if (check solver None) != SATISFIABLE then
    raise (ExampleException "")
  else
    Printf.printf "Test passed.\n" ;
    ()

(*
    ApplyResult ar = ApplyTactic(ctx, ctx.MkTactic("simplify"), g);
  if (ar.NumSubgoals == 1 && (ar.Subgoals[0].IsDecidedSat || ar.Subgoals[0].IsDecidedUnsat))
    throw new TestFailedException();
    
    ar = ApplyTactic(ctx, ctx.MkTactic("smt"), g);
    if (ar.NumSubgoals != 1 || !ar.Subgoals[0].IsDecidedSat)
      throw new TestFailedException();
      
            g.Assert(ctx.MkEq(ctx.MkNumeral(1, ctx.MkBitVecSort(32)),
                                      ctx.MkNumeral(2, ctx.MkBitVecSort(32))));
            ar = ApplyTactic(ctx, ctx.MkTactic("smt"), g);
            if (ar.NumSubgoals != 1 || !ar.Subgoals[0].IsDecidedUnsat)
                throw new TestFailedException();


            Goal g2 = ctx.MkGoal(true, true);
            ar = ApplyTactic(ctx, ctx.MkTactic("smt"), g2);
            if (ar.NumSubgoals != 1 || !ar.Subgoals[0].IsDecidedSat)
                throw new TestFailedException();

            g2 = ctx.MkGoal(true, true);
            g2.Assert(ctx.MkFalse());
            ar = ApplyTactic(ctx, ctx.MkTactic("smt"), g2);
            if (ar.NumSubgoals != 1 || !ar.Subgoals[0].IsDecidedUnsat)
                throw new TestFailedException();

            Goal g3 = ctx.MkGoal(true, true);
            Expr xc = ctx.MkConst(ctx.MkSymbol("x"), ctx.IntSort);
            Expr yc = ctx.MkConst(ctx.MkSymbol("y"), ctx.IntSort);
            g3.Assert(ctx.MkEq(xc, ctx.MkNumeral(1, ctx.IntSort)));
            g3.Assert(ctx.MkEq(yc, ctx.MkNumeral(2, ctx.IntSort)));
            BoolExpr constr = ctx.MkEq(xc, yc);
            g3.Assert(constr);
            ar = ApplyTactic(ctx, ctx.MkTactic("smt"), g3);
            if (ar.NumSubgoals != 1 || !ar.Subgoals[0].IsDecidedUnsat)
                throw new TestFailedException();

            ModelConverterTest(ctx);

            // Real num/den test.
            RatNum rn = ctx.MkReal(42, 43);
            Expr inum = rn.Numerator;
            Expr iden = rn.Denominator;
            Console.WriteLine("Numerator: " + inum + " Denominator: " + iden);
            if (inum.ToString() != "42" || iden.ToString() != "43")
                throw new TestFailedException();

            if (rn.ToDecimalString(3) != "0.976?")
                throw new TestFailedException();

            BigIntCheck(ctx, ctx.MkReal("-1231231232/234234333"));
            BigIntCheck(ctx, ctx.MkReal("-123123234234234234231232/234234333"));
            BigIntCheck(ctx, ctx.MkReal("-234234333"));
            BigIntCheck(ctx, ctx.MkReal("234234333/2"));


            string bn = "1234567890987654321";

            if (ctx.MkInt(bn).BigInteger.ToString() != bn)
                throw new TestFailedException();

            if (ctx.MkBV(bn, 128).BigInteger.ToString() != bn)
                throw new TestFailedException();

            if (ctx.MkBV(bn, 32).BigInteger.ToString() == bn)
                throw new TestFailedException();

            // Error handling test.
            try
            {
                IntExpr i = ctx.MkInt("1/2");
                throw new TestFailedException(); // unreachable
            }
            catch (Z3Exception)
            {
            }
        }
*)


let _ = 
  if not (Log.open_ "z3.log") then
    raise (ExampleException "Log couldn't be opened.")
  else
    (
      Printf.printf "Running Z3 version %s\n" Version.to_string ;
      let cfg = (Some [("model", "true"); ("proof", "false")]) in
      let ctx = (mk_context cfg) in
      let is = (Symbol.mk_int ctx 42) in
      let ss = (Symbol.mk_string ctx "mySymbol") in
      let bs = (Sort.mk_bool ctx) in
      let ints = (mk_int_sort ctx) in
      let rs = (mk_real_sort ctx) in
      Printf.printf "int symbol: %s\n" (Symbol.to_string (is :> symbol));
      Printf.printf "string symbol: %s\n" (Symbol.to_string (ss :> symbol));
      Printf.printf "bool sort: %s\n" (Sort.to_string bs);
      Printf.printf "int sort: %s\n" (Sort.to_string ints);
      Printf.printf "real sort: %s\n" (Sort.to_string rs);
      Printf.printf "Disposing...\n";
      basic_tests ctx ;
      Gc.full_major ()
    );
  Printf.printf "Exiting.\n";
;;
