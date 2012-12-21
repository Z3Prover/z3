(* 
   Copyright (C) 2012 Microsoft Corporation
   Author: CM Wintersteiger (cwinter) 2012-12-17
*)

open Z3
open Z3.Context

exception ExampleException of string

let _ = 
  if not (Log.open_ "z3.log") then
    raise (ExampleException "Log couldn't be opened.")
  else
    (
      Printf.printf "Running Z3 version %s\n" Version.to_string ;
      let cfg = [("model", "true"); ("proof", "false")] in
      let ctx = (new context cfg) in
      let is = (mk_symbol_int ctx 42) in
      let ss = (mk_symbol_string ctx "mySymbol") in
      Printf.printf "int symbol: %s\n" (Symbol.to_string (is :> symbol));
      Printf.printf "string symbol: %s\n" (Symbol.to_string (ss :> symbol));
      Printf.printf "Disposing...\n";
      ctx#dispose (* can do, but we'd rather let it go out of scope *) ;
    );
  Printf.printf "Exiting.\n";
;;
