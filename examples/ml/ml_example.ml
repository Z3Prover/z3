(* 
   Copyright (C) 2012 Microsoft Corporation
   Author: CM Wintersteiger (cwinter) 2012-12-17
*)

open Z3
open Z3.Arithmetic

exception ExampleException of string

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
      Gc.full_major ()
    );
  Printf.printf "Exiting.\n";
;;
