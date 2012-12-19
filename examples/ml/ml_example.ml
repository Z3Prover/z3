(* 
   Copyright (C) 2012 Microsoft Corporation
   Author: CM Wintersteiger (cwinter) 2012-12-17
*)

open Z3
 
let _ = ignore(Log.open_ "z3.log") ;
  let cfg = Some [("model", "true"); ("proof", "false")] in
  let ctx = (new context cfg) in
  Printf.printf "Disposing...\n";
  ctx#dispose ;
  Printf.printf "Exiting.\n";
;;
