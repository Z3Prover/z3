(* 
   Copyright (C) 2012 Microsoft Corporation
   Author: CM Wintersteiger (cwinter) 2012-12-17
*)

open Z3

exception ExampleException of string

let _ = 
  if not (Log.open_ "z3.log") then
    raise (ExampleException "Log couldn't be opened.")
  else
    (
      Printf.printf "Running Z3 version %s\n" Version.to_string ;
      let cfg = [("model", "true"); ("proof", "false")] in
      let ctx = (new context cfg) in
      Printf.printf "Disposing...\n";
      ctx#dispose (* can do, but we'd rather let it go out of scope *) ;
    );
  Printf.printf "Exiting.\n";
;;
