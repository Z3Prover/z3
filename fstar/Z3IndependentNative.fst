module Z3IndependentNative

open FStar.All
module N = Z3Native
module Root = Z3SortedRootDocument
module Marshal = Z3NativeProof
module Checker = Z3IndependentChecker
(* Keep verified native realizations in the extraction root's dependency closure. *)
module BooleanContext = Z3IndependentBooleanContext
module ScopeLookup = Z3IndependentScopeLookup

let check (assertions:list N.ast) (proof:N.ast) : ML Root.root_verdict =
  let doc, schema = Marshal.marshal_with_datatypes assertions proof in
  Checker.check schema doc
