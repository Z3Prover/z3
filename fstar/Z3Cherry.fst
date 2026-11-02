module Z3Cherry

open FStar.All
open Z3AstTheory
open Z3UnifiedProof
module P = Z3ProofDocument

let constructor_op = Z3DatatypeLemma.op_constructor
let recognizer_op = Z3DatatypeLemma.op_recognizer
let accessor_op = Z3DatatypeLemma.op_accessor
let rational_op = Z3ValueTheory.op_num_rational

type marshaled = {
  document: P.document;
  schema: Z3DatatypeSignature.schema;
}

let mix (a b:nat) : nat = (a * 65599 + b) % 1048573

let rec hash_chars (fuel:nat) (cs:list FStar.Char.char) : Tot nat (decreases fuel) =
  if fuel = 0 then 0 else
  match cs with
  | [] -> 0
  | c :: rest -> mix (FStar.Char.int_of_char c) (hash_chars (fuel - 1) rest)

let rec hash_expression (fuel:nat) (e:expr) : Tot nat (decreases fuel) =
  if fuel = 0 then 0 else
  match e with
  | Var index _ -> mix 1 (index % 1048573)
  | App d args ->
    mix (hash_chars 64 (FStar.String.list_of_string d.decl_name))
        (hash_arguments (fuel - 1) args)
  | Quantifier _ _ _ body -> mix 3 (hash_expression (fuel - 1) body)

and hash_arguments (fuel:nat) (args:list expr) : Tot nat (decreases fuel) =
  if fuel = 0 then 0 else
  match args with
  | [] -> 0
  | e :: rest ->
    mix (hash_expression ((fuel - 1) / 2) e)
        (hash_arguments ((fuel - 1) / 2) rest)

let assertion_hash (j:judgment) : nat =
  match j with
  | Holds e -> hash_expression 64 e
  | Equal a b -> mix (hash_expression 32 a) (hash_expression 32 b)
  | Observational a b -> mix (hash_expression 32 a) (hash_expression 32 b)

let marshal ([@@@FStar.Attributes.cherry_borrowed] assertions:list Z3Native.ast)
            (proof:Z3Native.ast) : ML marshaled =
  let doc, schema = Z3NativeProof.marshal_with_datatypes assertions proof in
  { document = doc; schema = schema }

let sorted (force:bool) (m:marshaled) : bool =
  force || Cons? m.schema.cases

let check (force_sorted:bool) ([@@@FStar.Attributes.cherry_borrowed] m:marshaled)
  : option nat =
  if sorted force_sorted m then Z3SortedProof.check_document_epsilon m.schema m.document
  else P.check_document_indexed assertion_hash m.document

let diagnose (force_sorted:bool) ([@@@FStar.Attributes.cherry_borrowed] m:marshaled)
  : P.document_diagnostic =
  if sorted force_sorted m then Z3SortedProof.diagnose_document_epsilon m.schema m.document
  else P.diagnose_document_indexed assertion_hash m.document

(* The opt-in accounting mode `verified-sorts-v1`: one diagnosed check, whose result is the
   verdict. On the legacy route quantifier introductions use the checked guard
   (Z3VerifiedDocument); the sorted route never reads binder certificates and is unchanged. *)
let diagnose_verified (force_sorted:bool) ([@@@FStar.Attributes.cherry_borrowed] m:marshaled)
  : Z3VerifiedDocument.verified_diagnostic =
  if sorted force_sorted m
  then { Z3VerifiedDocument.diagnostic = Z3SortedProof.diagnose_document_epsilon m.schema m.document;
         Z3VerifiedDocument.reports = [] }
  else Z3VerifiedDocument.diagnose_document_verified_indexed assertion_hash m.document

let verified_rows ([@@@FStar.Attributes.cherry_borrowed] d:Z3VerifiedDocument.verified_diagnostic)
  : list string =
  Z3VerifiedDocument.report_rows d.Z3VerifiedDocument.reports

(* The opt-in accounting mode `verified-dag-v1`: the document marshaled once with the prepared
   certificates of its quantifier introductions, then one diagnosed check, whose result is the
   verdict. *)
noeq
type marshaled_dag = {
  dag_base: marshaled;
  dag_companions: Z3ProofIndex.index_tree Z3DagDocument.prepared;
}

let marshal_dag ([@@@FStar.Attributes.cherry_borrowed] assertions:list Z3Native.ast)
                (proof:Z3Native.ast) : ML marshaled_dag =
  let doc, schema, companions = Z3NativeProof.marshal_with_datatypes_dag assertions proof in
  { dag_base = { document = doc; schema = schema }; dag_companions = companions }

let diagnose_dag (force_sorted:bool) ([@@@FStar.Attributes.cherry_borrowed] m:marshaled_dag)
  : Z3VerifiedDocument.verified_diagnostic =
  if sorted force_sorted m.dag_base
  then { Z3VerifiedDocument.diagnostic = Z3SortedProof.diagnose_document_epsilon m.dag_base.schema m.dag_base.document;
         Z3VerifiedDocument.reports = [] }
  else Z3VerifiedDocument.diagnose_document_dag_indexed assertion_hash m.dag_base.document m.dag_companions

let dag_rows ([@@@FStar.Attributes.cherry_borrowed] d:Z3VerifiedDocument.verified_diagnostic)
  : list string =
  Z3VerifiedDocument.dag_report_rows d.Z3VerifiedDocument.reports

(* A diagnosed document needs no second check: the result recorded by its diagnosis is its verdict, in
   the sorted path (Z3SortedProof.lemma_diagnose_document_epsilon) and in the legacy path
   (Z3ProofDocument.lemma_diagnose_document_indexed). *)
let lemma_diagnose_is_check (force_sorted:bool) (m:marshaled)
  : Lemma (P.diagnostic_result (diagnose force_sorted m) == check force_sorted m) =
  if sorted force_sorted m then (
    Z3SortedProof.lemma_diagnose_document_epsilon m.schema m.document;
    match Z3SortedProof.diagnose_document_epsilon m.schema m.document with
    | P.DocumentChecked _ _ | P.DocumentRejected _ _ _ -> ())
  else
    P.lemma_diagnose_document_indexed assertion_hash m.document
