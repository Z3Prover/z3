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
  if sorted force_sorted m then Z3SortedProof.check_document m.schema m.document
  else P.check_document_indexed assertion_hash m.document

let diagnose (force_sorted:bool) ([@@@FStar.Attributes.cherry_borrowed] m:marshaled)
  : P.document_diagnostic =
  if sorted force_sorted m then Z3SortedProof.diagnose_document m.schema m.document
  else P.diagnose_document_indexed assertion_hash m.document
