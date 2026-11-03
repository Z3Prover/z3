module Z3SortedInteger

open Z3AstTheory
open Z3ValueTheory
module A = Z3LinearArithmeticAst
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module L = FStar.List.Tot

noeq
type carrier (base:sort -> Type0) = {
  encode: int -> base A.int_s;
  decode: base A.int_s -> int;
  integer_isomorphism: u:unit{
    (forall (n:int). decode (encode n) == n) /\
    (forall (v:base A.int_s). encode (decode v) == v)};
}

let rec integer_sorts (ss:list sort) : Tot bool (decreases ss) =
  match ss with [] -> true | s :: rest -> s = A.int_s && integer_sorts rest

type operation =
  | Numeral : int -> operation
  | Calculate : A.operation -> operation
  | Compare : A.relation -> operation
  | Other

let operation_typed (f:func_decl) (op:operation) : bool =
  match op with
  | Numeral _ -> f.domain = [] && f.range = A.int_s
  | Calculate a ->
    f.range = A.int_s && integer_sorts f.domain &&
    (a = A.Add || a = A.Mul || a = A.Sub)
  | Compare r ->
    f.domain = [A.int_s; A.int_s] && f.range = bool_sort && r <> A.Eq
  | Other -> true

let classify (f:func_decl) : op:operation{operation_typed f op} =
  let numeral:option A.coefficient = if f.range = A.int_s then A.numeral (App f []) else None in
  match numeral with
  | Some (n, 1) -> Numeral n
  | _ ->
  if f.range = A.int_s && integer_sorts f.domain then
    (match A.operation_of f (S.dummy_fields f.domain) with
     | Some A.Add -> Calculate A.Add
     | Some A.Mul -> Calculate A.Mul
     | Some A.Sub -> Calculate A.Sub
     | _ -> Other)
  else if f.domain = [A.int_s; A.int_s] && f.range = bool_sort then
    (match A.comparison (App f [Var 0 A.int_s; Var 0 A.int_s]) with
     | Some (r, _, _) -> if r <> A.Eq then Compare r else Other
     | _ -> Other)
  else Other

let rec sum (xs:list int) : Tot int (decreases xs) =
  match xs with [] -> 0 | x :: rest -> x + sum rest

let rec product (xs:list int) : Tot int (decreases xs) =
  match xs with [] -> 1 | x :: rest -> x * product rest

let subtract (xs:list int) : int =
  match xs with [] -> 0 | [x] -> -x | x :: rest -> x - sum rest

let calculate (op:A.operation{op = A.Add || op = A.Mul || op = A.Sub}) (xs:list int) : int =
  match op with
  | A.Add -> sum xs
  | A.Mul -> product xs
  | A.Sub -> subtract xs
  | _ -> FStar.Pervasives.false_elim ()

let compare (r:A.relation) (x y:int) : bool =
  match r with A.Le -> x <= y | A.Lt -> x < y | A.Ge -> y <= x | A.Gt -> y < x | A.Eq -> x = y

let rec lemma_registered_sort (sigma:V.signature) (f:func_decl)
  : Lemma (requires L.mem f sigma)
          (ensures V.datatype_sort sigma f.range)
          (decreases sigma) =
  match sigma with [] -> () | g :: rest -> if f <> g then lemma_registered_sort rest f

let value (#base:sort -> Type0) (s:S.checked_schema) (integers:carrier base) (n:int)
  : V.value base (S.signature s) A.int_s =
  V.Scalar A.int_s (integers.encode n)

let number (#base:sort -> Type0) (s:S.checked_schema) (integers:carrier base)
           (v:V.value base (S.signature s) A.int_s) : int =
  match v with
  | V.Scalar _ n -> integers.decode n
  | V.Constructor f _ ->
    lemma_registered_sort (S.signature s) f;
    FStar.Pervasives.false_elim ()

let lemma_value (#base:sort -> Type0) (s:S.checked_schema) (integers:carrier base)
                (v:V.value base (S.signature s) A.int_s)
  : Lemma (value s integers (number s integers v) == v) =
  match v with
  | V.Scalar _ _ -> ()
  | V.Constructor f _ -> lemma_registered_sort (S.signature s) f

let rec numbers (#base:sort -> Type0) (s:S.checked_schema) (integers:carrier base)
                (ss:list sort{integer_sorts ss})
                (xs:V.arguments base (S.signature s) ss)
  : Tot (list int) (decreases ss) =
  match ss, xs with
  | [], [] -> []
  | _ :: rest, x :: tail -> number s integers x :: numbers s integers rest tail
  | _, _ -> FStar.Pervasives.false_elim ()

(* Typed-root G2 slice: the integer layer is a ghost specification, because
   `other` (and S.application) are ghost. `classify` above stays Tot and
   executable. *)
let application (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (integers:carrier base) (other:V.interpretation base (S.signature s))
                (f:func_decl) (xs:V.arguments base (S.signature s) f.domain)
  : GTot (V.value base (S.signature s) f.range) =
  match classify f with
  | Numeral n -> value s integers n
  | Calculate op -> value s integers (calculate op (numbers s integers f.domain xs))
  | Compare r ->
    (match xs with
     | [x; y] -> V.Scalar bool_sort
         (bc.encode_bool (compare r (number s integers x) (number s integers y)))
     | _ -> FStar.Pervasives.false_elim ())
  | Other -> S.application s bc other f xs

let rec lemma_argument_sorts (args:list expr) (ss:list sort)
  : Lemma (requires sorts_match args ss)
          (ensures L.map get_sort args == ss /\
                   L.length args == L.length ss /\
                   A.same_sort A.int_s args == integer_sorts ss)
          (decreases args) =
  match args, ss with
  | a :: rest, t :: tail ->
    V.lemma_sort_eq (get_sort a) t;
    lemma_argument_sorts rest tail
  | _, _ -> ()

let rec lemma_dummy_sorts (ss:list sort)
  : Lemma (L.map get_sort (S.dummy_fields ss) == ss /\
           L.length (S.dummy_fields ss) == L.length ss /\
           A.same_sort A.int_s (S.dummy_fields ss) == integer_sorts ss)
          (decreases ss) =
  match ss with [] -> () | _ :: rest -> lemma_dummy_sorts rest

let lemma_calculate (f:func_decl) (args:list expr) (op:A.operation)
  : Lemma (requires f.range == A.int_s /\ sorts_match args f.domain /\
                    A.operation_of f args == Some op)
          (ensures (op == A.Add \/ op == A.Mul \/ op == A.Sub) /\
                   classify f == Calculate op /\ integer_sorts f.domain) =
  lemma_argument_sorts args f.domain;
  lemma_dummy_sorts f.domain;
  match args with
  | [] -> ()
  | [_] -> ()
  | [_; _] -> ()
  | _ -> ()
