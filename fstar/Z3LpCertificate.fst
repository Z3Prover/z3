module Z3LpCertificate

open Z3AstTheory
open Z3ProofIndex
open FStar.List.Tot
module L = FStar.List.Tot
module A = Z3LinearArithmeticAst

(* Native parameters are data, never a foreign checker verdict. *)
type raw_parameter =
  | Rational : int -> int -> raw_parameter
  | Expression : expr -> raw_parameter
  | Unsupported : raw_parameter

type rational = int & pos
type polynomial = list (rational & nat)
type relation = | Le | Lt | Eq | Gt | Ge
type rule =
  | Input | Linear | IntegerTighten | IntegerLattice | Gomory
  | MonomialSubstitute | MonomialInterval | Discharge

type fact = {
  relation: relation;
  contradiction: bool;
  rhs: rational;
  epsilon: rational;
  lhs: polynomial;
}

type variable = {
  term: expr;
  integer: bool;
  definition: polynomial;
}

type monomial = {
  column: nat;
  factors: list nat;
}

type column_bounds = {
  bound_column: nat;
  lower: option nat;
  upper: option nat;
}

[@@FStar.Attributes.cherry_boxed]
type step = {
  rule: rule;
  conclusion: fact;
  input: option nat;
  assumption: option nat;
  id: nat;
  equation: fact;
  pivot: option nat;
  definition: option nat;
  source: option nat;
  divisor: rational;
  premises: list (nat & rational);
  bounds: list column_bounds;
}

type certificate = {
  variables: list variable;
  monomials: list monomial;
  steps: list step;
  root: nat;
}

type parser (a:Type) = list raw_parameter -> Tot (option (a & list raw_parameter))

[@@FStar.Attributes.custard_inline]
let bind (#a #b:Type) (p:parser a) (f:a -> parser b) : parser b =
  fun ps -> p ps >>= (fun (x, rest) -> f x rest)

[@@FStar.Attributes.custard_inline]
let ( let* ) = bind
[@@FStar.Attributes.custard_inline]
let pure (#a:Type) (x:a) : parser a = fun ps -> Some (x, ps)
let reject (#a:Type) : parser a = fun _ -> None

let read_rational : parser rational = fun ps ->
  match ps with
  | Rational n d :: rest -> if d > 0 then Some ((n, d), rest) else None
  | _ -> None

let read_uint : parser nat =
  let* (n, d) = read_rational in
  if d = 1 && n >= 0 && n <= 4294967295 then pure #nat n else reject

let read_index : parser (option nat) =
  let* n = read_uint in
  pure (if n = 4294967295 then None else Some n)

let read_bool : parser bool =
  let* n = read_uint in
  if n <= 1 then pure (n = 1) else reject

let read_expression : parser expr = fun ps ->
  match ps with Expression e :: rest -> Some (e, rest) | _ -> None

let rec read_many (#a:Type) (n:nat) (p:parser a)
  : Tot (parser (list a)) (decreases n) =
  if n = 0 then pure [] else
  let* x = p in
  let* xs = read_many (n - 1) p in
  pure (x :: xs)

let counted (#a:Type) (p:parser a) : parser (list a) =
  let* n = read_uint in
  fun rest -> if n <= L.length rest then read_many n p rest else None

let read_term : parser (rational & nat) =
  let* c = read_rational in
  let* j = read_uint in
  pure (c, j)

let read_fact : parser fact =
  let* k = read_uint in
  let* contradiction = read_bool in
  let* rhs = read_rational in
  let* epsilon = read_rational in
  let* lhs = counted read_term in
  if k > 4 then reject else
  let relation = if k = 0 then Le else if k = 1 then Lt else if k = 2 then Eq
                 else if k = 3 then Gt else Ge in
  pure { relation = relation; contradiction = contradiction; rhs = rhs;
         epsilon = epsilon; lhs = lhs }

let read_variable : parser variable =
  let* term = read_expression in
  let* integer = read_bool in
  let* definition = counted read_term in
  if get_sort term <> (if integer then A.int_s else A.real_s) then reject
  else pure { term = term; integer = integer; definition = definition }

let read_monomial : parser monomial =
  let* column = read_uint in
  let* factors = counted read_uint in
  pure { column = column; factors = factors }

let read_premise : parser (nat & rational) =
  let* j = read_uint in
  let* c = read_rational in
  pure (j, c)

let read_bounds : parser column_bounds =
  let* column = read_uint in
  let* lower = read_index in
  let* upper = read_index in
  pure { bound_column = column; lower = lower; upper = upper }

let read_step : parser step =
  let* k = read_uint in
  let* conclusion = read_fact in
  let* input = read_index in
  let* assumption = read_index in
  let* id = read_uint in
  let* equation = read_fact in
  let* pivot = read_index in
  let* definition = read_index in
  let* source = read_index in
  let* divisor = read_rational in
  let* premises = counted read_premise in
  let* bounds = counted read_bounds in
  if k > 7 then reject else
  let rule = if k = 0 then Input else if k = 1 then Linear
             else if k = 2 then IntegerTighten else if k = 3 then IntegerLattice
             else if k = 4 then Gomory else if k = 5 then MonomialSubstitute
             else if k = 6 then MonomialInterval else Discharge in
  pure { rule = rule; conclusion = conclusion; input = input; assumption = assumption;
         id = id; equation = equation; pivot = pivot; definition = definition;
         source = source; divisor = divisor; premises = premises; bounds = bounds }

let rec polynomial_refs (limit:nat) (p:polynomial) : Tot bool (decreases p) =
  match p with [] -> true | (_, j) :: rest -> j < limit && polynomial_refs limit rest

let rec lookup (#a:Type) (xs:list a) (j:nat) : Tot (option a) (decreases xs) =
  match xs with
  | [] -> None
  | x :: rest -> if j = 0 then Some x else lookup rest (j - 1)

let rec variables_valid (seen:list variable) (vs:list variable)
  : Tot bool (decreases vs) =
  match vs with
  | [] -> true
  | v :: rest ->
    polynomial_refs (L.length seen) v.definition &&
    (not v.integer || L.for_all (fun (t:rational & nat) -> let ((_, d), j) = t in
       d = 1 && (match lookup seen j with Some w -> w.integer | None -> false)) v.definition) &&
    variables_valid (seen @ [v]) rest

let optional_ref (limit:nat) (j:option nat) : bool =
  match j with None -> true | Some j -> j < limit

let required_ref (limit:nat) (j:option nat) : bool =
  match j with None -> false | Some j -> j < limit

let step_refs (nv nm index:nat) (s:step) : bool =
  polynomial_refs nv s.conclusion.lhs && polynomial_refs nv s.equation.lhs &&
  L.for_all (fun (p:nat & rational) -> fst p < index) s.premises &&
  optional_ref nv s.pivot && optional_ref nv s.source && optional_ref nm s.definition &&
  L.for_all (fun (b:column_bounds) -> b.bound_column < nv &&
     optional_ref (L.length s.premises) b.lower &&
     optional_ref (L.length s.premises) b.upper) s.bounds &&
  (if s.rule = Discharge then required_ref index s.assumption else s.assumption = None) &&
  (match s.rule with
   | Input -> Some? s.input && not s.conclusion.contradiction && s.premises = []
   | Gomory | IntegerLattice -> required_ref nv s.pivot
   | MonomialSubstitute -> required_ref nm s.definition
   | MonomialInterval -> required_ref nm s.definition && required_ref nv s.pivot
   | _ -> true)

let rec steps_valid (nv nm index:nat) (ss:list step) : Tot bool (decreases ss) =
  match ss with
  | [] -> true
  | s :: rest -> step_refs nv nm index s && steps_valid nv nm (index + 1) rest

(* Structural validation only. Neither facts nor variable definitions are
   accepted as arithmetic truths by this decoder. *)
let well_formed (c:certificate) : bool =
  let nv = L.length c.variables in
  variables_valid [] c.variables &&
  L.for_all (fun (m:monomial) -> m.column < nv &&
     L.for_all (fun (j:nat) -> j < nv) m.factors) c.monomials &&
  steps_valid nv (L.length c.monomials) 0 c.steps && c.root < L.length c.steps

let read_certificate : parser certificate =
  let* version = read_uint in
  if version <> 1 then reject else
  let* variables = counted read_variable in
  let* monomials = counted read_monomial in
  let* steps = counted read_step in
  let* root = read_uint in
  pure { variables = variables; monomials = monomials; steps = steps; root = root }

let decode (ps:list raw_parameter) : option (c:certificate{well_formed c}) =
  match read_certificate ps with
  | Some (c, []) -> if well_formed c then Some c else None
  | _ -> None
