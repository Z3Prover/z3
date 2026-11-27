module Z3ArithmeticFactorSyntax

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native --fuel 1 --ifuel 1 --z3rlimit 10"

open Z3AstTheory
open Z3ClauseSyntax
module L = FStar.List.Tot
module A = Z3LinearArithmeticAst
module P = Z3LinearArithmeticTheory
module N = Z3NlaLemma
module B = Z3BooleanRewriteSyntax
module C = Z3CanonicalOps

let rec position (atoms:list expr) (e:expr) : Tot (option nat) (decreases atoms) =
  match atoms with
  | [] -> None
  | a :: rest ->
    if a = e then Some 0
    else (match position rest e with Some n -> Some (n + 1) | None -> None)

let constant (n:int) : N.poly = P.constant n 1
let atom (n:nat) : N.poly = P.variable [n]
let plus (p q:N.poly) : N.poly = P.add p q
let negate (p:N.poly) : N.poly = P.scale (-1) 1 p
let normal (p:N.poly) : N.poly = { p with P.mono = P.collect p.mono [] }

(* Expansion is quadratic in the operands; larger products stay unchecked. *)
let max_terms : nat = 4096

let times (p q:N.poly) : option N.poly =
  if L.length p.mono * L.length q.mono <= max_terms
  then Some (normal (N.multiply p q)) else None

let rec sum (ps:list N.poly) : Tot N.poly (decreases ps) =
  match ps with [] -> constant 0 | p :: rest -> plus p (sum rest)

let rec product (ps:list N.poly) : Tot (option N.poly) (decreases ps) =
  match ps with
  | [] -> Some (constant 1)
  | p :: rest -> (match product rest with Some q -> times p q | None -> None)

let subtract (ps:list N.poly) : option N.poly =
  match ps with
  | [] -> None
  | [p] -> Some (negate p)
  | p :: rest -> Some (plus p (negate (sum rest)))

let leaf (atoms:list expr) (e:expr) : option N.poly =
  match position atoms e with Some n -> Some (atom n) | None -> None

let rec poly_of (fuel:nat) (atoms:list expr) (e:expr)
  : Tot (option N.poly) (decreases %[fuel; 0]) =
  if fuel = 0 then None
  else match A.numeral e with
  | Some (n, d) -> if d = 1 then Some (constant n) else leaf atoms e
  | None ->
    (match e with
     | App f args ->
       (match A.operation_of f args with
        | Some A.Add ->
          (match poly_args (fuel - 1) atoms args with Some ps -> Some (sum ps) | None -> None)
        | Some A.Mul ->
          (match poly_args (fuel - 1) atoms args with Some ps -> product ps | None -> None)
        | Some A.Sub ->
          (match poly_args (fuel - 1) atoms args with Some ps -> subtract ps | None -> None)
        | _ -> leaf atoms e)
     | _ -> leaf atoms e)

and poly_args (fuel:nat) (atoms:list expr) (args:list expr)
  : Tot (option (list N.poly)) (decreases %[fuel; 1; args]) =
  match args with
  | [] -> Some []
  | a :: rest ->
    (match poly_of fuel atoms a, poly_args fuel atoms rest with
     | Some p, Some ps -> Some (p :: ps)
     | _, _ -> None)

let same_poly (p q:N.poly) : bool =
  let d = normal (plus p (negate q)) in
  d.cst = 0 && P.all_zero d.mono

(* The atom table only fixes indices; any table is sound. *)
let rec atoms_of (e:expr) (acc:list expr) : Tot (list expr) (decreases e) =
  match e with
  | App f args ->
    if get_sort e = bool_sort then atoms_args args acc
    else if not (A.numeric_sort (get_sort e)) then acc
    else if A.numeral e = None &&
            (match A.operation_of f args with
             | Some A.Add | Some A.Mul | Some A.Sub -> true
             | _ -> false)
    then atoms_args args acc
    else if L.mem e acc then acc else e :: acc
  | _ -> if L.mem e acc then acc else e :: acc

and atoms_args (args:list expr) (acc:list expr) : Tot (list expr) (decreases args) =
  match args with [] -> acc | a :: rest -> atoms_args rest (atoms_of a acc)

(* Recognizers for the right-hand side. *)

let zero_numeral (e:expr) : bool = A.numeral e = Some (0, 1)

let zero_comparison (atoms:list expr) (s:sort) (e:expr) : option (A.relation & N.poly) =
  match A.comparison e with
  | Some (r, x, z) ->
    if get_sort x = s && zero_numeral z then
      (match poly_of 64 atoms x with Some p -> Some (r, p) | None -> None)
    else None
  | None -> None

let zero_factors (atoms:list expr) (s:sort) (e:expr) : option (N.poly & N.poly) =
  match e with
  | App f [x; y] ->
    if B.connective_app B.Disjunction f [x; y] then
      (match zero_comparison atoms s x, zero_comparison atoms s y with
       | Some (A.Eq, p), Some (A.Eq, q) -> Some (p, q)
       | _, _ -> None)
    else None
  | _ -> None

let sign_factors (atoms:list expr) (s:sort) (e:expr) : option (N.poly & N.poly) =
  match e with
  | App f [x; y] ->
    if f = eq_decl bool_sort then
      (match zero_comparison atoms s x, zero_comparison atoms s y with
       | Some (A.Ge, p), Some (A.Ge, q) -> Some (p, q)
       | _, _ -> None)
    else None
  | _ -> None

let negated (e:expr) : option expr =
  match e with App f [x] -> if f = not_decl then Some x else None | _ -> None

(* Both factors must be non-constant polynomials, as in Z3's find_nl_factor. *)
let nonconstant (p:N.poly) : bool = not (P.all_zero (normal p).mono)

let factorization (p f g:N.poly) : bool =
  nonconstant f && nonconstant g &&
  (match times f g with Some q -> same_poly p q | None -> false)

let factored (atoms:list expr) (s:sort) (r:A.relation) (p:N.poly) (e:expr) : bool =
  if r = A.Eq then
    (match zero_factors atoms s e with
     | Some (f, g) -> factorization p f g
     | None -> false)
  else if r = A.Ge || r = A.Le then
    (match e with
     | App d [c; z] ->
       B.connective_app B.Disjunction d [c; z] &&
       (match (if r = A.Ge then Some c else negated c) with
        | Some c' ->
          (match sign_factors atoms s c', zero_factors atoms s z with
           | Some (f', g'), Some (f, g) ->
             same_poly f f' && same_poly g g' && factorization p f g
           | _, _ -> false)
        | None -> false)
     | _ -> false)
  else false

let candidate_shape (b:expr) : bool =
  match b with App f [_; _] -> C.canonical_or f | _ -> false

let check (a b:expr) : bool =
  match A.comparison a with
  | Some (r, x, z) ->
    (r = A.Eq || r = A.Ge || r = A.Le) && zero_numeral z && candidate_shape b &&
    Some? (expression_budget 4096 a) && Some? (expression_budget 4096 b) &&
    (let atoms = atoms_of a (atoms_of b []) in
     match poly_of 64 atoms x with
     | Some p -> factored atoms (get_sort x) r p b
     | None -> false)
  | None -> false

