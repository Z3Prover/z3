module Z3ArithmeticFactor

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native --fuel 1 --ifuel 1 --z3rlimit 10"

open FStar.Real
open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module L = FStar.List.Tot
module A = Z3LinearArithmeticAst
module E = Z3LinearArithmeticEmbed
module P = Z3LinearArithmeticTheory
module N = Z3NlaLemma
module B = Z3BooleanRewrite
module O = Z3ObservationalEquality
module AR = Z3ArithmeticRewrite

(* Factored sign rewrites (arith_rewriter::factor_le_ge_eq). For a numeric p
   with a common factor f, Z3 rewrites with g = p / f:
     p = 0   ~>  or (f = 0) (g = 0)
     p >= 0  ~>  or (= (f >= 0) (g >= 0)) (or (f = 0) (g = 0))
     p <= 0  ~>  or (not (= (f >= 0) (g >= 0))) (or (f = 0) (g = 0))
   The step is checked by ring normalization: p and f * g must have the same
   normal form, and both occurrences of f (and of g) must normalize alike.
   Only +, *, - and integer numerals are interpreted. Every other numeric term,
   including division, to_real, and rational numerals, is an opaque atom, so no
   field law is used. All comparisons have the sort of p and a zero numeral on
   the right; other shapes are left unchecked. *)

(* Polynomials with integer coefficients over indices of an atom table. *)

let rec position (atoms:list expr) (e:expr) : Tot (option nat) (decreases atoms) =
  match atoms with
  | [] -> None
  | a :: rest ->
    if a = e then Some 0
    else (match position rest e with Some n -> Some (n + 1) | None -> None)

let atom_values (i:interpretation value) (nu:value -> real) (rho:env value)
                (atoms:list expr) : nat -> real =
  fun n -> match N.nth atoms n with Some a -> nu (eval i a rho) | None -> 0.0R

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
  match b with App f [_; _] -> f.decl_name = "or" | _ -> false

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

(* ---------- Soundness ---------- *)

let pvalue (p:N.poly) (r:nat -> real) : real = N.value p r

let pvalues (ps:list N.poly) (r:nat -> real) : list real = L.map (fun p -> pvalue p r) ps

let rec lemma_position (atoms:list expr) (e:expr) (n:nat)
  : Lemma (requires position atoms e == Some n) (ensures N.nth atoms n == Some e)
          (decreases atoms) =
  match atoms with
  | [] -> ()
  | a :: rest -> if a = e then () else lemma_position rest e (n - 1)

#push-options "--fuel 2"
let lemma_constant (n:int) (r:nat -> real) : Lemma (pvalue (constant n) r == of_int n) =
  assert_norm (P.monomial_value #N.monomial [] (fun m -> N.monomial_value m r) == 0.0R)

let lemma_atom (n:nat) (r:nat -> real) : Lemma (pvalue (atom n) r == r n) =
  assert_norm (N.monomial_value [n] r == r n *. 1.0R);
  assert_norm (P.monomial_value [(1, [n])] (fun m -> N.monomial_value m r) ==
               of_int 1 *. N.monomial_value [n] r +.
               P.monomial_value #N.monomial [] (fun m -> N.monomial_value m r))
#pop-options

#push-options "--fuel 0 --ifuel 0 --using_facts_from 'Prims FStar.Real'"
let lemma_unit_sum (a b x y:real)
  : Lemma (requires a == 1.0R /\ b == 1.0R) (ensures a *. x +. b *. y == x +. y) = ()

let lemma_negative_unit (a x:real)
  : Lemma (requires a == 0.0R -. 1.0R) (ensures a *. x == 0.0R -. x) = ()
#pop-options

let lemma_plus (p q:N.poly) (r:nat -> real)
  : Lemma (pvalue (plus p q) r == pvalue p r +. pvalue q r) =
  let rr = fun m -> N.monomial_value m r in
  P.lemma_add p q rr;
  lemma_unit_sum (of_int q.denom) (of_int p.denom) (P.value p rr) (P.value q rr)

let lemma_negate (p:N.poly) (r:nat -> real)
  : Lemma (pvalue (negate p) r == 0.0R -. pvalue p r) =
  let rr = fun m -> N.monomial_value m r in
  P.lemma_scale (-1) 1 p rr;
  lemma_negative_unit (of_int (-1)) (P.value p rr)

let lemma_normal (p:N.poly) (r:nat -> real)
  : Lemma (pvalue (normal p) r == pvalue p r) =
  P.lemma_collect p.mono [] (fun m -> N.monomial_value m r)

let lemma_times (p q t:N.poly) (r:nat -> real)
  : Lemma (requires times p q == Some t) (ensures pvalue t r == pvalue p r *. pvalue q r) =
  N.lemma_multiply p q r;
  lemma_normal (N.multiply p q) r

let rec lemma_sum (ps:list N.poly) (r:nat -> real)
  : Lemma (ensures pvalue (sum ps) r == E.numeric_sum (pvalues ps r)) (decreases ps) =
  match ps with
  | [] -> lemma_constant 0 r
  | p :: rest -> lemma_sum rest r; lemma_plus p (sum rest) r

let rec lemma_product (ps:list N.poly) (t:N.poly) (r:nat -> real)
  : Lemma (requires product ps == Some t)
          (ensures pvalue t r == E.numeric_product (pvalues ps r)) (decreases ps) =
  match ps with
  | [] -> lemma_constant 1 r
  | p :: rest ->
    let q = Some?.v (product rest) in
    lemma_product rest q r;
    lemma_times p q t r

#push-options "--fuel 2"
let lemma_subtract (ps:list N.poly) (t:N.poly) (r:nat -> real)
  : Lemma (requires subtract ps == Some t)
          (ensures pvalue t r == E.numeric_subtract (pvalues ps r)) =
  match ps with
  | [] -> ()
  | [p] -> lemma_negate p r
  | p :: rest ->
    lemma_sum rest r;
    lemma_negate (sum rest) r;
    lemma_plus p (negate (sum rest)) r
#pop-options

let lemma_leaf (atoms:list expr) (e:expr) (p:N.poly)
               (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires leaf atoms e == Some p)
          (ensures pvalue p (atom_values i nu rho atoms) == nu (eval i e rho)) =
  let n = Some?.v (position atoms e) in
  lemma_position atoms e n;
  lemma_atom n (atom_values i nu rho atoms)

#push-options "--fuel 2"
let lemma_numeral (e:expr) (n:int) (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_operators i nu /\ A.numeral e == Some (n, 1))
          (ensures nu (eval i e rho) == of_int n) =
  assert (A.linearize 4 e == Some (P.constant n 1));
  E.lemma_linearize 4 e (P.constant n 1) i nu rho;
  assert_norm (P.monomial_value #expr [] (E.valuation i nu rho) == 0.0R)
#pop-options

#push-options "--z3rlimit 20"
let rec lemma_poly_of (fuel:nat) (atoms:list expr) (e:expr) (p:N.poly)
                      (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_operators i nu /\ poly_of fuel atoms e == Some p)
          (ensures pvalue p (atom_values i nu rho atoms) == nu (eval i e rho))
          (decreases %[fuel; 0]) =
  let r = atom_values i nu rho atoms in
  match A.numeral e with
  | Some (n, d) ->
    if d = 1 then (lemma_numeral e n i nu rho; lemma_constant n r)
    else lemma_leaf atoms e p i nu rho
  | None ->
    (match e with
     | App f args ->
       (match A.operation_of f args with
        | Some A.Add ->
          let ps = Some?.v (poly_args (fuel - 1) atoms args) in
          lemma_poly_args (fuel - 1) atoms args ps i nu rho;
          lemma_sum ps r;
          E.lemma_add_application f args i nu rho
        | Some A.Mul ->
          let ps = Some?.v (poly_args (fuel - 1) atoms args) in
          lemma_poly_args (fuel - 1) atoms args ps i nu rho;
          lemma_product ps p r;
          E.lemma_mul_application f args i nu rho
        | Some A.Sub ->
          let ps = Some?.v (poly_args (fuel - 1) atoms args) in
          lemma_poly_args (fuel - 1) atoms args ps i nu rho;
          lemma_subtract ps p r;
          assert (nu (eval i e rho) == E.numeric_subtract (L.map nu (eval_args i args rho)))
        | _ -> lemma_leaf atoms e p i nu rho)
     | _ -> lemma_leaf atoms e p i nu rho)

and lemma_poly_args (fuel:nat) (atoms:list expr) (args:list expr) (ps:list N.poly)
                    (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_operators i nu /\ poly_args fuel atoms args == Some ps)
          (ensures pvalues ps (atom_values i nu rho atoms) == L.map nu (eval_args i args rho))
          (decreases %[fuel; 1; args]) =
  match args, ps with
  | a :: rest, p :: tail ->
    lemma_poly_of fuel atoms a p i nu rho;
    lemma_poly_args fuel atoms rest tail i nu rho
  | _, _ -> ()
#pop-options

let lemma_same_poly (p q:N.poly) (r:nat -> real)
  : Lemma (requires same_poly p q) (ensures pvalue p r == pvalue q r) =
  let d = normal (plus p (negate q)) in
  lemma_normal (plus p (negate q)) r;
  lemma_plus p (negate q) r;
  lemma_negate q r;
  P.lemma_all_zero d.mono (fun m -> N.monomial_value m r)

let sign_holds (r:A.relation) (v:real) : prop =
  match r with
  | A.Eq -> v == 0.0R
  | A.Ge -> v >=. 0.0R
  | A.Le -> v <=. 0.0R
  | A.Gt -> v >. 0.0R
  | A.Lt -> v <. 0.0R

let lemma_zero_comparison (atoms:list expr) (s:sort) (e:expr) (r:A.relation) (p:N.poly)
                          (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ eq_sound i /\
                    zero_comparison atoms s e == Some (r, p))
          (ensures get_sort e == bool_sort /\
                   (lit_true i rho e <==> sign_holds r (pvalue p (atom_values i nu rho atoms)))) =
  let _, x, z = Some?.v (A.comparison e) in
  lemma_numeral z 0 i nu rho;
  lemma_poly_of 64 atoms x p i nu rho;
  match e with
  | App _ [_; _] ->
    if r = A.Eq then (
      let equal ()
        : Lemma (requires nu (eval i x rho) == nu (eval i z rho))
                (ensures eval i x rho == eval i z rho) =
        AR.lemma_numeric_values_equal x z i nu rho in
      FStar.Classical.move_requires equal ())
    else AR.lemma_numeric_comparison e x z r i nu rho
  | _ -> ()

#push-options "--fuel 3"
let lemma_binary_or (d:func_decl) (c z:expr) (i:interpretation value) (rho:env value)
  : Lemma (requires or_sound i /\ B.connective_app B.Disjunction d [c; z])
          (ensures get_sort (App d [c; z]) == bool_sort /\
                   (lit_true i rho (App d [c; z]) <==> lit_true i rho c \/ lit_true i rho z)) =
  assert (d.decl_name == "or")
#pop-options

let lemma_zero_factors (atoms:list expr) (s:sort) (e:expr) (f g:N.poly)
                       (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ eq_sound i /\ or_sound i /\
                    zero_factors atoms s e == Some (f, g))
          (ensures (let r = atom_values i nu rho atoms in
                    get_sort e == bool_sort /\
                    (lit_true i rho e <==> pvalue f r == 0.0R \/ pvalue g r == 0.0R))) =
  match e with
  | App d [x; y] ->
    lemma_zero_comparison atoms s x A.Eq f i nu rho;
    lemma_zero_comparison atoms s y A.Eq g i nu rho;
    lemma_binary_or d x y i rho
  | _ -> ()

let lemma_sign_factors (atoms:list expr) (s:sort) (e:expr) (f g:N.poly)
                       (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ O.boolean_model i /\ eq_sound i /\
                    sign_factors atoms s e == Some (f, g))
          (ensures (let r = atom_values i nu rho atoms in
                    get_sort e == bool_sort /\
                    (lit_true i rho e <==> ((pvalue f r >=. 0.0R) <==> (pvalue g r >=. 0.0R))))) =
  match e with
  | App _ [x; y] ->
    lemma_zero_comparison atoms s x A.Ge f i nu rho;
    lemma_zero_comparison atoms s y A.Ge g i nu rho;
    (match eval i x rho, eval i y rho with
     | VBool _, VBool _ -> ()
     | _, _ -> ())
  | _ -> ()

let lemma_negated (e c:expr) (i:interpretation value) (rho:env value)
  : Lemma (requires O.boolean_model i /\ not_sound i /\ negated e == Some c /\
                    get_sort c == bool_sort)
          (ensures get_sort e == bool_sort /\ (lit_true i rho e <==> ~(lit_true i rho c))) =
  match e with
  | App f [x] ->
    assert (f.decl_name == "not" /\ x == c);
    (match eval i c rho with
     | VBool _ -> assert (lit_true i rho e <==> eval i x rho == VBool false)
     | _ -> ())
  | _ -> ()

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10 --using_facts_from 'Prims FStar.Real'"
let lemma_zero_product (x y:real)
  : Lemma ((x *. y == 0.0R) <==> (x == 0.0R \/ y == 0.0R)) =
  if x >. 0.0R then () else if x <. 0.0R then () else ()
#pop-options

let lemma_zero_case (atoms:list expr) (s:sort) (p f g q:N.poly) (e:expr)
                    (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ eq_sound i /\ or_sound i /\
                    zero_factors atoms s e == Some (f, g) /\ times f g == Some q /\ same_poly p q)
          (ensures get_sort e == bool_sort /\
                   (lit_true i rho e <==> sign_holds A.Eq (pvalue p (atom_values i nu rho atoms)))) =
  let r = atom_values i nu rho atoms in
  lemma_zero_factors atoms s e f g i nu rho;
  lemma_times f g q r;
  lemma_same_poly p q r;
  lemma_zero_product (pvalue f r) (pvalue g r)

let lemma_sign_case (atoms:list expr) (s:sort) (rel:A.relation) (p f g f' g' q:N.poly)
                    (d:func_decl) (c c' z:expr)
                    (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ O.boolean_model i /\ not_sound i /\
                    eq_sound i /\ or_sound i /\ B.connective_app B.Disjunction d [c; z] /\
                    ((rel == A.Ge /\ c' == c) \/ (rel == A.Le /\ negated c == Some c')) /\
                    sign_factors atoms s c' == Some (f', g') /\
                    zero_factors atoms s z == Some (f, g) /\
                    same_poly f f' /\ same_poly g g' /\ times f g == Some q /\ same_poly p q)
          (ensures get_sort (App d [c; z]) == bool_sort /\
                   (lit_true i rho (App d [c; z]) <==>
                    sign_holds rel (pvalue p (atom_values i nu rho atoms)))) =
  let r = atom_values i nu rho atoms in
  lemma_sign_factors atoms s c' f' g' i nu rho;
  lemma_zero_factors atoms s z f g i nu rho;
  if rel = A.Le then lemma_negated c c' i rho;
  lemma_same_poly f f' r;
  lemma_same_poly g g' r;
  lemma_times f g q r;
  lemma_same_poly p q r;
  AR.lemma_product_sign_numbers (pvalue f r) (pvalue g r);
  lemma_binary_or d c z i rho

let lemma_factored (atoms:list expr) (s:sort) (rel:A.relation) (p:N.poly) (e:expr)
                   (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ O.boolean_model i /\ not_sound i /\
                    eq_sound i /\ or_sound i /\ factored atoms s rel p e)
          (ensures get_sort e == bool_sort /\
                   (lit_true i rho e <==> sign_holds rel (pvalue p (atom_values i nu rho atoms)))) =
  if rel = A.Eq then (
    let f, g = Some?.v (zero_factors atoms s e) in
    lemma_zero_case atoms s p f g (Some?.v (times f g)) e i nu rho)
  else match e with
  | App d [c; z] ->
    let c' = Some?.v (if rel = A.Ge then Some c else negated c) in
    let f', g' = Some?.v (sign_factors atoms s c') in
    let f, g = Some?.v (zero_factors atoms s z) in
    lemma_sign_case atoms s rel p f g f' g' (Some?.v (times f g)) d c c' z i nu rho
  | _ -> ()

let lemma_check (a b:expr) (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ O.boolean_model i /\ not_sound i /\
                    eq_sound i /\ or_sound i /\ check a b)
          (ensures eval i a rho == eval i b rho) =
  let rel, x, z = Some?.v (A.comparison a) in
  let atoms = atoms_of a (atoms_of b []) in
  let p = Some?.v (poly_of 64 atoms x) in
  assert (zero_comparison atoms (get_sort x) a == Some (rel, p));
  lemma_zero_comparison atoms (get_sort x) a rel p i nu rho;
  lemma_factored atoms (get_sort x) rel p b i nu rho;
  O.lemma_observations_values i rho a b

let lemma_check_sound (a b:expr) (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\ O.boolean_model i /\
                    not_sound i /\ eq_sound i /\ or_sound i /\ check a b)
          (ensures eval i a rho == eval i b rho) =
  let aux (nu:value -> real)
    : Lemma (requires E.numeric_model i nu) (ensures eval i a rho == eval i b rho) =
    lemma_check a b i nu rho in
  FStar.Classical.exists_elim (eval i a rho == eval i b rho)
    #(value -> real) #(fun nu -> E.numeric_model i nu) () (fun nu -> aux nu)
