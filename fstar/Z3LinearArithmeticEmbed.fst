module Z3LinearArithmeticEmbed

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open FStar.Real
open FStar.List.Tot
open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
module A = Z3LinearArithmeticAst
module P = Z3LinearArithmeticTheory

let rec numeric_sum (xs:list real) : Tot real (decreases xs) =
  match xs with [] -> 0.0R | x :: rest -> x +. numeric_sum rest

let rec numeric_product (xs:list real) : Tot real (decreases xs) =
  match xs with [] -> 1.0R | x :: rest -> x *. numeric_product rest

let numeric_subtract (xs:list real) : real =
  match xs with
  | [] -> 0.0R
  | [x] -> 0.0R -. x
  | x :: rest -> x -. numeric_sum rest

let numeric_relation (r:A.relation) (x y:real) : prop =
  match r with
  | A.Le -> x <=. y
  | A.Lt -> x <. y
  | A.Ge -> y <=. x
  | A.Gt -> y <. x
  | A.Eq -> x == y

(* Only the standard interpretation of typed arithmetic operators is assumed;
   no certificate, polynomial, or linearization occurs in this contract. *)
let numeric_operators (i:interpretation value) (nu:value -> real) : prop =
  (forall (n:int). nu (VInt n) == of_int n) /\
  (forall (e:expr) (rho:env value) (n:int) (d:pos).
    A.numeral e == Some (n, d) ==>
    of_int d *. nu (eval i e rho) == of_int n) /\
  (forall (f:func_decl) (args:list expr) (rho:env value) (op:A.operation).
    A.operation_of f args == Some op ==>
    (let xs = map nu (eval_args i args rho) in
     let v = nu (eval i (App f args) rho) in
     match op with
     | A.Add -> v == numeric_sum xs
     | A.Mul -> v == numeric_product xs
     | A.Sub -> v == numeric_subtract xs
     | A.ToReal -> (match xs with [x] -> v == x | _ -> False)
     | A.Div -> (match xs with [x; y] -> ~(y == 0.0R) ==> v *. y == x | _ -> False))) /\
  (forall (e a b:expr) (rho:env value) (r:A.relation).
    A.comparison e == Some (r, a, b) /\ r <> A.Eq ==>
    (lit_true i rho e <==> numeric_relation r (nu (eval i a rho)) (nu (eval i b rho))))

(* The value type has no real constructor. Real term equality additionally
   needs reflection from the numeric projection, not just operator laws. *)
let numeric_model (i:interpretation value) (nu:value -> real) : prop =
  numeric_operators i nu /\
  (forall (e:expr) (rho:env value).
    get_sort e == A.int_s ==> VInt? (eval i e rho)) /\
  (forall (a b:expr) (rho:env value).
    get_sort a == A.real_s /\ get_sort b == A.real_s /\
    nu (eval i a rho) == nu (eval i b rho) ==>
    eval i a rho == eval i b rho)

let lemma_add_application (f:func_decl) (args:list expr)
                          (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires numeric_operators i nu /\ A.operation_of f args == Some A.Add)
          (ensures nu (eval i (App f args) rho) ==
                   numeric_sum (map nu (eval_args i args rho))) = ()

let lemma_mul_application (f:func_decl) (args:list expr)
                          (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires numeric_operators i nu /\ A.operation_of f args == Some A.Mul)
          (ensures nu (eval i (App f args) rho) ==
                   numeric_product (map nu (eval_args i args rho))) = ()

let valuation (i:interpretation value) (nu:value -> real) (rho:env value) : expr -> real =
  fun e -> nu (eval i e rho)

let denotes (p:A.poly) (v:real) (r:expr -> real) : prop =
  P.value p r == of_int p.denom *. v

let rec denotations (ps:list A.poly) (xs:list real) (r:expr -> real)
  : Tot prop (decreases ps) =
  match ps, xs with
  | [], [] -> True
  | p :: rest, x :: tail -> denotes p x r /\ denotations rest tail r
  | _, _ -> False

#push-options "--using_facts_from 'Prims FStar.Real' --fuel 0 --ifuel 0"

let lemma_scaled_sum (a b x y:real)
  : Lemma (b *. (a *. x) +. a *. (b *. y) == (a *. b) *. (x +. y)) = ()

let lemma_scaled_product (a b x y:real)
  : Lemma ((a *. x) *. (b *. y) == (a *. b) *. (x *. y)) = ()

let lemma_product_value (a b x y px qx tx:real)
  : Lemma (requires px == a *. x /\ qx == b *. y /\ tx == px *. qx)
          (ensures tx == (a *. b) *. (x *. y)) =
  calc (==) {
    tx;
    == {} px *. qx;
    == {} (a *. x) *. (b *. y);
    == { lemma_scaled_product a b x y } (a *. b) *. (x *. y);
  }

let lemma_scaled_quotient (a b c x y z:real)
  : Lemma (requires b *. y == c /\ z *. y == x)
          (ensures b *. (a *. x) == (c *. a) *. z) = ()

let lemma_negative_quotient (a b c x z:real)
  : Lemma (requires b *. (a *. x) == (c *. a) *. z)
          (ensures (0.0R -. b) *. (a *. x) == ((0.0R -. c) *. a) *. z) = ()

let lemma_scaled_value (n d a x z:real)
  : Lemma (requires n *. x == d *. z)
          (ensures n *. (a *. x) == (d *. a) *. z) = ()

#pop-options

let lemma_denotes_intro (p:A.poly) (x:real) (r:expr -> real)
  : Lemma (requires P.value p r == of_int p.denom *. x)
          (ensures denotes p x r) = ()

let lemma_denotes_add (p q:A.poly) (x y:real) (r:expr -> real)
  : Lemma (requires denotes p x r /\ denotes q y r)
          (ensures denotes (P.add p q) (x +. y) r) =
  P.lemma_add p q r;
  lemma_scaled_sum (of_int p.denom) (of_int q.denom) x y;
  assert (of_int (p.denom * q.denom) == of_int p.denom *. of_int q.denom);
  assert (P.value p r == of_int p.denom *. x);
  assert (P.value q r == of_int q.denom *. y);
  assert ((P.add p q).denom == p.denom * q.denom);
  assert (P.value (P.add p q) r == of_int (p.denom * q.denom) *. (x +. y));
  ()

let rec lemma_sum (ps:list A.poly) (xs:list real) (r:expr -> real)
  : Lemma (requires denotations ps xs r)
          (ensures denotes (P.sum ps) (numeric_sum xs) r)
          (decreases ps) =
  match ps, xs with
  | p :: rest, x :: tail ->
    assert (denotes p x r);
    lemma_sum rest tail r;
    lemma_denotes_add p (P.sum rest) x (numeric_sum tail) r
  | _, _ -> ()

let lemma_denotes_multiply (p q t:A.poly) (x y:real) (r:expr -> real)
  : Lemma (requires denotes p x r /\ denotes q y r /\ P.multiply p q == Some t)
          (ensures denotes t (x *. y) r) =
  P.lemma_multiply_denominator p q t;
  P.lemma_multiply p q t r;
  P.lemma_of_int_product p.denom q.denom;
  assert (P.value p r == of_int p.denom *. x);
  assert (P.value q r == of_int q.denom *. y);
  lemma_product_value (of_int p.denom) (of_int q.denom) x y
    (P.value p r) (P.value q r) (P.value t r);
  assert (P.value t r == of_int t.denom *. (x *. y));
  lemma_denotes_intro t (x *. y) r

let rec lemma_product (ps:list A.poly) (xs:list real) (p:A.poly) (r:expr -> real)
  : Lemma (requires denotations ps xs r /\ P.product ps == Some p)
          (ensures denotes p (numeric_product xs) r)
          (decreases ps) =
  match ps, xs with
  | q :: rest, x :: tail ->
    let t = Some?.v (P.product rest) in
    lemma_product rest tail t r;
    lemma_denotes_multiply q t p x (numeric_product tail) r
  | _, _ -> ()

let lemma_denotes_negative (p:A.poly) (x:real) (r:expr -> real)
  : Lemma (requires denotes p x r)
          (ensures denotes (P.scale (-1) 1 p) (0.0R -. x) r) =
  P.lemma_scale (-1) 1 p r;
  assert ((P.scale (-1) 1 p).denom == p.denom);
  assert (P.value (P.scale (-1) 1 p) r == of_int p.denom *. (0.0R -. x))

let lemma_subtract (ps:list A.poly) (xs:list real) (p:A.poly) (r:expr -> real)
  : Lemma (requires denotations ps xs r /\ A.subtract ps == Some p)
          (ensures denotes p (numeric_subtract xs) r) =
  match ps, xs with
  | [q], [x] -> lemma_denotes_negative q x r
  | q :: rest, x :: tail ->
    lemma_sum rest tail r;
    lemma_denotes_negative (P.sum rest) (numeric_sum tail) r;
    lemma_denotes_add q (P.scale (-1) 1 (P.sum rest)) x (0.0R -. numeric_sum tail) r
  | _, _ -> ()

let lemma_denotes_scale (n:int) (d:pos) (p:A.poly) (x z:real) (r:expr -> real)
  : Lemma (requires denotes p x r /\ of_int n *. x == of_int d *. z)
          (ensures denotes (P.scale n d p) z r) =
  P.lemma_scale n d p r;
  P.lemma_of_int_product d p.denom;
  lemma_scaled_value (of_int n) (of_int d) (of_int p.denom) x z

let lemma_divide (p q t:A.poly) (x y z:real) (r:expr -> real)
  : Lemma (requires denotes p x r /\ denotes q y r /\
                    A.divide p q == Some t /\ (~(y == 0.0R) ==> z *. y == x))
          (ensures denotes t z r) =
  P.lemma_all_zero q.mono r;
  assert (P.value q r == of_int q.cst);
  assert (of_int q.denom *. y == of_int q.cst);
  assert (~(y == 0.0R));
  assert (z *. y == x);
  lemma_scaled_quotient 1.0R (of_int q.denom) (of_int q.cst) x y z;
  if q.cst > 0 then (
    assert (t == P.scale q.denom q.cst p);
    lemma_denotes_scale q.denom q.cst p x z r)
  else (
    assert (t == P.scale (-q.denom) (-q.cst) p);
    lemma_negative_quotient 1.0R (of_int q.denom) (of_int q.cst) x z;
    lemma_denotes_scale (-q.denom) (-q.cst) p x z r)

#push-options "--fuel 4"

let rec lemma_linearize (fuel:nat) (e:expr) (p:A.poly)
                         (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires numeric_operators i nu /\ A.linearize fuel e == Some p)
          (ensures denotes p (nu (eval i e rho)) (valuation i nu rho))
          (decreases %[fuel; 0]) =
  assert (fuel > 0);
  match A.numeral e with
  | Some _ -> ()
  | None ->
    (match e with
     | App f args ->
       (match A.operation_of f args with
        | None -> ()
        | Some op ->
          A.lemma_linearize_application fuel f args op;
          lemma_linearize_args (fuel - 1) args i nu rho;
          let ps = Some?.v (A.linearize_args (fuel - 1) args) in
          let xs = map nu (eval_args i args rho) in
          let r = valuation i nu rho in
          assert (A.combine op ps e == Some p);
          (match op, ps with
           | A.Add, _ -> lemma_sum ps xs r
           | A.Mul, _ ->
             (match P.product ps with
              | Some q -> lemma_product ps xs q r
              | None -> ())
           | A.Sub, _ -> lemma_subtract ps xs p r
           | A.Div, [a; b] ->
             (match A.divide a b with
              | Some q ->
                (match xs with
                 | [x; y] -> lemma_divide a b q x y (nu (eval i e rho)) r
                 | _ -> ())
              | None -> ())
           | A.ToReal, [_] -> ()
           | _, _ -> ()))
     | _ -> ())

and lemma_linearize_args (fuel:nat) (args:list expr)
                         (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires numeric_operators i nu /\ Some? (A.linearize_args fuel args))
          (ensures denotations (Some?.v (A.linearize_args fuel args))
                               (map nu (eval_args i args rho)) (valuation i nu rho))
          (decreases %[fuel; 1; args]) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_linearize fuel a (Some?.v (A.linearize fuel a)) i nu rho;
    lemma_linearize_args fuel rest i nu rho

#pop-options

let embedding_model (i:interpretation value) (nu:value -> real) : prop =
  numeric_model i nu /\ boolean_model i /\ not_sound i /\ eq_sound i /\ or_sound i

let satisfied (i:interpretation value) (rho:env value) (positive:bool) (e:expr) : prop =
  if positive then lit_true i rho e else ~(lit_true i rho e)

let parsed_holds (positive:bool) (r:A.relation) (x y:real) : prop =
  if r = A.Eq then positive ==> x == y
  else if positive then numeric_relation r x y else ~(numeric_relation r x y)

let lemma_comparison (i:interpretation value) (nu:value -> real) (rho:env value)
                     (positive:bool) (e a b:expr) (r:A.relation)
  : Lemma (requires embedding_model i nu /\ A.comparison e == Some (r, a, b) /\
                    satisfied i rho positive e)
          (ensures parsed_holds positive r (nu (eval i a rho)) (nu (eval i b rho)) /\
                   get_sort e == bool_sort /\ get_sort a == get_sort b) =
  match e with
  | App _ [_; _] -> ()
  | _ -> ()

let rec lemma_literal (fuel:nat) (positive:bool) (e:expr) (p:bool)
                      (r:A.relation) (a b:expr)
                      (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires embedding_model i nu /\ A.literal fuel positive e == Some (p, r, a, b) /\
                    satisfied i rho positive e)
          (ensures parsed_holds p r (nu (eval i a rho)) (nu (eval i b rho)) /\
                   get_sort e == bool_sort /\ get_sort a == get_sort b)
          (decreases fuel) =
  match e with
  | App f [q] ->
    lemma_literal (fuel - 1) (not positive) q p r a b i nu rho
  | _ -> lemma_comparison i nu rho positive e a b r

let reversed (positive:bool) (r:A.relation) : bool =
  (positive && (r = A.Ge || r = A.Gt)) ||
  (not positive && (r = A.Le || r = A.Lt))

let difference (positive:bool) (r:A.relation) (x y:real) : real =
  if reversed positive r then y -. x else x -. y

let lemma_oriented (positive:bool) (rel:A.relation) (p q:A.poly)
                   (x y:real) (r:expr -> real)
  : Lemma (requires denotes p x r /\ denotes q y r)
          (ensures P.value (fst (A.oriented positive rel p q)) r ==
                   of_int (fst (A.oriented positive rel p q)).denom *.
                   difference positive rel x y) =
  if reversed positive rel then (
    lemma_denotes_negative p x r;
    lemma_denotes_add q (P.scale (-1) 1 p) y (0.0R -. x) r)
  else (
    lemma_denotes_negative q y r;
    lemma_denotes_add p (P.scale (-1) 1 q) x (0.0R -. y) r)

let lemma_integer_step (d:pos) (n m:int) (v:real)
  : Lemma (requires v == of_int d *. (of_int n -. of_int m) /\ v <. 0.0R)
          (ensures v +. of_int d <=. 0.0R) =
  assert (n < m);
  assert (n + 1 <= m);
  assert (of_int n +. 1.0R <=. of_int m)

let lemma_weighted (c:A.coefficient) (p:bool) (rel:A.relation) (integer:bool)
                   (pa pb:A.poly) (x y:real) (nx ny:int) (rv:expr -> real)
  : Lemma (requires fst c <> 0 /\ (rel <> A.Eq \/ p) /\
                    denotes pa x rv /\ denotes pb y rv /\ parsed_holds p rel x y /\
                    (integer ==> x == of_int nx /\ y == of_int ny))
          (ensures P.holds (A.weighted c p rel integer pa pb) rv) =
  let n, d = c in
  lemma_oriented p rel pa pb x y rv;
  let raw, strict = A.oriented p rel pa pb in
  assert (P.value raw rv == of_int raw.denom *. difference p rel x y);
  assert (if rel = A.Eq then P.value raw rv == 0.0R
          else if strict then P.value raw rv <. 0.0R else P.value raw rv <=. 0.0R);
  let integral = integer && rel <> A.Eq && strict in
  let adjusted = if integral then { raw with P.cst = raw.cst + raw.denom } else raw in
  if integral then (
    if reversed p rel then lemma_integer_step raw.denom ny nx (P.value raw rv)
    else lemma_integer_step raw.denom nx ny (P.value raw rv);
    assert (P.value adjusted rv == P.value raw rv +. of_int raw.denom));
  let weight = if rel = A.Eq || n > 0 then n else -n in
  P.lemma_scale weight d adjusted rv;
  assert (if rel = A.Eq then P.value adjusted rv == 0.0R
          else if strict && not integral then P.value adjusted rv <. 0.0R
          else P.value adjusted rv <=. 0.0R)

let integer_value (v:value) : int = match v with VInt n -> n | _ -> 0

#push-options "--fuel 4"

let lemma_prepare_literal (c:A.coefficient) (positive:bool) (e:expr) (out:A.contribution)
                          (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires embedding_model i nu /\ A.prepare_literal c positive e == Some out /\
                    satisfied i rho positive e)
          (ensures P.holds out (valuation i nu rho)) =
  if fst c = 0 then ()
  else
    let p, rel, a, b = Some?.v (A.literal 16 positive e) in
    lemma_literal 16 positive e p rel a b i nu rho;
    let pa = Some?.v (A.linearize 256 a) in
    let pb = Some?.v (A.linearize 256 b) in
    lemma_linearize 256 a pa i nu rho;
    lemma_linearize 256 b pb i nu rho;
    let va = eval i a rho in
    let vb = eval i b rho in
    lemma_weighted c p rel (get_sort a = A.int_s) pa pb (nu va) (nu vb)
                   (integer_value va) (integer_value vb) (valuation i nu rho)

#pop-options

let rec assumptions_hold (i:interpretation value) (rho:env value) (xs:list (bool & expr))
  : Tot prop (decreases xs) =
  match xs with
  | [] -> True
  | (positive, e) :: rest -> satisfied i rho positive e /\ assumptions_hold i rho rest

let rec lemma_prepare (xs:list (bool & expr)) (cs:list A.coefficient)
                      (ps:list A.contribution)
                      (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires embedding_model i nu /\ A.prepare xs cs == Some ps /\ assumptions_hold i rho xs)
          (ensures P.all_hold ps (valuation i nu rho))
          (decreases xs) =
  match xs, cs with
  | (positive, e) :: rest, c :: tail ->
    lemma_prepare_literal c positive e (Some?.v (A.prepare_literal c positive e)) i nu rho;
    lemma_prepare rest tail (Some?.v (A.prepare rest tail)) i nu rho
  | _, _ -> ()

let rec lemma_assumptions (facts:list expr) (lits:list expr)
                          (i:interpretation value) (rho:env value)
  : Lemma (requires conj_holds i rho facts /\ ~(clause_holds i rho lits))
          (ensures assumptions_hold i rho
                    (map A.positive_literal facts @ map A.negative_literal lits))
          (decreases %[facts; lits]) =
  match facts with
  | _ :: rest -> lemma_assumptions rest lits i rho
  | [] ->
    (match lits with [] -> () | _ :: rest -> lemma_assumptions [] rest i rho)

let lemma_check_sound (cs:list A.coefficient) (conclusion:expr) (facts:list expr)
                      (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires embedding_model i nu /\ A.check cs conclusion facts /\ conj_holds i rho facts)
          (ensures lit_true i rho conclusion) =
  let aux (_:squash (~(lit_true i rho conclusion))) : Lemma False =
    assert (~(clause_holds i rho (formula_clause conclusion)));
    lemma_assumptions facts (formula_clause conclusion) i rho;
    let ps = Some?.v (A.prepare (A.assumptions conclusion facts) cs) in
    lemma_prepare (A.assumptions conclusion facts) cs ps i nu rho;
    P.lemma_accepts_sound ps (valuation i nu rho)
  in
  FStar.Classical.excluded_middle (lit_true i rho conclusion);
  FStar.Classical.or_elim #(lit_true i rho conclusion) #(~(lit_true i rho conclusion))
    #(fun () -> lit_true i rho conclusion) (fun _ -> ()) (fun h -> aux h)

let lemma_check_with_numeric_model (cs:list A.coefficient) (conclusion:expr) (facts:list expr)
                                  (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> real). numeric_model i nu) /\
                    boolean_model i /\ not_sound i /\ eq_sound i /\ or_sound i /\
                    A.check cs conclusion facts /\ conj_holds i rho facts)
          (ensures lit_true i rho conclusion) =
  FStar.Classical.exists_elim (lit_true i rho conclusion)
    #(value -> real) #(fun nu -> numeric_model i nu) ()
    (fun nu -> lemma_check_sound cs conclusion facts i nu rho)
