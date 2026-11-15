module Z3SortedBv

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open Z3AstTheory
open FStar.List.Tot
module B = Z3BvSyntax
module D = Z3ExprScope
module V = Z3DatatypeValue
module L = FStar.List.Tot
module M = FStar.Math.Lemmas
module U = FStar.UInt
module R = Z3ClauseSyntax
module BS = Z3BooleanSyntax
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module BR = Z3SortedBooleanRewrite
module C = Z3CanonicalOps

let rec bit_values (truth:expr -> GTot bool) (args:list expr)
  : GTot (list bool) (decreases args) =
  match args with [] -> [] | e :: rest -> truth e :: bit_values truth rest

(* Expression valuation is unconstrained off well-scoped terms.  The following
   laws specify only the numeral, range, and addition operations; they do not
   mention the normalizer or its acceptance predicate. *)
let rec value_sum (number:expr -> GTot int) (es:list expr) : GTot int (decreases es) =
  match es with
  | [] -> 0
  | e :: rest -> number e + value_sum number rest

let range_model (number:expr -> GTot int) : prop =
  forall (w:pos) (e:expr).
    D.scoped [] e /\ get_sort e == B.bv_sort w ==>
    0 <= number e /\ number e < pow2 w

let add_model (number:expr -> GTot int) : prop =
  range_model number /\
  (forall (e:expr) (w:pos) (n:int).
    D.scoped [] e /\ B.numeral e == Some (w, n) ==> number e == n) /\
  (forall (f:func_decl) (args:list expr) (w:pos).
    D.scoped [] (App f args) /\ B.add_width f args == Some w ==>
    number (App f args) == value_sum number args % pow2 w)

let word_model (number:expr -> GTot int) (truth:expr -> GTot bool) : prop =
  add_model number /\
  truth R.true_expr /\ not (truth R.false_expr) /\
  (forall (e:expr) (w:pos) (args:list expr).
    D.scoped [] e /\ B.word_parts e == Some (w, args) ==>
    number e == B.bits_number (bit_values truth args)) /\
  (forall (e:expr) (s:B.extraction).
    D.scoped [] e /\ B.extract_parts e == Some s ==>
    number e == (number s.operand / pow2 s.low) % pow2 (s.high - s.low + 1)) /\
  (forall (e:expr) (c:B.concatenation).
    D.scoped [] e /\ B.concat_parts e == Some c ==>
    number e == number c.left * pow2 c.right_width + number c.right) /\
  (forall (e:expr) (c:B.concatenation3).
    D.scoped [] e /\ B.concat3_parts e == Some c ==>
    number e == number c.first * pow2 (c.width2 + c.width3) +
                number c.second * pow2 c.width3 + number c.third)

(* Primitive Boolean operator laws; none mentions a checker or a rewrite. *)
let rec truth_all (truth:expr -> GTot bool) (args:list expr) : GTot bool (decreases args) =
  match args with [] -> true | e :: rest -> truth e && truth_all truth rest

let boolean_model (truth:expr -> GTot bool) : prop =
  truth R.true_expr /\ not (truth R.false_expr) /\
  (forall (a:expr).
    D.scoped [] a /\ get_sort a == bool_sort ==>
    truth (R.mk_not_expr a) == not (truth a)) /\
  (forall (a b:expr).
    D.scoped [] a /\ D.scoped [] b /\ get_sort a == bool_sort /\ get_sort b == bool_sort ==>
    truth (R.mk_eq_expr a b) == (truth a = truth b) /\
    truth (App BS.boolean_xor_decl [a; b]) == (truth a <> truth b)) /\
  (forall (c a b:expr).
    D.scoped [] c /\ D.scoped [] a /\ D.scoped [] b /\
    get_sort c == bool_sort /\ get_sort a == bool_sort /\ get_sort b == bool_sort ==>
    truth (App BS.boolean_ite_decl [c; a; b]) == (if truth c then truth a else truth b)) /\
  (forall (args:list expr).
    D.scoped_args [] args /\ L.for_all (fun e -> get_sort e = bool_sort) args ==>
    truth (App (R.and_decl args) args) == truth_all truth args)

let order_model (number:expr -> GTot int) (truth:expr -> GTot bool) : prop =
  word_model number truth /\ boolean_model truth /\
  (forall (e:expr) (c:B.unsigned_comparison).
    D.scoped [] e /\ B.unsigned_parts e == Some c ==>
    truth e == B.unsigned_value c.relation (number c.lhs) (number c.rhs)) /\
  (forall (w:pos) (a b:expr).
    D.scoped [] a /\ D.scoped [] b /\ get_sort a == B.bv_sort w /\ get_sort b == B.bv_sort w ==>
    truth (R.mk_eq_expr a b) == (number a = number b)) /\
  (forall (a b:expr).
    D.scoped [] a /\ D.scoped [] b /\ get_sort a == bool_sort /\ get_sort b == bool_sort ==>
    truth (App (R.or_decl [a; b]) [a; b]) == (truth a || truth b))

let choice_model (number:expr -> GTot int) (truth:expr -> GTot bool) : prop =
  forall (w:pos) (c t u:expr).
    D.scoped [] c /\ D.scoped [] t /\ D.scoped [] u /\
    get_sort c == bool_sort /\ get_sort t == B.bv_sort w /\ get_sort u == B.bv_sort w ==>
    number (App (B.term_ite_decl (get_sort t)) [c; t; u]) ==
      (if truth c then number t else number u)

let complement_model (number:expr -> GTot int) : prop =
  forall (f:func_decl) (x:expr) (w:pos).
    D.scoped [] (App f [x]) /\ B.operation f [x] == Some (w, B.op_not) ==>
    number (App f [x]) == U.lognot (U.to_uint_t w (number x))

let rec lemma_total_append (number:expr -> GTot int) (xs ys:list expr)
  : Lemma (ensures value_sum number (L.append xs ys) == value_sum number xs + value_sum number ys)
          (decreases xs) =
  match xs with [] -> () | _ :: rest -> lemma_total_append number rest ys

let lemma_add_residues (p:pos) (a b x y:int)
  : Lemma (requires a % p == x % p /\ b % p == y % p)
          (ensures (a + b) % p == (x + y) % p) =
  M.lemma_mod_plus_distr_l a b p;
  M.lemma_mod_plus_distr_r (a % p) b p;
  M.lemma_mod_plus_distr_l x y p;
  M.lemma_mod_plus_distr_r (x % p) y p

(* The addition law above is the same right-folded modular operation used by
   the legacy binary/n-ary evaluator, not an extra certificate assumption. *)
let rec word_sum (w:pos) (xs:list (U.uint_t w)) : Tot int (decreases xs) =
  match xs with [] -> 0 | x :: rest -> x + word_sum w rest

let rec lemma_calculate_nary_add (w:pos) (xs:list (U.uint_t w))
  : Lemma (requires Cons? xs)
          (ensures B.calculate_nary w B.op_add xs == word_sum w xs % pow2 w)
          (decreases xs) =
  match xs with
  | [] -> ()
  | [x] -> M.small_mod x (pow2 w)
  | x :: y :: rest ->
    lemma_calculate_nary_add w (y :: rest);
    M.lemma_mod_plus_distr_r x (word_sum w (y :: rest)) (pow2 w)

let lemma_calculate_add (w:pos) (x y:U.uint_t w)
  : Lemma (B.calculate w B.op_add [x; y] == word_sum w [x; y] % pow2 w) =
  ()

let rec expression_words (number:expr -> GTot int) (w:pos) (args:list expr)
  : GTot (list (U.uint_t w)) (decreases args) =
  match args with
  | [] -> []
  | e :: rest -> U.to_uint_t w (number e) :: expression_words number w rest

let rec lemma_expression_words (number:expr -> GTot int) (w:pos) (args:list expr)
  : Lemma (requires range_model number /\ D.scoped_args [] args /\
                    L.for_all (fun e -> get_sort e = B.bv_sort w) args)
          (ensures word_sum w (expression_words number w args) == value_sum number args)
          (decreases args) =
  match args with
  | [] -> ()
  | e :: rest ->
    M.small_mod (number e) (pow2 w);
    lemma_expression_words number w rest

let rec lemma_summands (number:expr -> GTot int) (w:pos) (e:expr) (n:int) (atoms:list expr)
  : Lemma (requires add_model number /\ D.scoped [] e /\ B.summands w e == Some (n, atoms))
          (ensures get_sort e == B.bv_sort w /\
                   number e == (n + value_sum number atoms) % pow2 w)
          (decreases e) =
  match B.numeral e with
  | Some (q, k) -> M.small_mod k (pow2 w)
  | None ->
    (match e with
     | App f args ->
       (match B.add_width f args with
        | Some q -> lemma_summands_args number w args n atoms
        | None -> M.small_mod (number e) (pow2 w))
     | _ -> ())

and lemma_summands_args (number:expr -> GTot int) (w:pos) (args:list expr)
                        (n:int) (atoms:list expr)
  : Lemma (requires add_model number /\ D.scoped_args [] args /\
                    B.summands_args w args == Some (n, atoms))
          (ensures value_sum number args % pow2 w == (n + value_sum number atoms) % pow2 w)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    (match B.summands w a, B.summands_args w rest with
     | Some (n1, xs), Some (n2, ys) ->
       lemma_summands number w a n1 xs;
       lemma_summands_args number w rest n2 ys;
       lemma_total_append number xs ys;
       lemma_add_residues (pow2 w) (number a) (value_sum number rest)
         (n1 + value_sum number xs) (n2 + value_sum number ys)
     | _, _ -> ())

let lemma_equivalent (number:expr -> GTot int) (a b:expr)
  : Lemma (requires add_model number /\ B.equivalent a b)
          (ensures number a == number b) =
  let w = Some?.v (B.common_width a b) in
  let (n, xs) = Some?.v (B.summands w a) in
  let (m, ys) = Some?.v (B.summands w b) in
  lemma_summands number w a n xs;
  lemma_summands number w b m ys;
  lemma_add_residues (pow2 w) n (value_sum number xs) m (value_sum number ys)

(* Explicit bridge to the independently typed evaluator.  The projection can
   be defined on all sorted values, but reflection is needed only for scoped
   expressions of a common bit-vector sort. *)
let typed_number (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                 (rho:V.environment base sigma [])
                 (project:(s:sort -> V.value base sigma s -> GTot int)) (e:expr)
  : GTot int =
  if D.scoped [] e then project (get_sort e) (V.evaluate sigma i [] rho e) else 0

let lemma_equivalent_typed (#base:sort -> Type0) (sigma:V.signature)
                           (i:V.interpretation base sigma) (rho:V.environment base sigma [])
                           (project:(s:sort -> V.value base sigma s -> GTot int))
                           (a b:expr)
  : Lemma (requires B.equivalent a b /\ add_model (typed_number sigma i rho project) /\
                    (forall (w:pos) (x y:expr).
                      D.scoped [] x /\ D.scoped [] y /\
                      get_sort x == B.bv_sort w /\ get_sort y == B.bv_sort w /\
                      project (get_sort x) (V.evaluate sigma i [] rho x) ==
                      project (get_sort y) (V.evaluate sigma i [] rho y) ==>
                      V.evaluate sigma i [] rho x == V.evaluate sigma i [] rho y))
          (ensures V.evaluate sigma i [] rho a == V.evaluate sigma i [] rho b) =
  let w = Some?.v (B.common_width a b) in
  let (n, xs) = Some?.v (B.summands w a) in
  let (m, ys) = Some?.v (B.summands w b) in
  lemma_summands (typed_number sigma i rho project) w a n xs;
  lemma_summands (typed_number sigma i rho project) w b m ys;
  lemma_equivalent (typed_number sigma i rho project) a b

let rec lemma_bit_values_length (truth:expr -> GTot bool) (args:list expr)
  : Lemma (ensures L.length (bit_values truth args) == L.length args) (decreases args) =
  match args with [] -> () | _ :: rest -> lemma_bit_values_length truth rest

let rec lemma_number_bounds (bs:list bool)
  : Lemma (B.bits_number bs < pow2 (L.length bs)) (decreases bs) =
  match bs with
  | [] -> ()
  | _ :: rest -> lemma_number_bounds rest; M.pow2_plus 1 (L.length rest)

let rec lemma_number_equal (xs ys:list bool)
  : Lemma (requires L.length xs == L.length ys)
          (ensures (B.bits_number xs == B.bits_number ys) <==> xs == ys)
          (decreases xs) =
  match xs, ys with
  | [], [] -> ()
  | a :: rest, b :: tail ->
    lemma_number_equal rest tail;
    let x = if a then 1 else 0 in
    let y = if b then 1 else 0 in
    M.lemma_mod_plus x (B.bits_number rest) 2;
    M.lemma_mod_plus y (B.bits_number tail) 2;
    M.small_mod x 2;
    M.small_mod y 2
  | _, _ -> ()

let rec lemma_numeral_bits (truth:expr -> GTot bool) (width:nat) (n:nat)
  : Lemma (requires truth R.true_expr /\ not (truth R.false_expr) /\ n < pow2 width)
          (ensures L.length (B.numeral_bits width n) == width /\
                   D.scoped_args [] (B.numeral_bits width n) /\
                   L.for_all (fun e -> get_sort e = bool_sort) (B.numeral_bits width n) /\
                   B.bits_number (bit_values truth (B.numeral_bits width n)) == n)
          (decreases width) =
  if width = 0 then ()
  else (
    M.pow2_plus 1 (width - 1);
    lemma_numeral_bits truth (width - 1) (n / 2);
    M.lemma_div_mod n 2;
    assert (n % 2 = 0 \/ n % 2 = 1))

let lemma_parts (number:expr -> GTot int) (truth:expr -> GTot bool)
                (e:expr) (width:pos) (args:list expr)
  : Lemma (requires word_model number truth /\ D.scoped [] e /\ B.parts e == Some (width, args))
          (ensures width <= 4096 /\ L.length args == width /\
                   D.scoped_args [] args /\
                   L.for_all (fun a -> get_sort a = bool_sort) args /\
                   get_sort e == B.bv_sort width /\
                   number e == B.bits_number (bit_values truth args)) =
  if Some? (B.word_parts e) then
    (match e with App _ _ -> () | _ -> ())
  else (
    let _, n = Some?.v (B.numeral e) in
    lemma_numeral_bits truth width n)

let rec lemma_constant_bits (truth:expr -> GTot bool) (args:list expr) (bs:list bool)
  : Lemma (requires truth R.true_expr /\ not (truth R.false_expr) /\ B.constant_bits args == Some bs)
          (ensures bit_values truth args == bs)
          (decreases args) =
  match args with
  | [] -> ()
  | _ :: rest -> lemma_constant_bits truth rest (Some?.v (B.constant_bits rest))

let lemma_literal_equivalent (number:expr -> GTot int) (truth:expr -> GTot bool) (a b:expr)
  : Lemma (requires word_model number truth /\ D.scoped [] a /\ D.scoped [] b /\
                    B.literal_equivalent a b)
          (ensures get_sort a == get_sort b /\ number a == number b) =
  let w, args = Some?.v (B.word_parts a) in
  lemma_parts number truth a w args;
  lemma_constant_bits truth args (Some?.v (B.constant_bits args))

let rec lemma_boolean_args (args:list expr)
  : Lemma (requires L.for_all (fun a -> get_sort a = bool_sort) args)
          (ensures sorts_match args (L.map (fun _ -> bool_sort) args))
          (decreases args) =
  match args with [] -> () | _ :: rest -> lemma_boolean_args rest

let lemma_word_shape (args:list expr)
  : Lemma (requires L.length args > 0 /\ L.length args <= 4096 /\
                    D.scoped_args [] args /\ L.for_all (fun a -> get_sort a = bool_sort) args)
          (ensures D.scoped [] (B.word args) /\
                   B.word_parts (B.word args) == Some (L.length args, args) /\
                   get_sort (B.word args) == B.bv_sort (L.length args)) =
  lemma_boolean_args args

let rec lemma_split_shape (n:nat) (args:list expr)
  : Lemma (requires n <= L.length args /\ D.scoped_args [] args /\
                    L.for_all (fun a -> get_sort a = bool_sort) args)
          (ensures (let a, b = L.splitAt n args in
                    L.length a == n /\ L.length b == L.length args - n /\
                    D.scoped_args [] a /\ D.scoped_args [] b /\
                    L.for_all (fun e -> get_sort e = bool_sort) a /\
                    L.for_all (fun e -> get_sort e = bool_sort) b))
          (decreases n) =
  if n = 0 then ()
  else match args with _ :: rest -> lemma_split_shape (n - 1) rest | [] -> ()

let rec lemma_split_values (truth:expr -> GTot bool) (n:nat) (args:list expr)
  : Lemma (requires n <= L.length args)
          (ensures (let a, b = L.splitAt n args in
                    L.splitAt n (bit_values truth args) ==
                      (bit_values truth a, bit_values truth b)))
          (decreases n) =
  if n = 0 then ()
  else match args with _ :: rest -> lemma_split_values truth (n - 1) rest | [] -> ()

let rec lemma_split_number (n:nat) (bs:list bool)
  : Lemma (requires n <= L.length bs)
          (ensures (let a, b = L.splitAt n bs in
                    B.bits_number bs == B.bits_number a + pow2 n * B.bits_number b))
          (decreases n) =
  if n = 0 then ()
  else match bs with
    | _ :: rest ->
      lemma_split_number (n - 1) rest;
      M.pow2_plus 1 (n - 1);
      let a, b = L.splitAt (n - 1) rest in
      assert (pow2 n == 2 * pow2 (n - 1));
      assert (2 * B.bits_number rest ==
              2 * B.bits_number a + pow2 n * B.bits_number b)
    | [] -> ()

let lemma_split_divmod (n:nat) (bs:list bool)
  : Lemma (requires n <= L.length bs)
          (ensures (let a, b = L.splitAt n bs in
                    B.bits_number bs / pow2 n == B.bits_number b /\
                    B.bits_number bs % pow2 n == B.bits_number a)) =
  let a, b = L.splitAt n bs in
  lemma_split_number n bs;
  let rec lengths (n:nat) (bs:list bool)
    : Lemma (requires n <= L.length bs)
            (ensures L.length (fst (L.splitAt n bs)) == n)
            (decreases n) =
    if n = 0 then ()
    else match bs with _ :: rest -> lengths (n - 1) rest | [] -> () in
  lengths n bs;
  lemma_number_bounds a;
  assert (L.length a == n);
  assert (B.bits_number bs == B.bits_number a + B.bits_number b * pow2 n);
  M.lemma_div_plus (B.bits_number a) (B.bits_number b) (pow2 n);
  M.small_div (B.bits_number a) (pow2 n);
  M.lemma_mod_plus (B.bits_number a) (B.bits_number b) (pow2 n);
  M.small_mod (B.bits_number a) (pow2 n)

let lemma_extract_rewrite (number:expr -> GTot int) (truth:expr -> GTot bool)
                          (e result:expr)
  : Lemma (requires word_model number truth /\ D.scoped [] e /\
                    B.extract_rewrite e == Some result)
          (ensures D.scoped [] result /\ get_sort e == get_sort result /\ number e == number result) =
  let s = Some?.v (B.extract_parts e) in
  let width, args = Some?.v (B.parts s.operand) in
  let n = s.high - s.low + 1 in
  lemma_parts number truth s.operand width args;
  lemma_bit_values_length truth args;
  lemma_split_shape s.low args;
  lemma_split_values truth s.low args;
  let prefix, tail = L.splitAt s.low args in
  lemma_split_divmod s.low (bit_values truth args);
  lemma_split_shape n tail;
  lemma_split_values truth n tail;
  lemma_bit_values_length truth tail;
  let middle, suffix = L.splitAt n tail in
  lemma_split_divmod n (bit_values truth tail);
  lemma_word_shape middle;
  lemma_parts number truth result n middle

let rec lemma_append_number (xs ys:list bool)
  : Lemma (B.bits_number (xs @ ys) ==
           B.bits_number xs + pow2 (L.length xs) * B.bits_number ys)
          (decreases xs) =
  match xs with
  | [] -> ()
  | b :: rest ->
    let n = L.length rest in
    let nr = B.bits_number rest in
    let ny = B.bits_number ys in
    let d = if b then 1 else 0 in
    calc (==) {
      B.bits_number (xs @ ys);
      == { }
      d + 2 * B.bits_number (rest @ ys);
      == { lemma_append_number rest ys }
      d + 2 * (nr + pow2 n * ny);
      == { M.distributivity_add_right 2 nr (pow2 n * ny) }
      (d + 2 * nr) + 2 * (pow2 n * ny);
      == { M.paren_mul_right 2 (pow2 (L.length rest)) (B.bits_number ys) }
      (d + 2 * nr) + (2 * pow2 n) * ny;
      == { M.pow2_plus 1 (L.length rest); assert_norm (pow2 1 == 2);
           assert (pow2 (1 + n) == 2 * pow2 n) }
      (d + 2 * nr) + pow2 (1 + n) * ny;
      == { }
      B.bits_number xs + pow2 (L.length xs) * ny;
    }

let rec lemma_append_args (truth:expr -> GTot bool) (xs ys:list expr)
  : Lemma (requires D.scoped_args [] xs /\ D.scoped_args [] ys /\
                    L.for_all (fun a -> get_sort a = bool_sort) xs /\
                    L.for_all (fun a -> get_sort a = bool_sort) ys)
          (ensures D.scoped_args [] (xs @ ys) /\
                   L.for_all (fun a -> get_sort a = bool_sort) (xs @ ys) /\
                   bit_values truth (xs @ ys) == bit_values truth xs @ bit_values truth ys)
          (decreases xs) =
  match xs with [] -> () | _ :: rest -> lemma_append_args truth rest ys

let lemma_concat_parts (number:expr -> GTot int) (truth:expr -> GTot bool)
                       (e:expr) (c:B.concatenation)
  : Lemma (requires word_model number truth /\ D.scoped [] e /\ B.concat_parts e == Some c)
          (ensures D.scoped [] c.left /\ D.scoped [] c.right /\
                   get_sort e == B.bv_sort (c.left_width + c.right_width) /\
                   number e == number c.left * pow2 c.right_width + number c.right) =
  match e with App _ _ -> () | _ -> ()

let lemma_concat_rewrite (number:expr -> GTot int) (truth:expr -> GTot bool)
                         (e result:expr)
  : Lemma (requires word_model number truth /\ D.scoped [] e /\
                    B.concat_rewrite e == Some result)
          (ensures D.scoped [] result /\ get_sort e == get_sort result /\ number e == number result) =
  let c = Some?.v (B.concat_parts e) in
  let _, xs = Some?.v (B.parts c.left) in
  let _, ys = Some?.v (B.parts c.right) in
  lemma_concat_parts number truth e c;
  lemma_parts number truth c.left c.left_width xs;
  lemma_parts number truth c.right c.right_width ys;
  lemma_append_args truth ys xs;
  lemma_bit_values_length truth ys;
  lemma_append_number (bit_values truth ys) (bit_values truth xs);
  assert (B.bits_number (bit_values truth (ys @ xs)) ==
    B.bits_number (bit_values truth xs) * pow2 c.right_width +
    B.bits_number (bit_values truth ys));
  assert (number e == B.bits_number (bit_values truth (ys @ xs)));
  lemma_word_shape (ys @ xs);
  lemma_parts number truth result (c.left_width + c.right_width) (ys @ xs)

#push-options "--fuel 4 --ifuel 2"
let lemma_boolean_app (f:func_decl) (args:list expr)
  : Lemma (requires D.scoped_args [] args /\
                    L.for_all (fun a -> get_sort a = bool_sort) args /\
                    f.domain == L.map (fun _ -> bool_sort) args /\ f.range == bool_sort)
          (ensures D.scoped [] (App f args) /\ get_sort (App f args) == bool_sort) =
  lemma_boolean_args args

let lemma_full_adder_shape (a b carry:expr)
  : Lemma (requires D.scoped [] a /\ D.scoped [] b /\ D.scoped [] carry /\
                    get_sort a == bool_sort /\ get_sort b == bool_sort /\ get_sort carry == bool_sort)
          (ensures D.scoped [] (B.sum_bit a b carry) /\ D.scoped [] (B.carry_bit a b carry) /\
                   get_sort (B.sum_bit a b carry) == bool_sort /\
                   get_sort (B.carry_bit a b carry) == bool_sort) =
  lemma_boolean_app BS.boolean_xor_decl [a; b];
  lemma_boolean_app BS.boolean_xor_decl [App BS.boolean_xor_decl [a; b]; carry];
  lemma_boolean_app (R.eq_decl bool_sort) [a; b];
  lemma_boolean_app BS.boolean_ite_decl [R.mk_eq_expr a b; a; carry]

let lemma_full_adder (truth:expr -> GTot bool) (a b carry:expr)
  : Lemma (requires boolean_model truth /\ D.scoped [] a /\ D.scoped [] b /\ D.scoped [] carry /\
                    get_sort a == bool_sort /\ get_sort b == bool_sort /\ get_sort carry == bool_sort)
          (ensures truth (B.sum_bit a b carry) == ((truth a <> truth b) <> truth carry) /\
                   truth (B.carry_bit a b carry) ==
                     (if truth a = truth b then truth a else truth carry)) =
  lemma_full_adder_shape a b carry;
  assert (truth (App BS.boolean_xor_decl [a; b]) == (truth a <> truth b));
  assert (truth (R.mk_eq_expr a b) == (truth a = truth b))
#pop-options

let lemma_carry_arithmetic (n:nat) (a b c s d:nat) (k:nat{k <= 1}) (x y z:nat)
  : Lemma (requires s + 2 * d == a + b + c /\ z + pow2 n * k == x + y + d)
          (ensures s + 2 * z + pow2 (n + 1) * k == a + 2 * x + b + 2 * y + c) =
  M.pow2_plus 1 n;
  if k = 0 then () else ()

let rec lemma_add_values (carry:bool) (xs ys:list bool)
  : Lemma (requires L.length xs == L.length ys)
          (ensures (let sums, overflow = B.add_values carry xs ys in
                    L.length sums == L.length xs /\
                    B.bits_number sums + pow2 (L.length xs) * B.bit_number overflow ==
                      B.bits_number xs + B.bits_number ys + B.bit_number carry))
          (decreases xs) =
  match xs, ys with
  | a :: rest, b :: tail ->
    let next = if a = b then a else carry in
    lemma_add_values next rest tail;
    let sums, overflow = B.add_values next rest tail in
    assert (B.add_values carry xs ys == (((a <> b) <> carry) :: sums, overflow));
    assert (L.length xs == L.length rest + 1);
    assert (B.bits_number xs == B.bit_number a + 2 * B.bits_number rest);
    assert (B.bits_number ys == B.bit_number b + 2 * B.bits_number tail);
    assert (B.bits_number (((a <> b) <> carry) :: sums) ==
              B.bit_number ((a <> b) <> carry) + 2 * B.bits_number sums);
    lemma_carry_arithmetic (L.length rest) (B.bit_number a) (B.bit_number b) (B.bit_number carry)
      (B.bit_number ((a <> b) <> carry)) (B.bit_number next) (B.bit_number overflow)
      (B.bits_number rest) (B.bits_number tail) (B.bits_number sums);
    assert (B.bits_number ((a <> b <> carry) :: sums) +
            pow2 (L.length xs) * B.bit_number overflow ==
            B.bits_number xs + B.bits_number ys + B.bit_number carry)
  | _, _ -> ()

let rec lemma_add_bits (truth:expr -> GTot bool) (carry:expr) (xs ys:list expr)
  : Lemma (requires boolean_model truth /\
                    D.scoped [] carry /\ get_sort carry == bool_sort /\
                    D.scoped_args [] xs /\ D.scoped_args [] ys /\
                    L.length xs == L.length ys /\
                    L.for_all (fun a -> get_sort a = bool_sort) xs /\
                    L.for_all (fun a -> get_sort a = bool_sort) ys)
          (ensures (let sums, overflow = B.add_bits carry xs ys in
                    L.length sums == L.length xs /\ D.scoped_args [] sums /\
                    L.for_all (fun a -> get_sort a = bool_sort) sums /\
                    D.scoped [] overflow /\ get_sort overflow == bool_sort /\
                    (bit_values truth sums, truth overflow) ==
                      B.add_values (truth carry) (bit_values truth xs) (bit_values truth ys)))
          (decreases xs) =
  match xs, ys with
  | a :: rest, b :: tail ->
    lemma_full_adder_shape a b carry;
    lemma_full_adder truth a b carry;
    lemma_add_bits truth (B.carry_bit a b carry) rest tail
  | _, _ -> ()

let lemma_add_number (width:nat) (xs ys sums:list bool) (overflow:bool) (pa pb:int)
  : Lemma (requires L.length xs == width /\ L.length ys == width /\
                    (sums, overflow) == B.add_values false xs ys /\
                    pa == B.bits_number xs /\ pb == B.bits_number ys)
          (ensures pa + pb == B.bits_number sums + pow2 width * B.bit_number overflow) =
  lemma_add_values false xs ys

let lemma_addition_rewrite (number:expr -> GTot int) (truth:expr -> GTot bool)
                           (e result:expr)
  : Lemma (requires word_model number truth /\ boolean_model truth /\ D.scoped [] e /\
                    B.addition_rewrite e == Some result)
          (ensures D.scoped [] result /\ get_sort e == get_sort result /\ number e == number result) =
  match e with
  | App f [a; b] ->
    let width, _ = Some?.v (B.operation f [a; b]) in
    let _, xs = Some?.v (B.parts a) in
    let _, ys = Some?.v (B.parts b) in
    lemma_parts number truth a width xs;
    lemma_parts number truth b width ys;
    lemma_bit_values_length truth xs;
    lemma_bit_values_length truth ys;
    lemma_add_bits truth R.false_expr xs ys;
    let sums, overflow = B.add_bits R.false_expr xs ys in
    lemma_add_number width (bit_values truth xs) (bit_values truth ys)
      (bit_values truth sums) (truth overflow) (number a) (number b);
    lemma_word_shape sums;
    lemma_parts number truth result width sums;
    lemma_bit_values_length truth sums;
    lemma_number_bounds (bit_values truth sums);
    M.lemma_mod_plus (B.bits_number (bit_values truth sums))
      (B.bit_number (truth overflow)) (pow2 width);
    M.small_mod (B.bits_number (bit_values truth sums)) (pow2 width);
    assert ((number a + number b) % pow2 width == B.bits_number (bit_values truth sums));
    assert (B.add_width f [a; b] == Some width);
    assert (number e == (number a + number b) % pow2 width)
  | _ -> ()

let lemma_concat_shape (m n:pos) (x y:expr)
  : Lemma (requires m + n <= 4096 /\ D.scoped [] x /\ D.scoped [] y /\
                    get_sort x == B.bv_sort m /\ get_sort y == B.bv_sort n)
          (ensures D.scoped [] (B.concat m n x y) /\ get_sort (B.concat m n x y) == B.bv_sort (m + n) /\
                   B.concat_parts (B.concat m n x y) ==
                     Some { B.left_width = m; B.right_width = n; B.left = x; B.right = y }) =
  assert (sort_eq (B.bv_sort m) (B.bv_sort m));
  assert (sort_eq (B.bv_sort n) (B.bv_sort n))

let lemma_concat_value (number:expr -> GTot int) (truth:expr -> GTot bool)
                       (m n:pos) (x y:expr)
  : Lemma (requires word_model number truth /\ m + n <= 4096 /\
                    D.scoped [] x /\ D.scoped [] y /\
                    get_sort x == B.bv_sort m /\ get_sort y == B.bv_sort n)
          (ensures D.scoped [] (B.concat m n x y) /\ get_sort (B.concat m n x y) == B.bv_sort (m + n) /\
                   number (B.concat m n x y) == number x * pow2 n + number y) =
  lemma_concat_shape m n x y;
  lemma_concat_parts number truth (B.concat m n x y)
    { B.left_width = m; B.right_width = n; B.left = x; B.right = y }

#push-options "--fuel 0 --ifuel 0 --using_facts_from 'Prims FStar.Math.Lemmas'"
let lemma_concat_association_numbers (m n:nat) (x y z:int)
  : Lemma ((x * pow2 m + y) * pow2 n + z ==
           x * pow2 (m + n) + (y * pow2 n + z)) =
  M.pow2_plus m n
#pop-options

let lemma_concat3_parts (number:expr -> GTot int) (truth:expr -> GTot bool)
                        (e:expr) (c:B.concatenation3)
  : Lemma (requires word_model number truth /\ D.scoped [] e /\ B.concat3_parts e == Some c)
          (ensures D.scoped [] c.first /\ D.scoped [] c.second /\ D.scoped [] c.third /\
                   get_sort c.first == B.bv_sort c.width1 /\ get_sort c.second == B.bv_sort c.width2 /\
                   get_sort c.third == B.bv_sort c.width3 /\ c.width1 + c.width2 + c.width3 <= 4096 /\
                   get_sort e == B.bv_sort (c.width1 + c.width2 + c.width3) /\
                   number e == number c.first * pow2 (c.width2 + c.width3) +
                               number c.second * pow2 c.width3 + number c.third) =
  match e with App _ _ -> () | _ -> ()

let lemma_concat_association_rewrite (number:expr -> GTot int) (truth:expr -> GTot bool)
                                    (e result:expr)
  : Lemma (requires word_model number truth /\ D.scoped [] e /\
                    B.concat_association_rewrite e == Some result)
          (ensures D.scoped [] result /\ get_sort e == get_sort result /\ number e == number result) =
  match B.concat3_parts e with
  | Some (c:B.concatenation3) ->
    lemma_concat3_parts number truth e c;
    lemma_concat_value number truth c.width2 c.width3 c.second c.third;
    lemma_concat_value number truth c.width1 (c.width2 + c.width3) c.first
      (B.concat c.width2 c.width3 c.second c.third)
  | None ->
    let c:B.concatenation = Some?.v (B.concat_parts e) in
    let left:B.concatenation = Some?.v (B.concat_parts c.left) in
    assert (c.left_width == left.left_width + left.right_width);
    assert (result == B.concat left.left_width (left.right_width + c.right_width) left.left
      (B.concat left.right_width c.right_width left.right c.right));
    lemma_concat_parts number truth e c;
    lemma_concat_parts number truth c.left left;
    lemma_concat_value number truth left.right_width c.right_width left.right c.right;
    lemma_concat_value number truth left.left_width (left.right_width + c.right_width) left.left
      (B.concat left.right_width c.right_width left.right c.right);
    lemma_concat_association_numbers left.right_width c.right_width
      (number left.left) (number left.right) (number c.right)

let lemma_concat3_rewrite (number:expr -> GTot int) (truth:expr -> GTot bool)
                          (e result:expr)
  : Lemma (requires word_model number truth /\ D.scoped [] e /\
                    B.concat3_rewrite e == Some result)
          (ensures D.scoped [] result /\ get_sort e == get_sort result /\ number e == number result) =
  assert (B.concat_association_rewrite e == Some result);
  lemma_concat_association_rewrite number truth e result

#push-options "--fuel 4 --ifuel 2"
let lemma_unsigned_shape (width:pos) (op:decl_kind) (a b:expr)
  : Lemma (requires width <= 4096 /\ (op = B.op_ult \/ op = B.op_ule \/ op = B.op_uge) /\
                    D.scoped [] a /\ D.scoped [] b /\
                    get_sort a == B.bv_sort width /\ get_sort b == B.bv_sort width)
          (ensures D.scoped [] (B.unsigned width op a b) /\
                   B.unsigned_parts (B.unsigned width op a b) ==
                     Some { B.width = width; B.relation = op; B.lhs = a; B.rhs = b }) =
  assert (sort_eq (B.bv_sort width) (B.bv_sort width));
  assert (sorts_match [a; b] [B.bv_sort width; B.bv_sort width])

let lemma_compare_step_shape (a b lower:expr)
  : Lemma (requires D.scoped [] a /\ D.scoped [] b /\ D.scoped [] lower /\
                    get_sort a == bool_sort /\ get_sort b == bool_sort /\ get_sort lower == bool_sort)
          (ensures D.scoped [] (B.compare_step a b lower) /\ get_sort (B.compare_step a b lower) == bool_sort) =
  lemma_boolean_app (R.eq_decl bool_sort) [a; b];
  assert (D.scoped [] (R.mk_not_expr a));
  lemma_boolean_app BS.boolean_ite_decl [R.mk_eq_expr a b; lower; R.mk_not_expr a]

let lemma_compare_step (truth:expr -> GTot bool) (a b lower:expr)
  : Lemma (requires boolean_model truth /\ D.scoped [] a /\ D.scoped [] b /\ D.scoped [] lower /\
                    get_sort a == bool_sort /\ get_sort b == bool_sort /\ get_sort lower == bool_sort)
          (ensures truth (B.compare_step a b lower) ==
                     (if truth a = truth b then truth lower else not (truth a))) =
  lemma_compare_step_shape a b lower;
  assert (truth (R.mk_eq_expr a b) == (truth a = truth b));
  assert (truth (R.mk_not_expr a) == not (truth a))
#pop-options

let lemma_unsigned_parts (number:expr -> GTot int) (truth:expr -> GTot bool)
                         (e:expr) (c:B.unsigned_comparison)
  : Lemma (requires order_model number truth /\ D.scoped [] e /\ B.unsigned_parts e == Some c)
          (ensures c.width <= 4096 /\ D.scoped [] c.lhs /\ D.scoped [] c.rhs /\
                   get_sort c.lhs == B.bv_sort c.width /\ get_sort c.rhs == B.bv_sort c.width /\
                   get_sort e == bool_sort /\
                   (c.relation = B.op_ult \/ c.relation = B.op_ule \/ c.relation = B.op_uge) /\
                   truth e == B.unsigned_value c.relation (number c.lhs) (number c.rhs)) =
  match e with App _ _ -> () | _ -> ()

let rec lemma_le_values (lower:bool) (xs ys:list bool)
  : Lemma (requires L.length xs == L.length ys)
          (ensures B.le_values lower xs ys ==
                     (B.bits_number xs < B.bits_number ys ||
                       (B.bits_number xs = B.bits_number ys && lower)))
          (decreases xs) =
  match xs, ys with
  | a :: rest, b :: tail -> lemma_le_values (if a = b then lower else not a) rest tail
  | _, _ -> ()

let rec lemma_le_bits (truth:expr -> GTot bool) (lower:expr) (xs ys:list expr)
  : Lemma (requires boolean_model truth /\ D.scoped [] lower /\ get_sort lower == bool_sort /\
                    D.scoped_args [] xs /\ D.scoped_args [] ys /\ L.length xs == L.length ys /\
                    L.for_all (fun e -> get_sort e = bool_sort) xs /\
                    L.for_all (fun e -> get_sort e = bool_sort) ys)
          (ensures D.scoped [] (B.le_bits lower xs ys) /\ get_sort (B.le_bits lower xs ys) == bool_sort /\
                   truth (B.le_bits lower xs ys) ==
                     B.le_values (truth lower) (bit_values truth xs) (bit_values truth ys))
          (decreases xs) =
  match xs, ys with
  | a :: rest, b :: tail ->
    lemma_compare_step_shape a b lower;
    lemma_compare_step truth a b lower;
    lemma_le_bits truth (B.compare_step a b lower) rest tail
  | _, _ -> ()

let lemma_extract_parts (number:expr -> GTot int) (truth:expr -> GTot bool)
                        (e:expr) (s:B.extraction)
  : Lemma (requires word_model number truth /\ D.scoped [] e /\ B.extract_parts e == Some s)
          (ensures D.scoped [] s.operand /\ get_sort s.operand == B.bv_sort s.source_width /\
                   get_sort e == B.bv_sort (s.high - s.low + 1) /\
                   number e == (number s.operand / pow2 s.low) % pow2 (s.high - s.low + 1)) =
  match e with App _ _ -> () | _ -> ()

let lemma_slice_shape (width:pos) (high low:nat) (x:expr)
  : Lemma (requires width <= 4096 /\ low <= high /\ high < width /\
                    D.scoped [] x /\ get_sort x == B.bv_sort width)
          (ensures D.scoped [] (B.order_slice width high low x) /\
                   B.extract_parts (B.order_slice width high low x) ==
                     Some { B.source_width = width; B.high = high; B.low = low; B.operand = x } /\
                   get_sort (B.order_slice width high low x) == B.bv_sort (high - low + 1)) =
  assert (sort_eq (B.bv_sort width) (B.bv_sort width))

let lemma_literal (number:expr -> GTot int) (truth:expr -> GTot bool) (w:pos) (n:int)
  : Lemma (requires word_model number truth /\ w <= 4096 /\ 0 <= n /\ n < pow2 w)
          (ensures D.scoped [] (B.literal w n) /\ get_sort (B.literal w n) == B.bv_sort w /\
                   number (B.literal w n) == n) =
  assert (B.numeral (B.literal w n) == Some (w, n))

let lemma_low_slice (number:expr -> GTot int) (truth:expr -> GTot bool)
                    (width:pos) (m:pos{m < width}) (x:expr)
  : Lemma (requires word_model number truth /\ width <= 4096 /\
                    D.scoped [] x /\ get_sort x == B.bv_sort width)
          (ensures number (B.order_slice width (m - 1) 0 x) == number x % pow2 m) =
  lemma_slice_shape width (m - 1) 0 x;
  lemma_extract_parts number truth (B.order_slice width (m - 1) 0 x)
    { B.source_width = width; B.high = m - 1; B.low = 0; B.operand = x };
  assert (pow2 0 == 1)

let lemma_split_compare (width:pos) (m:pos{m < width}) (n:nat{n < pow2 m})
                        (x:nat{x < pow2 width})
  : Lemma ((n <= x) ==
            ((x / pow2 m) % pow2 (width - m) <> 0 || n <= x % pow2 m)) =
  M.pow2_plus m (width - m);
  M.lemma_div_mod x (pow2 m);
  assert (x / pow2 m < pow2 (width - m));
  M.small_mod (x / pow2 m) (pow2 (width - m))

#push-options "--fuel 4 --ifuel 2"
let lemma_alternative (number:expr -> GTot int) (truth:expr -> GTot bool)
                      (w:pos) (upper zero lower:expr)
  : Lemma (requires order_model number truth /\ D.scoped [] upper /\ D.scoped [] zero /\
                    D.scoped [] lower /\ get_sort upper == B.bv_sort w /\
                    get_sort zero == B.bv_sort w /\ get_sort lower == bool_sort)
          (ensures D.scoped [] (B.alternative upper zero lower) /\
                   get_sort (B.alternative upper zero lower) == bool_sort /\
                   truth (B.alternative upper zero lower) ==
                     (number upper <> number zero || truth lower)) =
  assert (D.scoped [] (R.mk_eq_expr upper zero));
  assert (get_sort (R.mk_eq_expr upper zero) == bool_sort);
  assert (truth (R.mk_eq_expr upper zero) == (number upper = number zero));
  assert (D.scoped [] (R.mk_not_expr (R.mk_eq_expr upper zero)));
  assert (truth (R.mk_not_expr (R.mk_eq_expr upper zero)) == (number upper <> number zero));
  lemma_boolean_app (R.or_decl [R.mk_not_expr (R.mk_eq_expr upper zero); lower])
    [R.mk_not_expr (R.mk_eq_expr upper zero); lower]
#pop-options

let lemma_split_rewrite (number:expr -> GTot int) (truth:expr -> GTot bool) (e result:expr)
  : Lemma (requires order_model number truth /\ D.scoped [] e /\ B.split_rewrite e == Some result)
          (ensures D.scoped [] result /\ get_sort result == bool_sort /\ truth e == truth result) =
  let c = Some?.v (B.unsigned_parts e) in
  let width, n = Some?.v (B.numeral c.lhs) in
  let m = B.needed_width width n in
  lemma_unsigned_parts number truth e c;
  let upper = B.order_slice width (width - 1) m c.rhs in
  let lower = B.order_slice width (m - 1) 0 c.rhs in
  lemma_slice_shape width (width - 1) m c.rhs;
  lemma_slice_shape width (m - 1) 0 c.rhs;
  lemma_extract_parts number truth upper
    { B.source_width = width; B.high = width - 1; B.low = m; B.operand = c.rhs };
  lemma_low_slice number truth width m c.rhs;
  lemma_literal number truth (width - m) 0;
  lemma_literal number truth m n;
  lemma_unsigned_shape m B.op_ule (B.literal m n) lower;
  lemma_unsigned_parts number truth (B.unsigned m B.op_ule (B.literal m n) lower)
    { B.width = m; B.relation = B.op_ule; B.lhs = B.literal m n; B.rhs = lower };
  lemma_alternative number truth (width - m) upper (B.literal (width - m) 0)
    (B.unsigned m B.op_ule (B.literal m n) lower);
  lemma_split_compare width m n (number c.rhs)

let lemma_order_rewrite (number:expr -> GTot int) (truth:expr -> GTot bool) (e result:expr)
  : Lemma (requires order_model number truth /\ D.scoped [] e /\ B.order_rewrite e == Some result)
          (ensures D.scoped [] result /\ get_sort result == bool_sort /\ truth e == truth result) =
  let c = Some?.v (B.unsigned_parts e) in
  lemma_unsigned_parts number truth e c;
  if c.lhs = c.rhs then ()
  else if c.relation = B.op_ult || c.relation = B.op_uge then (
    lemma_unsigned_shape c.width B.op_ule c.rhs c.lhs;
    lemma_unsigned_parts number truth (B.unsigned c.width B.op_ule c.rhs c.lhs)
      { B.width = c.width; B.relation = B.op_ule; B.lhs = c.rhs; B.rhs = c.lhs };
    if c.relation = B.op_ult then
      assert (result == R.mk_not_expr (B.unsigned c.width B.op_ule c.rhs c.lhs))
    else assert (result == B.unsigned c.width B.op_ule c.rhs c.lhs))
  else if B.numeral c.lhs = Some (c.width, 0) then ()
  else if Some? (B.parts c.lhs) && Some? (B.parts c.rhs) then (
    let _, xs = Some?.v (B.parts c.lhs) in
    let _, ys = Some?.v (B.parts c.rhs) in
    lemma_parts number truth c.lhs c.width xs;
    lemma_parts number truth c.rhs c.width ys;
    lemma_bit_values_length truth xs;
    lemma_bit_values_length truth ys;
    lemma_le_bits truth R.true_expr xs ys;
    lemma_le_values true (bit_values truth xs) (bit_values truth ys))
  else lemma_split_rewrite number truth e result

let typed_truth (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                (rho:V.environment base sigma [])
                (project:(s:sort -> V.value base sigma s -> GTot bool)) (e:expr)
  : GTot bool =
  if D.scoped [] e then project (get_sort e) (V.evaluate sigma i [] rho e) else false

let word_reflection (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                    (rho:V.environment base sigma [])
                    (project:(s:sort -> V.value base sigma s -> GTot int)) : prop =
  forall (w:pos) (x y:expr).
    D.scoped [] x /\ D.scoped [] y /\
    get_sort x == B.bv_sort w /\ get_sort y == B.bv_sort w /\
    project (get_sort x) (V.evaluate sigma i [] rho x) ==
    project (get_sort y) (V.evaluate sigma i [] rho y) ==>
    V.evaluate sigma i [] rho x == V.evaluate sigma i [] rho y

let boolean_reflection (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                       (rho:V.environment base sigma [])
                       (project:(s:sort -> V.value base sigma s -> GTot bool)) : prop =
  forall (x y:expr).
    D.scoped [] x /\ D.scoped [] y /\ get_sort x == bool_sort /\ get_sort y == bool_sort /\
    project (get_sort x) (V.evaluate sigma i [] rho x) ==
    project (get_sort y) (V.evaluate sigma i [] rho y) ==>
    V.evaluate sigma i [] rho x == V.evaluate sigma i [] rho y

let lemma_literal_equivalent_typed (#base:sort -> Type0) (sigma:V.signature)
                    (i:V.interpretation base sigma) (rho:V.environment base sigma [])
                    (project:(s:sort -> V.value base sigma s -> GTot int))
                    (bproject:(s:sort -> V.value base sigma s -> GTot bool)) (a b:expr)
  : Lemma (requires D.scoped [] a /\ D.scoped [] b /\ B.literal_equivalent a b /\
                    word_model (typed_number sigma i rho project) (typed_truth sigma i rho bproject) /\
                    word_reflection sigma i rho project)
          (ensures V.evaluate sigma i [] rho a == V.evaluate sigma i [] rho b) =
  lemma_literal_equivalent (typed_number sigma i rho project) (typed_truth sigma i rho bproject) a b;
  let w, _ = Some?.v (B.word_parts a) in
  assert (get_sort a == B.bv_sort w)

let lemma_extract_rewrite_typed (#base:sort -> Type0) (sigma:V.signature)
                    (i:V.interpretation base sigma) (rho:V.environment base sigma [])
                    (project:(s:sort -> V.value base sigma s -> GTot int))
                    (bproject:(s:sort -> V.value base sigma s -> GTot bool)) (e result:expr)
  : Lemma (requires D.scoped [] e /\ B.extract_rewrite e == Some result /\
                    word_model (typed_number sigma i rho project) (typed_truth sigma i rho bproject) /\
                    word_reflection sigma i rho project)
          (ensures D.scoped [] result /\ V.evaluate sigma i [] rho e == V.evaluate sigma i [] rho result) =
  lemma_extract_rewrite (typed_number sigma i rho project) (typed_truth sigma i rho bproject) e result;
  let s = Some?.v (B.extract_parts e) in
  assert (get_sort e == B.bv_sort (s.high - s.low + 1))

let lemma_concat_rewrite_typed (#base:sort -> Type0) (sigma:V.signature)
                    (i:V.interpretation base sigma) (rho:V.environment base sigma [])
                    (project:(s:sort -> V.value base sigma s -> GTot int))
                    (bproject:(s:sort -> V.value base sigma s -> GTot bool)) (e result:expr)
  : Lemma (requires D.scoped [] e /\ B.concat_rewrite e == Some result /\
                    word_model (typed_number sigma i rho project) (typed_truth sigma i rho bproject) /\
                    word_reflection sigma i rho project)
          (ensures D.scoped [] result /\ V.evaluate sigma i [] rho e == V.evaluate sigma i [] rho result) =
  lemma_concat_rewrite (typed_number sigma i rho project) (typed_truth sigma i rho bproject) e result;
  let c = Some?.v (B.concat_parts e) in
  assert (get_sort e == B.bv_sort (c.left_width + c.right_width))

let lemma_addition_rewrite_typed (#base:sort -> Type0) (sigma:V.signature)
                    (i:V.interpretation base sigma) (rho:V.environment base sigma [])
                    (project:(s:sort -> V.value base sigma s -> GTot int))
                    (bproject:(s:sort -> V.value base sigma s -> GTot bool)) (e result:expr)
  : Lemma (requires D.scoped [] e /\ B.addition_rewrite e == Some result /\
                    word_model (typed_number sigma i rho project) (typed_truth sigma i rho bproject) /\
                    boolean_model (typed_truth sigma i rho bproject) /\ word_reflection sigma i rho project)
          (ensures D.scoped [] result /\ V.evaluate sigma i [] rho e == V.evaluate sigma i [] rho result) =
  lemma_addition_rewrite (typed_number sigma i rho project) (typed_truth sigma i rho bproject) e result;
  match e with
  | App f args ->
    let w, _ = Some?.v (B.operation f args) in
    assert (get_sort e == B.bv_sort w)
  | _ -> ()

let lemma_concat_association_rewrite_typed (#base:sort -> Type0) (sigma:V.signature)
                    (i:V.interpretation base sigma) (rho:V.environment base sigma [])
                    (project:(s:sort -> V.value base sigma s -> GTot int))
                    (bproject:(s:sort -> V.value base sigma s -> GTot bool)) (e result:expr)
  : Lemma (requires D.scoped [] e /\ B.concat_association_rewrite e == Some result /\
                    word_model (typed_number sigma i rho project) (typed_truth sigma i rho bproject) /\
                    word_reflection sigma i rho project)
          (ensures D.scoped [] result /\ V.evaluate sigma i [] rho e == V.evaluate sigma i [] rho result) =
  lemma_concat_association_rewrite (typed_number sigma i rho project) (typed_truth sigma i rho bproject) e result;
  match B.concat3_parts e with
  | Some c -> assert (get_sort e == B.bv_sort (c.width1 + c.width2 + c.width3))
  | None ->
    let c = Some?.v (B.concat_parts e) in
    assert (get_sort e == B.bv_sort (c.left_width + c.right_width))

let lemma_order_rewrite_typed (#base:sort -> Type0) (sigma:V.signature)
                    (i:V.interpretation base sigma) (rho:V.environment base sigma [])
                    (project:(s:sort -> V.value base sigma s -> GTot int))
                    (bproject:(s:sort -> V.value base sigma s -> GTot bool)) (e result:expr)
  : Lemma (requires D.scoped [] e /\ B.order_rewrite e == Some result /\
                    order_model (typed_number sigma i rho project) (typed_truth sigma i rho bproject) /\
                    boolean_reflection sigma i rho bproject)
          (ensures D.scoped [] result /\ V.evaluate sigma i [] rho e == V.evaluate sigma i [] rho result) =
  lemma_order_rewrite (typed_number sigma i rho project) (typed_truth sigma i rho bproject) e result;
  let c = Some?.v (B.unsigned_parts e) in
  assert (get_sort e == bool_sort)

let rec lemma_bit_equalities (truth:expr -> GTot bool) (xs ys:list expr)
  : Lemma (requires boolean_model truth /\ D.scoped_args [] xs /\ D.scoped_args [] ys /\
                    L.length xs == L.length ys /\
                    L.for_all (fun x -> get_sort x = bool_sort) xs /\
                    L.for_all (fun x -> get_sort x = bool_sort) ys)
          (ensures D.scoped_args [] (B.bit_equalities xs ys) /\
                   L.for_all (fun x -> get_sort x = bool_sort) (B.bit_equalities xs ys) /\
                   (truth_all truth (B.bit_equalities xs ys) <==>
                    bit_values truth xs == bit_values truth ys))
          (decreases xs) =
  match xs, ys with
  | x :: rest, y :: tail ->
    lemma_bit_equalities truth rest tail;
    lemma_boolean_app (R.eq_decl bool_sort) [x; y];
    assert (truth (R.mk_eq_expr x y) == (truth x = truth y))
  | _, _ -> ()

let rec lemma_boolean_domain_map (args:list expr)
  : Lemma (R.boolean_domain args == L.map (fun _ -> bool_sort) args) (decreases args) =
  match args with [] -> () | _ :: rest -> lemma_boolean_domain_map rest

let lemma_equality_rewrite (number:expr -> GTot int) (truth:expr -> GTot bool)
                           (e result:expr)
  : Lemma (requires order_model number truth /\ D.scoped [] e /\
                    B.equality_rewrite e == Some result)
          (ensures D.scoped [] result /\ get_sort e == bool_sort /\ get_sort result == bool_sort /\
                   truth e == truth result) =
  match e with
  | App f [a; b] ->
    let width, xs = Some?.v (B.parts a) in
    let _, ys = Some?.v (B.parts b) in
    lemma_parts number truth a width xs;
    lemma_parts number truth b width ys;
    lemma_bit_values_length truth xs;
    lemma_bit_values_length truth ys;
    lemma_number_equal (bit_values truth xs) (bit_values truth ys);
    lemma_bit_equalities truth xs ys;
    lemma_boolean_domain_map (B.bit_equalities xs ys);
    lemma_boolean_app (R.and_decl (B.bit_equalities xs ys)) (B.bit_equalities xs ys);
    assert (truth result == truth_all truth (B.bit_equalities xs ys));
    assert (e == R.mk_eq_expr a b);
    assert (truth e == (number a = number b))
  | _ -> ()

let lemma_equality_rewrite_typed (#base:sort -> Type0) (sigma:V.signature)
                    (i:V.interpretation base sigma) (rho:V.environment base sigma [])
                    (project:(s:sort -> V.value base sigma s -> GTot int))
                    (bproject:(s:sort -> V.value base sigma s -> GTot bool)) (e result:expr)
  : Lemma (requires D.scoped [] e /\ B.equality_rewrite e == Some result /\
                    order_model (typed_number sigma i rho project) (typed_truth sigma i rho bproject) /\
                    boolean_reflection sigma i rho bproject)
          (ensures D.scoped [] result /\ V.evaluate sigma i [] rho e == V.evaluate sigma i [] rho result) =
  lemma_equality_rewrite (typed_number sigma i rho project) (typed_truth sigma i rho bproject) e result

let lemma_split_numeral (x y n p:int)
  : Lemma (requires p > 0 /\ 0 <= y /\ y < p)
          (ensures (x * p + y == n) <==> (x == n / p /\ y == n % p)) =
  M.lemma_div_mod n p;
  M.lemma_div_plus y x p;
  M.small_div y p;
  M.lemma_mod_plus y x p;
  M.small_mod y p

let lemma_numeral_parts (number:expr -> GTot int) (truth:expr -> GTot bool)
                        (e:expr) (w:pos) (n:int)
  : Lemma (requires word_model number truth /\ D.scoped [] e /\ B.numeral e == Some (w,n))
          (ensures w <= 4096 /\ 0 <= n /\ n < pow2 w /\ get_sort e == B.bv_sort w /\ number e == n) =
  match e with App _ _ -> () | _ -> ()

#push-options "--fuel 0 --ifuel 0 --using_facts_from 'Prims FStar.Math.Lemmas'"
let lemma_div_bound (m n:pos) (x:nat{x < pow2 (m + n)})
  : Lemma (0 <= x / pow2 n /\ x / pow2 n < pow2 m) =
  M.pow2_plus m n;
  M.lemma_div_mod x (pow2 n)
#pop-options

let lemma_concat_numeric_result (v n x y p:int)
  : Lemma (requires p > 0 /\ 0 <= y /\ y < p /\ v == x * p + y)
          (ensures (v == n) <==> (x == n / p /\ y == n % p)) =
  lemma_split_numeral x y n p

#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"
let lemma_concat_numeral_equality (number:expr -> GTot int) (truth:expr -> GTot bool)
                                  (a b result:expr)
  : Lemma (requires order_model number truth /\ D.scoped [] a /\ D.scoped [] b /\
                    B.concat_numeral_equality a b == Some result)
          (ensures D.scoped [] result /\ get_sort result == bool_sort /\
                   truth result == (number a = number b)) =
  let c:B.concatenation = Some?.v (B.concat_parts a) in
  let width, n = Some?.v (B.numeral b) in
  lemma_concat_parts number truth a c;
  lemma_numeral_parts number truth b width n;
  assert (width == c.left_width + c.right_width);
  let p = pow2 c.right_width in
  lemma_concat_numeric_result (number a) n (number c.left) (number c.right) (pow2 c.right_width);
  lemma_div_bound c.left_width c.right_width n;
  lemma_literal number truth c.left_width (n / p);
  lemma_literal number truth c.right_width (n % p);
  let r = R.mk_eq_expr c.right (B.literal c.right_width (n % p)) in
  let l = R.mk_eq_expr c.left (B.literal c.left_width (n / p)) in
  assert (truth r == (number c.right = n % p));
  assert (truth l == (number c.left = n / p));
  assert (D.scoped [] r /\ D.scoped [] l);
  assert (get_sort r == bool_sort /\ get_sort l == bool_sort);
  lemma_boolean_domain_map [r; l];
  lemma_boolean_app (R.and_decl [r; l]) [r; l];
  assert (result == App (R.and_decl [r; l]) [r; l]);
  assert (truth result == (truth r && truth l))
#pop-options

let lemma_concat_equality_rewrite (number:expr -> GTot int) (truth:expr -> GTot bool)
                                  (e result:expr)
  : Lemma (requires order_model number truth /\ D.scoped [] e /\
                    B.concat_equality_rewrite e == Some result)
          (ensures D.scoped [] result /\ get_sort e == bool_sort /\ get_sort result == bool_sort /\
                   truth e == truth result) =
  match e with
  | App _ [a; b] ->
    if Some? (B.concat_numeral_equality a b) then
      lemma_concat_numeral_equality number truth a b result
    else lemma_concat_numeral_equality number truth b a result;
    let c = if Some? (B.concat_parts a) then Some?.v (B.concat_parts a) else Some?.v (B.concat_parts b) in
    assert (e == R.mk_eq_expr a b);
    assert (truth e == (number a = number b))
  | _ -> ()

let lemma_concat_equality_rewrite_typed (#base:sort -> Type0) (sigma:V.signature)
                    (i:V.interpretation base sigma) (rho:V.environment base sigma [])
                    (project:(s:sort -> V.value base sigma s -> GTot int))
                    (bproject:(s:sort -> V.value base sigma s -> GTot bool)) (e result:expr)
  : Lemma (requires D.scoped [] e /\ B.concat_equality_rewrite e == Some result /\
                    order_model (typed_number sigma i rho project) (typed_truth sigma i rho bproject) /\
                    boolean_reflection sigma i rho bproject)
          (ensures D.scoped [] result /\ V.evaluate sigma i [] rho e == V.evaluate sigma i [] rho result) =
  lemma_concat_equality_rewrite (typed_number sigma i rho project) (typed_truth sigma i rho bproject) e result

let lemma_ite_parts (source c t u:expr)
  : Lemma (requires D.scoped [] source /\ B.ite_parts source == Some (c, t, u))
          (ensures source == App (B.term_ite_decl (get_sort t)) [c; t; u] /\
                   D.scoped [] c /\ D.scoped [] t /\ D.scoped [] u /\
                   get_sort c == bool_sort /\ get_sort t == get_sort u /\
                   get_sort source == get_sort t) =
  match source with App _ _ -> () | _ -> ()

#push-options "--fuel 4 --ifuel 2"
let lemma_numeral_branch (number:expr -> GTot int) (truth:expr -> GTot bool)
                         (w:pos) (guard other target:expr) (equal:bool)
  : Lemma (requires order_model number truth /\ D.scoped [] guard /\ D.scoped [] other /\
                    D.scoped [] target /\ get_sort guard == bool_sort /\
                    get_sort other == B.bv_sort w /\ get_sort target == B.bv_sort w)
          (ensures D.scoped [] (B.numeral_branch guard other target equal) /\
                   get_sort (B.numeral_branch guard other target equal) == bool_sort /\
                   truth (B.numeral_branch guard other target equal) ==
                     (if equal then truth guard || number other = number target
                      else truth guard && number other = number target)) =
  let e = R.mk_eq_expr other target in
  assert (D.scoped [] e /\ get_sort e == bool_sort);
  assert (truth e == (number other = number target));
  if equal then (
    lemma_boolean_domain_map [guard; e];
    lemma_boolean_app (R.or_decl [guard; e]) [guard; e])
  else (
    lemma_boolean_domain_map [guard; e];
    lemma_boolean_app (R.and_decl [guard; e]) [guard; e])

let lemma_mixed_comparison (number:expr -> GTot int) (truth:expr -> GTot bool)
                           (source target result:expr)
  : Lemma (requires order_model number truth /\ choice_model number truth /\
                    D.scoped [] source /\ D.scoped [] target /\
                    B.mixed_comparison source target == Some result)
          (ensures D.scoped [] result /\ get_sort result == bool_sort /\
                   get_sort source == get_sort target /\
                   truth result == (number source = number target)) =
  let c, t, u = Some?.v (B.ite_parts source) in
  let width, n = Some?.v (B.numeral target) in
  lemma_ite_parts source c t u;
  lemma_numeral_parts number truth target width n;
  assert (D.scoped [] c /\ D.scoped [] t /\ D.scoped [] u);
  assert (get_sort c == bool_sort /\ get_sort t == get_sort u);
  if Some? (B.numeral t) then (
    let _, k = Some?.v (B.numeral t) in
    lemma_numeral_parts number truth t width k;
    assert (number source == (if truth c then number t else number u));
    if n = k then lemma_numeral_branch number truth width c u target true
    else lemma_numeral_branch number truth width (R.mk_not_expr c) u target false)
  else (
    let _, k = Some?.v (B.numeral u) in
    lemma_numeral_parts number truth u width k;
    assert (number source == (if truth c then number t else number u));
    if n = k then lemma_numeral_branch number truth width (R.mk_not_expr c) t target true
    else lemma_numeral_branch number truth width c t target false)
#pop-options

let lemma_mixed_equality (number:expr -> GTot int) (truth:expr -> GTot bool)
                         (e result:expr)
  : Lemma (requires order_model number truth /\ choice_model number truth /\ D.scoped [] e /\
                    B.mixed_equality e == Some result)
          (ensures D.scoped [] result /\ get_sort e == bool_sort /\ get_sort result == bool_sort /\
                   truth e == truth result) =
  match e with
  | App _ [a; b] ->
    if Some? (B.mixed_comparison a b) then
      lemma_mixed_comparison number truth a b result
    else lemma_mixed_comparison number truth b a result;
    let width, n = if Some? (B.numeral a) then Some?.v (B.numeral a) else Some?.v (B.numeral b) in
    assert (e == R.mk_eq_expr a b);
    assert (truth e == (number a = number b))
  | _ -> ()

let lemma_order_rewrite_all (number:expr -> GTot int) (truth:expr -> GTot bool) (e result:expr)
  : Lemma (requires order_model number truth /\ choice_model number truth /\
                    B.order_rewrite_all e == Some result)
          (ensures D.scoped [] e /\ D.scoped [] result /\ get_sort e == bool_sort /\
                   get_sort result == bool_sort /\ truth e == truth result) =
  if Some? (B.mixed_equality e) then lemma_mixed_equality number truth e result
  else lemma_order_rewrite number truth e result;
  if Some? (B.mixed_equality e) then ()
  else let c = Some?.v (B.unsigned_parts e) in lemma_unsigned_parts number truth e c

let lemma_order_rewrite_all_typed (#base:sort -> Type0) (sigma:V.signature)
                    (i:V.interpretation base sigma) (rho:V.environment base sigma [])
                    (project:(s:sort -> V.value base sigma s -> GTot int))
                    (bproject:(s:sort -> V.value base sigma s -> GTot bool)) (e result:expr)
  : Lemma (requires D.scoped [] e /\ B.order_rewrite_all e == Some result /\
                    order_model (typed_number sigma i rho project) (typed_truth sigma i rho bproject) /\
                    choice_model (typed_number sigma i rho project) (typed_truth sigma i rho bproject) /\
                    boolean_reflection sigma i rho bproject)
          (ensures D.scoped [] result /\ V.evaluate sigma i [] rho e == V.evaluate sigma i [] rho result) =
  lemma_order_rewrite_all (typed_number sigma i rho project) (typed_truth sigma i rho bproject) e result

let lemma_complement_value (number:expr -> GTot int) (truth:expr -> GTot bool)
                           (width:pos) (x:expr)
  : Lemma (requires word_model number truth /\ complement_model number /\ width <= 4096 /\
                    D.scoped [] x /\ get_sort x == B.bv_sort width)
          (ensures D.scoped [] (B.complement width x) /\ get_sort (B.complement width x) == B.bv_sort width /\
                   number (B.complement width x) == U.lognot (U.to_uint_t width (number x))) =
  assert (sort_eq (B.bv_sort width) (B.bv_sort width));
  assert (D.scoped [] (B.complement width x));
  match B.complement width x with
  | App f args -> assert (B.operation f args == Some (width, B.op_not))
  | _ -> ()

let lemma_not_number (width:pos) (x:U.uint_t width)
  : Lemma (U.lognot x == pow2 width - 1 - x) =
  U.lemma_lognot_value_mod #width x;
  M.small_mod (pow2 width - 1 - x) (pow2 width)

let lemma_not_concat_numbers (m n:pos) (x:U.uint_t m) (y:U.uint_t n) (z:U.uint_t (m + n))
  : Lemma (requires z == x * pow2 n + y)
          (ensures U.lognot z == U.lognot x * pow2 n + U.lognot y) =
  lemma_not_number m x;
  lemma_not_number n y;
  lemma_not_number (m + n) z;
  M.pow2_plus m n;
  M.distributivity_sub_left (pow2 m - 1) x (pow2 n);
  M.distributivity_sub_left (pow2 m) 1 (pow2 n)

let lemma_not_operation (number:expr -> GTot int) (f:func_decl) (x:expr) (w:pos)
  : Lemma (requires complement_model number /\ D.scoped [] (App f [x]) /\
                    B.operation f [x] == Some (w, B.op_not))
          (ensures number (App f [x]) == U.lognot (U.to_uint_t w (number x))) =
  ()

let lemma_complement_concat_value (number:expr -> GTot int) (truth:expr -> GTot bool)
                                 (m n:pos) (x y:expr)
  : Lemma (requires word_model number truth /\ complement_model number /\ m + n <= 4096 /\
                    D.scoped [] x /\ D.scoped [] y /\
                    get_sort x == B.bv_sort m /\ get_sort y == B.bv_sort n)
          (ensures (let result = B.concat m n (B.complement m x) (B.complement n y) in
                    D.scoped [] result /\ get_sort result == B.bv_sort (m + n) /\
                    number result == U.lognot (U.to_uint_t m (number x)) * pow2 n +
                                     U.lognot (U.to_uint_t n (number y)))) =
  lemma_complement_value number truth m x;
  lemma_complement_value number truth n y;
  lemma_concat_value number truth m n (B.complement m x) (B.complement n y)

let lemma_not_concat_rewrite (number:expr -> GTot int) (truth:expr -> GTot bool) (e result:expr)
  : Lemma (requires word_model number truth /\ complement_model number /\ D.scoped [] e /\
                    B.not_concat_rewrite e == Some result)
          (ensures D.scoped [] result /\ get_sort e == get_sort result /\ number e == number result) =
  match e with
  | App f [x] ->
    let c = Some?.v (B.concat_parts x) in
    let width = c.left_width + c.right_width in
    assert (result == B.concat c.left_width c.right_width
      (B.complement c.left_width c.left) (B.complement c.right_width c.right));
    lemma_concat_parts number truth x c;
    lemma_not_operation number f x width;
    M.small_mod (number c.left) (pow2 c.left_width);
    M.small_mod (number c.right) (pow2 c.right_width);
    M.small_mod (number x) (pow2 width);
    assert (U.to_uint_t c.left_width (number c.left) == number c.left);
    assert (U.to_uint_t c.right_width (number c.right) == number c.right);
    assert (U.to_uint_t width (number x) == number x);
    lemma_not_concat_numbers c.left_width c.right_width
      (number c.left) (number c.right) (number x);
    lemma_complement_concat_value number truth c.left_width c.right_width c.left c.right;
    assert (number e == U.lognot #width (number x));
    assert (number result == U.lognot #width (number x))
  | _ -> ()

let lemma_not_concat_rewrite_typed (#base:sort -> Type0) (sigma:V.signature)
                    (i:V.interpretation base sigma) (rho:V.environment base sigma [])
                    (project:(s:sort -> V.value base sigma s -> GTot int))
                    (bproject:(s:sort -> V.value base sigma s -> GTot bool)) (e result:expr)
  : Lemma (requires D.scoped [] e /\ B.not_concat_rewrite e == Some result /\
                    word_model (typed_number sigma i rho project) (typed_truth sigma i rho bproject) /\
                    complement_model (typed_number sigma i rho project) /\ word_reflection sigma i rho project)
          (ensures D.scoped [] result /\ V.evaluate sigma i [] rho e == V.evaluate sigma i [] rho result) =
  lemma_not_concat_rewrite (typed_number sigma i rho project) (typed_truth sigma i rho bproject) e result;
  match e with
  | App _ [x] ->
    let c = Some?.v (B.concat_parts x) in
    assert (get_sort e == B.bv_sort (c.left_width + c.right_width))
  | _ -> ()

let lemma_word_rewrite_typed (#base:sort -> Type0) (sigma:V.signature)
                    (i:V.interpretation base sigma) (rho:V.environment base sigma [])
                    (project:(s:sort -> V.value base sigma s -> GTot int))
                    (bproject:(s:sort -> V.value base sigma s -> GTot bool)) (e result:expr)
  : Lemma (requires D.scoped [] e /\ B.word_rewrite e == Some result /\
                    order_model (typed_number sigma i rho project) (typed_truth sigma i rho bproject) /\
                    complement_model (typed_number sigma i rho project) /\
                    word_reflection sigma i rho project /\ boolean_reflection sigma i rho bproject)
          (ensures D.scoped [] result /\ V.evaluate sigma i [] rho e == V.evaluate sigma i [] rho result) =
  if Some? (B.equality_rewrite e) then
    lemma_equality_rewrite_typed sigma i rho project bproject e result
  else if Some? (B.concat_equality_rewrite e) then
    lemma_concat_equality_rewrite_typed sigma i rho project bproject e result
  else if Some? (B.extract_rewrite e) then
    lemma_extract_rewrite_typed sigma i rho project bproject e result
  else if Some? (B.concat_rewrite e) then
    lemma_concat_rewrite_typed sigma i rho project bproject e result
  else if Some? (B.addition_rewrite e) then
    lemma_addition_rewrite_typed sigma i rho project bproject e result
  else if Some? (B.concat3_rewrite e) then (
    assert (B.concat_association_rewrite e == Some result);
    lemma_concat_association_rewrite_typed sigma i rho project bproject e result)
  else if Some? (B.concat_association_rewrite e) then
    lemma_concat_association_rewrite_typed sigma i rho project bproject e result
  else lemma_not_concat_rewrite_typed sigma i rho project bproject e result

#push-options "--fuel 4 --ifuel 2 --z3rlimit 100"
let lemma_projection (number:expr -> GTot int) (truth:expr -> GTot bool)
                     (width:pos) (source:expr) (bit:nat)
  : Lemma (requires order_model number truth /\ width <= 4096 /\ bit < width /\
                    D.scoped [] source /\ get_sort source == B.bv_sort width)
          (ensures D.scoped [] (B.projection width source bit) /\
                   get_sort (B.projection width source bit) == bool_sort /\
                   truth (B.projection width source bit) ==
                     ((number source / pow2 bit) % 2 <> 0)) =
  lemma_literal number truth 1 1;
  let extracted = B.projection_operand width source bit in
  assert (D.scoped [] extracted);
  if width = 1 then (
    assert (bit == 0);
    assert (extracted == source);
    assert_norm (pow2 0 == 1 /\ pow2 1 == 2);
    M.small_mod (number source) 2)
  else (
    let s : B.extraction =
      { B.source_width = width; B.high = bit; B.low = bit; B.operand = source } in
    lemma_slice_shape width bit bit source;
    assert (extracted == B.order_slice width bit bit source);
    assert (B.extract_parts extracted == Some s);
    lemma_extract_parts number truth extracted s);
  assert_norm (pow2 1 == 2);
  assert (number extracted == (number source / pow2 bit) % 2);
  let comparison : B.unsigned_comparison =
    { B.width = 1; B.relation = B.op_ule; B.lhs = B.literal 1 1; B.rhs = extracted } in
  assert (B.unsigned_parts (B.projection width source bit) == Some comparison);
  assert (D.scoped [] (B.projection width source bit));
  lemma_unsigned_parts number truth (B.projection width source bit) comparison;
  assert (0 <= (number source / pow2 bit) % 2 /\ (number source / pow2 bit) % 2 < 2)
#pop-options

let lemma_projection_step (n:nat) (start:nat) (b:bool) (tail:nat)
  : Lemma (requires b == ((n / pow2 start) % 2 <> 0) /\ tail == n / pow2 (start + 1))
          (ensures (if b then 1 else 0) + 2 * tail == n / pow2 start) =
  M.pow2_plus start 1;
  M.division_multiplication_lemma n (pow2 start) 2;
  M.lemma_div_mod (n / pow2 start) 2;
  assert ((n / pow2 start) % 2 = 0 \/ (n / pow2 start) % 2 = 1)

let lemma_bits_cons (b:bool) (bs:list bool)
  : Lemma (B.bits_number (b :: bs) == (if b then 1 else 0) + 2 * B.bits_number bs) = ()

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let rec lemma_projection_bits (number:expr -> GTot int) (truth:expr -> GTot bool)
                              (width:pos) (source:expr) (start count:nat)
  : Lemma (requires order_model number truth /\ width <= 4096 /\ start + count == width /\
                    D.scoped [] source /\ get_sort source == B.bv_sort width)
          (ensures L.length (B.projection_bits width source start count) == count /\
                   D.scoped_args [] (B.projection_bits width source start count) /\
                   L.for_all (fun e -> get_sort e = bool_sort) (B.projection_bits width source start count) /\
                   B.bits_number (bit_values truth (B.projection_bits width source start count)) ==
                     number source / pow2 start)
          (decreases count) =
  let n = number source in
  if count = 0 then M.small_div n (pow2 width)
  else (
    lemma_projection number truth width source start;
    assert (start + count == width);
    assert (start + 1 + (count - 1) == width);
    lemma_projection_bits number truth width source (start + 1) (count - 1);
    assert (B.projection_bits width source start count ==
      B.projection width source start :: B.projection_bits width source (start + 1) (count - 1));
    assert (bit_values truth (B.projection_bits width source start count) ==
      truth (B.projection width source start) ::
      bit_values truth (B.projection_bits width source (start + 1) (count - 1)));
    lemma_bits_cons (truth (B.projection width source start))
      (bit_values truth (B.projection_bits width source (start + 1) (count - 1)));
    lemma_projection_step n start (truth (B.projection width source start))
      (B.bits_number (bit_values truth (B.projection_bits width source (start + 1) (count - 1)))))
#pop-options

let rec lemma_matching_projections (width:pos) (source:expr) (start count:nat) (args:list expr)
  : Lemma (requires B.matching_projections width source start count args)
          (ensures args == B.projection_bits width source start count)
          (decreases args) =
  match args with
  | [] -> ()
  | _ :: rest -> lemma_matching_projections width source (start + 1) (count - 1) rest

let lemma_div_one (n:int) : Lemma (n / 1 == n) = ()

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let lemma_projection_equivalent (number:expr -> GTot int) (truth:expr -> GTot bool) (a b:expr)
  : Lemma (requires order_model number truth /\ D.scoped [] a /\ D.scoped [] b /\
                    B.projection_equivalent a b)
          (ensures get_sort a == get_sort b /\ number a == number b) =
  let width, args = Some?.v (B.word_parts b) in
  lemma_matching_projections width a 0 width args;
  lemma_parts number truth b width args;
  lemma_projection_bits number truth width a 0 width;
  assert_norm (pow2 0 == 1);
  lemma_div_one (number a);
  assert (args == B.projection_bits width a 0 width);
  assert (number b == B.bits_number (bit_values truth args));
  assert (B.bits_number (bit_values truth args) == number a / pow2 0)
#pop-options

let lemma_projection_equivalent_typed (#base:sort -> Type0) (sigma:V.signature)
                    (i:V.interpretation base sigma) (rho:V.environment base sigma [])
                    (project:(s:sort -> V.value base sigma s -> GTot int))
                    (bproject:(s:sort -> V.value base sigma s -> GTot bool)) (a b:expr)
  : Lemma (requires D.scoped [] a /\ D.scoped [] b /\ B.projection_equivalent a b /\
                    order_model (typed_number sigma i rho project) (typed_truth sigma i rho bproject) /\
                    word_reflection sigma i rho project)
          (ensures V.evaluate sigma i [] rho a == V.evaluate sigma i [] rho b) =
  lemma_projection_equivalent (typed_number sigma i rho project) (typed_truth sigma i rho bproject) a b;
  let width, _ = Some?.v (B.word_parts b) in
  assert (get_sort a == B.bv_sort width)

let rec lemma_bits_equivalent_typed (#base:sort -> Type0) (s:S.checked_schema)
                   (bc:S.boolean_carrier base) (model:T.scalar_model base)
                   (other:V.interpretation base (S.signature s))
                   (rho:V.environment base (S.signature s) []) (xs ys:list expr)
  : Lemma (requires D.scoped_args [] xs /\ D.scoped_args [] ys /\
                    B.bits_equivalent xs ys)
          (ensures bit_values (T.truth_at s bc model other [] rho) xs ==
                   bit_values (T.truth_at s bc model other [] rho) ys)
          (decreases xs) =
  match xs, ys with
  | x :: rest, y :: tail ->
    BR.lemma_equivalent s bc model other [] rho 64 8 x y;
    lemma_bits_equivalent_typed s bc model other rho rest tail
  | _, _ -> ()

let lemma_word_equivalent_sorted (#base:sort -> Type0) (s:S.checked_schema)
                   (bc:S.boolean_carrier base) (model:T.scalar_model base)
                   (other:V.interpretation base (S.signature s))
                   (rho:V.environment base (S.signature s) [])
                   (project:(t:sort -> V.value base (S.signature s) t -> GTot int))
                   (a b:expr)
  : Lemma (requires D.scoped [] a /\ D.scoped [] b /\ B.word_equivalent a b /\
                    word_model (typed_number (S.signature s) (T.interpretation s bc model other) rho project)
                               (T.truth_at s bc model other [] rho) /\
                    word_reflection (S.signature s) (T.interpretation s bc model other) rho project)
          (ensures V.evaluate (S.signature s) (T.interpretation s bc model other) [] rho a ==
                   V.evaluate (S.signature s) (T.interpretation s bc model other) [] rho b) =
  let number = typed_number (S.signature s) (T.interpretation s bc model other) rho project in
  let truth = T.truth_at s bc model other [] rho in
  let width, xs = Some?.v (B.parts a) in
  let _, ys = Some?.v (B.parts b) in
  lemma_parts number truth a width xs;
  lemma_parts number truth b width ys;
  lemma_bits_equivalent_typed s bc model other rho xs ys

let lemma_word_equivalent_all_typed (#base:sort -> Type0) (s:S.checked_schema)
                   (bc:S.boolean_carrier base) (model:T.scalar_model base)
                   (other:V.interpretation base (S.signature s))
                   (rho:V.environment base (S.signature s) [])
                   (project:(t:sort -> V.value base (S.signature s) t -> GTot int))
                   (a b:expr)
  : Lemma (requires B.word_equivalent_all a b /\
                    order_model (typed_number (S.signature s) (T.interpretation s bc model other) rho project)
                                (T.truth_at s bc model other [] rho) /\
                    word_reflection (S.signature s) (T.interpretation s bc model other) rho project)
          (ensures V.evaluate (S.signature s) (T.interpretation s bc model other) [] rho a ==
                   V.evaluate (S.signature s) (T.interpretation s bc model other) [] rho b) =
  let number = typed_number (S.signature s) (T.interpretation s bc model other) rho project in
  let truth = T.truth_at s bc model other [] rho in
  if B.literal_equivalent a b then (
    lemma_literal_equivalent number truth a b;
    let w, _ = Some?.v (B.word_parts a) in
    assert (get_sort a == B.bv_sort w))
  else if B.literal_equivalent b a then (
    lemma_literal_equivalent number truth b a;
    let w, _ = Some?.v (B.word_parts b) in
    assert (get_sort b == B.bv_sort w))
  else if B.word_equivalent a b then
    lemma_word_equivalent_sorted s bc model other rho project a b
  else if B.projection_equivalent a b then (
    lemma_projection_equivalent number truth a b;
    let w, _ = Some?.v (B.word_parts b) in
    assert (get_sort a == B.bv_sort w))
  else (
    lemma_projection_equivalent number truth b a;
    let w, _ = Some?.v (B.word_parts a) in
    assert (get_sort b == B.bv_sort w))

(* Primitive binary/n-ary bvadd and bvmul law for extraction distribution. *)
let arith_model (number:expr -> GTot int) : prop =
  forall (f:func_decl) (args:list expr) (w:pos) (op:decl_kind).
    D.scoped [] (App f args) /\ B.arith f args == Some (w, op) ==>
    number (App f args) == B.calculate_nary w op (expression_words number w args)

let lemma_extract_extract (z:nat) (tl w:nat) (h l:nat)
  : Lemma (requires l <= h /\ h < w)
          (ensures ((((z / pow2 tl) % pow2 w) / pow2 l) % pow2 (h - l + 1) ==
                    (z / pow2 (l + tl)) % pow2 (h - l + 1))) =
  let a = z / pow2 tl in
  M.pow2_modulo_division_lemma_1 a l w;
  M.pow2_plus tl l;
  M.division_multiplication_lemma z (pow2 tl) (pow2 l);
  M.pow2_modulo_modulo_lemma_1 (z / pow2 (l + tl)) (h - l + 1) (w - l)

#push-options "--fuel 3 --ifuel 2 --z3rlimit 60"
let lemma_extract_slice (number:expr -> GTot int) (truth:expr -> GTot bool)
                        (w:pos) (h l:nat) (x y:expr)
  : Lemma (requires word_model number truth /\ D.scoped [] x /\ D.scoped [] y /\ B.slice w h l x y)
          (ensures h < w /\ l <= h /\
                   get_sort x == B.bv_sort w /\ get_sort y == B.bv_sort (h - l + 1) /\
                   number y == (number x / pow2 l) % pow2 (h - l + 1)) =
  let s = Some?.v (B.extract_parts y) in
  lemma_extract_parts number truth y s;
  if s.source_width = w && s.high = h && s.low = l && s.operand = x then ()
  else (
    let t = Some?.v (B.extract_parts x) in
    lemma_extract_parts number truth x t;
    lemma_extract_extract (number t.operand) t.low w h l)
#pop-options

let rec low_words (k:pos) (w:pos{k <= w}) (xs:list (U.uint_t w)) (ys:list (U.uint_t k))
  : Tot bool (decreases xs) =
  match xs, ys with
  | [], [] -> true
  | x :: xs', y :: ys' -> y = x % pow2 k && low_words k w xs' ys'
  | _, _ -> false

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let rec lemma_low_words (k:pos) (w:pos{k <= w}) (op:decl_kind)
                        (xs:list (U.uint_t w)) (ys:list (U.uint_t k))
  : Lemma (requires (op = B.op_add \/ op = B.op_mul) /\ low_words k w xs ys)
          (ensures B.calculate_nary w op xs % pow2 k == B.calculate_nary k op ys)
          (decreases xs) =
  match xs, ys with
  | [], [] -> ()
  | [x], [y] -> ()
  | x :: x2 :: xs', y :: y2 :: ys' ->
    lemma_low_words k w op (x2 :: xs') (y2 :: ys');
    let c = B.calculate_nary w op (x2 :: xs') in
    if op = B.op_add then (
      M.pow2_modulo_modulo_lemma_1 (x + c) k w;
      M.lemma_mod_plus_distr_l x c (pow2 k);
      M.lemma_mod_plus_distr_r (x % pow2 k) c (pow2 k))
    else (
      M.pow2_modulo_modulo_lemma_1 (x * c) k w;
      M.lemma_mod_mul_distr_l x c (pow2 k);
      M.lemma_mod_mul_distr_r (x % pow2 k) c (pow2 k))
  | _, _ -> ()
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let rec lemma_extract_slices (number:expr -> GTot int) (truth:expr -> GTot bool)
                     (w:pos) (h:nat) (xs ys:list expr)
  : Lemma (requires word_model number truth /\ h < w /\
                    D.scoped_args [] xs /\ D.scoped_args [] ys /\ B.slices w h xs ys)
          (ensures low_words (h + 1) w (expression_words number w xs)
                                       (expression_words number (h + 1) ys))
          (decreases xs) =
  match xs, ys with
  | x :: xs', y :: ys' ->
    lemma_extract_slice number truth w h 0 x y;
    assert_norm (pow2 0 == 1);
    M.small_mod (number x) (pow2 w);
    M.small_mod (number y) (pow2 (h + 1));
    lemma_extract_slices number truth w h xs' ys'
  | _, _ -> ()
#pop-options

#push-options "--fuel 3 --ifuel 2 --z3rlimit 80"
let lemma_extract_distribute (number:expr -> GTot int) (truth:expr -> GTot bool) (a b:expr)
  : Lemma (requires word_model number truth /\ arith_model number /\
                    D.scoped [] a /\ D.scoped [] b /\ B.distribute a b)
          (ensures get_sort a == get_sort b /\ number a == number b) =
  let s = Some?.v (B.extract_parts a) in
  lemma_extract_parts number truth a s;
  match s.operand, b with
  | App f xs, App g ys ->
    let w, op = Some?.v (B.arith f xs) in
    let k = s.high + 1 in
    lemma_extract_slices number truth w s.high xs ys;
    lemma_low_words k w op (expression_words number w xs) (expression_words number k ys);
    assert_norm (pow2 0 == 1)
  | _, _ -> ()
#pop-options

#push-options "--fuel 3 --ifuel 2 --z3rlimit 60"
let lemma_extract_conditional (number:expr -> GTot int) (truth:expr -> GTot bool) (a b:expr)
  : Lemma (requires word_model number truth /\ choice_model number truth /\
                    D.scoped [] a /\ D.scoped [] b /\ B.conditional a b)
          (ensures get_sort a == get_sort b /\ number a == number b) =
  let s = Some?.v (B.extract_parts a) in
  let c, t, e = Some?.v (B.ite_parts s.operand) in
  let _, t', e' = Some?.v (B.ite_parts b) in
  lemma_extract_parts number truth a s;
  lemma_ite_parts s.operand c t e;
  lemma_ite_parts b c t' e';
  lemma_extract_slice number truth s.source_width s.high s.low t t';
  lemma_extract_slice number truth s.source_width s.high s.low e e'
#pop-options

let lemma_extract_concat_low (n:pos) (x y:nat) (h l:nat)
  : Lemma (requires l <= h /\ h < n)
          (ensures ((x * pow2 n + y) / pow2 l) % pow2 (h - l + 1) ==
                   (y / pow2 l) % pow2 (h - l + 1)) =
  let k = h + 1 in
  let v = x * pow2 n + y in
  let c = x * pow2 (n - k) in
  M.pow2_plus (n - k) k;
  assert (pow2 (n - k) * pow2 k == pow2 n);
  M.paren_mul_right x (pow2 (n - k)) (pow2 k);
  assert (v == y + c * pow2 k);
  M.lemma_mod_plus y c (pow2 k);
  assert (v % pow2 k == y % pow2 k);
  M.pow2_modulo_division_lemma_1 v l k;
  M.pow2_modulo_division_lemma_1 y l k;
  assert (k - l == h - l + 1)

let lemma_extract_concat_high (n:pos) (x y:nat) (h l:nat)
  : Lemma (requires y < pow2 n /\ n <= l /\ l <= h)
          (ensures ((x * pow2 n + y) / pow2 l) % pow2 (h - l + 1) ==
                   (x / pow2 (l - n)) % pow2 (h - l + 1)) =
  let v = x * pow2 n + y in
  M.lemma_div_plus y x (pow2 n);
  M.small_div y (pow2 n);
  assert (v == y + x * pow2 n);
  assert (v / pow2 n == x);
  M.pow2_plus n (l - n);
  assert (pow2 n * pow2 (l - n) == pow2 l);
  M.division_multiplication_lemma v (pow2 n) (pow2 (l - n))

let lemma_extract_shift_concat (j l:nat) (x y:nat)
  : Lemma (ensures (x * pow2 (j + l) + y) / pow2 l == x * pow2 j + y / pow2 l) =
  M.pow2_plus j l;
  M.paren_mul_right x (pow2 j) (pow2 l);
  assert (x * pow2 (j + l) + y == y + (x * pow2 j) * pow2 l);
  M.lemma_div_plus y (x * pow2 j) (pow2 l)

let lemma_extract_low_concat (wx wy:pos) (x q:nat)
  : Lemma (requires q < pow2 wy)
          (ensures (x * pow2 wy + q) % pow2 (wx + wy) == (x % pow2 wx) * pow2 wy + q) =
  let p = x % pow2 wx in
  M.pow2_multiplication_modulo_lemma_2 x (wx + wy) wy;
  assert ((x * pow2 wy) % pow2 (wx + wy) == p * pow2 wy);
  M.lemma_mod_plus_distr_l (x * pow2 wy) q (pow2 (wx + wy));
  M.lemma_mod_lt x (pow2 wx);
  M.lemma_mult_le_right (pow2 wy) p (pow2 wx - 1);
  M.distributivity_sub_left (pow2 wx) 1 (pow2 wy);
  M.pow2_plus wx wy;
  M.small_mod (p * pow2 wy + q) (pow2 (wx + wy))

let lemma_extract_concat_across (n:pos) (wx wy:pos) (x y:nat) (h l:nat)
  : Lemma (requires y < pow2 n /\ l < n /\ n <= h /\ wx = h - n + 1 /\ wy = n - l)
          (ensures ((x * pow2 n + y) / pow2 l) % pow2 (wx + wy) ==
                   ((x / pow2 0) % pow2 wx) * pow2 wy + (y / pow2 l) % pow2 wy) =
  assert_norm (pow2 0 == 1);
  lemma_extract_shift_concat wy l x y;
  M.lemma_div_lt_nat y n l;
  M.small_mod (y / pow2 l) (pow2 wy);
  lemma_extract_low_concat wx wy x (y / pow2 l)

#push-options "--fuel 3 --ifuel 2 --z3rlimit 60"
let lemma_extract_piece (number:expr -> GTot int) (truth:expr -> GTot bool)
                        (w k:pos) (h l:nat) (x y:expr)
  : Lemma (requires word_model number truth /\ D.scoped [] x /\ D.scoped [] y /\
                    get_sort x == B.bv_sort w /\ k = h - l + 1 /\ B.piece w h l x y)
          (ensures h < w /\ get_sort y == B.bv_sort k /\
                   number y == (number x / pow2 l) % pow2 k) =
  if l = 0 && h + 1 = w && y = x then (
    assert_norm (pow2 0 == 1);
    M.small_mod (number x) (pow2 w))
  else lemma_extract_slice number truth w h l x y
#pop-options

#push-options "--fuel 3 --ifuel 2 --z3rlimit 100"
let lemma_extract_concatenated (number:expr -> GTot int) (truth:expr -> GTot bool) (a b:expr)
  : Lemma (requires word_model number truth /\ D.scoped [] a /\ D.scoped [] b /\ B.concatenated a b)
          (ensures get_sort a == get_sort b /\ number a == number b) =
  let s = Some?.v (B.extract_parts a) in
  lemma_extract_parts number truth a s;
  let c = Some?.v (B.concat_parts s.operand) in
  lemma_concat_parts number truth s.operand c;
  let m = c.left_width in
  let n = c.right_width in
  let k = s.high - s.low + 1 in
  let x = number c.left in
  let y = number c.right in
  if s.high < n then (
    lemma_extract_piece number truth n k s.high s.low c.right b;
    lemma_extract_concat_low n x y s.high s.low)
  else if n <= s.low then (
    lemma_extract_piece number truth m k (s.high - n) (s.low - n) c.left b;
    lemma_extract_concat_high n x y s.high s.low)
  else (
    let d = Some?.v (B.concat_parts b) in
    lemma_concat_parts number truth b d;
    lemma_extract_piece number truth m d.left_width (s.high - n) 0 c.left d.left;
    lemma_extract_piece number truth n d.right_width (n - 1) s.low c.right d.right;
    assert (d.left_width + d.right_width == k);
    assert (get_sort a == B.bv_sort k /\ get_sort b == B.bv_sort k);
    lemma_extract_concat_across n d.left_width d.right_width x y s.high s.low;
    assert (number b == (x / pow2 0 % pow2 d.left_width) * pow2 d.right_width +
                        y / pow2 s.low % pow2 d.right_width);
    assert (number a == (x * pow2 n + y) / pow2 s.low % pow2 k))
#pop-options

let lemma_extract_check_typed (#base:sort -> Type0) (sigma:V.signature)
                    (i:V.interpretation base sigma) (rho:V.environment base sigma [])
                    (project:(s:sort -> V.value base sigma s -> GTot int))
                    (bproject:(s:sort -> V.value base sigma s -> GTot bool)) (a b:expr)
  : Lemma (requires B.extract_check a b /\
                    word_model (typed_number sigma i rho project) (typed_truth sigma i rho bproject) /\
                    arith_model (typed_number sigma i rho project) /\
                    choice_model (typed_number sigma i rho project) (typed_truth sigma i rho bproject) /\
                    word_reflection sigma i rho project)
          (ensures V.evaluate sigma i [] rho a == V.evaluate sigma i [] rho b) =
  let number = typed_number sigma i rho project in
  let truth = typed_truth sigma i rho bproject in
  if B.distribute a b then lemma_extract_distribute number truth a b
  else if B.conditional a b then lemma_extract_conditional number truth a b
  else lemma_extract_concatenated number truth a b;
  let s = Some?.v (B.extract_parts a) in
  assert (get_sort a == B.bv_sort (s.high - s.low + 1))

(* The exhaustive evaluator needs only primitive ground Boolean, equality,
   zero-extension and BV operator laws.  It does not assume anything about
   the evaluator or its acceptance predicate. *)
let rec truth_any (truth:expr -> GTot bool) (args:list expr) : GTot bool (decreases args) =
  match args with [] -> false | e :: rest -> truth e || truth_any truth rest

let exhaustive_model (number:expr -> GTot int) (truth:expr -> GTot bool) : prop =
  word_model number truth /\
  (forall (e:expr) (z:B.zero_extension).
    D.scoped [] e /\ B.zero_extend_parts e == Some z ==> number e == number z.argument) /\
  (forall (f:func_decl). C.canonical_true f ==> truth (App f [])) /\
  (forall (f:func_decl). C.canonical_false f ==> not (truth (App f []))) /\
  (forall (f:func_decl) (a:expr).
    D.scoped [] (App f [a]) /\ C.canonical_not f ==> truth (App f [a]) == not (truth a)) /\
  (forall (f:func_decl) (args:list expr).
    D.scoped [] (App f args) /\ C.canonical_and f ==> truth (App f args) == truth_all truth args) /\
  (forall (f:func_decl) (args:list expr).
    D.scoped [] (App f args) /\ C.canonical_or f ==> truth (App f args) == truth_any truth args) /\
  (forall (f:func_decl) (a b:expr).
    D.scoped [] (App f [a; b]) /\ C.canonical_eq f /\ get_sort a == bool_sort ==>
    truth (App f [a; b]) == (truth a = truth b)) /\
  (forall (f:func_decl) (a b:expr) (w:pos).
    D.scoped [] (App f [a; b]) /\ C.canonical_eq f /\
    get_sort a == B.bv_sort w /\ get_sort b == B.bv_sort w ==>
    truth (App f [a; b]) == (number a = number b)) /\
  (forall (e:expr) (c:B.unsigned_comparison).
    D.scoped [] e /\ B.unsigned_parts e == Some c ==>
    truth e == B.unsigned_value c.relation (number c.lhs) (number c.rhs))

let rec exhaustive_total_bits (tbl:B.leaf_table) : Tot nat (decreases tbl) =
  match tbl with [] -> 0 | (_, w) :: rest -> w + exhaustive_total_bits rest

let rec lemma_exhaustive_within_bits (tbl:B.leaf_table) (acc:nat)
  : Lemma (requires B.within_bits tbl acc)
          (ensures acc + exhaustive_total_bits tbl <= B.max_leaf_bits)
          (decreases tbl) =
  match tbl with [] -> () | (_, w) :: rest -> lemma_exhaustive_within_bits rest (acc + w)

let rec lemma_exhaustive_index (x:expr & pos) (tbl:B.leaf_table) (k:nat)
  : Lemma (requires B.index_of x tbl == Some k)
          (ensures k < L.length tbl /\ L.index tbl k == x)
          (decreases tbl) =
  match tbl with
  | y :: rest -> if y = x then () else
    (match B.index_of x rest with Some j -> lemma_exhaustive_index x rest j | None -> ())
  | [] -> ()

let rec exhaustive_in_range (ws:list pos) (r:list int) : Tot bool (decreases ws) =
  match ws, r with
  | [], [] -> true
  | w :: ws', x :: r' -> 0 <= x && x < pow2 w && exhaustive_in_range ws' r'
  | _, _ -> false

let rec lemma_exhaustive_vectors (ws:list pos) (f:list int -> bool) (r:list int)
  : Lemma (requires B.for_all_vectors ws f /\ exhaustive_in_range ws r)
          (ensures f r)
          (decreases %[ws; 0; 0]) =
  match ws, r with
  | [], [] -> ()
  | w :: rest, x :: r' -> lemma_exhaustive_heads rest (pow2 w) f x r'
  | _, _ -> ()

and lemma_exhaustive_heads (rest:list pos) (k:nat) (f:list int -> bool) (x:int) (r':list int)
  : Lemma (requires B.for_all_heads rest k f /\ 0 <= x /\ x < k /\ exhaustive_in_range rest r')
          (ensures f (x :: r'))
          (decreases %[rest; 1; k]) =
  if x = k - 1 then lemma_exhaustive_vectors rest (B.with_head f (k - 1)) r'
  else lemma_exhaustive_heads rest (k - 1) f x r'

let exhaustive_agrees (number:expr -> GTot int) (tbl:B.leaf_table) (v:nat -> int) : prop =
  forall (k:nat). k < L.length tbl ==> v k == number (fst (L.index tbl k))

let lemma_exhaustive_leaf (number:expr -> GTot int) (tbl:B.leaf_table)
                          (v:nat -> int) (w:pos) (e:expr)
  : Lemma (requires exhaustive_agrees number tbl v /\ Some? (B.leaf tbl v w e))
          (ensures get_sort e == B.bv_sort w /\ number e == Some?.v (B.leaf tbl v w e)) =
  let k = Some?.v (B.index_of (e, w) tbl) in
  lemma_exhaustive_index (e, w) tbl k

let lemma_exhaustive_bv_add_shape (tbl:B.leaf_table) (v:nat -> int)
                                 (w:pos) (f:func_decl) (x y:expr)
  : Lemma (requires None? (B.numeral (App f [x; y])) /\ None? (B.concat_parts (App f [x; y])) /\
                    B.operation f [x; y] == Some (w, B.op_add) /\ Some? (B.eval_bv tbl v w (App f [x; y])))
          (ensures Some? (B.eval_bv tbl v w x) /\ Some? (B.eval_bv tbl v w y) /\
                   Some?.v (B.eval_bv tbl v w (App f [x; y])) ==
                     (Some?.v (B.eval_bv tbl v w x) + Some?.v (B.eval_bv tbl v w y)) % pow2 w) = ()

let lemma_exhaustive_bv_concat_shape (tbl:B.leaf_table) (v:nat -> int) (w:pos)
                                    (f:func_decl) (x y:expr) (c:B.concatenation)
  : Lemma (requires None? (B.numeral (App f [x; y])) /\ B.concat_parts (App f [x; y]) == Some c /\
                    Some? (B.eval_bv tbl v w (App f [x; y])))
          (ensures c.left == x /\ c.right == y /\ c.left_width + c.right_width == w /\
                   Some? (B.eval_bv tbl v c.left_width x) /\ Some? (B.eval_bv tbl v c.right_width y) /\
                   Some?.v (B.eval_bv tbl v w (App f [x; y])) ==
                   Some?.v (B.eval_bv tbl v c.left_width x) * pow2 c.right_width +
                   Some?.v (B.eval_bv tbl v c.right_width y)) = ()

let lemma_exhaustive_bv_other_shape (tbl:B.leaf_table) (v:nat -> int) (w:pos) (e:expr)
  : Lemma (requires None? (B.numeral e) /\ (match e with App _ [_] | App _ [_; _] -> False | _ -> True))
          (ensures B.eval_bv tbl v w e == B.leaf tbl v w e) = ()

#push-options "--fuel 3 --ifuel 2 --z3rlimit 60"
let rec lemma_exhaustive_eval_bv (number:expr -> GTot int) (truth:expr -> GTot bool)
                      (tbl:B.leaf_table) (v:nat -> int) (w:pos) (e:expr)
  : Lemma (requires exhaustive_model number truth /\ D.scoped [] e /\
                    exhaustive_agrees number tbl v /\ Some? (B.eval_bv tbl v w e))
          (ensures get_sort e == B.bv_sort w /\ number e == Some?.v (B.eval_bv tbl v w e))
          (decreases e) =
  match B.numeral e with
  | Some (q, n) -> lemma_numeral_parts number truth e q n
  | None ->
    (match e with
     | App f [x] ->
       (match B.extract_parts e, B.zero_extend_parts e with
        | Some (s:B.extraction), _ ->
          lemma_extract_parts number truth e s;
          lemma_exhaustive_eval_bv number truth tbl v s.source_width x
        | None, Some (z:B.zero_extension) ->
          assert (z.argument == x);
          assert (number e == number z.argument);
          lemma_exhaustive_eval_bv number truth tbl v z.input_width x
        | None, None -> lemma_exhaustive_leaf number tbl v w e)
     | App f [x; y] ->
       (match B.concat_parts e, B.operation f [x; y] with
        | Some (c:B.concatenation), _ ->
          lemma_exhaustive_bv_concat_shape tbl v w f x y c;
          lemma_concat_parts number truth e c;
          lemma_exhaustive_eval_bv number truth tbl v c.left_width x;
          lemma_exhaustive_eval_bv number truth tbl v c.right_width y
        | None, Some (q, op) ->
          if q = w && op = B.op_add then (
            lemma_exhaustive_bv_add_shape tbl v w f x y;
            lemma_exhaustive_eval_bv number truth tbl v w x;
            lemma_exhaustive_eval_bv number truth tbl v w y;
            assert (B.add_width f [x; y] == Some w);
            assert (value_sum number [x; y] == number x + number y))
          else lemma_exhaustive_leaf number tbl v w e
        | None, None -> lemma_exhaustive_leaf number tbl v w e)
     | _ -> lemma_exhaustive_bv_other_shape tbl v w e; lemma_exhaustive_leaf number tbl v w e)
#pop-options

#push-options "--fuel 3 --ifuel 2 --z3rlimit 80"
let rec lemma_exhaustive_eval_bool (number:expr -> GTot int) (truth:expr -> GTot bool)
                        (tbl:B.leaf_table) (v:nat -> int) (e:expr)
  : Lemma (requires exhaustive_model number truth /\ D.scoped [] e /\
                    exhaustive_agrees number tbl v /\ Some? (B.eval_bool tbl v e))
          (ensures get_sort e == bool_sort /\ truth e == Some?.v (B.eval_bool tbl v e))
          (decreases e) =
  match e with
  | App f args ->
    if C.canonical_true f && args = [] then ()
    else if C.canonical_false f && args = [] then ()
    else if C.canonical_not f then
      (match args with
       | [a] -> lemma_exhaustive_eval_bool number truth tbl v a
       | _ -> ())
    else if C.canonical_or f then lemma_exhaustive_eval_or number truth tbl v args
    else if C.canonical_and f then lemma_exhaustive_eval_and number truth tbl v args
    else if C.canonical_eq f then
      (match args with
       | [a; b] ->
         if B.boolean_pair a b then (
           lemma_exhaustive_eval_bool number truth tbl v a;
           lemma_exhaustive_eval_bool number truth tbl v b)
         else (
           let w = Some?.v (B.equal_width a b) in
           lemma_exhaustive_eval_bv number truth tbl v w a;
           lemma_exhaustive_eval_bv number truth tbl v w b)
       | _ -> ())
    else
      (match args with
       | [a; b] ->
         let c = Some?.v (B.unsigned_parts e) in
         assert (c.B.lhs == a /\ c.B.rhs == b);
         lemma_exhaustive_eval_bv number truth tbl v c.B.width a;
         lemma_exhaustive_eval_bv number truth tbl v c.B.width b
       | _ -> ())
  | _ -> ()

and lemma_exhaustive_eval_or (number:expr -> GTot int) (truth:expr -> GTot bool)
                  (tbl:B.leaf_table) (v:nat -> int) (args:list expr)
  : Lemma (requires exhaustive_model number truth /\ D.scoped_args [] args /\
                    exhaustive_agrees number tbl v /\ Some? (B.eval_or tbl v args))
          (ensures truth_any truth args == Some?.v (B.eval_or tbl v args))
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_exhaustive_eval_bool number truth tbl v a;
    lemma_exhaustive_eval_or number truth tbl v rest

and lemma_exhaustive_eval_and (number:expr -> GTot int) (truth:expr -> GTot bool)
                   (tbl:B.leaf_table) (v:nat -> int) (args:list expr)
  : Lemma (requires exhaustive_model number truth /\ D.scoped_args [] args /\
                    exhaustive_agrees number tbl v /\ Some? (B.eval_and tbl v args))
          (ensures truth_all truth args == Some?.v (B.eval_and tbl v args))
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_exhaustive_eval_bool number truth tbl v a;
    lemma_exhaustive_eval_and number truth tbl v rest
#pop-options

let rec exhaustive_actual (number:expr -> GTot int) (tbl:B.leaf_table)
  : GTot (list int) (decreases tbl) =
  match tbl with [] -> [] | (e, _) :: rest -> number e :: exhaustive_actual number rest

let rec lemma_exhaustive_actual_length (number:expr -> GTot int) (tbl:B.leaf_table)
  : Lemma (ensures L.length (exhaustive_actual number tbl) == L.length tbl) (decreases tbl) =
  match tbl with [] -> () | _ :: rest -> lemma_exhaustive_actual_length number rest

let rec lemma_exhaustive_actual_index (number:expr -> GTot int) (tbl:B.leaf_table) (k:nat)
  : Lemma (requires k < L.length tbl)
          (ensures L.length (exhaustive_actual number tbl) == L.length tbl /\
                   L.index (exhaustive_actual number tbl) k == number (fst (L.index tbl k)))
          (decreases tbl) =
  lemma_exhaustive_actual_length number tbl;
  match tbl with [] -> () | _ :: rest -> if k = 0 then () else lemma_exhaustive_actual_index number rest (k - 1)

let rec lemma_exhaustive_actual_range (number:expr -> GTot int) (tbl:B.leaf_table)
  : Lemma (requires range_model number /\ L.for_all B.closed_leaf tbl)
          (ensures exhaustive_in_range (B.widths tbl) (exhaustive_actual number tbl))
          (decreases tbl) =
  match tbl with
  | [] -> ()
  | (e, w) :: rest -> lemma_exhaustive_actual_range number rest

let lemma_exhaustive_actual_agrees (number:expr -> GTot int) (tbl:B.leaf_table)
  : Lemma (exhaustive_agrees number tbl (B.vector_value (exhaustive_actual number tbl))) =
  let aux (k:nat)
    : Lemma (k < L.length tbl ==>
             B.vector_value (exhaustive_actual number tbl) k == number (fst (L.index tbl k))) =
    if k < L.length tbl then lemma_exhaustive_actual_index number tbl k in
  FStar.Classical.forall_intro aux

let lemma_exhaustive_valid (number:expr -> GTot int) (truth:expr -> GTot bool) (e:expr)
  : Lemma (requires exhaustive_model number truth /\ B.exhaustive_valid e)
          (ensures D.scoped [] e /\ get_sort e == bool_sort /\ truth e) =
  let tbl = B.leaves_bool [] e in
  let r = exhaustive_actual number tbl in
  lemma_exhaustive_actual_range number tbl;
  lemma_exhaustive_vectors (B.widths tbl) (B.clause_true tbl e) r;
  lemma_exhaustive_actual_agrees number tbl;
  lemma_exhaustive_eval_bool number truth tbl (B.vector_value r) e

let lemma_exhaustive_valid_typed (#base:sort -> Type0) (sigma:V.signature)
                    (i:V.interpretation base sigma) (rho:V.environment base sigma [])
                    (project:(s:sort -> V.value base sigma s -> GTot int))
                    (bproject:(s:sort -> V.value base sigma s -> GTot bool)) (e:expr)
  : Lemma (requires B.exhaustive_valid e /\
                    exhaustive_model (typed_number sigma i rho project) (typed_truth sigma i rho bproject))
          (ensures D.scoped [] e /\ get_sort e == bool_sort /\
                   bproject (get_sort e) (V.evaluate sigma i [] rho e)) =
  lemma_exhaustive_valid (typed_number sigma i rho project) (typed_truth sigma i rho bproject) e

let lemma_exhaustive_valid_sorted (#base:sort -> Type0) (s:S.checked_schema)
                   (bc:S.boolean_carrier base) (model:T.scalar_model base)
                   (other:V.interpretation base (S.signature s))
                   (rho:V.environment base (S.signature s) [])
                   (project:(t:sort -> V.value base (S.signature s) t -> GTot int)) (e:expr)
  : Lemma (requires B.exhaustive_valid e /\
                    exhaustive_model
                      (typed_number (S.signature s) (T.interpretation s bc model other) rho project)
                      (T.truth_at s bc model other [] rho))
          (ensures D.scoped [] e /\ get_sort e == bool_sort /\
                   V.evaluate (S.signature s) (T.interpretation s bc model other) [] rho e ==
                   T.boolean s bc true) =
  lemma_exhaustive_valid
    (typed_number (S.signature s) (T.interpretation s bc model other) rho project)
    (T.truth_at s bc model other [] rho) e;
  T.lemma_boolean s bc (V.evaluate (S.signature s) (T.interpretation s bc model other) [] rho e)

let lemma_exhaustive_equivalent_typed (#base:sort -> Type0) (s:S.checked_schema)
                   (bc:S.boolean_carrier base) (model:T.scalar_model base)
                   (other:V.interpretation base (S.signature s))
                   (rho:V.environment base (S.signature s) [])
                   (project:(t:sort -> V.value base (S.signature s) t -> GTot int))
                   (a b:expr)
  : Lemma (requires B.exhaustive_equivalent a b /\
                    exhaustive_model
                      (typed_number (S.signature s) (T.interpretation s bc model other) rho project)
                      (T.truth_at s bc model other [] rho))
          (ensures D.scoped [] a /\ D.scoped [] b /\ get_sort a == get_sort b /\
                   V.evaluate (S.signature s) (T.interpretation s bc model other) [] rho a ==
                   V.evaluate (S.signature s) (T.interpretation s bc model other) [] rho b) =
  lemma_exhaustive_valid
    (typed_number (S.signature s) (T.interpretation s bc model other) rho project)
    (T.truth_at s bc model other [] rho) (R.mk_eq_expr a b);
  T.lemma_equality_at s bc model other [] rho a b
