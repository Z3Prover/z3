module Z3BvWord

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open FStar.List.Tot
module BV = Z3BvLemma
module B = Z3BooleanRewrite
module SM = Z3ScopedModel
module D = Z3Definitions
module L = FStar.List.Tot
module M = FStar.Math.Lemmas
module U = FStar.UInt

let rec lemma_number_bounds (bs:list bool)
  : Lemma (BV.bits_number bs < pow2 (L.length bs)) (decreases bs)
  = match bs with
    | [] -> ()
    | _ :: rest ->
      lemma_number_bounds rest;
      M.pow2_plus 1 (L.length rest)

let rec lemma_number_equal (xs ys:list bool)
  : Lemma (requires L.length xs == L.length ys)
          (ensures (BV.bits_number xs == BV.bits_number ys) <==> xs == ys)
          (decreases xs)
  = match xs, ys with
    | [], [] -> ()
    | a :: rest, b :: tail ->
      lemma_number_equal rest tail;
      let x = if a then 1 else 0 in
      let y = if b then 1 else 0 in
      M.lemma_mod_plus x (BV.bits_number rest) 2;
      M.lemma_mod_plus y (BV.bits_number tail) 2;
      M.small_mod x 2;
      M.small_mod y 2
    | _, _ -> ()

let rec numeral_bits (width:nat) (n:nat) : Tot (list expr) (decreases width) =
  if width = 0 then []
  else (if n % 2 = 0 then false_expr else true_expr) :: numeral_bits (width - 1) (n / 2)

let rec lemma_numeral_bits (i:interpretation value) (rho:env value) (width:nat) (n:nat)
  : Lemma (requires SM.literal_model i /\ n < pow2 width)
          (ensures L.length (numeral_bits width n) == width /\
                   D.scoped_args [] (numeral_bits width n) /\
                   L.for_all (fun e -> get_sort e = bool_sort) (numeral_bits width n) /\
                   BV.bits_number (BV.bit_values i rho (numeral_bits width n)) == n)
          (decreases width)
  = if width = 0 then ()
    else (
      M.pow2_plus 1 (width - 1);
      lemma_numeral_bits i rho (width - 1) (n / 2);
      M.lemma_div_mod n 2;
      assert (n % 2 = 0 \/ n % 2 = 1))

let parts (e:expr) : option (pos & list expr) =
  match BV.word_parts e with
  | Some p -> Some p
  | None ->
    (match BV.numeral e with
     | Some (width, n) -> Some (width, numeral_bits width n)
     | None -> None)

let lemma_parts (i:interpretation value) (rho:env value)
                (project:pos -> value -> int) (e:expr) (width:pos) (args:list expr)
  : Lemma (requires BV.bv_model i project /\ SM.literal_model i /\
                    D.scoped [] e /\ parts e == Some (width, args))
          (ensures width <= 4096 /\ L.length args == width /\
                   D.scoped_args [] args /\
                   L.for_all (fun a -> get_sort a = bool_sort) args /\
                   get_sort e == BV.bv_sort width /\
                   project width (eval i e rho) == BV.bits_number (BV.bit_values i rho args))
  = if Some? (BV.word_parts e) then
      (match e with App _ _ -> () | _ -> ())
    else (
      let _, n = Some?.v (BV.numeral e) in
      lemma_numeral_bits i rho width n)

let word (args:list expr) : expr =
  App { decl_name = "mkbv"; domain = L.map (fun _ -> bool_sort) args;
        range = BV.bv_sort (L.length args); interp = Some BV.op_mkbv;
        int_params = [L.length args] } args

let rec constant_bits (args:list expr) : Tot (option (list bool)) (decreases args) =
  match args with
  | [] -> Some []
  | a :: rest ->
    if a <> true_expr && a <> false_expr then None
    else (match constant_bits rest with
      | Some bs -> Some ((a = true_expr) :: bs)
      | None -> None)

let rec lemma_constant_bits (i:interpretation value) (rho:env value)
                            (args:list expr) (bs:list bool)
  : Lemma (requires SM.literal_model i /\ constant_bits args == Some bs)
          (ensures BV.bit_values i rho args == bs)
          (decreases args)
  = match args with
    | [] -> ()
    | _ :: rest -> lemma_constant_bits i rho rest (Some?.v (constant_bits rest))

let rec bit_equalities (xs ys:list expr) : Tot (list expr) (decreases xs) =
  match xs, ys with
  | x :: rest, y :: tail -> mk_eq_expr x y :: bit_equalities rest tail
  | _, _ -> []

let rec lemma_bit_equalities (i:interpretation value) (rho:env value) (xs ys:list expr)
  : Lemma (requires B.boolean_rewrite_model i /\ L.length xs == L.length ys /\
                    L.for_all (fun x -> get_sort x = bool_sort) xs /\
                    L.for_all (fun x -> get_sort x = bool_sort) ys)
          (ensures (conj_holds i rho (bit_equalities xs ys) <==>
                    BV.bit_values i rho xs == BV.bit_values i rho ys))
          (decreases xs)
  = match xs, ys with
    | x :: rest, y :: tail ->
      lemma_bit_equalities i rho rest tail;
      (match eval i x rho, eval i y rho with VBool _, VBool _ -> () | _, _ -> ())
    | _, _ -> ()

let equality_rewrite (e:expr) : option expr =
  match e with
  | App f [a; b] ->
    if f <> eq_decl (get_sort a) || get_sort a <> get_sort b then None
    else (match parts a, parts b with
      | Some (w, xs), Some (w', ys) ->
        if w <> w' then None
        else let eqs = bit_equalities xs ys in
          Some (App (B.connective_decl B.Conjunction eqs) eqs)
      | _, _ -> None)
  | _ -> None

let lemma_equality_rewrite (i:interpretation value) (rho:env value)
                           (project:pos -> value -> int) (e result:expr)
  : Lemma (requires BV.bv_model i project /\ B.boolean_rewrite_model i /\
                    D.scoped [] e /\ equality_rewrite e == Some result)
          (ensures eval i e rho == eval i result rho)
  = match e with
    | App f [a; b] ->
      let width, xs = Some?.v (parts a) in
      let _, ys = Some?.v (parts b) in
      lemma_parts i rho project a width xs;
      lemma_parts i rho project b width ys;
      lemma_number_equal (BV.bit_values i rho xs) (BV.bit_values i rho ys);
      lemma_bit_equalities i rho xs ys;
      assert ((eval i a rho == eval i b rho) <==>
        project width (eval i a rho) == project width (eval i b rho));
      assert (lit_true i rho result <==>
        conj_holds i rho (bit_equalities xs ys));
      assert (lit_true i rho e <==> lit_true i rho result);
      (match eval i e rho, eval i result rho with VBool _, VBool _ -> () | _, _ -> ())
    | _ -> ()

let literal_equivalent (a b:expr) : bool =
  match BV.word_parts a, BV.numeral b with
  | Some (w, args), Some (w', n) ->
    w = w' && (match constant_bits args with Some bs -> BV.bits_number bs = n | None -> false)
  | _, _ -> false

let lemma_literal_equivalent (i:interpretation value) (rho:env value)
                             (project:pos -> value -> int) (a b:expr)
  : Lemma (requires BV.bv_model i project /\ B.boolean_rewrite_model i /\
                    D.scoped [] a /\ D.scoped [] b /\ literal_equivalent a b)
          (ensures eval i a rho == eval i b rho)
  = let width, args = Some?.v (BV.word_parts a) in
    lemma_parts i rho project a width args;
    lemma_constant_bits i rho args (Some?.v (constant_bits args));
    BV.lemma_reflect i rho project width a b

let rec lemma_boolean_args (args:list expr)
  : Lemma (requires L.for_all (fun a -> get_sort a = bool_sort) args)
          (ensures sorts_match args (L.map (fun _ -> bool_sort) args))
          (decreases args)
  = match args with [] -> () | _ :: rest -> lemma_boolean_args rest

let lemma_word_shape (args:list expr)
  : Lemma (requires L.length args > 0 /\ L.length args <= 4096 /\
                    D.scoped_args [] args /\ L.for_all (fun a -> get_sort a = bool_sort) args)
          (ensures D.scoped [] (word args) /\
                   BV.word_parts (word args) == Some (L.length args, args) /\
                   get_sort (word args) == BV.bv_sort (L.length args))
  = lemma_boolean_args args

let rec lemma_split_shape (n:nat) (args:list expr)
  : Lemma (requires n <= L.length args /\ D.scoped_args [] args /\
                    L.for_all (fun a -> get_sort a = bool_sort) args)
          (ensures (let a, b = L.splitAt n args in
                    L.length a == n /\ L.length b == L.length args - n /\
                    D.scoped_args [] a /\ D.scoped_args [] b /\
                    L.for_all (fun e -> get_sort e = bool_sort) a /\
                    L.for_all (fun e -> get_sort e = bool_sort) b))
          (decreases n)
  = if n = 0 then ()
    else match args with _ :: rest -> lemma_split_shape (n - 1) rest | [] -> ()

let rec lemma_split_values (i:interpretation value) (rho:env value) (n:nat) (args:list expr)
  : Lemma (requires n <= L.length args)
          (ensures (let a, b = L.splitAt n args in
                    L.splitAt n (BV.bit_values i rho args) ==
                      (BV.bit_values i rho a, BV.bit_values i rho b)))
          (decreases n)
  = if n = 0 then ()
    else match args with _ :: rest -> lemma_split_values i rho (n - 1) rest | [] -> ()

let rec lemma_split_number (n:nat) (bs:list bool)
  : Lemma (requires n <= L.length bs)
          (ensures (let a, b = L.splitAt n bs in
                    BV.bits_number bs == BV.bits_number a + pow2 n * BV.bits_number b))
          (decreases n)
  = if n = 0 then ()
    else match bs with
      | _ :: rest ->
        lemma_split_number (n - 1) rest;
        M.pow2_plus 1 (n - 1);
        let a, b = L.splitAt (n - 1) rest in
        assert (pow2 n == 2 * pow2 (n - 1));
        assert (2 * BV.bits_number rest ==
                2 * BV.bits_number a + pow2 n * BV.bits_number b)
      | [] -> ()

let extract_rewrite (e:expr) : option expr =
  match BV.extract_parts e with
  | Some s ->
    (match parts s.operand with
     | Some (width, args) ->
       if width <> s.source_width || s.high >= L.length args then None
       else let _, tail = L.splitAt s.low args in
         Some (word (fst (L.splitAt (s.high - s.low + 1) tail)))
     | None -> None)
  | None -> None

let lemma_split_divmod (n:nat) (bs:list bool)
  : Lemma (requires n <= L.length bs)
          (ensures (let a, b = L.splitAt n bs in
                    BV.bits_number bs / pow2 n == BV.bits_number b /\
                    BV.bits_number bs % pow2 n == BV.bits_number a))
  = let a, b = L.splitAt n bs in
    lemma_split_number n bs;
    let rec lengths (n:nat) (bs:list bool)
      : Lemma (requires n <= L.length bs)
              (ensures L.length (fst (L.splitAt n bs)) == n)
              (decreases n)
      = if n = 0 then ()
        else match bs with _ :: rest -> lengths (n - 1) rest | [] -> () in
    lengths n bs;
    lemma_number_bounds a;
    assert (L.length a == n);
    assert (BV.bits_number bs == BV.bits_number a + BV.bits_number b * pow2 n);
    M.lemma_div_plus (BV.bits_number a) (BV.bits_number b) (pow2 n);
    M.small_div (BV.bits_number a) (pow2 n);
    M.lemma_mod_plus (BV.bits_number a) (BV.bits_number b) (pow2 n);
    M.small_mod (BV.bits_number a) (pow2 n)

let lemma_extract_rewrite (i:interpretation value) (rho:env value)
                          (project:pos -> value -> int) (e result:expr)
  : Lemma (requires BV.bv_model i project /\ B.boolean_rewrite_model i /\
                    D.scoped [] e /\ extract_rewrite e == Some result)
          (ensures eval i e rho == eval i result rho)
  = let s = Some?.v (BV.extract_parts e) in
    let width, args = Some?.v (parts s.operand) in
    let n = s.high - s.low + 1 in
    BV.lemma_extract_parts i rho project e s;
    lemma_parts i rho project s.operand width args;
    lemma_split_shape s.low args;
    lemma_split_values i rho s.low args;
    let prefix, tail = L.splitAt s.low args in
    lemma_split_divmod s.low (BV.bit_values i rho args);
    assert (project width (eval i s.operand rho) / pow2 s.low ==
      BV.bits_number (BV.bit_values i rho tail));
    lemma_split_shape n tail;
    lemma_split_values i rho n tail;
    let middle, suffix = L.splitAt n tail in
    lemma_split_divmod n (BV.bit_values i rho tail);
    assert (BV.bits_number (BV.bit_values i rho tail) % pow2 n ==
      BV.bits_number (BV.bit_values i rho middle));
    lemma_word_shape middle;
    lemma_parts i rho project result n middle;
    BV.lemma_reflect i rho project n e result

let rec lemma_append_number (xs ys:list bool)
  : Lemma (BV.bits_number (xs @ ys) ==
           BV.bits_number xs + pow2 (L.length xs) * BV.bits_number ys)
          (decreases xs)
  = match xs with
    | [] -> ()
    | _ :: rest ->
      lemma_append_number rest ys;
      M.pow2_plus 1 (L.length rest);
      assert_norm (pow2 1 == 2);
      M.paren_mul_right 2 (pow2 (L.length rest)) (BV.bits_number ys)

let rec lemma_append_args (i:interpretation value) (rho:env value) (xs ys:list expr)
  : Lemma (requires D.scoped_args [] xs /\ D.scoped_args [] ys /\
                    L.for_all (fun a -> get_sort a = bool_sort) xs /\
                    L.for_all (fun a -> get_sort a = bool_sort) ys)
          (ensures D.scoped_args [] (xs @ ys) /\
                   L.for_all (fun a -> get_sort a = bool_sort) (xs @ ys) /\
                   BV.bit_values i rho (xs @ ys) == BV.bit_values i rho xs @ BV.bit_values i rho ys)
          (decreases xs)
  = match xs with [] -> () | _ :: rest -> lemma_append_args i rho rest ys

let concat_rewrite (e:expr) : option expr =
  match BV.concat_parts e with
  | Some c ->
    (match parts c.left, parts c.right with
     | Some (w, xs), Some (w', ys) ->
       if w = c.left_width && w' = c.right_width then Some (word (ys @ xs)) else None
     | _, _ -> None)
  | None -> None

let lemma_concat_rewrite (i:interpretation value) (rho:env value)
                         (project:pos -> value -> int) (e result:expr)
  : Lemma (requires BV.bv_model i project /\ B.boolean_rewrite_model i /\
                    D.scoped [] e /\ concat_rewrite e == Some result)
          (ensures eval i e rho == eval i result rho)
  = let c = Some?.v (BV.concat_parts e) in
    let _, xs = Some?.v (parts c.left) in
    let _, ys = Some?.v (parts c.right) in
    BV.lemma_concat_parts i rho project e c;
    lemma_parts i rho project c.left c.left_width xs;
    lemma_parts i rho project c.right c.right_width ys;
    lemma_append_args i rho ys xs;
    assert (L.length (BV.bit_values i rho ys) == c.right_width);
    lemma_append_number (BV.bit_values i rho ys) (BV.bit_values i rho xs);
    assert (BV.bits_number (BV.bit_values i rho (ys @ xs)) ==
      BV.bits_number (BV.bit_values i rho xs) * pow2 c.right_width +
      BV.bits_number (BV.bit_values i rho ys));
    assert (project (c.left_width + c.right_width) (eval i e rho) ==
      BV.bits_number (BV.bit_values i rho (ys @ xs)));
    lemma_word_shape (ys @ xs);
    lemma_parts i rho project result (c.left_width + c.right_width) (ys @ xs);
    BV.lemma_reflect i rho project (c.left_width + c.right_width) e result

let bit_number (b:bool) : nat = if b then 1 else 0

let sum_bit (a b carry:expr) : expr =
  App B.boolean_xor_decl [App B.boolean_xor_decl [a; b]; carry]

let carry_bit (a b carry:expr) : expr =
  App B.boolean_ite_decl [mk_eq_expr a b; a; carry]

#push-options "--fuel 4 --ifuel 2"
let lemma_boolean_app (f:func_decl) (args:list expr)
  : Lemma (requires D.scoped_args [] args /\
                    L.for_all (fun a -> get_sort a = bool_sort) args /\
                    f.domain == L.map (fun _ -> bool_sort) args /\ f.range == bool_sort)
          (ensures D.scoped [] (App f args) /\ get_sort (App f args) == bool_sort)
  = lemma_boolean_args args

let lemma_full_adder_shape (a b carry:expr)
  : Lemma (requires D.scoped [] a /\ D.scoped [] b /\ D.scoped [] carry /\
                    get_sort a == bool_sort /\ get_sort b == bool_sort /\ get_sort carry == bool_sort)
          (ensures D.scoped [] (sum_bit a b carry) /\ D.scoped [] (carry_bit a b carry) /\
                   get_sort (sum_bit a b carry) == bool_sort /\
                   get_sort (carry_bit a b carry) == bool_sort)
  = lemma_boolean_app B.boolean_xor_decl [a; b];
    lemma_boolean_app B.boolean_xor_decl [App B.boolean_xor_decl [a; b]; carry];
    lemma_boolean_app (eq_decl bool_sort) [a; b];
    lemma_boolean_app B.boolean_ite_decl [mk_eq_expr a b; a; carry]
#pop-options

let lemma_full_adder (i:interpretation value) (rho:env value) (a b carry:expr)
  : Lemma (requires B.boolean_rewrite_model i /\
                    get_sort a == bool_sort /\ get_sort b == bool_sort /\ get_sort carry == bool_sort)
          (ensures B.bool_value (eval i (sum_bit a b carry) rho) ==
                     ((B.bool_value (eval i a rho) <> B.bool_value (eval i b rho)) <>
                       B.bool_value (eval i carry rho)) /\
                   B.bool_value (eval i (carry_bit a b carry) rho) ==
                     (if B.bool_value (eval i a rho) = B.bool_value (eval i b rho)
                      then B.bool_value (eval i a rho) else B.bool_value (eval i carry rho)))
  = match eval i a rho, eval i b rho, eval i carry rho with
    | VBool x, VBool y, VBool c ->
      assert (eval i (sum_bit a b carry) rho == VBool ((x <> y) <> c));
      assert (eval i (carry_bit a b carry) rho == VBool (if x = y then x else c))
    | _, _, _ -> ()

let rec add_bits (carry:expr) (xs ys:list expr)
  : Tot (list expr & expr) (decreases xs) =
  match xs, ys with
  | a :: rest, b :: tail ->
    let sums, overflow = add_bits (carry_bit a b carry) rest tail in
    sum_bit a b carry :: sums, overflow
  | _, _ -> [], carry

let lemma_carry_arithmetic (n:nat) (a b c s d:nat) (k:nat{k <= 1}) (x y z:nat)
  : Lemma (requires s + 2 * d == a + b + c /\ z + pow2 n * k == x + y + d)
          (ensures s + 2 * z + pow2 (n + 1) * k == a + 2 * x + b + 2 * y + c)
  = M.pow2_plus 1 n;
    if k = 0 then () else ()

let rec add_values (carry:bool) (xs ys:list bool)
  : Tot (list bool & bool) (decreases xs) =
  match xs, ys with
  | a :: rest, b :: tail ->
    let sums, overflow = add_values (if a = b then a else carry) rest tail in
    ((a <> b) <> carry) :: sums, overflow
  | _, _ -> [], carry

let rec lemma_add_values (carry:bool) (xs ys:list bool)
  : Lemma (requires L.length xs == L.length ys)
          (ensures (let sums, overflow = add_values carry xs ys in
                    L.length sums == L.length xs /\
                    BV.bits_number sums + pow2 (L.length xs) * bit_number overflow ==
                      BV.bits_number xs + BV.bits_number ys + bit_number carry))
          (decreases xs)
  = match xs, ys with
    | a :: rest, b :: tail ->
      let next = if a = b then a else carry in
      lemma_add_values next rest tail;
      let sums, overflow = add_values next rest tail in
      assert (add_values carry xs ys == (((a <> b) <> carry) :: sums, overflow));
      assert (L.length xs == L.length rest + 1);
      assert (BV.bits_number xs == bit_number a + 2 * BV.bits_number rest);
      assert (BV.bits_number ys == bit_number b + 2 * BV.bits_number tail);
      lemma_carry_arithmetic (L.length rest) (bit_number a) (bit_number b) (bit_number carry)
        (bit_number ((a <> b) <> carry)) (bit_number next) (bit_number overflow)
        (BV.bits_number rest) (BV.bits_number tail) (BV.bits_number sums)
    | _, _ -> ()

let rec lemma_add_bits (i:interpretation value) (rho:env value)
                       (carry:expr) (xs ys:list expr)
  : Lemma (requires B.boolean_rewrite_model i /\
                    D.scoped [] carry /\ get_sort carry == bool_sort /\
                    D.scoped_args [] xs /\ D.scoped_args [] ys /\
                    L.length xs == L.length ys /\
                    L.for_all (fun a -> get_sort a = bool_sort) xs /\
                    L.for_all (fun a -> get_sort a = bool_sort) ys)
          (ensures (let sums, overflow = add_bits carry xs ys in
                    L.length sums == L.length xs /\ D.scoped_args [] sums /\
                    L.for_all (fun a -> get_sort a = bool_sort) sums /\
                    D.scoped [] overflow /\ get_sort overflow == bool_sort /\
                    (BV.bit_values i rho sums, B.bool_value (eval i overflow rho)) ==
                      add_values (B.bool_value (eval i carry rho))
                        (BV.bit_values i rho xs) (BV.bit_values i rho ys)))
          (decreases xs)
  = match xs, ys with
    | a :: rest, b :: tail ->
      lemma_full_adder_shape a b carry;
      lemma_full_adder i rho a b carry;
      lemma_add_bits i rho (carry_bit a b carry) rest tail
    | _, _ -> ()

let addition_rewrite (e:expr) : option expr =
  match e with
  | App f [a; b] ->
    (match BV.operation f [a; b], parts a, parts b with
     | Some (width, op), Some (w, xs), Some (w', ys) ->
       if op = BV.op_add && w = width && w' = width
       then Some (word (fst (add_bits false_expr xs ys))) else None
     | _, _, _ -> None)
  | _ -> None

let lemma_addition_rewrite (i:interpretation value) (rho:env value)
                           (project:pos -> value -> int) (e result:expr)
  : Lemma (requires BV.bv_model i project /\ B.boolean_rewrite_model i /\
                    D.scoped [] e /\ addition_rewrite e == Some result)
          (ensures eval i e rho == eval i result rho)
  = match e with
    | App f [a; b] ->
      let width, _ = Some?.v (BV.operation f [a; b]) in
      let _, xs = Some?.v (parts a) in
      let _, ys = Some?.v (parts b) in
      lemma_parts i rho project a width xs;
      lemma_parts i rho project b width ys;
      lemma_add_bits i rho false_expr xs ys;
      lemma_add_values false (BV.bit_values i rho xs) (BV.bit_values i rho ys);
      let sums, overflow = add_bits false_expr xs ys in
      lemma_word_shape sums;
      lemma_parts i rho project result width sums;
      lemma_number_bounds (BV.bit_values i rho sums);
      assert (project width (eval i a rho) + project width (eval i b rho) ==
        BV.bits_number (BV.bit_values i rho sums) +
        pow2 width * bit_number (B.bool_value (eval i overflow rho)));
      M.lemma_mod_plus (BV.bits_number (BV.bit_values i rho sums))
        (bit_number (B.bool_value (eval i overflow rho))) (pow2 width);
      M.small_mod (BV.bits_number (BV.bit_values i rho sums)) (pow2 width);
      assert ((project width (eval i a rho) + project width (eval i b rho)) % pow2 width ==
        BV.bits_number (BV.bit_values i rho sums));
      BV.lemma_word i rho project width a;
      BV.lemma_word i rho project width b;
      BV.lemma_operation i rho project f [a; b] width BV.op_add;
      BV.lemma_reflect i rho project width e result
    | _ -> ()

let rec bits_equivalent (xs ys:list expr) : Tot bool (decreases xs) =
  match xs, ys with
  | [], [] -> true
  | x :: rest, y :: tail -> B.boolean_equiv 64 8 x y && bits_equivalent rest tail
  | _, _ -> false

let rec lemma_bits_equivalent (i:interpretation value) (rho:env value) (xs ys:list expr)
  : Lemma (requires B.boolean_rewrite_model i /\ bits_equivalent xs ys)
          (ensures BV.bit_values i rho xs == BV.bit_values i rho ys)
          (decreases xs)
  = match xs, ys with
    | x :: rest, y :: tail ->
      B.lemma_boolean_equiv_sound 64 8 i rho x y;
      lemma_bits_equivalent i rho rest tail
    | _, _ -> ()

let word_equivalent (a b:expr) : bool =
  match parts a, parts b with
  | Some (w, xs), Some (w', ys) -> w = w' && bits_equivalent xs ys
  | _, _ -> false

let lemma_word_equivalent (i:interpretation value) (rho:env value)
                          (project:pos -> value -> int) (a b:expr)
  : Lemma (requires BV.bv_model i project /\ B.boolean_rewrite_model i /\
                    D.scoped [] a /\ D.scoped [] b /\ word_equivalent a b)
          (ensures eval i a rho == eval i b rho)
  = let width, xs = Some?.v (parts a) in
    let _, ys = Some?.v (parts b) in
    lemma_parts i rho project a width xs;
    lemma_parts i rho project b width ys;
    lemma_bits_equivalent i rho xs ys;
    BV.lemma_reflect i rho project width a b

let concat (m n:pos) (x y:expr) : expr =
  App { decl_name = "concat"; domain = [BV.bv_sort m; BV.bv_sort n];
        range = BV.bv_sort (m + n); interp = Some BV.op_concat; int_params = [m; n] } [x; y]

let lemma_concat_shape (m n:pos) (x y:expr)
  : Lemma (requires m + n <= 4096 /\ D.scoped [] x /\ D.scoped [] y /\
                    get_sort x == BV.bv_sort m /\ get_sort y == BV.bv_sort n)
          (ensures D.scoped [] (concat m n x y) /\ get_sort (concat m n x y) == BV.bv_sort (m + n) /\
                   BV.concat_parts (concat m n x y) ==
                     Some { BV.left_width = m; BV.right_width = n; BV.left = x; BV.right = y })
  = assert (sort_eq (BV.bv_sort m) (BV.bv_sort m));
    assert (sort_eq (BV.bv_sort n) (BV.bv_sort n))

let lemma_concat_value (i:interpretation value) (rho:env value)
                       (project:pos -> value -> int) (m n:pos) (x y:expr)
  : Lemma (requires BV.bv_model i project /\ m + n <= 4096 /\
                    D.scoped [] x /\ D.scoped [] y /\
                    get_sort x == BV.bv_sort m /\ get_sort y == BV.bv_sort n)
          (ensures D.scoped [] (concat m n x y) /\ get_sort (concat m n x y) == BV.bv_sort (m + n) /\
                   project (m + n) (eval i (concat m n x y) rho) ==
                     project m (eval i x rho) * pow2 n + project n (eval i y rho))
  = lemma_concat_shape m n x y;
    BV.lemma_concat_parts i rho project (concat m n x y)
      { BV.left_width = m; BV.right_width = n; BV.left = x; BV.right = y }

let concat_association_rewrite (e:expr) : option expr =
  match BV.concat3_parts e with
  | Some (c:BV.concatenation3) ->
    Some (concat c.width1 (c.width2 + c.width3) c.first
      (concat c.width2 c.width3 c.second c.third))
  | None ->
    (match BV.concat_parts e with
     | Some (c:BV.concatenation) ->
       (match BV.concat_parts c.left with
        | Some (left:BV.concatenation) ->
          if c.left_width <> left.left_width + left.right_width then None
          else Some (concat left.left_width (left.right_width + c.right_width) left.left
            (concat left.right_width c.right_width left.right c.right))
        | None -> None)
     | None -> None)

#push-options "--fuel 0 --ifuel 0 --using_facts_from 'Prims FStar.Math.Lemmas'"
let lemma_concat_association_numbers (m n:nat) (x y z:int)
  : Lemma ((x * pow2 m + y) * pow2 n + z ==
           x * pow2 (m + n) + (y * pow2 n + z)) =
  M.pow2_plus m n
#pop-options

let lemma_concat_association_rewrite (i:interpretation value) (rho:env value)
                                    (project:pos -> value -> int) (e result:expr)
  : Lemma (requires BV.bv_model i project /\ D.scoped [] e /\
                    concat_association_rewrite e == Some result)
          (ensures eval i e rho == eval i result rho) =
  match BV.concat3_parts e with
  | Some (c:BV.concatenation3) ->
    BV.lemma_concat3_parts i rho project e c;
    lemma_concat_value i rho project c.width2 c.width3 c.second c.third;
    lemma_concat_value i rho project c.width1 (c.width2 + c.width3) c.first
      (concat c.width2 c.width3 c.second c.third);
    BV.lemma_reflect i rho project (c.width1 + c.width2 + c.width3) e result
  | None ->
    let c:BV.concatenation = Some?.v (BV.concat_parts e) in
    let left:BV.concatenation = Some?.v (BV.concat_parts c.left) in
    BV.lemma_concat_parts i rho project e c;
    BV.lemma_concat_parts i rho project c.left left;
    lemma_concat_value i rho project left.right_width c.right_width left.right c.right;
    lemma_concat_value i rho project left.left_width (left.right_width + c.right_width) left.left
      (concat left.right_width c.right_width left.right c.right);
    lemma_concat_association_numbers left.right_width c.right_width
      (project left.left_width (eval i left.left rho))
      (project left.right_width (eval i left.right rho))
      (project c.right_width (eval i c.right rho));
    BV.lemma_reflect i rho project (c.left_width + c.right_width) e result

let concat_numeral_equality (a b:expr) : option expr =
  match BV.concat_parts a, BV.numeral b with
  | Some (c:BV.concatenation), Some (width, n) ->
    if width <> c.left_width + c.right_width then None
    else let eqs =
      [mk_eq_expr c.right (BV.literal c.right_width (n % pow2 c.right_width));
       mk_eq_expr c.left (BV.literal c.left_width (n / pow2 c.right_width))] in
      Some (App (B.connective_decl B.Conjunction eqs) eqs)
  | _, _ -> None

let concat_equality_rewrite (e:expr) : option expr =
  match e with
  | App f [a; b] ->
    if f <> eq_decl (get_sort a) || get_sort a <> get_sort b then None
    else (match concat_numeral_equality a b with
      | Some result -> Some result
      | None -> concat_numeral_equality b a)
  | _ -> None

#push-options "--fuel 4 --ifuel 2"
let lemma_concat_numeral_equality (i:interpretation value) (rho:env value)
                                 (project:pos -> value -> int) (a b result:expr)
  : Lemma (requires BV.bv_model i project /\ B.boolean_rewrite_model i /\
                    D.scoped [] a /\ D.scoped [] b /\
                    concat_numeral_equality a b == Some result)
          (ensures (eval i a rho == eval i b rho) <==> lit_true i rho result)
  = let c:BV.concatenation = Some?.v (BV.concat_parts a) in
    let width, n = Some?.v (BV.numeral b) in
    BV.lemma_concat_parts i rho project a c;
    BV.lemma_word i rho project c.left_width c.left;
    BV.lemma_word i rho project c.right_width c.right;
    BV.lemma_word i rho project width b;
    assert (project width (eval i b rho) == n);
    let x = project c.left_width (eval i c.left rho) in
    let y = project c.right_width (eval i c.right rho) in
    let p = pow2 c.right_width in
    M.pow2_plus c.left_width c.right_width;
    M.lemma_div_mod n p;
    assert (n / p >= 0 /\ n / p < pow2 c.left_width);
    BV.lemma_literal_shape c.left_width (n / p);
    BV.lemma_literal_shape c.right_width (n % p);
    BV.lemma_literal i rho project c.left_width (n / p);
    BV.lemma_literal i rho project c.right_width (n % p);
    M.lemma_div_plus y x p;
    M.small_div y p;
    M.lemma_mod_plus y x p;
    M.small_mod y p;
    assert ((x * p + y == n) <==> (x == n / p /\ y == n % p));
    assert ((eval i a rho == eval i b rho) <==>
      project width (eval i a rho) == project width (eval i b rho));
    assert ((eval i c.right rho == eval i (BV.literal c.right_width (n % p)) rho) <==>
      y == n % p);
    assert ((eval i c.left rho == eval i (BV.literal c.left_width (n / p)) rho) <==>
      x == n / p);
    let r = mk_eq_expr c.right (BV.literal c.right_width (n % p)) in
    let l = mk_eq_expr c.left (BV.literal c.left_width (n / p)) in
    assert (lit_true i rho r <==> eval i c.right rho == eval i (BV.literal c.right_width (n % p)) rho);
    assert (lit_true i rho l <==> eval i c.left rho == eval i (BV.literal c.left_width (n / p)) rho);
    assert (lit_true i rho result <==> (lit_true i rho r /\ lit_true i rho l))

let lemma_concat_equality_rewrite (i:interpretation value) (rho:env value)
                                 (project:pos -> value -> int) (e result:expr)
  : Lemma (requires BV.bv_model i project /\ B.boolean_rewrite_model i /\
                    D.scoped [] e /\ concat_equality_rewrite e == Some result)
          (ensures eval i e rho == eval i result rho)
  = match e with
    | App f [a; b] ->
      if Some? (concat_numeral_equality a b) then
        lemma_concat_numeral_equality i rho project a b result
      else lemma_concat_numeral_equality i rho project b a result;
      (match eval i e rho, eval i result rho with VBool _, VBool _ -> () | _, _ -> ())
    | _ -> ()
#pop-options

let concat3_rewrite (e:expr) : option expr =
  match BV.concat3_parts e with
  | Some c -> Some (concat c.width1 (c.width2 + c.width3) c.first
      (concat c.width2 c.width3 c.second c.third))
  | None -> None

let lemma_concat3_rewrite (i:interpretation value) (rho:env value)
                         (project:pos -> value -> int) (e result:expr)
  : Lemma (requires BV.bv_model i project /\ D.scoped [] e /\ concat3_rewrite e == Some result)
          (ensures eval i e rho == eval i result rho)
  = let c = Some?.v (BV.concat3_parts e) in
    let width = c.width1 + c.width2 + c.width3 in
    (match e with App _ [_; _; _] -> () | _ -> ());
    assert (D.scoped [] c.first /\ D.scoped [] c.second /\ D.scoped [] c.third);
    assert (get_sort c.first == BV.bv_sort c.width1 /\
      get_sort c.second == BV.bv_sort c.width2 /\ get_sort c.third == BV.bv_sort c.width3);
    assert (project width (eval i e rho) ==
      project c.width1 (eval i c.first rho) * pow2 (c.width2 + c.width3) +
      project c.width2 (eval i c.second rho) * pow2 c.width3 +
      project c.width3 (eval i c.third rho));
    lemma_concat_value i rho project c.width2 c.width3 c.second c.third;
    lemma_concat_value i rho project c.width1 (c.width2 + c.width3) c.first
      (concat c.width2 c.width3 c.second c.third);
    BV.lemma_reflect i rho project width e result

let complement (width:pos) (x:expr) : expr =
  App { decl_name = "bvnot"; domain = [BV.bv_sort width]; range = BV.bv_sort width;
        interp = Some BV.op_not; int_params = [width] } [x]

let lemma_complement_value (i:interpretation value) (rho:env value)
                           (project:pos -> value -> int) (width:pos) (x:expr)
  : Lemma (requires BV.bv_model i project /\ width <= 4096 /\
                    D.scoped [] x /\ get_sort x == BV.bv_sort width)
          (ensures D.scoped [] (complement width x) /\ get_sort (complement width x) == BV.bv_sort width /\
                   project width (eval i (complement width x) rho) ==
                     U.lognot #width (U.to_uint_t width (project width (eval i x rho))))
  = assert (sort_eq (BV.bv_sort width) (BV.bv_sort width));
    assert (D.scoped [] (complement width x));
    BV.lemma_word i rho project width x;
    match complement width x with App f args -> BV.lemma_operation i rho project f args width BV.op_not | _ -> ()

let lemma_not_number (width:pos) (x:U.uint_t width)
  : Lemma (U.lognot x == pow2 width - 1 - x)
  = U.lemma_lognot_value_mod #width x;
    M.small_mod (pow2 width - 1 - x) (pow2 width)

let lemma_not_concat_numbers (m n:pos) (x:U.uint_t m) (y:U.uint_t n) (z:U.uint_t (m + n))
  : Lemma (requires z == x * pow2 n + y)
          (ensures U.lognot z == U.lognot x * pow2 n + U.lognot y)
  = lemma_not_number m x;
    lemma_not_number n y;
    lemma_not_number (m + n) z;
    M.pow2_plus m n;
    M.distributivity_sub_left (pow2 m - 1) x (pow2 n);
    M.distributivity_sub_left (pow2 m) 1 (pow2 n)

let not_concat_rewrite (e:expr) : option expr =
  match e with
  | App f [x] ->
    (match BV.operation f [x], BV.concat_parts x with
     | Some (width, op), Some (c:BV.concatenation) ->
       if op = BV.op_not && width = c.left_width + c.right_width then
         Some (concat c.left_width c.right_width
           (complement c.left_width c.left) (complement c.right_width c.right))
       else None
     | _, _ -> None)
  | _ -> None

let lemma_complement_concat_value (i:interpretation value) (rho:env value)
                                 (project:pos -> value -> int) (m n:pos) (x y:expr)
  : Lemma (requires BV.bv_model i project /\ m + n <= 4096 /\
                    D.scoped [] x /\ D.scoped [] y /\
                    get_sort x == BV.bv_sort m /\ get_sort y == BV.bv_sort n)
          (ensures (let result = concat m n (complement m x) (complement n y) in
                    D.scoped [] result /\ get_sort result == BV.bv_sort (m + n) /\
                    project (m + n) (eval i result rho) ==
                      U.lognot #m (U.to_uint_t m (project m (eval i x rho))) * pow2 n +
                      U.lognot #n (U.to_uint_t n (project n (eval i y rho)))))
  = lemma_complement_value i rho project m x;
    lemma_complement_value i rho project n y;
    lemma_concat_value i rho project m n (complement m x) (complement n y)

let lemma_not_concat_rewrite (i:interpretation value) (rho:env value)
                            (project:pos -> value -> int) (e result:expr)
  : Lemma (requires BV.bv_model i project /\ D.scoped [] e /\ not_concat_rewrite e == Some result)
          (ensures eval i e rho == eval i result rho)
  = match e with
    | App f [x] ->
      let c = Some?.v (BV.concat_parts x) in
      let width = c.left_width + c.right_width in
      assert (result == concat c.left_width c.right_width
        (complement c.left_width c.left) (complement c.right_width c.right));
      BV.lemma_concat_parts i rho project x c;
      BV.lemma_word i rho project c.left_width c.left;
      BV.lemma_word i rho project c.right_width c.right;
      BV.lemma_word i rho project width x;
      BV.lemma_operation i rho project f [x] width BV.op_not;
      assert (project width (eval i e rho) == U.lognot #width (project width (eval i x rho)));
      lemma_not_concat_numbers c.left_width c.right_width
        (project c.left_width (eval i c.left rho)) (project c.right_width (eval i c.right rho))
        (project width (eval i x rho));
      lemma_complement_concat_value i rho project c.left_width c.right_width c.left c.right;
      BV.lemma_reflect i rho project width e result
    | _ -> ()

let rewrite (e:expr) : option expr =
  if not (D.scoped [] e) then None
  else let r = equality_rewrite e in
  if Some? r then r else
  let r = concat_equality_rewrite e in
  if Some? r then r else
  let r = extract_rewrite e in
  if Some? r then r else
  let r = concat_rewrite e in
  if Some? r then r else
  let r = addition_rewrite e in
  if Some? r then r else
  let r = concat3_rewrite e in
  if Some? r then r else
  let r = concat_association_rewrite e in
  if Some? r then r else not_concat_rewrite e

let lemma_rewrite (i:interpretation value) (rho:env value)
                  (project:pos -> value -> int) (e result:expr)
  : Lemma (requires BV.bv_model i project /\ B.boolean_rewrite_model i /\
                    rewrite e == Some result)
          (ensures eval i e rho == eval i result rho)
  = if Some? (equality_rewrite e) then lemma_equality_rewrite i rho project e result
    else if Some? (concat_equality_rewrite e) then lemma_concat_equality_rewrite i rho project e result
    else if Some? (extract_rewrite e) then lemma_extract_rewrite i rho project e result
    else if Some? (concat_rewrite e) then lemma_concat_rewrite i rho project e result
    else if Some? (addition_rewrite e) then lemma_addition_rewrite i rho project e result
    else if Some? (concat3_rewrite e) then lemma_concat3_rewrite i rho project e result
    else if Some? (concat_association_rewrite e) then lemma_concat_association_rewrite i rho project e result
    else lemma_not_concat_rewrite i rho project e result

let equivalent (a b:expr) : bool =
  D.scoped [] a && D.scoped [] b &&
    (literal_equivalent a b || literal_equivalent b a || word_equivalent a b)

let lemma_equivalent (i:interpretation value) (rho:env value)
                     (project:pos -> value -> int) (a b:expr)
  : Lemma (requires BV.bv_model i project /\ B.boolean_rewrite_model i /\ equivalent a b)
          (ensures eval i a rho == eval i b rho)
  = if literal_equivalent a b then lemma_literal_equivalent i rho project a b
    else if literal_equivalent b a then lemma_literal_equivalent i rho project b a
    else lemma_word_equivalent i rho project a b
