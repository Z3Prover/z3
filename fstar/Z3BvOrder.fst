module Z3BvOrder

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module BV = Z3BvLemma
module W = Z3BvWord
module B = Z3BooleanRewrite
module D = Z3Definitions
module A = Z3ArrayRewrite
module L = FStar.List.Tot
module M = FStar.Math.Lemmas

let unsigned (width:pos) (op:decl_kind) (a b:expr) : expr =
  App { decl_name = if op = BV.op_ult then "bvult" else if op = BV.op_ule then "bvule" else "bvuge";
        domain = [BV.bv_sort width; BV.bv_sort width]; range = bool_sort;
        interp = Some op; int_params = [width] } [a; b]

#push-options "--fuel 4 --ifuel 2"
let lemma_unsigned_shape (width:pos) (op:decl_kind) (a b:expr)
  : Lemma (requires width <= 4096 /\ (op = BV.op_ult \/ op = BV.op_ule \/ op = BV.op_uge) /\
                    D.scoped [] a /\ D.scoped [] b /\
                    get_sort a == BV.bv_sort width /\ get_sort b == BV.bv_sort width)
          (ensures D.scoped [] (unsigned width op a b) /\
                   BV.unsigned_parts (unsigned width op a b) ==
                     Some { BV.width = width; BV.relation = op; BV.lhs = a; BV.rhs = b })
  = assert (sort_eq (BV.bv_sort width) (BV.bv_sort width));
    assert (sorts_match [a; b] [BV.bv_sort width; BV.bv_sort width])
#pop-options

let lemma_unsigned_parts (i:interpretation value) (rho:env value)
                         (project:pos -> value -> int) (e:expr) (c:BV.unsigned_comparison)
  : Lemma (requires BV.bv_model i project /\ D.scoped [] e /\ BV.unsigned_parts e == Some c)
          (ensures c.width <= 4096 /\ D.scoped [] c.lhs /\ D.scoped [] c.rhs /\
                   get_sort c.lhs == BV.bv_sort c.width /\ get_sort c.rhs == BV.bv_sort c.width /\
                   (c.relation = BV.op_ult \/ c.relation = BV.op_ule \/ c.relation = BV.op_uge) /\
                   eval i e rho == VBool (BV.unsigned_value c.relation
                     (project c.width (eval i c.lhs rho)) (project c.width (eval i c.rhs rho))))
  = match e with App _ _ -> () | _ -> ()

let compare_step (a b lower:expr) : expr =
  App B.boolean_ite_decl [mk_eq_expr a b; lower; mk_not_expr a]

#push-options "--fuel 4 --ifuel 2"
let lemma_compare_step_shape (a b lower:expr)
  : Lemma (requires D.scoped [] a /\ D.scoped [] b /\ D.scoped [] lower /\
                    get_sort a == bool_sort /\ get_sort b == bool_sort /\ get_sort lower == bool_sort)
          (ensures D.scoped [] (compare_step a b lower) /\ get_sort (compare_step a b lower) == bool_sort)
  = W.lemma_boolean_app (eq_decl bool_sort) [a; b];
    assert (D.scoped [] (mk_not_expr a));
    W.lemma_boolean_app B.boolean_ite_decl [mk_eq_expr a b; lower; mk_not_expr a]
#pop-options

let lemma_compare_step (i:interpretation value) (rho:env value) (a b lower:expr)
  : Lemma (requires B.boolean_rewrite_model i /\
                    get_sort a == bool_sort /\ get_sort b == bool_sort /\ get_sort lower == bool_sort)
          (ensures B.bool_value (eval i (compare_step a b lower) rho) ==
                     (if B.bool_value (eval i a rho) = B.bool_value (eval i b rho)
                      then B.bool_value (eval i lower rho) else not (B.bool_value (eval i a rho))))
  = match eval i a rho, eval i b rho, eval i lower rho with
    | VBool x, VBool y, VBool z ->
      assert (eval i (compare_step a b lower) rho == VBool (if x = y then z else not x))
    | _, _, _ -> ()

let rec le_values (lower:bool) (xs ys:list bool) : Tot bool (decreases xs) =
  match xs, ys with
  | a :: rest, b :: tail -> le_values (if a = b then lower else not a) rest tail
  | _, _ -> lower

let rec lemma_le_values (lower:bool) (xs ys:list bool)
  : Lemma (requires L.length xs == L.length ys)
          (ensures le_values lower xs ys ==
                     (BV.bits_number xs < BV.bits_number ys ||
                       (BV.bits_number xs = BV.bits_number ys && lower)))
          (decreases xs)
  = match xs, ys with
    | a :: rest, b :: tail ->
      lemma_le_values (if a = b then lower else not a) rest tail
    | _, _ -> ()

let rec le_bits (lower:expr) (xs ys:list expr) : Tot expr (decreases xs) =
  match xs, ys with
  | a :: rest, b :: tail -> le_bits (compare_step a b lower) rest tail
  | _, _ -> lower

let rec lemma_le_bits (i:interpretation value) (rho:env value) (lower:expr) (xs ys:list expr)
  : Lemma (requires B.boolean_rewrite_model i /\ D.scoped [] lower /\ get_sort lower == bool_sort /\
                    D.scoped_args [] xs /\ D.scoped_args [] ys /\ L.length xs == L.length ys /\
                    L.for_all (fun e -> get_sort e = bool_sort) xs /\
                    L.for_all (fun e -> get_sort e = bool_sort) ys)
          (ensures D.scoped [] (le_bits lower xs ys) /\ get_sort (le_bits lower xs ys) == bool_sort /\
                   B.bool_value (eval i (le_bits lower xs ys) rho) ==
                     le_values (B.bool_value (eval i lower rho)) (BV.bit_values i rho xs) (BV.bit_values i rho ys))
          (decreases xs)
  = match xs, ys with
    | a :: rest, b :: tail ->
      lemma_compare_step_shape a b lower;
      lemma_compare_step i rho a b lower;
      lemma_le_bits i rho (compare_step a b lower) rest tail
    | _, _ -> ()

let numeral_branch (guard other target:expr) (equal:bool) : expr =
  let args = [guard; mk_eq_expr other target] in
  App (B.connective_decl (if equal then B.Disjunction else B.Conjunction) args) args

let mixed_comparison (source target:expr) : option expr =
  match A.ite_parts source, BV.numeral target with
  | Some (c, t, u), Some (w, n) ->
    (match BV.numeral t with
     | Some (w', k) ->
       if w <> w' || get_sort u <> BV.bv_sort w then None
       else Some (numeral_branch (if n = k then c else mk_not_expr c) u target (n = k))
     | None ->
       (match BV.numeral u with
        | Some (w', k) ->
          if w <> w' || get_sort t <> BV.bv_sort w then None
          else Some (numeral_branch (if n = k then mk_not_expr c else c) t target (n = k))
        | None -> None))
  | _, _ -> None

#push-options "--fuel 4 --ifuel 2"
let lemma_mixed_comparison (i:interpretation value) (rho:env value)
                           (project:pos -> value -> int) (source target result:expr)
  : Lemma (requires BV.bv_model i project /\ B.boolean_rewrite_model i /\ A.term_ite_sound i /\
                    D.scoped [] source /\ D.scoped [] target /\ mixed_comparison source target == Some result)
          (ensures ((eval i source rho == eval i target rho) <==> lit_true i rho result))
  = let c, t, u = Some?.v (A.ite_parts source) in
    let width, n = Some?.v (BV.numeral target) in
    (match source with
     | App _ _ ->
       assert (eval i source rho ==
         (if B.bool_value (eval i c rho) then eval i t rho else eval i u rho))
     | _ -> ());
    if Some? (BV.numeral t) then (
      let _, k = Some?.v (BV.numeral t) in
      assert (project width (eval i t rho) == k);
      assert (project width (eval i target rho) == n);
      assert ((eval i t rho == eval i target rho) <==> k = n);
      assert (lit_true i rho result <==>
        (if n = k then lit_true i rho c \/ eval i u rho == eval i target rho
         else not (lit_true i rho c) /\ eval i u rho == eval i target rho));
      match eval i c rho with VBool _ -> () | _ -> ())
    else (
      let _, k = Some?.v (BV.numeral u) in
      assert (project width (eval i u rho) == k);
      assert (project width (eval i target rho) == n);
      assert ((eval i u rho == eval i target rho) <==> k = n);
      assert (lit_true i rho result <==>
        (if n = k then not (lit_true i rho c) \/ eval i t rho == eval i target rho
         else lit_true i rho c /\ eval i t rho == eval i target rho));
      match eval i c rho with VBool _ -> () | _ -> ())
#pop-options

let mixed_equality (e:expr) : option expr =
  match e with
  | App f [a; b] ->
    if f <> eq_decl (get_sort a) || get_sort a <> get_sort b then None
    else (match mixed_comparison a b with Some r -> Some r | None -> mixed_comparison b a)
  | _ -> None

let lemma_mixed_equality (i:interpretation value) (rho:env value)
                        (project:pos -> value -> int) (e result:expr)
  : Lemma (requires BV.bv_model i project /\ B.boolean_rewrite_model i /\ A.term_ite_sound i /\
                    D.scoped [] e /\ mixed_equality e == Some result)
          (ensures eval i e rho == eval i result rho)
  = match e with
    | App _ [a; b] ->
      if Some? (mixed_comparison a b) then lemma_mixed_comparison i rho project a b result
      else lemma_mixed_comparison i rho project b a result;
      (match eval i e rho, eval i result rho with VBool _, VBool _ -> () | _, _ -> ())
    | _ -> ()

let rec needed_width (width:pos) (n:nat{n < pow2 width})
  : Tot (m:pos{m <= width /\ n < pow2 m}) (decreases width) =
  if width > 1 && n < pow2 (width - 1) then needed_width (width - 1) n else width

let slice (width:pos) (high low:nat) (x:expr) : expr =
  App { decl_name = "extract"; domain = [BV.bv_sort width]; range = BV.bv_sort (high - low + 1);
        interp = Some BV.op_extract; int_params = [width; high; low] } [x]

let lemma_slice_shape (width:pos) (high low:nat) (x:expr)
  : Lemma (requires width <= 4096 /\ low <= high /\ high < width /\
                    D.scoped [] x /\ get_sort x == BV.bv_sort width)
          (ensures D.scoped [] (slice width high low x) /\
                   BV.extract_parts (slice width high low x) ==
                     Some { BV.source_width = width; BV.high = high; BV.low = low; BV.operand = x } /\
                   get_sort (slice width high low x) == BV.bv_sort (high - low + 1))
  = assert (sort_eq (BV.bv_sort width) (BV.bv_sort width))

let lemma_low_slice (i:interpretation value) (rho:env value)
                    (project:pos -> value -> int) (width:pos) (m:pos{m < width}) (x:expr)
  : Lemma (requires BV.bv_model i project /\ width <= 4096 /\
                    D.scoped [] x /\ get_sort x == BV.bv_sort width)
          (ensures project m (eval i (slice width (m - 1) 0 x) rho) ==
                     project width (eval i x rho) % pow2 m)
  = lemma_slice_shape width (m - 1) 0 x;
    BV.lemma_extract_parts i rho project (slice width (m - 1) 0 x)
      { BV.source_width = width; BV.high = m - 1; BV.low = 0; BV.operand = x };
    assert (pow2 0 == 1)

let alternative (upper zero lower:expr) : expr =
  let args = [mk_not_expr (mk_eq_expr upper zero); lower] in
  App (B.connective_decl B.Disjunction args) args

#push-options "--fuel 4 --ifuel 2"
let lemma_alternative (i:interpretation value) (rho:env value) (upper zero lower:expr)
  : Lemma (requires B.boolean_rewrite_model i /\ get_sort upper == get_sort zero /\ get_sort lower == bool_sort)
          (ensures lit_true i rho (alternative upper zero lower) <==>
                     ~(eval i upper rho == eval i zero rho) \/ lit_true i rho lower)
  = ()
#pop-options

let split_formula (width:pos) (m:pos{m < width}) (n:nat) (x:expr) : expr =
  alternative (slice width (width - 1) m x) (BV.literal (width - m) 0)
    (unsigned m BV.op_ule (BV.literal m n) (slice width (m - 1) 0 x))

let split_rewrite (e:expr) : option expr =
  match BV.unsigned_parts e with
  | Some c ->
    (match BV.numeral c.lhs with
     | Some (w, n) ->
       if c.relation <> BV.op_ule || w <> c.width then None
       else let m = needed_width w n in
         if m < w then Some (split_formula w m n c.rhs) else None
     | None -> None)
  | None -> None

let lemma_split_compare (width:pos) (m:pos{m < width}) (n:nat{n < pow2 m})
                        (x:nat{x < pow2 width})
  : Lemma ((n <= x) ==
            ((x / pow2 m) % pow2 (width - m) <> 0 || n <= x % pow2 m))
  = M.pow2_plus m (width - m);
    M.lemma_div_mod x (pow2 m);
    assert (x / pow2 m < pow2 (width - m));
    M.small_mod (x / pow2 m) (pow2 (width - m))

#push-options "--fuel 4 --ifuel 2"
let lemma_split_rewrite (i:interpretation value) (rho:env value)
                        (project:pos -> value -> int) (e result:expr)
  : Lemma (requires BV.bv_model i project /\ B.boolean_rewrite_model i /\
                    D.scoped [] e /\ split_rewrite e == Some result)
          (ensures eval i e rho == eval i result rho)
  = let c = Some?.v (BV.unsigned_parts e) in
    let width, n = Some?.v (BV.numeral c.lhs) in
    let m = needed_width width n in
    lemma_unsigned_parts i rho project e c;
    BV.lemma_word i rho project width c.rhs;
    let upper = slice width (width - 1) m c.rhs in
    let lower = slice width (m - 1) 0 c.rhs in
    lemma_slice_shape width (width - 1) m c.rhs;
    lemma_slice_shape width (m - 1) 0 c.rhs;
    BV.lemma_extract_parts i rho project upper
      { BV.source_width = width; BV.high = width - 1; BV.low = m; BV.operand = c.rhs };
    lemma_low_slice i rho project width m c.rhs;
    BV.lemma_literal_shape (width - m) 0;
    BV.lemma_literal i rho project (width - m) 0;
    BV.lemma_literal_shape m n;
    BV.lemma_literal i rho project m n;
    lemma_unsigned_shape m BV.op_ule (BV.literal m n) lower;
    lemma_unsigned_parts i rho project (unsigned m BV.op_ule (BV.literal m n) lower)
      { BV.width = m; BV.relation = BV.op_ule; BV.lhs = BV.literal m n; BV.rhs = lower };
    lemma_alternative i rho upper (BV.literal (width - m) 0)
      (unsigned m BV.op_ule (BV.literal m n) lower);
    lemma_split_compare width m n (project width (eval i c.rhs rho));
    assert ((eval i upper rho == eval i (BV.literal (width - m) 0) rho) <==>
      project (width - m) (eval i upper rho) == 0);
    assert (project width (eval i c.lhs rho) == n);
    assert (lit_true i rho e <==> n <= project width (eval i c.rhs rho));
    assert (lit_true i rho result <==>
      project (width - m) (eval i upper rho) <> 0 \/
      n <= project m (eval i lower rho));
    assert (project (width - m) (eval i upper rho) ==
      (project width (eval i c.rhs rho) / pow2 m) % pow2 (width - m));
    assert (lit_true i rho e <==> lit_true i rho result);
    (match eval i result rho with VBool _ -> () | _ -> ())
#pop-options

let order_rewrite (e:expr) : option expr =
  match BV.unsigned_parts e with
  | Some c ->
    if c.relation = BV.op_ult then Some (mk_not_expr (unsigned c.width BV.op_ule c.rhs c.lhs))
    else if c.relation = BV.op_uge then Some (unsigned c.width BV.op_ule c.rhs c.lhs)
    else if BV.numeral c.lhs = Some (c.width, 0) then Some true_expr
    else (match W.parts c.lhs, W.parts c.rhs with
      | Some (w, xs), Some (w', ys) ->
        if w = c.width && w' = c.width then Some (le_bits true_expr xs ys) else None
      | _, _ -> split_rewrite e)
  | None -> None

let lemma_order_rewrite (i:interpretation value) (rho:env value)
                        (project:pos -> value -> int) (e result:expr)
  : Lemma (requires BV.bv_model i project /\ B.boolean_rewrite_model i /\
                    D.scoped [] e /\ order_rewrite e == Some result)
          (ensures eval i e rho == eval i result rho)
  = let c = Some?.v (BV.unsigned_parts e) in
    lemma_unsigned_parts i rho project e c;
    if c.relation = BV.op_ult || c.relation = BV.op_uge then (
      lemma_unsigned_shape c.width BV.op_ule c.rhs c.lhs;
      lemma_unsigned_parts i rho project (unsigned c.width BV.op_ule c.rhs c.lhs)
        { BV.width = c.width; BV.relation = BV.op_ule; BV.lhs = c.rhs; BV.rhs = c.lhs };
      assert (eval i (unsigned c.width BV.op_ule c.rhs c.lhs) rho ==
        VBool (project c.width (eval i c.rhs rho) <= project c.width (eval i c.lhs rho))))
    else if BV.numeral c.lhs = Some (c.width, 0) then (
      BV.lemma_word i rho project c.width c.rhs;
      assert (project c.width (eval i c.lhs rho) == 0))
    else if Some? (W.parts c.lhs) && Some? (W.parts c.rhs) then (
      let _, xs = Some?.v (W.parts c.lhs) in
      let _, ys = Some?.v (W.parts c.rhs) in
      W.lemma_parts i rho project c.lhs c.width xs;
      W.lemma_parts i rho project c.rhs c.width ys;
      lemma_le_bits i rho true_expr xs ys;
      lemma_le_values true (BV.bit_values i rho xs) (BV.bit_values i rho ys);
      (match eval i result rho with VBool _ -> () | _ -> ()))
    else lemma_split_rewrite i rho project e result

let rewrite (e:expr) : option expr =
  if not (D.scoped [] e) then None
  else match mixed_equality e with Some r -> Some r | None -> order_rewrite e

let lemma_rewrite (i:interpretation value) (rho:env value)
                  (project:pos -> value -> int) (e result:expr)
  : Lemma (requires BV.bv_model i project /\ B.boolean_rewrite_model i /\ A.term_ite_sound i /\
                    rewrite e == Some result)
          (ensures eval i e rho == eval i result rho)
  = if Some? (mixed_equality e) then lemma_mixed_equality i rho project e result
    else lemma_order_rewrite i rho project e result
