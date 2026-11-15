module Z3BvSyntax

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open Z3AstTheory
open FStar.List.Tot
module D = Z3ExprScope
module L = FStar.List.Tot
module U = FStar.UInt
module R = Z3ClauseSyntax
module BS = Z3BooleanSyntax
module T = Z3OperatorTags
module X = Z3BooleanRewriteSyntax
module C = Z3CanonicalOps

(* Transport tags and executable recognizers copied from Z3BvLemma. *)
let op_and : decl_kind = 100
let op_or : decl_kind = 101
let op_xor : decl_kind = 102
let op_not : decl_kind = 103
let op_add : decl_kind = 104
let op_mul : decl_kind = 105
let op_sub : decl_kind = 106
let op_neg : decl_kind = 107
let op_numeral : decl_kind = 108
let op_udiv : decl_kind = 109
let op_urem : decl_kind = 110
let op_extract : decl_kind = 111
let op_concat : decl_kind = 112
let op_mkbv : decl_kind = 113
let op_ult : decl_kind = 114
let op_ule : decl_kind = 115
let op_uge : decl_kind = 116
let op_shl : decl_kind = 117
let op_lshr : decl_kind = 118
let op_zero_extend : decl_kind = 119

let bv_sort (width:int) : sort = SortApp (BvSymbol width) []

let numeral (e:expr) : option (pos & int) =
  match e with
  | App f [] ->
    (match f.int_params with
     | [width; n] ->
       if width > 0 && width <= 4096 && f.range = bv_sort width &&
          f.domain = [] && f.interp = Some op_numeral && n >= 0 && n < pow2 width
       then Some (width, n) else None
     | _ -> None)
  | _ -> None

let operation (f:func_decl) (args:list expr) : option (pos & decl_kind) =
  match f.int_params, f.interp with
  | [width], Some op ->
    if width > 0 && width <= 4096 && f.range = bv_sort width &&
       sorts_match args f.domain && f.domain = L.map (fun _ -> bv_sort width) args &&
       (((op = op_not || op = op_neg) && L.length args = 1) ||
        ((op = op_and || op = op_or || op = op_xor || op = op_add ||
          op = op_mul || op = op_sub || op = op_udiv || op = op_urem ||
          op = op_shl || op = op_lshr) && L.length args = 2))
    then Some (width, op) else None
  | _, _ -> None

type extraction = {
  source_width: pos;
  high: h:nat{h < source_width};
  low: l:nat{l <= high};
  operand: expr
}

type concatenation = {
  left_width: pos;
  right_width: pos;
  left: expr;
  right: expr
}

type concatenation3 = {
  width1: pos;
  width2: pos;
  width3: pos;
  first: expr;
  second: expr;
  third: expr
}

let concat3_parts (e:expr) : option concatenation3 =
  match e with
  | App f [x; y; z] ->
    (match f.int_params with
     | [a; b; c] ->
       if a > 0 && b > 0 && c > 0 && a + b + c <= 4096 && f.interp = Some op_concat &&
          f.domain = [bv_sort a; bv_sort b; bv_sort c] && f.range = bv_sort (a + b + c) &&
          get_sort x = bv_sort a && get_sort y = bv_sort b && get_sort z = bv_sort c
       then Some { width1 = a; width2 = b; width3 = c; first = x; second = y; third = z } else None
     | _ -> None)
  | _ -> None

type unsigned_comparison = {
  width: pos;
  relation: decl_kind;
  lhs: expr;
  rhs: expr
}

let unsigned_parts (e:expr) : option unsigned_comparison =
  match e with
  | App f [a; b] ->
    (match f.int_params, f.interp with
     | [w], Some op ->
       if w > 0 && w <= 4096 && (op = op_ult || op = op_ule || op = op_uge) &&
          f.range = bool_sort && f.domain = [bv_sort w; bv_sort w] &&
          get_sort a = bv_sort w && get_sort b = bv_sort w
       then Some { width = w; relation = op; lhs = a; rhs = b } else None
     | _, _ -> None)
  | _ -> None

let unsigned_value (op:decl_kind) (a b:int) : bool =
  if op = op_ult then a < b else if op = op_ule then a <= b else a >= b

let extract_parts (e:expr) : option extraction =
  match e with
  | App f [x] ->
    (match f.int_params with
     | [w; h; l] ->
       if f.interp = Some op_extract && w > 0 && w <= 4096 &&
          l >= 0 && h >= l && h < w && get_sort x = bv_sort w &&
          f.domain = [bv_sort w] && f.range = bv_sort (h - l + 1)
       then Some { source_width = w; high = h; low = l; operand = x } else None
     | _ -> None)
  | _ -> None

let concat_parts (e:expr) : option concatenation =
  match e with
  | App f [x; y] ->
    (match f.int_params with
     | [m; n] ->
       if f.interp = Some op_concat && m > 0 && n > 0 && m + n <= 4096 &&
          get_sort x = bv_sort m && get_sort y = bv_sort n &&
          f.domain = [bv_sort m; bv_sort n] && f.range = bv_sort (m + n)
       then Some { left_width = m; right_width = n; left = x; right = y } else None
     | _ -> None)
  | _ -> None

type zero_extension = {
  input_width: pos;
  extra_width: nat;
  argument: expr
}

let zero_extend_parts (e:expr) : option zero_extension =
  match e with
  | App f [x] ->
    (match f.int_params with
     | [w; k] ->
       if f.interp = Some op_zero_extend && w > 0 && k >= 0 && w + k <= 4096 &&
          f.domain = [bv_sort w] && f.range = bv_sort (w + k) && get_sort x = bv_sort w
       then Some { input_width = w; extra_width = k; argument = x } else None
     | _ -> None)
  | _ -> None

let word_parts (e:expr) : option (pos & list expr) =
  match e with
  | App f args ->
    (match f.int_params with
     | [w] ->
       if w > 0 && w <= 4096 && w = L.length args && f.interp = Some op_mkbv &&
          f.range = bv_sort w && f.domain = L.map (fun _ -> bool_sort) args &&
          L.for_all (fun a -> get_sort a = bool_sort) args
       then Some (w, args) else None
     | _ -> None)
  | _ -> None

let rec bits_number (bs:list bool) : Tot nat (decreases bs) =
  match bs with [] -> 0 | b :: rest -> (if b then 1 else 0) + 2 * bits_number rest

let calculate (width:pos) (op:decl_kind) (xs:list (U.uint_t width)) : U.uint_t width =
  match xs with
  | [x] -> if op = op_not then U.lognot x else U.sub_mod 0 x
  | [x; y] ->
    if op = op_and then U.logand x y
    else if op = op_or then U.logor x y
    else if op = op_xor then U.logxor x y
    else if op = op_add then U.add_mod x y
    else if op = op_mul then U.mul_mod x y
    else if op = op_udiv then (if y = 0 then U.ones width else U.udiv x y)
    else if op = op_urem then (if y = 0 then x else U.mod x y)
    else if op = op_shl then U.shift_left x y
    else if op = op_lshr then U.shift_right x y
    else U.sub_mod x y
  | _ -> 0

let nary_operation (f:func_decl) (args:list expr) : option (pos & decl_kind) =
  match f.int_params, f.interp with
  | [width], Some op ->
    if width > 0 && width <= 4096 && f.range = bv_sort width &&
       sorts_match args f.domain && f.domain = L.map (fun _ -> bv_sort width) args &&
       (op = op_add || op = op_mul) && L.length args >= 3
    then Some (width, op) else None
  | _, _ -> None

let rec calculate_nary (width:pos) (op:decl_kind) (xs:list (U.uint_t width))
  : Tot (U.uint_t width) (decreases xs) =
  match xs with
  | [] -> 0
  | [x] -> x
  | x :: y :: rest ->
    if op = op_add then U.add_mod x (calculate_nary width op (y :: rest))
    else U.mul_mod x (calculate_nary width op (y :: rest))

let literal (width:pos) (n:int) : expr =
  App { decl_name = "bv"; domain = []; range = bv_sort width;
        interp = Some op_numeral; int_params = [width; n] } []

let rec constants (width:pos) (args:list expr) : Tot (option (list (U.uint_t width))) (decreases args) =
  match args with
  | [] -> Some []
  | a :: rest ->
    (match numeral a, constants width rest with
     | Some (w, n), Some ns -> if w = width then Some (n :: ns) else None
     | _, _ -> None)

let simple (width:pos) (op:decl_kind) (args:list expr) : option expr =
  match args with
  | [App f [x]] ->
    if (op = op_not || op = op_neg) && operation f [x] = Some (width, op)
    then Some x else None
  | [x; y] ->
    if x = y && (op = op_and || op = op_or) then Some x
    else if x = y && (op = op_xor || op = op_sub) then Some (literal width 0)
    else (match numeral y with
          | Some (w, n) ->
            if w <> width then None
            else if n = 0 && (op = op_or || op = op_xor || op = op_add ||
                              op = op_sub || op = op_urem || op = op_shl ||
                              op = op_lshr) then Some x
            else if n = 0 && (op = op_and || op = op_mul) then Some y
            else if n = 0 && op = op_udiv then Some (literal width (U.ones width))
            else if n = 1 && (op = op_mul || op = op_udiv) then Some x
            else if n = 1 && op = op_urem then Some (literal width 0)
            else None
          | None -> None)
  | _ -> None

(* Z3BvExtract.arith and Z3BvAddNormalize's executable normalizer. *)
let slice (w:pos) (h l:nat) (x y:expr) : bool =
  h < w && l <= h &&
  (match extract_parts y with
   | None -> false
   | Some s ->
     (s.source_width = w && s.high = h && s.low = l && s.operand = x) ||
     (match extract_parts x with
      | None -> false
      | Some t ->
        t.high - t.low + 1 = w && s.source_width = t.source_width &&
        s.high = h + t.low && s.low = l + t.low && s.operand = t.operand))

let rec slices (w:pos) (h:nat) (xs ys:list expr) : Tot bool (decreases xs) =
  match xs, ys with
  | [], [] -> true
  | x :: xs', y :: ys' -> slice w h 0 x y && slices w h xs' ys'
  | _, _ -> false

let arith (f:func_decl) (args:list expr) : option (pos & decl_kind) =
  match operation f args with
  | Some (w, op) -> if op = op_add || op = op_mul then Some (w, op) else None
  | None -> nary_operation f args

let distribute (a b:expr) : bool =
  match extract_parts a with
  | None -> false
  | Some s ->
    s.low = 0 &&
    (match s.operand, b with
     | App f xs, App g ys ->
       (match arith f xs, arith g ys with
        | Some (w, op), Some (k, op') ->
          w = s.source_width && k = s.high + 1 && op = op' && slices w s.high xs ys
        | _, _ -> false)
     | _, _ -> false)

let piece (w:pos) (h l:nat) (x y:expr) : bool =
  (l = 0 && h + 1 = w && y = x) || slice w h l x y

let concatenated (a b:expr) : bool =
  match extract_parts a with
  | None -> false
  | Some s ->
    (match concat_parts s.operand with
     | None -> false
     | Some c ->
       let m = c.left_width in
       let n = c.right_width in
       s.source_width = m + n &&
       (if s.high < n then piece n s.high s.low c.right b
        else if n <= s.low then piece m (s.high - n) (s.low - n) c.left b
        else (match concat_parts b with
              | None -> false
              | Some d ->
                d.left_width = s.high - n + 1 && d.right_width = n - s.low &&
                piece m (s.high - n) 0 c.left d.left &&
                piece n (n - 1) s.low c.right d.right)))

let max_nodes : nat = 512

let add_width (f:func_decl) (args:list expr) : option pos =
  match arith f args with
  | Some (w, op) -> if op = op_add then Some w else None
  | None -> None

let reserved (f:func_decl) : bool = f.interp = Some op_numeral || f.interp = Some op_add

let rec summands (w:pos) (e:expr) : Tot (option (int & list expr)) (decreases e) =
  match numeral e with
  | Some (q, n) -> if q = w then Some (n, []) else None
  | None ->
    (match e with
     | App f args ->
       (match add_width f args with
        | Some q -> if q = w then summands_args w args else None
        | None -> if reserved f || get_sort e <> bv_sort w then None else Some (0, [e]))
     | _ -> None)

and summands_args (w:pos) (args:list expr) : Tot (option (int & list expr)) (decreases args) =
  match args with
  | [] -> Some (0, [])
  | a :: rest ->
    (match summands w a, summands_args w rest with
     | Some (n, xs), Some (m, ys) -> Some (n + m, L.append xs ys)
     | _, _ -> None)

let own_width (e:expr) : option pos =
  match numeral e with
  | Some (w, _) -> Some w
  | None -> (match e with App f args -> add_width f args | _ -> None)

let common_width (a b:expr) : option pos =
  match own_width a with
  | Some w -> Some w
  | None -> own_width b

let same_sum (w:pos) (a b:expr) : bool =
  match summands w a, summands w b with
  | Some (n, xs), Some (m, ys) -> n % pow2 w = m % pow2 w && xs = ys
  | _, _ -> false

let equivalent (a b:expr) : bool =
  if not (Some? (expression_budget max_nodes a) && Some? (expression_budget max_nodes b)) then false
  else if not (D.scoped [] a && D.scoped [] b) then false
  else match common_width a b with
       | Some w -> same_sum w a b
       | None -> false

(* Executable word constructors and recognizers, from Z3BvWord. *)
let rec numeral_bits (width:nat) (n:nat) : Tot (list expr) (decreases width) =
  if width = 0 then []
  else (if n % 2 = 0 then R.false_expr else R.true_expr) :: numeral_bits (width - 1) (n / 2)

let parts (e:expr) : option (pos & list expr) =
  match word_parts e with
  | Some p -> Some p
  | None ->
    (match numeral e with
     | Some (width, n) -> Some (width, numeral_bits width n)
     | None -> None)

let word (args:list expr) : expr =
  App { decl_name = "mkbv"; domain = L.map (fun _ -> bool_sort) args;
        range = bv_sort (L.length args); interp = Some op_mkbv;
        int_params = [L.length args] } args

let rec constant_bits (args:list expr) : Tot (option (list bool)) (decreases args) =
  match args with
  | [] -> Some []
  | a :: rest ->
    if a <> R.true_expr && a <> R.false_expr then None
    else (match constant_bits rest with
      | Some bs -> Some ((a = R.true_expr) :: bs)
      | None -> None)

let rec bit_equalities (xs ys:list expr) : Tot (list expr) (decreases xs) =
  match xs, ys with
  | x :: rest, y :: tail -> R.mk_eq_expr x y :: bit_equalities rest tail
  | _, _ -> []

let equality_rewrite (e:expr) : option expr =
  match e with
  | App f [a; b] ->
    if f <> R.eq_decl (get_sort a) || get_sort a <> get_sort b then None
    else (match parts a, parts b with
      | Some (w, xs), Some (w', ys) ->
        if w <> w' then None
        else let eqs = bit_equalities xs ys in
          Some (App (R.and_decl eqs) eqs)
      | _, _ -> None)
  | _ -> None

let literal_equivalent (a b:expr) : bool =
  match word_parts a, numeral b with
  | Some (w, args), Some (w', n) ->
    w = w' && (match constant_bits args with Some bs -> bits_number bs = n | None -> false)
  | _, _ -> false

let extract_rewrite (e:expr) : option expr =
  match extract_parts e with
  | Some s ->
    (match parts s.operand with
     | Some (width, args) ->
       if width <> s.source_width || s.high >= L.length args then None
       else let _, tail = L.splitAt s.low args in
         Some (word (fst (L.splitAt (s.high - s.low + 1) tail)))
     | None -> None)
  | None -> None

let concat_rewrite (e:expr) : option expr =
  match concat_parts e with
  | Some c ->
    (match parts c.left, parts c.right with
     | Some (w, xs), Some (w', ys) ->
       if w = c.left_width && w' = c.right_width then Some (word (ys @ xs)) else None
     | _, _ -> None)
  | None -> None

let bit_number (b:bool) : nat = if b then 1 else 0

let sum_bit (a b carry:expr) : expr =
  App BS.boolean_xor_decl [App BS.boolean_xor_decl [a; b]; carry]

let carry_bit (a b carry:expr) : expr =
  App BS.boolean_ite_decl [R.mk_eq_expr a b; a; carry]

let rec add_bits (carry:expr) (xs ys:list expr)
  : Tot (list expr & expr) (decreases xs) =
  match xs, ys with
  | a :: rest, b :: tail ->
    let sums, overflow = add_bits (carry_bit a b carry) rest tail in
    sum_bit a b carry :: sums, overflow
  | _, _ -> [], carry

let rec add_values (carry:bool) (xs ys:list bool)
  : Tot (list bool & bool) (decreases xs) =
  match xs, ys with
  | a :: rest, b :: tail ->
    let sums, overflow = add_values (if a = b then a else carry) rest tail in
    ((a <> b) <> carry) :: sums, overflow
  | _, _ -> [], carry

let addition_rewrite (e:expr) : option expr =
  match e with
  | App f [a; b] ->
    (match operation f [a; b], parts a, parts b with
     | Some (width, op), Some (w, xs), Some (w', ys) ->
       if op = op_add && w = width && w' = width
       then Some (word (fst (add_bits R.false_expr xs ys))) else None
     | _, _, _ -> None)
  | _ -> None

let concat (m n:pos) (x y:expr) : expr =
  App { decl_name = "concat"; domain = [bv_sort m; bv_sort n];
        range = bv_sort (m + n); interp = Some op_concat; int_params = [m; n] } [x; y]

let concat_association_rewrite (e:expr) : option expr =
  match concat3_parts e with
  | Some (c:concatenation3) ->
    Some (concat c.width1 (c.width2 + c.width3) c.first
      (concat c.width2 c.width3 c.second c.third))
  | None ->
    (match concat_parts e with
     | Some (c:concatenation) ->
       (match concat_parts c.left with
        | Some (left:concatenation) ->
          if c.left_width <> left.left_width + left.right_width then None
          else Some (concat left.left_width (left.right_width + c.right_width) left.left
            (concat left.right_width c.right_width left.right c.right))
        | None -> None)
     | None -> None)

let concat_numeral_equality (a b:expr) : option expr =
  match concat_parts a, numeral b with
  | Some (c:concatenation), Some (width, n) ->
    if width <> c.left_width + c.right_width then None
    else let eqs =
      [R.mk_eq_expr c.right (literal c.right_width (n % pow2 c.right_width));
       R.mk_eq_expr c.left (literal c.left_width (n / pow2 c.right_width))] in
      Some (App (R.and_decl eqs) eqs)
  | _, _ -> None

let concat_equality_rewrite (e:expr) : option expr =
  match e with
  | App f [a; b] ->
    if f <> R.eq_decl (get_sort a) || get_sort a <> get_sort b then None
    else (match concat_numeral_equality a b with
      | Some result -> Some result
      | None -> concat_numeral_equality b a)
  | _ -> None

let concat3_rewrite (e:expr) : option expr =
  match concat3_parts e with
  | Some c -> Some (concat c.width1 (c.width2 + c.width3) c.first
      (concat c.width2 c.width3 c.second c.third))
  | None -> None

let complement (width:pos) (x:expr) : expr =
  App { decl_name = "bvnot"; domain = [bv_sort width]; range = bv_sort width;
        interp = Some op_not; int_params = [width] } [x]

let not_concat_rewrite (e:expr) : option expr =
  match e with
  | App f [x] ->
    (match operation f [x], concat_parts x with
     | Some (width, op), Some (c:concatenation) ->
       if op = op_not && width = c.left_width + c.right_width then
         Some (concat c.left_width c.right_width
           (complement c.left_width c.left) (complement c.right_width c.right))
       else None
     | _, _ -> None)
  | _ -> None

let word_rewrite (e:expr) : option expr =
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

let rec bits_equivalent (xs ys:list expr) : Tot bool (decreases xs) =
  match xs, ys with
  | [], [] -> true
  | x :: rest, y :: tail -> X.boolean_equiv 64 8 x y && bits_equivalent rest tail
  | _, _ -> false

let word_equivalent (a b:expr) : bool =
  match parts a, parts b with
  | Some (w, xs), Some (w', ys) -> w = w' && bits_equivalent xs ys
  | _, _ -> false

let projection_operand (width:pos) (source:expr) (bit:nat) : expr =
  if width = 1 && bit = 0 then source
  else App { decl_name = "extract"; domain = [bv_sort width];
             range = bv_sort 1; interp = Some op_extract;
             int_params = [width; bit; bit] } [source]

let projection (width:pos) (source:expr) (bit:nat) : expr =
  App { decl_name = "bvule"; domain = [bv_sort 1; bv_sort 1];
        range = bool_sort; interp = Some op_ule; int_params = [1] }
      [literal 1 1; projection_operand width source bit]

let rec projection_bits (width:pos) (source:expr) (start count:nat)
  : Tot (list expr) (decreases count) =
  if count = 0 then []
  else projection width source start :: projection_bits width source (start + 1) (count - 1)

let rec matching_projections (width:pos) (source:expr) (start count:nat) (args:list expr)
  : Tot bool (decreases args) =
  match args with
  | [] -> count = 0
  | a :: rest ->
    count > 0 && a = projection width source start &&
      matching_projections width source (start + 1) (count - 1) rest

let projection_equivalent (a b:expr) : bool =
  match word_parts b with
  | Some (width, args) ->
    get_sort a = bv_sort width && matching_projections width a 0 width args
  | None -> false

let word_equivalent_all (a b:expr) : bool =
  D.scoped [] a && D.scoped [] b &&
    (literal_equivalent a b || literal_equivalent b a || word_equivalent a b ||
     projection_equivalent a b || projection_equivalent b a)

(* Z3BvOrder.slice is named order_slice here: Z3BvExtract.slice already
   occupies that identifier in this shared syntax module. *)
let unsigned (width:pos) (op:decl_kind) (a b:expr) : expr =
  App { decl_name = if op = op_ult then "bvult" else if op = op_ule then "bvule" else "bvuge";
        domain = [bv_sort width; bv_sort width]; range = bool_sort;
        interp = Some op; int_params = [width] } [a; b]

let compare_step (a b lower:expr) : expr =
  App BS.boolean_ite_decl [R.mk_eq_expr a b; lower; R.mk_not_expr a]

let rec le_values (lower:bool) (xs ys:list bool) : Tot bool (decreases xs) =
  match xs, ys with
  | a :: rest, b :: tail -> le_values (if a = b then lower else not a) rest tail
  | _, _ -> lower

let rec le_bits (lower:expr) (xs ys:list expr) : Tot expr (decreases xs) =
  match xs, ys with
  | a :: rest, b :: tail -> le_bits (compare_step a b lower) rest tail
  | _, _ -> lower

let term_ite_decl (s:sort) : func_decl =
  { decl_name = "if"; domain = [bool_sort; s; s]; range = s;
    interp = Some T.op_ite; int_params = [] }

let ite_parts (e:expr) : option (expr & expr & expr) =
  match e with
  | App f [c; t; u] ->
    if get_sort c = bool_sort && get_sort t = get_sort u &&
       f = term_ite_decl (get_sort t) then Some (c, t, u) else None
  | _ -> None

let numeral_branch (guard other target:expr) (equal:bool) : expr =
  let args = [guard; R.mk_eq_expr other target] in
  App (if equal then R.or_decl args else R.and_decl args) args

let mixed_comparison (source target:expr) : option expr =
  match ite_parts source, numeral target with
  | Some (c, t, u), Some (w, n) ->
    (match numeral t with
     | Some (w', k) ->
       if w <> w' || get_sort u <> bv_sort w then None
       else Some (numeral_branch (if n = k then c else R.mk_not_expr c) u target (n = k))
     | None ->
       (match numeral u with
        | Some (w', k) ->
          if w <> w' || get_sort t <> bv_sort w then None
          else Some (numeral_branch (if n = k then R.mk_not_expr c else c) t target (n = k))
        | None -> None))
  | _, _ -> None

let mixed_equality (e:expr) : option expr =
  match e with
  | App f [a; b] ->
    if f <> R.eq_decl (get_sort a) || get_sort a <> get_sort b then None
    else (match mixed_comparison a b with Some r -> Some r | None -> mixed_comparison b a)
  | _ -> None

let rec needed_width (width:pos) (n:nat{n < pow2 width})
  : Tot (m:pos{m <= width /\ n < pow2 m}) (decreases width) =
  if width > 1 && n < pow2 (width - 1) then needed_width (width - 1) n else width

let order_slice (width:pos) (high low:nat) (x:expr) : expr =
  App { decl_name = "extract"; domain = [bv_sort width]; range = bv_sort (high - low + 1);
        interp = Some op_extract; int_params = [width; high; low] } [x]

let alternative (upper zero lower:expr) : expr =
  let args = [R.mk_not_expr (R.mk_eq_expr upper zero); lower] in
  App (R.or_decl args) args

let split_formula (width:pos) (m:pos{m < width}) (n:nat) (x:expr) : expr =
  alternative (order_slice width (width - 1) m x) (literal (width - m) 0)
    (unsigned m op_ule (literal m n) (order_slice width (m - 1) 0 x))

let split_rewrite (e:expr) : option expr =
  match unsigned_parts e with
  | Some c ->
    (match numeral c.lhs with
     | Some (w, n) ->
       if c.relation <> op_ule || w <> c.width then None
       else let m = needed_width w n in
         if m < w then Some (split_formula w m n c.rhs) else None
     | None -> None)
  | None -> None

let order_rewrite (e:expr) : option expr =
  match unsigned_parts e with
  | Some c ->
    if c.lhs = c.rhs then Some (if c.relation = op_ult then R.false_expr else R.true_expr)
    else if c.relation = op_ult then Some (R.mk_not_expr (unsigned c.width op_ule c.rhs c.lhs))
    else if c.relation = op_uge then Some (unsigned c.width op_ule c.rhs c.lhs)
    else if numeral c.lhs = Some (c.width, 0) then Some R.true_expr
    else (match parts c.lhs, parts c.rhs with
      | Some (w, xs), Some (w', ys) ->
        if w = c.width && w' = c.width then Some (le_bits R.true_expr xs ys) else None
      | _, _ -> split_rewrite e)
  | None -> None

let order_rewrite_all (e:expr) : option expr =
  if not (D.scoped [] e) then None
  else match mixed_equality e with Some r -> Some r | None -> order_rewrite e

(* Remaining Z3BvExtract predicates; slice, slices, arith, distribute,
   piece and concatenated above retain their original definitions. *)
let conditional (a b:expr) : bool =
  match extract_parts a with
  | None -> false
  | Some s ->
    (match ite_parts s.operand, ite_parts b with
     | Some (c, t, e), Some (c', t', e') ->
       c = c' && slice s.source_width s.high s.low t t' &&
       slice s.source_width s.high s.low e e'
     | _, _ -> false)

let extract_check (a b:expr) : bool =
  (distribute a b || conditional a b || concatenated a b) && D.scoped [] a && D.scoped [] b

(* Exact ground-expression and bounded exhaustive evaluator from
   Z3StandardModel and Z3BvExhaustive. *)
let rec ground (e:expr) : Tot bool (decreases e) =
  match e with
  | App _ args -> ground_args args
  | _ -> false
and ground_args (args:list expr) : Tot bool (decreases args) =
  match args with
  | [] -> true
  | a :: rest -> ground a && ground_args rest

let closed_ground (e:expr) : bool = ground e && D.scoped [] e
let max_width : pos = 4096
let max_leaf_bits : nat = 12
type leaf_table = list (expr & pos)

let rec index_of (x:expr & pos) (tbl:leaf_table) : Tot (option nat) (decreases tbl) =
  match tbl with
  | [] -> None
  | y :: rest ->
    if y = x then Some 0
    else (match index_of x rest with Some k -> Some (k + 1) | None -> None)

let exhaustive_reserved (f:func_decl) : bool =
  f.interp = Some op_numeral || f.interp = Some op_extract ||
  f.interp = Some op_concat || f.interp = Some op_zero_extend ||
  f.interp = Some op_add

let leaf (tbl:leaf_table) (v:nat -> int) (w:pos) (e:expr) : option int =
  match e with
  | App f _ ->
    if get_sort e = bv_sort w && not (exhaustive_reserved f)
    then (match index_of (e, w) tbl with Some k -> Some (v k) | None -> None)
    else None
  | _ -> None

let rec eval_bv (tbl:leaf_table) (v:nat -> int) (w:pos) (e:expr) : Tot (option int) (decreases e) =
  match numeral e with
  | Some (q, n) -> if q = w then Some n else None
  | None ->
    (match e with
     | App f [x] ->
       (match extract_parts e, zero_extend_parts e with
        | Some s, _ ->
          if s.high - s.low + 1 = w then
            (match eval_bv tbl v s.source_width x with
             | Some a -> Some ((a / pow2 s.low) % pow2 w)
             | None -> None)
          else None
        | None, Some z ->
          if z.input_width + z.extra_width = w then eval_bv tbl v z.input_width x else None
        | None, None -> leaf tbl v w e)
     | App f [x; y] ->
       (match concat_parts e, operation f [x; y] with
        | Some c, _ ->
          if c.left_width + c.right_width = w then
            (match eval_bv tbl v c.left_width x, eval_bv tbl v c.right_width y with
             | Some a, Some b -> Some (a * pow2 c.right_width + b)
             | _, _ -> None)
          else None
        | None, Some (q, op) ->
          if q = w && op = op_add then
            (match eval_bv tbl v w x, eval_bv tbl v w y with
             | Some a, Some b -> Some ((a + b) % pow2 w)
             | _, _ -> None)
          else leaf tbl v w e
        | None, None -> leaf tbl v w e)
     | _ -> leaf tbl v w e)

let bv_width (e:expr) : option pos =
  match numeral e with
  | Some (w, _) -> Some w
  | None ->
    (match extract_parts e, zero_extend_parts e, concat_parts e with
     | Some s, _, _ -> Some (s.high - s.low + 1)
     | _, Some z, _ -> Some (z.input_width + z.extra_width)
     | _, _, Some c -> Some (c.left_width + c.right_width)
     | _, _, _ ->
       (match e with
        | App f [x; y] ->
          (match operation f [x; y] with
           | Some (w, op) -> if op = op_add then Some w else None
           | None -> None)
        | _ -> None))

let equal_width (a b:expr) : option pos =
  match bv_width a with
  | Some w -> Some w
  | None -> bv_width b

let boolean_pair (a b:expr) : bool = get_sort a = bool_sort && get_sort b = bool_sort

let rec eval_bool (tbl:leaf_table) (v:nat -> int) (e:expr) : Tot (option bool) (decreases e) =
  match e with
  | App f args ->
    if get_sort e <> bool_sort then None
    else if C.canonical_true f && args = [] then Some true
    else if C.canonical_false f && args = [] then Some false
    else if C.canonical_not f then
      (match args with
       | [a] -> (match eval_bool tbl v a with Some b -> Some (not b) | None -> None)
       | _ -> None)
    else if C.canonical_or f then eval_or tbl v args
    else if C.canonical_and f then eval_and tbl v args
    else if C.canonical_eq f then
      (match args with
       | [a; b] ->
         if boolean_pair a b then
           (match eval_bool tbl v a, eval_bool tbl v b with
            | Some x, Some y -> Some (x = y)
            | _, _ -> None)
         else
           (match equal_width a b with
            | Some w ->
              (match eval_bv tbl v w a, eval_bv tbl v w b with
               | Some x, Some y -> Some (x = y)
               | _, _ -> None)
            | None -> None)
       | _ -> None)
    else
      (match args with
       | [a; b] ->
         (match unsigned_parts e with
          | Some c ->
            (match eval_bv tbl v c.width a, eval_bv tbl v c.width b with
             | Some x, Some y -> Some (unsigned_value c.relation x y)
             | _, _ -> None)
          | None -> None)
       | _ -> None)
  | _ -> None

and eval_or (tbl:leaf_table) (v:nat -> int) (args:list expr) : Tot (option bool) (decreases args) =
  match args with
  | [] -> Some false
  | a :: rest ->
    (match eval_bool tbl v a, eval_or tbl v rest with
     | Some x, Some y -> Some (x || y)
     | _, _ -> None)

and eval_and (tbl:leaf_table) (v:nat -> int) (args:list expr) : Tot (option bool) (decreases args) =
  match args with
  | [] -> Some true
  | a :: rest ->
    (match eval_bool tbl v a, eval_and tbl v rest with
     | Some x, Some y -> Some (x && y)
     | _, _ -> None)

let add_leaf (tbl:leaf_table) (x:expr & pos) : leaf_table =
  if L.mem x tbl then tbl else L.append tbl [x]

let rec leaves_bv (tbl:leaf_table) (w:pos) (e:expr) : Tot leaf_table (decreases e) =
  match numeral e with
  | Some _ -> tbl
  | None ->
    (match e with
     | App f [x] ->
       (match extract_parts e, zero_extend_parts e with
        | Some s, _ -> leaves_bv tbl s.source_width x
        | None, Some z -> leaves_bv tbl z.input_width x
        | None, None -> add_leaf tbl (e, w))
     | App f [x; y] ->
       (match concat_parts e, operation f [x; y] with
        | Some c, _ -> leaves_bv (leaves_bv tbl c.left_width x) c.right_width y
        | None, Some (q, op) ->
          if op = op_add then leaves_bv (leaves_bv tbl q x) q y else add_leaf tbl (e, w)
        | None, None -> add_leaf tbl (e, w))
     | _ -> add_leaf tbl (e, w))

let rec leaves_bool (tbl:leaf_table) (e:expr) : Tot leaf_table (decreases e) =
  match e with
  | App f args ->
    if C.canonical_not f || C.canonical_or f || C.canonical_and f then leaves_bools tbl args
    else if C.canonical_eq f then
      (match args with
       | [a; b] ->
         if boolean_pair a b then leaves_bool (leaves_bool tbl a) b
         else (match equal_width a b with
               | Some w -> leaves_bv (leaves_bv tbl w a) w b
               | None -> tbl)
       | _ -> tbl)
    else
      (match args with
       | [a; b] ->
         (match unsigned_parts e with
          | Some c -> leaves_bv (leaves_bv tbl c.width a) c.width b
          | None -> tbl)
       | _ -> tbl)
  | _ -> tbl

and leaves_bools (tbl:leaf_table) (args:list expr) : Tot leaf_table (decreases args) =
  match args with
  | [] -> tbl
  | a :: rest -> leaves_bools (leaves_bool tbl a) rest

let rec within_bits (tbl:leaf_table) (acc:nat) : Tot bool (decreases tbl) =
  if acc > max_leaf_bits then false
  else match tbl with
       | [] -> true
       | (_, w) :: rest -> within_bits rest (acc + w)

let closed_leaf (x:expr & pos) : bool =
  closed_ground (fst x) && snd x <= max_width && get_sort (fst x) = bv_sort (snd x)

let rec widths (tbl:leaf_table) : Tot (list pos) (decreases tbl) =
  match tbl with
  | [] -> []
  | (_, w) :: rest -> w :: widths rest

let with_head (f:list int -> bool) (x:int) (r:list int) : bool = f (x :: r)

let rec for_all_vectors (ws:list pos) (f:list int -> bool) : Tot bool (decreases %[ws; 0; 0]) =
  match ws with
  | [] -> f []
  | w :: rest -> for_all_heads rest (pow2 w) f

and for_all_heads (rest:list pos) (k:nat) (f:list int -> bool) : Tot bool (decreases %[rest; 1; k]) =
  if k = 0 then true
  else for_all_vectors rest (with_head f (k - 1)) && for_all_heads rest (k - 1) f

let vector_value (r:list int) : nat -> int =
  fun k -> if k < L.length r then L.index r k else 0

let clause_true (tbl:leaf_table) (e:expr) (r:list int) : bool =
  eval_bool tbl (vector_value r) e = Some true

let exhaustive_valid (e:expr) : bool =
  if not (Some? (expression_budget max_nodes e)) then false
  else if not (closed_ground e) then false
  else
    let tbl = leaves_bool [] e in
    if not (within_bits tbl 0) then false
    else if not (L.for_all closed_leaf tbl) then false
    else for_all_vectors (widths tbl) (clause_true tbl e)

let exhaustive_equivalent (a b:expr) : bool = exhaustive_valid (R.mk_eq_expr a b)
