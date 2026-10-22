module Z3BvLemma

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module D = Z3Definitions
module L = FStar.List.Tot
module U = FStar.UInt
module AR = Z3ArrayRewrite

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

let bv_sort (width:int) : sort = BaseSort ("BV" ^ Prims.string_of_int width)

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
          op = op_mul || op = op_sub || op = op_udiv || op = op_urem) && L.length args = 2))
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

let bit_values (i:interpretation value) (rho:env value) (args:list expr) : list bool =
  L.map (fun e -> Z3BooleanRewrite.bool_value (eval i e rho)) args

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

let words (width:pos) (project:pos -> value -> int) (vs:list value) : list (U.uint_t width) =
  L.map (fun v -> U.to_uint_t width (project width v)) vs

(* Closed terms avoid imposing bit-vector typing on arbitrary binder environments. *)
let bv_model (i:interpretation value) (project:pos -> value -> int) : prop =
  (forall (width:pos) (a b:expr) (rho:env value).
    D.scoped [] a /\ D.scoped [] b /\ get_sort a == bv_sort width /\ get_sort b == bv_sort width ==>
    ((eval i a rho == eval i b rho <==> project width (eval i a rho) == project width (eval i b rho)) /\
     0 <= project width (eval i a rho) /\ project width (eval i a rho) < pow2 width)) /\
  (forall (e:expr) (rho:env value) (width:pos) (n:int).
    numeral e == Some (width, n) ==> project width (eval i e rho) == n) /\
  (forall (f:func_decl) (args:list expr) (rho:env value) (width:pos) (op:decl_kind).
    D.scoped [] (App f args) /\ operation f args == Some (width, op) ==>
    project width (eval i (App f args) rho) ==
    calculate width op (words width project (eval_args i args rho))) /\
  (forall (f:func_decl) (args:list expr) (rho:env value) (width:pos) (op:decl_kind).
    D.scoped [] (App f args) /\ nary_operation f args == Some (width, op) ==>
    project width (eval i (App f args) rho) ==
    calculate_nary width op (words width project (eval_args i args rho))) /\
  (forall (e:expr) (rho:env value) (s:extraction).
    D.scoped [] e /\ extract_parts e == Some s ==>
    project (s.high - s.low + 1) (eval i e rho) ==
      (project s.source_width (eval i s.operand rho) / pow2 s.low) %
      pow2 (s.high - s.low + 1)) /\
  (forall (e:expr) (rho:env value) (c:concatenation).
    D.scoped [] e /\ concat_parts e == Some c ==>
    project (c.left_width + c.right_width) (eval i e rho) ==
      project c.left_width (eval i c.left rho) * pow2 c.right_width +
      project c.right_width (eval i c.right rho)) /\
  (forall (e:expr) (rho:env value) (width:pos) (args:list expr).
    D.scoped [] e /\ word_parts e == Some (width, args) ==>
    project width (eval i e rho) == bits_number (bit_values i rho args)) /\
  (forall (e:expr) (rho:env value) (c:unsigned_comparison).
    D.scoped [] e /\ unsigned_parts e == Some c ==>
    eval i e rho == VBool (unsigned_value c.relation
      (project c.width (eval i c.lhs rho)) (project c.width (eval i c.rhs rho)))) /\
  (forall (e:expr) (rho:env value) (c:concatenation3).
    D.scoped [] e /\ concat3_parts e == Some c ==>
    project (c.width1 + c.width2 + c.width3) (eval i e rho) ==
      project c.width1 (eval i c.first rho) * pow2 (c.width2 + c.width3) +
      project c.width2 (eval i c.second rho) * pow2 c.width3 +
      project c.width3 (eval i c.third rho))

let literal (width:pos) (n:int) : expr =
  App { decl_name = "bv"; domain = []; range = bv_sort width;
        interp = Some op_numeral; int_params = [width; n] } []

let lemma_literal_shape (width:pos) (n:int)
  : Lemma (D.scoped [] (literal width n) /\ get_sort (literal width n) == bv_sort width)
  = ()

#push-options "--fuel 4 --ifuel 2"
let lemma_ite_shape (width:pos) (c t u:expr)
  : Lemma (requires D.scoped [] c /\ D.scoped [] t /\ D.scoped [] u /\
                    get_sort c == bool_sort /\
                    get_sort t == bv_sort width /\ get_sort u == bv_sort width)
          (ensures D.scoped [] (App (AR.term_ite_decl (get_sort t)) [c; t; u]) /\
                   get_sort (App (AR.term_ite_decl (get_sort t)) [c; t; u]) == get_sort t)
  = assert (sort_eq (get_sort c) bool_sort);
    assert (sort_eq (get_sort t) (bv_sort width));
    assert (sort_eq (get_sort u) (bv_sort width));
    assert (sorts_match [u] [bv_sort width]);
    assert (sorts_match [t; u] [bv_sort width; bv_sort width]);
    assert (sorts_match [c; t; u] [bool_sort; bv_sort width; bv_sort width]);
    assert (D.scoped_args [] [u]);
    assert (D.scoped_args [] [t; u]);
    assert (D.scoped_args [] [c; t; u])
#pop-options

let lemma_literal (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                  (width:pos) (n:int)
  : Lemma (requires bv_model i project /\ width <= 4096 /\ 0 <= n /\ n < pow2 width)
          (ensures project width (eval i (literal width n) rho) == n)
  = assert (numeral (literal width n) == Some (width, n))

let lemma_word (i:interpretation value) (rho:env value) (project:pos -> value -> int)
               (width:pos) (e:expr)
  : Lemma (requires bv_model i project /\ D.scoped [] e /\ get_sort e == bv_sort width)
          (ensures 0 <= project width (eval i e rho) /\
                   project width (eval i e rho) < pow2 width /\
                   U.to_uint_t width (project width (eval i e rho)) == project width (eval i e rho))
  = assert (0 <= project width (eval i e rho) /\ project width (eval i e rho) < pow2 width);
    FStar.Math.Lemmas.small_mod (project width (eval i e rho)) (pow2 width)

let lemma_operation (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                    (f:func_decl) (args:list expr) (width:pos) (op:decl_kind)
  : Lemma (requires bv_model i project /\ D.scoped [] (App f args) /\
                    operation f args == Some (width, op))
          (ensures project width (eval i (App f args) rho) ==
                   calculate width op (words width project (eval_args i args rho)))
  = ()

let lemma_reflect (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                  (width:pos) (a b:expr)
  : Lemma (requires bv_model i project /\ D.scoped [] a /\ D.scoped [] b /\
                    get_sort a == bv_sort width /\ get_sort b == bv_sort width /\
                    project width (eval i a rho) == project width (eval i b rho))
          (ensures eval i a rho == eval i b rho)
  = ()

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
                              op = op_sub || op = op_urem) then Some x
            else if n = 0 && (op = op_and || op = op_mul) then Some y
            else if n = 0 && op = op_udiv then Some (literal width (U.ones width))
            else if n = 1 && (op = op_mul || op = op_udiv) then Some x
            else if n = 1 && op = op_urem then Some (literal width 0)
            else None
          | None -> None)
  | _ -> None

let conditional_comparison (source target:expr) : option expr =
  match AR.ite_parts source with
  | Some (c, t, u) ->
    (match numeral t, numeral u, numeral target with
     | Some (w, n), Some (w', m), Some (w'', k) ->
       if w <> w' || w <> w'' || n = m then None
       else if n = k then Some c
       else if m = k then Some (mk_not_expr c)
       else None
     | _, _, _ -> None)
  | None -> None

let comparison (e:expr) : option expr =
  match e with
  | App f [a; b] ->
    if f <> eq_decl (get_sort a) || get_sort a <> get_sort b then None
    else (match numeral a, numeral b with
          | Some (width, n), Some (width', m) ->
            if width = width' then Some (if n = m then true_expr else false_expr) else None
          | _, _ ->
            (match conditional_comparison a b with
             | Some result -> Some result
             | None -> conditional_comparison b a))
  | _ -> None

let basic_rewrite (e:expr) : option expr =
  if not (D.scoped [] e) then None
  else if Some? (comparison e) then comparison e
  else match e with
  | App f args ->
    (match operation f args with
     | Some (width, op) ->
       (match constants width args with
        | Some ns -> Some (literal width (calculate width op ns))
        | None -> simple width op args)
     | None -> None)
  | _ -> None

let rec lemma_constants (i:interpretation value) (rho:env value)
                        (project:pos -> value -> int) (width:pos) (args:list expr)
                        (ns:list (U.uint_t width))
  : Lemma (requires bv_model i project /\ constants width args == Some ns)
          (ensures words width project (eval_args i args rho) == ns)
          (decreases args)
  = match args with
    | [] -> ()
    | a :: rest ->
      let w, n = Some?.v (numeral a) in
      lemma_constants i rho project width rest (Some?.v (constants width rest));
      assert (w == width);
      assert (project width (eval i a rho) == n);
      FStar.Math.Lemmas.small_mod n (pow2 width);
      assert (U.to_uint_t width (project width (eval i a rho)) == n)

let lemma_simple (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                 (width:pos) (op:decl_kind) (args:list expr) (result:expr)
  : Lemma (requires bv_model i project /\ D.scoped_args [] args /\
                    L.for_all (fun a -> get_sort a = bv_sort width) args /\
                    width <= 4096 /\ simple width op args == Some result)
          (ensures get_sort result == bv_sort width /\ D.scoped [] result /\
                   calculate width op (words width project (eval_args i args rho)) ==
                   project width (eval i result rho))
  = match args with
    | [App f [x]] ->
      lemma_word i rho project width x;
      lemma_operation i rho project f [x] width op;
      lemma_word i rho project width (App f [x]);
      if op = op_not then U.lognot_self #width (project width (eval i x rho))
    | [x; y] ->
      lemma_word i rho project width x;
      lemma_word i rho project width y;
      lemma_literal i rho project width 0;
      let a = project width (eval i x rho) in
      assert (0 <= a /\ a < pow2 width);
      FStar.Math.Lemmas.small_mod a (pow2 width);
      if x = y && op = op_and then U.logand_self #width a
      else if x = y && op = op_or then U.logor_self #width a
      else if x = y && op = op_xor then U.logxor_self #width a
      else if x = y && op = op_sub then ()
      else (match numeral y with
            | Some (_, n) ->
              FStar.Math.Lemmas.small_mod n (pow2 width);
              if n = 0 && op = op_and then U.logand_lemma_1 #width a
              else if n = 0 && op = op_or then U.logor_lemma_1 #width a
              else if n = 0 && op = op_xor then U.logxor_lemma_1 #width a
              else if n = 0 && op = op_udiv then
                lemma_literal i rho project width (U.ones width)
              else ()
            | None -> ())
    | _ -> ()

let lemma_conditional_comparison (i:interpretation value) (rho:env value)
                                (project:pos -> value -> int) (source target result:expr)
  : Lemma (requires bv_model i project /\ Z3BooleanRewrite.boolean_rewrite_model i /\
                    AR.term_ite_sound i /\ D.scoped [] source /\ D.scoped [] target /\
                    conditional_comparison source target == Some result)
          (ensures (eval i source rho == eval i target rho) <==> lit_true i rho result)
  = let c, t, u = Some?.v (AR.ite_parts source) in
    let width, n = Some?.v (numeral t) in
    let _, m = Some?.v (numeral u) in
    let _, k = Some?.v (numeral target) in
    assert (project width (eval i t rho) == n);
    assert (project width (eval i u rho) == m);
    assert (project width (eval i target rho) == k);
    assert ((eval i t rho == eval i target rho) <==> n = k);
    assert ((eval i u rho == eval i target rho) <==> m = k);
    match source with
    | App f [c; t; u] ->
      assert (eval i source rho ==
        (if Z3BooleanRewrite.bool_value (eval i c rho) then eval i t rho else eval i u rho));
      (match eval i c rho with VBool _ -> () | _ -> ())
    | _ -> ()

let lemma_basic_rewrite (i:interpretation value) (rho:env value)
                  (project:pos -> value -> int) (e result:expr)
  : Lemma (requires bv_model i project /\ Z3BooleanRewrite.boolean_rewrite_model i /\
                    AR.term_ite_sound i /\
                    basic_rewrite e == Some result)
          (ensures eval i e rho == eval i result rho)
  = if Some? (comparison e) then
      (match e with
       | App f [a; b] ->
         (match numeral a, numeral b with
          | Some (width, n), Some (_, m) ->
            assert (project width (eval i a rho) == n);
            assert (project width (eval i b rho) == m);
            if n = m then lemma_reflect i rho project width a b
          | _, _ ->
            if Some? (conditional_comparison a b) then
              lemma_conditional_comparison i rho project a b result
            else lemma_conditional_comparison i rho project b a result);
         (match eval i e rho, eval i result rho with
          | VBool _, VBool _ -> ()
          | _, _ -> ())
       | _ -> ())
    else match e with
    | App f args ->
      (match operation f args with
       | Some (width, op) ->
         (match constants width args with
          | Some ns ->
            lemma_constants i rho project width args ns;
            lemma_literal i rho project width (calculate width op ns)
          | None ->
            lemma_simple i rho project width op args result);
         assert (D.scoped [] result /\ get_sort result == bv_sort width);
         lemma_operation i rho project f args width op;
         lemma_reflect i rho project width e result
       | None -> ())
    | _ -> ()

let unary (width:pos) (op:decl_kind) (x:expr) : expr =
  App { decl_name = "bvnot"; domain = [bv_sort width]; range = bv_sort width;
        interp = Some op; int_params = [width] } [x]

let bit_numeral (e:expr) : option int =
  match numeral e with Some (w, n) -> if w = 1 then Some n else None | None -> None

let bit_test (e:expr) : option (expr & int) =
  match e with
  | App f [x; n] ->
    if f <> eq_decl (get_sort x) || get_sort x <> get_sort n then None
    else (match bit_numeral n, bit_numeral x with
      | Some k, _ -> Some (x, k)
      | _, Some k -> Some (n, k)
      | _, _ -> None)
  | _ -> None

let bit_conditional (e:expr) : option expr =
  match AR.ite_parts e with
  | Some (c, t, u) ->
    (match bit_numeral t, bit_numeral u, bit_test c with
     | Some n, Some m, Some (x, k) ->
       if n = m then None
       else Some (if n = k then x else unary 1 op_not x)
     | _, _, _ -> None)
  | None -> None

let not_conditional (e:expr) : option expr =
  match e with
  | App f [a] ->
    (match operation f [a], AR.ite_parts a with
     | Some (width, op), Some (c, t, u) ->
       if op <> op_not then None
       else (match numeral t, numeral u with
         | Some (w, n), Some (w', m) ->
           if w <> width || w' <> width then None
           else Some (App (AR.term_ite_decl (bv_sort width))
             [c; literal width (U.lognot #width n); literal width (U.lognot #width m)])
         | _, _ -> None)
     | _, _ -> None)
  | _ -> None

let not_comparison (source target:expr) : option expr =
  match source with
  | App f [x] ->
    (match operation f [x], numeral target with
     | Some (width, op), Some (w, n) ->
       if op = op_not && width = w
       then Some (mk_eq_expr x (literal width (U.lognot #width n))) else None
     | _, _ -> None)
  | _ -> None

let encoded_comparison (source target:expr) : option expr =
  match AR.ite_parts target with
  | Some (c, t, u) ->
    (match bit_numeral t, bit_numeral u with
     | Some n, Some m ->
       if n = m || get_sort source <> bv_sort 1 then None
       else Some (mk_eq_expr (mk_eq_expr source t) c)
     | _, _ -> None)
  | None -> None

let comparison_bridge (e:expr) : option expr =
  match e with
  | App f [a; b] ->
    if f <> eq_decl (get_sort a) || get_sort a <> get_sort b then None
    else (match not_comparison a b, not_comparison b a,
                encoded_comparison a b, encoded_comparison b a with
      | Some r, _, _, _ | _, Some r, _, _ |
        _, _, Some r, _ | _, _, _, Some r -> Some r
      | _, _, _, _ ->
        if get_sort a = bv_sort 1 && numeral a = None && numeral b = None
        then Some (mk_eq_expr (mk_eq_expr a (literal 1 1)) (mk_eq_expr b (literal 1 1)))
        else None)
  | _ -> None

let lemma_bit_test (i:interpretation value) (rho:env value)
                   (project:pos -> value -> int) (e x:expr) (k:int)
  : Lemma (requires bv_model i project /\ Z3BooleanRewrite.boolean_rewrite_model i /\
                    D.scoped [] e /\ bit_test e == Some (x, k))
          (ensures D.scoped [] x /\ get_sort x == bv_sort 1 /\
                   0 <= k /\ k < 2 /\
                   (lit_true i rho e <==> project 1 (eval i x rho) == k))
  = match e with
    | App f [a; b] ->
      lemma_word i rho project 1 x;
      if Some? (bit_numeral b) then assert (project 1 (eval i b rho) == k)
      else assert (project 1 (eval i a rho) == k)
    | _ -> ()

let lemma_bit_conditional (i:interpretation value) (rho:env value)
                          (project:pos -> value -> int) (e result:expr)
  : Lemma (requires bv_model i project /\ Z3BooleanRewrite.boolean_rewrite_model i /\
                    AR.term_ite_sound i /\ D.scoped [] e /\
                    bit_conditional e == Some result)
          (ensures eval i e rho == eval i result rho)
  = let c, t, u = Some?.v (AR.ite_parts e) in
    let _, n = Some?.v (numeral t) in
    let x, k = Some?.v (bit_test c) in
    lemma_bit_test i rho project c x k;
    lemma_word i rho project 1 x;
    AR.lemma_ite_parts i rho e c t u;
    assert (project 1 (eval i t rho) == n);
    assert (project 1 (eval i u rho) == 1 - n);
    if n <> k then (
      let a = project 1 (eval i x rho) in
      U.lemma_lognot_value_mod #1 a;
      lemma_operation i rho project
        { decl_name = "bvnot"; domain = [bv_sort 1]; range = bv_sort 1;
          interp = Some op_not; int_params = [1] } [x] 1 op_not);
    (match eval i c rho with VBool _ -> () | _ -> ());
    lemma_reflect i rho project 1 e result

#push-options "--fuel 4 --ifuel 2"
let lemma_not_conditional (i:interpretation value) (rho:env value)
                          (project:pos -> value -> int) (e result:expr)
  : Lemma (requires bv_model i project /\ AR.term_ite_sound i /\
                    D.scoped [] e /\ not_conditional e == Some result)
          (ensures eval i e rho == eval i result rho)
  = match e with
    | App f [a] ->
      let width, _ = Some?.v (operation f [a]) in
      let c, t, u = Some?.v (AR.ite_parts a) in
      let _, n = Some?.v (numeral t) in
      let _, m = Some?.v (numeral u) in
      assert (D.scoped [] a);
      assert (D.scoped [] c /\ get_sort c == bool_sort);
      assert (project width (eval i t rho) == n);
      assert (project width (eval i u rho) == m);
      AR.lemma_ite_parts i rho a c t u;
      lemma_literal i rho project width (U.lognot #width n);
      lemma_literal i rho project width (U.lognot #width m);
      AR.lemma_ite_parts i rho result c
        (literal width (U.lognot #width n)) (literal width (U.lognot #width m));
      lemma_word i rho project width a;
      lemma_operation i rho project f [a] width op_not;
      let t' = literal width (U.lognot #width n) in
      let u' = literal width (U.lognot #width m) in
      lemma_literal_shape width (U.lognot #width n);
      lemma_literal_shape width (U.lognot #width m);
      lemma_ite_shape width c t' u';
      assert (D.scoped [] result /\ get_sort result == bv_sort width);
      lemma_reflect i rho project width e result
    | _ -> ()
#pop-options

let lemma_not_comparison (i:interpretation value) (rho:env value)
                         (project:pos -> value -> int) (source target result:expr)
  : Lemma (requires bv_model i project /\ Z3BooleanRewrite.boolean_rewrite_model i /\
                    D.scoped [] source /\ D.scoped [] target /\
                    not_comparison source target == Some result)
          (ensures (eval i source rho == eval i target rho) <==> lit_true i rho result)
  = match source with
    | App f [x] ->
      let width, _ = Some?.v (operation f [x]) in
      let _, n = Some?.v (numeral target) in
      lemma_word i rho project width x;
      lemma_operation i rho project f [x] width op_not;
      lemma_literal i rho project width (U.lognot #width n);
      assert (project width (eval i target rho) == n);
      U.lognot_self #width n;
      U.lognot_self #width (project width (eval i x rho));
      assert ((U.lognot #width (project width (eval i x rho)) == n) <==>
              (project width (eval i x rho) == U.lognot #width n));
      assert ((eval i source rho == eval i target rho) <==>
              project width (eval i source rho) == n);
      let k = literal width (U.lognot #width n) in
      assert (D.scoped [] k /\ get_sort k == bv_sort width);
      assert ((eval i x rho == eval i k rho) <==>
              project width (eval i x rho) == U.lognot #width n);
      assert (lit_true i rho result <==> eval i x rho == eval i k rho)
    | _ -> ()

let lemma_encoded_comparison (i:interpretation value) (rho:env value)
                             (project:pos -> value -> int) (source target result:expr)
  : Lemma (requires bv_model i project /\ Z3BooleanRewrite.boolean_rewrite_model i /\
                    AR.term_ite_sound i /\ D.scoped [] source /\ D.scoped [] target /\
                    encoded_comparison source target == Some result)
          (ensures (eval i source rho == eval i target rho) <==> lit_true i rho result)
  = let c, t, u = Some?.v (AR.ite_parts target) in
    let _, n = Some?.v (numeral t) in
    lemma_word i rho project 1 source;
    assert (project 1 (eval i t rho) == n);
    assert (project 1 (eval i u rho) == 1 - n);
    AR.lemma_ite_parts i rho target c t u;
    (match eval i c rho, eval i (mk_eq_expr source t) rho with
     | VBool _, VBool _ -> ()
     | _, _ -> ())

let lemma_comparison_bridge (i:interpretation value) (rho:env value)
                            (project:pos -> value -> int) (e result:expr)
  : Lemma (requires bv_model i project /\ Z3BooleanRewrite.boolean_rewrite_model i /\
                    AR.term_ite_sound i /\ D.scoped [] e /\
                    comparison_bridge e == Some result)
          (ensures eval i e rho == eval i result rho)
  = match e with
    | App f [a; b] ->
      if Some? (not_comparison a b) then lemma_not_comparison i rho project a b result
      else if Some? (not_comparison b a) then lemma_not_comparison i rho project b a result
      else if Some? (encoded_comparison a b) then lemma_encoded_comparison i rho project a b result
      else if Some? (encoded_comparison b a) then lemma_encoded_comparison i rho project b a result
      else (
        lemma_word i rho project 1 a;
        lemma_word i rho project 1 b;
        lemma_literal i rho project 1 1;
        assert ((eval i a rho == eval i b rho) <==>
                project 1 (eval i a rho) == project 1 (eval i b rho));
        assert (lit_true i rho (mk_eq_expr a (literal 1 1)) <==>
                project 1 (eval i a rho) == 1);
        assert (lit_true i rho (mk_eq_expr b (literal 1 1)) <==>
                project 1 (eval i b rho) == 1);
        match eval i (mk_eq_expr a (literal 1 1)) rho,
              eval i (mk_eq_expr b (literal 1 1)) rho with
        | VBool _, VBool _ -> ()
        | _, _ -> ());
      (match eval i e rho, eval i result rho with
       | VBool _, VBool _ -> ()
       | _, _ -> ())
    | _ -> ()

let extract_rewrite (e:expr) : option expr =
  match extract_parts e with
  | Some s ->
    if s.low = 0 && s.high + 1 = s.source_width then Some s.operand
    else (match numeral s.operand with
      | Some (w, n) ->
        if w = s.source_width then
          Some (literal (s.high - s.low + 1)
            ((n / pow2 s.low) % pow2 (s.high - s.low + 1)))
        else None
      | None ->
        (match concat_parts s.operand with
         | Some c ->
           if s.source_width <> c.left_width + c.right_width then None
           else if s.low = 0 && s.high + 1 = c.right_width then Some c.right
           else if s.low = c.right_width && s.high + 1 = s.source_width then Some c.left
           else None
         | None -> None))
  | None -> None

let concat_comparison (e:expr) : option expr =
  match e with
  | App f [a; b] ->
    if f <> eq_decl (get_sort a) || get_sort a <> get_sort b then None
    else (match concat_parts a, concat_parts b with
      | Some c, Some d ->
        if c.left_width = d.left_width && c.right_width = d.right_width && c.left = d.left
        then Some (mk_eq_expr c.right d.right) else None
      | _, _ -> None)
  | _ -> None

let lemma_extract_parts (i:interpretation value) (rho:env value)
                        (project:pos -> value -> int) (e:expr) (s:extraction)
  : Lemma (requires bv_model i project /\ D.scoped [] e /\ extract_parts e == Some s)
          (ensures D.scoped [] s.operand /\ get_sort s.operand == bv_sort s.source_width /\
                   get_sort e == bv_sort (s.high - s.low + 1) /\
                   project (s.high - s.low + 1) (eval i e rho) ==
                     (project s.source_width (eval i s.operand rho) / pow2 s.low) %
                     pow2 (s.high - s.low + 1))
  = match e with App _ [_] -> () | _ -> ()

let lemma_concat_parts (i:interpretation value) (rho:env value)
                       (project:pos -> value -> int) (e:expr) (c:concatenation)
  : Lemma (requires bv_model i project /\ D.scoped [] e /\ concat_parts e == Some c)
          (ensures D.scoped [] c.left /\ D.scoped [] c.right /\
                   get_sort c.left == bv_sort c.left_width /\
                   get_sort c.right == bv_sort c.right_width /\
                   get_sort e == bv_sort (c.left_width + c.right_width) /\
                   project (c.left_width + c.right_width) (eval i e rho) ==
                     project c.left_width (eval i c.left rho) * pow2 c.right_width +
                     project c.right_width (eval i c.right rho))
  = match e with App _ [_; _] -> () | _ -> ()

let lemma_extract_rewrite (i:interpretation value) (rho:env value)
                          (project:pos -> value -> int) (e result:expr)
  : Lemma (requires bv_model i project /\ D.scoped [] e /\ extract_rewrite e == Some result)
          (ensures eval i e rho == eval i result rho)
  = let s = Some?.v (extract_parts e) in
    lemma_extract_parts i rho project e s;
    lemma_word i rho project s.source_width s.operand;
    if s.low = 0 && s.high + 1 = s.source_width then (
      FStar.Math.Lemmas.small_mod (project s.source_width (eval i s.operand rho))
        (pow2 s.source_width))
    else if Some? (numeral s.operand) then (
      let _, n = Some?.v (numeral s.operand) in
      lemma_literal i rho project (s.high - s.low + 1)
        ((n / pow2 s.low) % pow2 (s.high - s.low + 1));
      lemma_literal_shape (s.high - s.low + 1)
        ((n / pow2 s.low) % pow2 (s.high - s.low + 1)))
    else (
      let c = Some?.v (concat_parts s.operand) in
      lemma_concat_parts i rho project s.operand c;
      lemma_word i rho project c.left_width c.left;
      lemma_word i rho project c.right_width c.right;
      let x = project c.left_width (eval i c.left rho) in
      let y = project c.right_width (eval i c.right rho) in
      let p = pow2 c.right_width in
      if s.low = 0 then (
        FStar.Math.Lemmas.lemma_mod_plus y x p;
        FStar.Math.Lemmas.small_mod y p)
      else (
        FStar.Math.Lemmas.lemma_div_plus y x p;
        FStar.Math.Lemmas.small_div y p;
        FStar.Math.Lemmas.small_mod x (pow2 c.left_width)));
    lemma_reflect i rho project (s.high - s.low + 1) e result

let lemma_concat_comparison (i:interpretation value) (rho:env value)
                            (project:pos -> value -> int) (e result:expr)
  : Lemma (requires bv_model i project /\ Z3BooleanRewrite.boolean_rewrite_model i /\
                    D.scoped [] e /\ concat_comparison e == Some result)
          (ensures eval i e rho == eval i result rho)
  = match e with
    | App f [a; b] ->
      let c = Some?.v (concat_parts a) in
      let d = Some?.v (concat_parts b) in
      lemma_concat_parts i rho project a c;
      lemma_concat_parts i rho project b d;
      assert ((eval i a rho == eval i b rho) <==>
        project (c.left_width + c.right_width) (eval i a rho) ==
        project (c.left_width + c.right_width) (eval i b rho));
      assert ((eval i c.right rho == eval i d.right rho) <==>
        project c.right_width (eval i c.right rho) ==
        project c.right_width (eval i d.right rho));
      (match eval i e rho, eval i result rho with
       | VBool _, VBool _ -> ()
       | _, _ -> ())
    | _ -> ()

let binary (width:pos) (op:decl_kind) (x y:expr) : expr =
  App { decl_name = (if op = op_add then "bvadd" else "bvmul");
        domain = [bv_sort width; bv_sort width]; range = bv_sort width;
        interp = Some op; int_params = [width] } [x; y]

#push-options "--fuel 4 --ifuel 2"
let lemma_binary_shape (width:pos) (op:decl_kind) (x y:expr)
  : Lemma (requires D.scoped [] x /\ D.scoped [] y /\
                    get_sort x == bv_sort width /\ get_sort y == bv_sort width)
          (ensures D.scoped [] (binary width op x y) /\
                   get_sort (binary width op x y) == bv_sort width)
  = assert (sorts_match [x; y] [bv_sort width; bv_sort width]);
    assert (D.scoped_args [] [x; y])
#pop-options

let lemma_binary_value (i:interpretation value) (rho:env value)
                       (project:pos -> value -> int) (width:pos) (op:decl_kind) (x y:expr)
  : Lemma (requires bv_model i project /\ width <= 4096 /\
                    (op = op_add \/ op = op_mul) /\
                    D.scoped [] x /\ D.scoped [] y /\
                    get_sort x == bv_sort width /\ get_sort y == bv_sort width)
          (ensures project width (eval i (binary width op x y) rho) ==
            (if op = op_add
             then (project width (eval i x rho) + project width (eval i y rho)) % pow2 width
             else (project width (eval i x rho) * project width (eval i y rho)) % pow2 width))
  = lemma_word i rho project width x;
    lemma_word i rho project width y;
    lemma_binary_shape width op x y;
    match binary width op x y with
    | App f args -> lemma_operation i rho project f args width op
    | _ -> ()

let left_identity (e:expr) : option expr =
  match e with
  | App f [x; y] ->
    (match operation f [x; y], numeral x with
     | Some (width, op), Some (w, n) ->
       if width <> w then None
       else if n = 0 && op = op_add then Some y
       else if n = 0 && op = op_mul then Some x
       else if n = 1 && op = op_mul then Some y
       else None
     | _, _ -> None)
  | _ -> None

let subtraction_rewrite (e:expr) : option expr =
  match e with
  | App f [x; y] ->
    (match operation f [x; y] with
     | Some (width, op) ->
       if op = op_sub then
         Some (binary width op_add x
           (binary width op_mul (literal width (U.ones width)) y))
       else None
     | None -> None)
  | _ -> None

let lemma_left_identity (i:interpretation value) (rho:env value)
                        (project:pos -> value -> int) (e result:expr)
  : Lemma (requires bv_model i project /\ D.scoped [] e /\ left_identity e == Some result)
          (ensures eval i e rho == eval i result rho)
  = match e with
    | App f [x; y] ->
      let width, op = Some?.v (operation f [x; y]) in
      let _, n = Some?.v (numeral x) in
      lemma_word i rho project width x;
      lemma_word i rho project width y;
      assert (project width (eval i x rho) == n);
      lemma_operation i rho project f [x; y] width op;
      lemma_reflect i rho project width e result
    | _ -> ()

let lemma_subtraction_words (width:pos) (a b:U.uint_t width)
  : Lemma (U.sub_mod a b == U.add_mod a (U.mul_mod (U.ones width) b))
  = let p = pow2 width in
    FStar.Math.Lemmas.lemma_mod_add_distr a ((p - 1) * b) p;
    FStar.Math.Lemmas.lemma_mod_plus (a - b) b p;
    assert (a + (p - 1) * b == a - b + b * p)

let lemma_subtraction_rewrite (i:interpretation value) (rho:env value)
                              (project:pos -> value -> int) (e result:expr)
  : Lemma (requires bv_model i project /\ D.scoped [] e /\ subtraction_rewrite e == Some result)
          (ensures eval i e rho == eval i result rho)
  = match e with
    | App f [x; y] ->
      let width, _ = Some?.v (operation f [x; y]) in
      let n = literal width (U.ones width) in
      let product = binary width op_mul n y in
      lemma_word i rho project width x;
      lemma_word i rho project width y;
      lemma_literal i rho project width (U.ones width);
      lemma_literal_shape width (U.ones width);
      lemma_binary_shape width op_mul n y;
      (match product with App g args -> lemma_operation i rho project g args width op_mul | _ -> ());
      lemma_word i rho project width product;
      lemma_binary_shape width op_add x product;
      (match result with App g args -> lemma_operation i rho project g args width op_add | _ -> ());
      lemma_operation i rho project f [x; y] width op_sub;
      let a = project width (eval i x rho) in
      let b = project width (eval i y rho) in
      lemma_subtraction_words width a b;
      lemma_reflect i rho project width e result
    | _ -> ()

let nary_rewrite (e:expr) : option expr =
  match e with
  | App f (x :: y :: z :: rest) ->
    (match nary_operation f (x :: y :: z :: rest) with
     | Some (width, op) ->
       if op = op_add || op = op_mul then
         Some (binary width op x
           (App { f with domain = L.tl f.domain } (y :: z :: rest)))
       else None
     | None -> None)
  | _ -> None

let coefficient_rewrite (e:expr) : option expr =
  match e with
  | App f [a; App g [b; x]] ->
    (match operation f [a; App g [b; x]], operation g [b; x], numeral a, numeral b with
     | Some (width, op), Some (w, op'), Some (w', n), Some (w'', m) ->
       if width = w && width = w' && width = w'' && op = op_mul && op' = op_mul
       then Some (binary width op_mul (literal width (U.mul_mod #width n m)) x)
       else None
     | _, _, _, _ -> None)
  | _ -> None

let isolate_equality (e:expr) : option expr =
  match e with
  | App f [App g [x; y]; z] ->
    if f <> eq_decl (get_sort z) then None
    else (match operation g [x; y] with
      | Some (width, op) ->
        if op = op_add && get_sort z = bv_sort width then
          Some (mk_eq_expr x (binary width op_add z
            (binary width op_mul (literal width (U.ones width)) y)))
        else None
      | None -> None)
  | _ -> None

let lemma_mul_associative (width:pos) (a b c:U.uint_t width)
  : Lemma (U.mul_mod a (U.mul_mod b c) == U.mul_mod (U.mul_mod a b) c)
  = let p = pow2 width in
    FStar.Math.Lemmas.lemma_mod_mul_distr_r a (b * c) p;
    FStar.Math.Lemmas.lemma_mod_mul_distr_l (a * b) c p;
    FStar.Math.Lemmas.paren_mul_right a b c

let lemma_nary_rewrite (i:interpretation value) (rho:env value)
                       (project:pos -> value -> int) (e result:expr)
  : Lemma (requires bv_model i project /\ D.scoped [] e /\ nary_rewrite e == Some result)
          (ensures eval i e rho == eval i result rho)
  = match e with
    | App f (x :: y :: z :: rest) ->
      let width, op = Some?.v (nary_operation f (x :: y :: z :: rest)) in
      let g = { f with domain = L.tl f.domain } in
      let tail = App g (y :: z :: rest) in
      assert (D.scoped_args [] (x :: y :: z :: rest));
      assert (D.scoped_args [] (y :: z :: rest));
      assert (sorts_match (y :: z :: rest) g.domain);
      assert (D.scoped [] tail /\ get_sort tail == bv_sort width);
      lemma_word i rho project width x;
      (match rest with
       | [] -> lemma_operation i rho project g [y; z] width op
       | _ :: _ ->
         assert (nary_operation g (y :: z :: rest) == Some (width, op));
         assert (project width (eval i tail rho) ==
           calculate_nary width op (words width project (eval_args i (y :: z :: rest) rho))));
      lemma_word i rho project width tail;
      lemma_binary_shape width op x tail;
      (match result with App h args -> lemma_operation i rho project h args width op | _ -> ());
      assert (project width (eval i e rho) ==
        calculate_nary width op (words width project (eval_args i (x :: y :: z :: rest) rho)));
      lemma_reflect i rho project width e result
    | _ -> ()

#push-options "--fuel 4 --ifuel 2"
let lemma_coefficient_rewrite (i:interpretation value) (rho:env value)
                              (project:pos -> value -> int) (e result:expr)
  : Lemma (requires bv_model i project /\ D.scoped [] e /\ coefficient_rewrite e == Some result)
          (ensures eval i e rho == eval i result rho)
  = match e with
    | App f [a; App g [b; x]] ->
      let width, _ = Some?.v (operation g [b; x]) in
      let _, n = Some?.v (numeral a) in
      let _, m = Some?.v (numeral b) in
      assert (D.scoped [] (App g [b; x]));
      assert (D.scoped_args [] [b; x]);
      lemma_word i rho project width x;
      lemma_word i rho project width a;
      lemma_word i rho project width b;
      assert (project width (eval i a rho) == n);
      assert (project width (eval i b rho) == m);
      lemma_word i rho project width (App g [b; x]);
      lemma_operation i rho project g [b; x] width op_mul;
      lemma_operation i rho project f [a; App g [b; x]] width op_mul;
      lemma_literal i rho project width (U.mul_mod #width n m);
      lemma_literal_shape width (U.mul_mod #width n m);
      lemma_binary_shape width op_mul (literal width (U.mul_mod #width n m)) x;
      lemma_binary_value i rho project width op_mul (literal width (U.mul_mod #width n m)) x;
      lemma_mul_associative width n m (project width (eval i x rho));
      assert (project width (eval i e rho) ==
        U.mul_mod #width n (U.mul_mod #width m (project width (eval i x rho))));
      assert (project width (eval i result rho) ==
        U.mul_mod #width (U.mul_mod #width n m) (project width (eval i x rho)));
      lemma_reflect i rho project width e result
    | _ -> ()
#pop-options

let lemma_isolate_words (width:pos) (a b c:U.uint_t width)
  : Lemma ((U.add_mod a b == c) <==> (a == U.add_mod c (U.mul_mod (U.ones width) b)))
  = lemma_subtraction_words width c b;
    U.lemma_sub_add_cancel a b;
    U.lemma_add_sub_cancel c b

#push-options "--fuel 4 --ifuel 2"
let lemma_isolate_equality (i:interpretation value) (rho:env value)
                           (project:pos -> value -> int) (e result:expr)
  : Lemma (requires bv_model i project /\ Z3BooleanRewrite.boolean_rewrite_model i /\
                    D.scoped [] e /\ isolate_equality e == Some result)
          (ensures eval i e rho == eval i result rho)
  = match e with
    | App f [App g [x; y]; z] ->
      let width, _ = Some?.v (operation g [x; y]) in
      let n = literal width (U.ones width) in
      let product = binary width op_mul n y in
      let difference = binary width op_add z product in
      assert (D.scoped [] (App g [x; y]));
      assert (D.scoped_args [] [x; y]);
      lemma_word i rho project width x;
      lemma_word i rho project width y;
      lemma_word i rho project width z;
      lemma_word i rho project width (App g [x; y]);
      lemma_operation i rho project g [x; y] width op_add;
      lemma_literal i rho project width (U.ones width);
      lemma_literal_shape width (U.ones width);
      lemma_binary_shape width op_mul n y;
      (match product with App h args -> lemma_operation i rho project h args width op_mul | _ -> ());
      lemma_word i rho project width product;
      lemma_binary_shape width op_add z product;
      (match difference with App h args -> lemma_operation i rho project h args width op_add | _ -> ());
      lemma_isolate_words width (project width (eval i x rho))
        (project width (eval i y rho)) (project width (eval i z rho));
      assert ((eval i (App g [x; y]) rho == eval i z rho) <==>
        project width (eval i (App g [x; y]) rho) == project width (eval i z rho));
      assert ((eval i x rho == eval i difference rho) <==>
        project width (eval i x rho) == project width (eval i difference rho));
      assert (project width (eval i difference rho) ==
        U.add_mod (project width (eval i z rho))
          (U.mul_mod (U.ones width) (project width (eval i y rho))));
      assert (lit_true i rho e <==>
        project width (eval i (App g [x; y]) rho) == project width (eval i z rho));
      assert (lit_true i rho result <==>
        project width (eval i x rho) == project width (eval i difference rho));
      assert (lit_true i rho e <==> lit_true i rho result);
      (match eval i e rho, eval i result rho with VBool _, VBool _ -> () | _, _ -> ())
    | _ -> ()
#pop-options

let double_equality (e:expr) : option expr =
  match e with
  | App f [App g [x; y]; App h [n; z]] ->
    (match operation g [x; y], operation h [n; z], numeral n with
     | Some (w, op), Some (w', op'), Some (w'', k) ->
       if f = eq_decl (bv_sort w) && w = w' && w = w'' && op = op_add && op' = op_mul &&
          k = 2 && x = z then Some (mk_eq_expr x y) else None
     | _, _, _ -> None)
  | _ -> None

let lemma_double_words (width:pos) (a b:U.uint_t width)
  : Lemma (requires 2 < pow2 width)
          (ensures (U.add_mod a b == U.mul_mod #width 2 a) <==> a == b)
  = assert (U.mul_mod #width 2 a == U.add_mod a a);
    U.lemma_add_sub_cancel b a;
    U.lemma_add_sub_cancel a a

let lemma_double_equality (i:interpretation value) (rho:env value)
                          (project:pos -> value -> int) (e result:expr)
  : Lemma (requires bv_model i project /\ Z3BooleanRewrite.boolean_rewrite_model i /\
                    D.scoped [] e /\ double_equality e == Some result)
          (ensures eval i e rho == eval i result rho)
  = match e with
    | App _ [App g [x; y]; App h [n; z]] ->
      let width, _ = Some?.v (operation g [x; y]) in
      lemma_word i rho project width x;
      lemma_word i rho project width y;
      lemma_word i rho project width n;
      lemma_word i rho project width (App g [x; y]);
      lemma_word i rho project width (App h [n; z]);
      assert (project width (eval i n rho) == 2);
      lemma_operation i rho project g [x; y] width op_add;
      lemma_operation i rho project h [n; z] width op_mul;
      lemma_double_words width (project width (eval i x rho)) (project width (eval i y rho));
      assert ((eval i (App g [x; y]) rho == eval i (App h [n; z]) rho) <==>
        project width (eval i (App g [x; y]) rho) == project width (eval i (App h [n; z]) rho));
      assert ((eval i x rho == eval i y rho) <==>
        project width (eval i x rho) == project width (eval i y rho));
      assert (lit_true i rho e <==> lit_true i rho result);
      (match eval i e rho, eval i result rho with VBool _, VBool _ -> () | _, _ -> ())
    | _ -> ()

let rewrite (e:expr) : option expr =
  if not (D.scoped [] e) then None
  else let r = basic_rewrite e in
  if Some? r then r else
  let r = bit_conditional e in
  if Some? r then r else
  let r = not_conditional e in
  if Some? r then r else
  let r = comparison_bridge e in
  if Some? r then r else
  let r = extract_rewrite e in
  if Some? r then r else
  let r = concat_comparison e in
  if Some? r then r else
  let r = left_identity e in
  if Some? r then r else
  let r = subtraction_rewrite e in
  if Some? r then r else
  let r = nary_rewrite e in
  if Some? r then r else
  let r = coefficient_rewrite e in
  if Some? r then r else
  let r = double_equality e in
  if Some? r then r else isolate_equality e

let lemma_rewrite (i:interpretation value) (rho:env value)
                  (project:pos -> value -> int) (e result:expr)
  : Lemma (requires bv_model i project /\ Z3BooleanRewrite.boolean_rewrite_model i /\
                    AR.term_ite_sound i /\ rewrite e == Some result)
          (ensures eval i e rho == eval i result rho)
  = if Some? (basic_rewrite e) then lemma_basic_rewrite i rho project e result
    else if Some? (bit_conditional e) then lemma_bit_conditional i rho project e result
    else if Some? (not_conditional e) then lemma_not_conditional i rho project e result
    else if Some? (comparison_bridge e) then lemma_comparison_bridge i rho project e result
    else if Some? (extract_rewrite e) then lemma_extract_rewrite i rho project e result
    else if Some? (concat_comparison e) then lemma_concat_comparison i rho project e result
    else if Some? (left_identity e) then lemma_left_identity i rho project e result
    else if Some? (subtraction_rewrite e) then lemma_subtraction_rewrite i rho project e result
    else if Some? (nary_rewrite e) then lemma_nary_rewrite i rho project e result
    else if Some? (coefficient_rewrite e) then lemma_coefficient_rewrite i rho project e result
    else if Some? (double_equality e) then lemma_double_equality i rho project e result
    else lemma_isolate_equality i rho project e result

let commutative (op:decl_kind) : bool =
  op = op_and || op = op_or || op = op_xor || op = op_add || op = op_mul

let commutative_equivalent (a b:expr) : bool =
  D.scoped [] a && D.scoped [] b &&
  (match a, b with
   | App f [x; y], App g [u; v] ->
     (match operation f [x; y], operation g [u; v] with
      | Some (width, op), Some (width', op') ->
        width = width' && op = op' && commutative op && x = v && y = u
      | _, _ -> false)
   | _, _ -> false)

let lemma_commutative (width:pos) (op:decl_kind) (a b:U.uint_t width)
  : Lemma (requires commutative op)
          (ensures calculate width op [a; b] == calculate width op [b; a])
  = if op = op_and then U.logand_commutative a b
    else if op = op_or then U.logor_commutative a b
    else if op = op_xor then U.logxor_commutative a b

let lemma_commutative_equivalent (i:interpretation value) (rho:env value)
                     (project:pos -> value -> int) (a b:expr)
  : Lemma (requires bv_model i project /\ commutative_equivalent a b)
          (ensures eval i a rho == eval i b rho)
  = match a, b with
    | App f [x; y], App g [u; v] ->
      let width, op = Some?.v (operation f [x; y]) in
      lemma_word i rho project width x;
      lemma_word i rho project width y;
      lemma_operation i rho project f [x; y] width op;
      lemma_operation i rho project g [u; v] width op;
      lemma_commutative width op (project width (eval i x rho)) (project width (eval i y rho));
      lemma_reflect i rho project width a b
    | _, _ -> ()

let distributive (a b:expr) : bool =
  match a, b with
  | App f [x; App g [y; z]], App h [App j [u; v]; App k [s; t]] ->
    (match operation f [x; App g [y; z]], operation g [y; z],
           operation h [App j [u; v]; App k [s; t]],
           operation j [u; v], operation k [s; t] with
     | Some (w, m), Some (w', p), Some (w'', q), Some (w''', r), Some (w'''', s') ->
       w = w' && w = w'' && w = w''' && w = w'''' &&
       m = op_mul && p = op_add && q = op_add && r = op_mul && s' = op_mul &&
       x = u && x = s && y = v && z = t
     | _, _, _, _, _ -> false)
  | _, _ -> false

let lemma_distributive_words (width:pos) (x y z:U.uint_t width)
  : Lemma (U.mul_mod x (U.add_mod y z) ==
           U.add_mod (U.mul_mod x y) (U.mul_mod x z))
  = let p = pow2 width in
    FStar.Math.Lemmas.lemma_mod_mul_distr_r x (y + z) p;
    FStar.Math.Lemmas.lemma_mod_plus_distr_l (x * y) (x * z) p;
    FStar.Math.Lemmas.lemma_mod_plus_distr_r ((x * y) % p) (x * z) p;
    FStar.Math.Lemmas.distributivity_add_right x y z

#push-options "--fuel 4 --ifuel 2"
let lemma_distributive (i:interpretation value) (rho:env value)
                       (project:pos -> value -> int) (a b:expr)
  : Lemma (requires bv_model i project /\ D.scoped [] a /\ D.scoped [] b /\
                    distributive a b)
          (ensures eval i a rho == eval i b rho)
  = match a, b with
    | App f [x; App g [y; z]], App h [App j [u; v]; App k [s; t]] ->
      let width, _ = Some?.v (operation g [y; z]) in
      assert (D.scoped_args [] [x; App g [y; z]]);
      assert (D.scoped [] (App g [y; z]));
      assert (D.scoped_args [] [y; z]);
      assert (D.scoped_args [] [App j [u; v]; App k [s; t]]);
      lemma_word i rho project width x;
      lemma_word i rho project width y;
      lemma_word i rho project width z;
      lemma_operation i rho project g [y; z] width op_add;
      lemma_word i rho project width (App g [y; z]);
      lemma_operation i rho project f [x; App g [y; z]] width op_mul;
      lemma_operation i rho project j [u; v] width op_mul;
      lemma_operation i rho project k [s; t] width op_mul;
      lemma_word i rho project width (App j [u; v]);
      lemma_word i rho project width (App k [s; t]);
      lemma_operation i rho project h [App j [u; v]; App k [s; t]] width op_add;
      lemma_distributive_words width (project width (eval i x rho))
        (project width (eval i y rho)) (project width (eval i z rho));
      lemma_reflect i rho project width a b
    | _, _ -> ()
#pop-options

let equivalent (a b:expr) : bool =
  commutative_equivalent a b ||
  (D.scoped [] a && D.scoped [] b && (distributive a b || distributive b a))

let lemma_equivalent (i:interpretation value) (rho:env value)
                     (project:pos -> value -> int) (a b:expr)
  : Lemma (requires bv_model i project /\ equivalent a b)
          (ensures eval i a rho == eval i b rho)
  = if commutative_equivalent a b then lemma_commutative_equivalent i rho project a b
    else if distributive a b then lemma_distributive i rho project a b
    else lemma_distributive i rho project b a
