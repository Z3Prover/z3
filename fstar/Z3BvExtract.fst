module Z3BvExtract

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native --fuel 1 --ifuel 1 --z3rlimit 10"

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module D = Z3Definitions
module L = FStar.List.Tot
module U = FStar.UInt
module M = FStar.Math.Lemmas
module A = Z3ArrayRewrite
module BV = Z3BvLemma

(* Extraction steps of bv_rewriter::mk_extract that move an extraction into
   its argument:

     ((_ extract h 0) (bvadd x1 ... xn))  ~>  (bvadd ((_ extract h 0) x1) ... ((_ extract h 0) xn))
     ((_ extract h 0) (bvmul x1 ... xn))  ~>  (bvmul ((_ extract h 0) x1) ... ((_ extract h 0) xn))
     ((_ extract h l) (ite c t e))        ~>  (ite c ((_ extract h l) t) ((_ extract h l) e))
     ((_ extract h l) (concat x y))       ~>  the bits [h:l] of y, of x, or a concatenation
                                              of the low bits of x and the high bits of y

   Addition and multiplication are only distributed over the low bits
   (l = 0): bits above the lowest one depend on carries out of the discarded
   bits, so ((_ extract 1 1) (bvadd #b01 #b01)) = #b1 but
   (bvadd ((_ extract 1 1) #b01) ((_ extract 1 1) #b01)) = #b0.
   The inner extractions are those of mk_extract_proc, which composes an
   extraction of an extraction: for xi = ((_ extract h2 l2) z), the target
   argument is ((_ extract (h + l2) (l + l2)) z).

   For a binary concatenation of x (width m, the high bits) and y (width n,
   the low bits), mk_extract keeps the arguments that the slice covers and
   extracts from the others: with h < n the result is the bits [h:l] of y,
   with n <= l the bits [h-n:l-n] of x, and otherwise the concatenation of
   the bits [h-n:0] of x and [n-1:l] of y. The bits of an argument are the
   argument itself when they are all of its bits, and otherwise an
   extraction as above. Concatenations of more than two arguments are not
   handled.

   Every width and index is read from the native declarations, which
   Z3BvLemma.extract_parts, Z3BvLemma.concat_parts and Z3BvLemma.operation
   already check against the sorts, and is compared as an integer with the
   corresponding width of the other side. The guard of a conditional is not
   interpreted; it must be the same term on both sides. Both sides must be
   closed terms, as required by Z3BvLemma.bv_model; steps under binders are
   left unchecked. *)

(* y is the extraction [h:l] of x, a term of width w. *)
let slice (w:pos) (h l:nat) (x y:expr) : bool =
  h < w && l <= h &&
  (match BV.extract_parts y with
   | None -> false
   | Some s ->
     (s.source_width = w && s.high = h && s.low = l && s.operand = x) ||
     (match BV.extract_parts x with
      | None -> false
      | Some t ->
        t.high - t.low + 1 = w && s.source_width = t.source_width &&
        s.high = h + t.low && s.low = l + t.low && s.operand = t.operand))

let rec slices (w:pos) (h:nat) (xs ys:list expr) : Tot bool (decreases xs) =
  match xs, ys with
  | [], [] -> true
  | x :: xs', y :: ys' -> slice w h 0 x y && slices w h xs' ys'
  | _, _ -> false

(* Binary or n-ary bvadd and bvmul. *)
let arith (f:func_decl) (args:list expr) : option (pos & decl_kind) =
  match BV.operation f args with
  | Some (w, op) -> if op = BV.op_add || op = BV.op_mul then Some (w, op) else None
  | None -> BV.nary_operation f args

let distribute (a b:expr) : bool =
  match BV.extract_parts a with
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

let conditional (a b:expr) : bool =
  match BV.extract_parts a with
  | None -> false
  | Some s ->
    (match A.ite_parts s.operand, A.ite_parts b with
     | Some (c, t, e), Some (c', t', e') ->
       c = c' && slice s.source_width s.high s.low t t' &&
       slice s.source_width s.high s.low e e'
     | _, _ -> false)

(* y is the bits [h:l] of x, a term of width w: x itself when these are all of
   its bits, otherwise an extraction as in slice. *)
let piece (w:pos) (h l:nat) (x y:expr) : bool =
  (l = 0 && h + 1 = w && y = x) || slice w h l x y

let concatenated (a b:expr) : bool =
  match BV.extract_parts a with
  | None -> false
  | Some s ->
    (match BV.concat_parts s.operand with
     | None -> false
     | Some c ->
       let m = c.left_width in
       let n = c.right_width in
       s.source_width = m + n &&
       (if s.high < n then piece n s.high s.low c.right b
        else if n <= s.low then piece m (s.high - n) (s.low - n) c.left b
        else (match BV.concat_parts b with
              | None -> false
              | Some d ->
                d.left_width = s.high - n + 1 && d.right_width = n - s.low &&
                piece m (s.high - n) 0 c.left d.left &&
                piece n (n - 1) s.low c.right d.right)))

let check (a b:expr) : bool =
  (distribute a b || conditional a b || concatenated a b) && D.scoped [] a && D.scoped [] b

(* Soundness *)

let lemma_extract_extract (z:nat) (tl w:nat) (h l:nat)
  : Lemma (requires l <= h /\ h < w)
          (ensures ((((z / pow2 tl) % pow2 w) / pow2 l) % pow2 (h - l + 1) ==
                    (z / pow2 (l + tl)) % pow2 (h - l + 1)))
  = let a = z / pow2 tl in
    M.pow2_modulo_division_lemma_1 a l w;
    M.pow2_plus tl l;
    M.division_multiplication_lemma z (pow2 tl) (pow2 l);
    M.pow2_modulo_modulo_lemma_1 (z / pow2 (l + tl)) (h - l + 1) (w - l)

let lemma_slice (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                (w:pos) (h l:nat) (x y:expr)
  : Lemma (requires BV.bv_model i project /\ D.scoped [] x /\ D.scoped [] y /\ slice w h l x y)
          (ensures h < w /\ l <= h /\
                   get_sort x == BV.bv_sort w /\ get_sort y == BV.bv_sort (h - l + 1) /\
                   project (h - l + 1) (eval i y rho) ==
                     (project w (eval i x rho) / pow2 l) % pow2 (h - l + 1))
  = let s = Some?.v (BV.extract_parts y) in
    BV.lemma_extract_parts i rho project y s;
    if s.source_width = w && s.high = h && s.low = l && s.operand = x then ()
    else (
      let t = Some?.v (BV.extract_parts x) in
      BV.lemma_extract_parts i rho project x t;
      BV.lemma_word i rho project t.source_width t.operand;
      lemma_extract_extract (project t.source_width (eval i t.operand rho)) t.low w h l)

let rec low_words (k:pos) (w:pos{k <= w}) (xs:list (U.uint_t w)) (ys:list (U.uint_t k))
  : Tot bool (decreases xs) =
  match xs, ys with
  | [], [] -> true
  | x :: xs', y :: ys' -> y = x % pow2 k && low_words k w xs' ys'
  | _, _ -> false

#push-options "--fuel 2 --ifuel 1"
let rec lemma_low_words (k:pos) (w:pos{k <= w}) (op:decl_kind)
                        (xs:list (U.uint_t w)) (ys:list (U.uint_t k))
  : Lemma (requires (op = BV.op_add \/ op = BV.op_mul) /\ low_words k w xs ys)
          (ensures BV.calculate_nary w op xs % pow2 k == BV.calculate_nary k op ys)
          (decreases xs)
  = match xs, ys with
    | [], [] -> ()
    | [x], [y] -> ()
    | x :: x2 :: xs', y :: y2 :: ys' ->
      lemma_low_words k w op (x2 :: xs') (y2 :: ys');
      let c = BV.calculate_nary w op (x2 :: xs') in
      if op = BV.op_add then (
        M.pow2_modulo_modulo_lemma_1 (x + c) k w;
        M.lemma_mod_plus_distr_l x c (pow2 k);
        M.lemma_mod_plus_distr_r (x % pow2 k) c (pow2 k))
      else (
        M.pow2_modulo_modulo_lemma_1 (x * c) k w;
        M.lemma_mod_mul_distr_l x c (pow2 k);
        M.lemma_mod_mul_distr_r (x % pow2 k) c (pow2 k))
    | _, _ -> ()
#pop-options

let rec lemma_slices (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                     (w:pos) (h:nat) (xs ys:list expr)
  : Lemma (requires BV.bv_model i project /\ h < w /\
                    D.scoped_args [] xs /\ D.scoped_args [] ys /\ slices w h xs ys)
          (ensures low_words (h + 1) w (BV.words w project (eval_args i xs rho))
                                       (BV.words (h + 1) project (eval_args i ys rho)))
          (decreases xs)
  = match xs, ys with
    | x :: xs', y :: ys' ->
      lemma_slice i rho project w h 0 x y;
      BV.lemma_word i rho project w x;
      BV.lemma_word i rho project (h + 1) y;
      lemma_slices i rho project w h xs' ys'
    | _, _ -> ()

#push-options "--fuel 4 --ifuel 2"
let lemma_arith (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                (f:func_decl) (args:list expr) (w:pos) (op:decl_kind)
  : Lemma (requires BV.bv_model i project /\ D.scoped [] (App f args) /\
                    arith f args == Some (w, op))
          (ensures (op = BV.op_add \/ op = BV.op_mul) /\
                   get_sort (App f args) == BV.bv_sort w /\
                   project w (eval i (App f args) rho) ==
                   BV.calculate_nary w op (BV.words w project (eval_args i args rho)))
  = match BV.operation f args, args with
    | Some _, [x; y] -> BV.lemma_operation i rho project f args w op
    | _, _ -> ()
#pop-options

let lemma_distribute (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                     (a b:expr)
  : Lemma (requires BV.bv_model i project /\ D.scoped [] a /\ D.scoped [] b /\ distribute a b)
          (ensures eval i a rho == eval i b rho)
  = let s = Some?.v (BV.extract_parts a) in
    BV.lemma_extract_parts i rho project a s;
    match s.operand, b with
    | App f xs, App g ys ->
      let w, op = Some?.v (arith f xs) in
      let k = s.high + 1 in
      lemma_arith i rho project f xs w op;
      lemma_arith i rho project g ys k op;
      lemma_slices i rho project w s.high xs ys;
      lemma_low_words k w op (BV.words w project (eval_args i xs rho))
                             (BV.words k project (eval_args i ys rho));
      BV.lemma_reflect i rho project k a b
    | _, _ -> ()

#push-options "--fuel 4 --ifuel 2"
let lemma_conditional (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                      (a b:expr)
  : Lemma (requires BV.bv_model i project /\ A.term_ite_sound i /\
                    D.scoped [] a /\ D.scoped [] b /\ conditional a b)
          (ensures eval i a rho == eval i b rho)
  = let s = Some?.v (BV.extract_parts a) in
    BV.lemma_extract_parts i rho project a s;
    match s.operand, b with
    | App _ [c; t; e], App _ [_; t'; e'] ->
      let w = s.source_width in
      lemma_slice i rho project w s.high s.low t t';
      lemma_slice i rho project w s.high s.low e e';
      A.lemma_ite_parts i rho s.operand c t e;
      A.lemma_ite_parts i rho b c t' e';
      BV.lemma_reflect i rho project (s.high - s.low + 1) a b
    | _, _ -> ()
#pop-options

(* The bits [h:l] of the concatenation x * 2^n + y of x and a word y < 2^n. *)
let lemma_concat_low (n:pos) (x y:nat) (h l:nat)
  : Lemma (requires l <= h /\ h < n)
          (ensures ((x * pow2 n + y) / pow2 l) % pow2 (h - l + 1) ==
                   (y / pow2 l) % pow2 (h - l + 1))
  = let k = h + 1 in
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

let lemma_concat_high (n:pos) (x y:nat) (h l:nat)
  : Lemma (requires y < pow2 n /\ n <= l /\ l <= h)
          (ensures ((x * pow2 n + y) / pow2 l) % pow2 (h - l + 1) ==
                   (x / pow2 (l - n)) % pow2 (h - l + 1))
  = let v = x * pow2 n + y in
    M.lemma_div_plus y x (pow2 n);
    M.small_div y (pow2 n);
    assert (v == y + x * pow2 n);
    assert (v / pow2 n == x);
    M.pow2_plus n (l - n);
    assert (pow2 n * pow2 (l - n) == pow2 l);
    M.division_multiplication_lemma v (pow2 n) (pow2 (l - n))

(* Dropping the l low bits of x * 2^(j + l) + y. *)
let lemma_shift_concat (j l:nat) (x y:nat)
  : Lemma (ensures (x * pow2 (j + l) + y) / pow2 l == x * pow2 j + y / pow2 l)
  = M.pow2_plus j l;
    M.paren_mul_right x (pow2 j) (pow2 l);
    assert (x * pow2 (j + l) + y == y + (x * pow2 j) * pow2 l);
    M.lemma_div_plus y (x * pow2 j) (pow2 l)

(* The wx + wy low bits of x * 2^wy + q, for q < 2^wy. *)
let lemma_low_concat (wx wy:pos) (x q:nat)
  : Lemma (requires q < pow2 wy)
          (ensures (x * pow2 wy + q) % pow2 (wx + wy) == (x % pow2 wx) * pow2 wy + q)
  = let p = x % pow2 wx in
    M.pow2_multiplication_modulo_lemma_2 x (wx + wy) wy;
    assert ((x * pow2 wy) % pow2 (wx + wy) == p * pow2 wy);
    M.lemma_mod_plus_distr_l (x * pow2 wy) q (pow2 (wx + wy));
    M.lemma_mod_lt x (pow2 wx);
    M.lemma_mult_le_right (pow2 wy) p (pow2 wx - 1);
    M.distributivity_sub_left (pow2 wx) 1 (pow2 wy);
    M.pow2_plus wx wy;
    M.small_mod (p * pow2 wy + q) (pow2 (wx + wy))

let lemma_concat_across (n:pos) (wx wy:pos) (x y:nat) (h l:nat)
  : Lemma (requires y < pow2 n /\ l < n /\ n <= h /\ wx = h - n + 1 /\ wy = n - l)
          (ensures ((x * pow2 n + y) / pow2 l) % pow2 (wx + wy) ==
                   ((x / pow2 0) % pow2 wx) * pow2 wy + (y / pow2 l) % pow2 wy)
  = assert_norm (pow2 0 == 1);
    lemma_shift_concat wy l x y;
    M.lemma_div_lt_nat y n l;
    M.small_mod (y / pow2 l) (pow2 wy);
    lemma_low_concat wx wy x (y / pow2 l)

(* y is the bits [h:l] of x, which are k bits. *)
let lemma_piece (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                (w k:pos) (h l:nat) (x y:expr)
  : Lemma (requires BV.bv_model i project /\ D.scoped [] x /\ D.scoped [] y /\
                    get_sort x == BV.bv_sort w /\ k = h - l + 1 /\ piece w h l x y)
          (ensures h < w /\ get_sort y == BV.bv_sort k /\
                   project k (eval i y rho) == (project w (eval i x rho) / pow2 l) % pow2 k)
  = if l = 0 && h + 1 = w && y = x then (
      BV.lemma_word i rho project w x;
      M.small_mod (project w (eval i x rho)) (pow2 w))
    else lemma_slice i rho project w h l x y

(* The three cases of concatenated, for the value x * 2^n + y of the
   concatenation of xt (x, width m) and yt (y, width n); the slice has k bits. *)
let lemma_concatenated_low (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                           (n k:pos) (h l:nat) (x y:nat) (yt b:expr)
  : Lemma (requires BV.bv_model i project /\ D.scoped [] yt /\ D.scoped [] b /\
                    get_sort yt == BV.bv_sort n /\ project n (eval i yt rho) == y /\
                    h < n /\ k = h - l + 1 /\ piece n h l yt b)
          (ensures get_sort b == BV.bv_sort k /\
                   project k (eval i b rho) == ((x * pow2 n + y) / pow2 l) % pow2 k)
  = lemma_piece i rho project n k h l yt b;
    lemma_concat_low n x y h l

let lemma_concatenated_high (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                            (m n k:pos) (h l:nat) (x y:nat) (xt b:expr)
  : Lemma (requires BV.bv_model i project /\ D.scoped [] xt /\ D.scoped [] b /\
                    get_sort xt == BV.bv_sort m /\ project m (eval i xt rho) == x /\
                    y < pow2 n /\ n <= l /\ l <= h /\ k = h - l + 1 /\ piece m (h - n) (l - n) xt b)
          (ensures get_sort b == BV.bv_sort k /\
                   project k (eval i b rho) == ((x * pow2 n + y) / pow2 l) % pow2 k)
  = lemma_piece i rho project m k (h - n) (l - n) xt b;
    lemma_concat_high n x y h l

let lemma_concatenated_across (i:interpretation value) (rho:env value)
                              (project:pos -> value -> int)
                              (m n k:pos) (h l:nat) (x y:nat) (xt yt b:expr) (d:BV.concatenation)
  : Lemma (requires BV.bv_model i project /\ D.scoped [] xt /\ D.scoped [] yt /\ D.scoped [] b /\
                    get_sort xt == BV.bv_sort m /\ project m (eval i xt rho) == x /\
                    get_sort yt == BV.bv_sort n /\ project n (eval i yt rho) == y /\
                    y < pow2 n /\ l < n /\ n <= h /\ k = h - l + 1 /\
                    BV.concat_parts b == Some d /\
                    d.left_width = h - n + 1 /\ d.right_width = n - l /\
                    piece m (h - n) 0 xt d.left /\ piece n (n - 1) l yt d.right)
          (ensures get_sort b == BV.bv_sort k /\
                   project k (eval i b rho) == ((x * pow2 n + y) / pow2 l) % pow2 k)
  = BV.lemma_concat_parts i rho project b d;
    lemma_piece i rho project m d.left_width (h - n) 0 xt d.left;
    lemma_piece i rho project n d.right_width (n - 1) l yt d.right;
    lemma_concat_across n d.left_width d.right_width x y h l

let lemma_concatenated (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                       (a b:expr)
  : Lemma (requires BV.bv_model i project /\ D.scoped [] a /\ D.scoped [] b /\ concatenated a b)
          (ensures eval i a rho == eval i b rho)
  = let s = Some?.v (BV.extract_parts a) in
    BV.lemma_extract_parts i rho project a s;
    let c = Some?.v (BV.concat_parts s.operand) in
    BV.lemma_concat_parts i rho project s.operand c;
    let m = c.left_width in
    let n = c.right_width in
    BV.lemma_word i rho project m c.left;
    BV.lemma_word i rho project n c.right;
    let x = project m (eval i c.left rho) in
    let y = project n (eval i c.right rho) in
    assert (project s.source_width (eval i s.operand rho) == x * pow2 n + y);
    let k = s.high - s.low + 1 in
    if s.high < n then lemma_concatenated_low i rho project n k s.high s.low x y c.right b
    else if n <= s.low then lemma_concatenated_high i rho project m n k s.high s.low x y c.left b
    else lemma_concatenated_across i rho project m n k s.high s.low x y c.left c.right b
           (Some?.v (BV.concat_parts b));
    BV.lemma_reflect i rho project k a b

let lemma_check (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                (a b:expr)
  : Lemma (requires BV.bv_model i project /\ A.term_ite_sound i /\ check a b)
          (ensures eval i a rho == eval i b rho)
  = if distribute a b then lemma_distribute i rho project a b
    else if conditional a b then lemma_conditional i rho project a b
    else lemma_concatenated i rho project a b

let lemma_check_sound (a b:expr) (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (project:pos -> value -> int). BV.bv_model i project) /\
                    A.term_ite_sound i /\ check a b)
          (ensures eval i a rho == eval i b rho) =
  let aux (project:pos -> value -> int)
    : Lemma (requires BV.bv_model i project) (ensures eval i a rho == eval i b rho) =
    lemma_check i rho project a b in
  FStar.Classical.exists_elim (eval i a rho == eval i b rho)
    #(pos -> value -> int) #(fun project -> BV.bv_model i project) () (fun project -> aux project)
