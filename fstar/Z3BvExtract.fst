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

   Addition and multiplication are only distributed over the low bits
   (l = 0): bits above the lowest one depend on carries out of the discarded
   bits, so ((_ extract 1 1) (bvadd #b01 #b01)) = #b1 but
   (bvadd ((_ extract 1 1) #b01) ((_ extract 1 1) #b01)) = #b0.
   The inner extractions are those of mk_extract_proc, which composes an
   extraction of an extraction: for xi = ((_ extract h2 l2) z), the target
   argument is ((_ extract (h + l2) (l + l2)) z).

   Every width and index is read from the native declarations, which
   Z3BvLemma.extract_parts and Z3BvLemma.operation already check against the
   sorts, and is compared as an integer with the corresponding width of the
   other side. The guard of a conditional is not interpreted; it must be the
   same term on both sides. Both sides must be closed terms, as required by
   Z3BvLemma.bv_model; steps under binders are left unchecked. *)

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

let check (a b:expr) : bool =
  (distribute a b || conditional a b) && D.scoped [] a && D.scoped [] b

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

let lemma_check (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                (a b:expr)
  : Lemma (requires BV.bv_model i project /\ A.term_ite_sound i /\ check a b)
          (ensures eval i a rho == eval i b rho)
  = if distribute a b then lemma_distribute i rho project a b
    else lemma_conditional i rho project a b

let lemma_check_sound (a b:expr) (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (project:pos -> value -> int). BV.bv_model i project) /\
                    A.term_ite_sound i /\ check a b)
          (ensures eval i a rho == eval i b rho) =
  let aux (project:pos -> value -> int)
    : Lemma (requires BV.bv_model i project) (ensures eval i a rho == eval i b rho) =
    lemma_check i rho project a b in
  FStar.Classical.exists_elim (eval i a rho == eval i b rho)
    #(pos -> value -> int) #(fun project -> BV.bv_model i project) () (fun project -> aux project)
