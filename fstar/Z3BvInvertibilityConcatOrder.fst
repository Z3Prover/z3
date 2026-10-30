module Z3BvInvertibilityConcatOrder

open Z3BvTheory
module I = Z3BvInvertibility
module M = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let lemma_lexicographic (p:pos) (a c:int) (b:nat{b < p}) (d:nat{d < p})
  : Lemma
    ((a * p + b == c * p + d <==> a == c /\ b == d) /\
     (a * p + b < c * p + d <==> a < c \/ (a == c /\ b < d)) /\
     (a * p + b <= c * p + d <==> a < c \/ (a == c /\ b <= d))) =
  if a < c then M.lemma_mult_le_right p (a + 1) c
  else if c < a then M.lemma_mult_le_right p (c + 1) a
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let lemma_range (#n:pos) (a:bv n)
  : Lemma (0 <= a /\ a < pow2 n) = ()

let lemma_signed_equal (#n:pos) (a c:bv n)
  : Lemma (to_int_signed a == to_int_signed c <==> a == c) =
  lemma_range a;
  lemma_range c

let lemma_concat_signed (#n:pos) (#m:pos) (a:bv n) (b:bv m)
  : Lemma
    (msb (bv_concat a b) == msb a /\
     to_int_signed (bv_concat a b) == to_int_signed a * pow2 m + b) =
  lemma_range a;
  lemma_range b;
  M.pow2_plus n m;
  M.pow2_plus (n - 1) m;
  lemma_lexicographic (pow2 m) a (pow2 (n - 1)) b 0;
  M.distributivity_sub_left a (pow2 n) (pow2 m)

let lexicographic (#n:pos) (#m:pos) (r:I.relation)
  (a:bv n) (b:bv m) (c:bv n) (d:bv m) : bool =
  match r with
  | I.Eq -> a = c && b = d
  | I.Ne -> a <> c || b <> d
  | I.Ult -> a < c || (a = c && b < d)
  | I.Ugt -> a > c || (a = c && b > d)
  | I.Ule -> a < c || (a = c && b <= d)
  | I.Uge -> a > c || (a = c && b >= d)
  | I.Slt -> to_int_signed a < to_int_signed c || (a = c && b < d)
  | I.Sgt -> to_int_signed a > to_int_signed c || (a = c && b > d)
  | I.Sle -> to_int_signed a < to_int_signed c || (a = c && b <= d)
  | I.Sge -> to_int_signed a > to_int_signed c || (a = c && b >= d)

let lemma_concat_order (#n:pos) (#m:pos) (r:I.relation)
  (a:bv n) (b:bv m) (c:bv n) (d:bv m)
  : Lemma
    (I.holds r (bv_concat a b) (bv_concat c d) <==>
      lexicographic r a b c d) =
  lemma_range a;
  lemma_range b;
  lemma_range c;
  lemma_range d;
  lemma_lexicographic (pow2 m) a c b d;
  lemma_lexicographic (pow2 m) c a d b;
  match r with
  | I.Eq | I.Ne | I.Ult | I.Ugt | I.Ule | I.Uge -> ()
  | I.Slt | I.Sgt | I.Sle | I.Sge ->
    lemma_concat_signed a b;
    lemma_concat_signed c d;
    lemma_signed_equal a c;
    lemma_lexicographic (pow2 m) (to_int_signed a) (to_int_signed c) b d;
    lemma_lexicographic (pow2 m) (to_int_signed c) (to_int_signed a) d b

let lemma_split (#n:pos) (#m:pos) (t:bv (n + m))
  : Lemma
    (bv_concat (bv_extract (n + m - 1) m t) (bv_extract (m - 1) 0 t) == t) =
  lemma_range t;
  M.lemma_div_lt t (n + m) m;
  M.lemma_div_mod t (pow2 m);
  M.modulo_lemma (t / pow2 m) (pow2 n);
  M.modulo_lemma t (pow2 (n + m));
  M.small_div t (pow2 (n + m));
  M.swap_mul (pow2 m) (t / pow2 m)
#pop-options
