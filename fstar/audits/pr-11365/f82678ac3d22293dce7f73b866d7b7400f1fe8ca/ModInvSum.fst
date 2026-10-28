module ModInvSum
open FStar.List.Tot

(* Model of the new branch of arith_rewriter::mk_eq_mod (PR #11365).
   Terms are abstracted by their integer values ts; cs are coefficients. *)
let symmod (a:int) (p:pos) : int =
  let r = a % p in if 2 * r > p then r - p else r

let rec dot (cs ts:list int) : Tot int (decreases cs) =
  match cs, ts with
  | c::cs', t::ts' -> c * t + dot cs' ts'
  | _ -> 0

let rec scale (p:pos) (b:int) (cs:list int) : list int =
  match cs with [] -> [] | c::cs' -> symmod (b * c) p :: scale p b cs'

let cong (p:pos) (x y:int) : prop = exists (k:int). x - y == k * p

let symmod_cong (a:int) (p:pos) : Lemma (cong p (symmod a p) a) =
  FStar.Math.Lemmas.lemma_div_mod a p;
  let q = a / p in
  if 2 * (a % p) > p then assert (symmod a p - a == (-(q+1)) * p)
  else assert (symmod a p - a == (-q) * p)

(* O1: reduced coefficients are in (-p/2, p/2] *)
let symmod_bound (a:int) (p:pos) : Lemma (2 * symmod a p <= p /\ 2 * symmod a p > - p) = ()

let cong_add (p:pos) (x y u v:int) : Lemma (requires cong p x y /\ cong p u v) (ensures cong p (x+u) (y+v)) =
  eliminate exists k1 k2. (x - y == k1 * p /\ u - v == k2 * p) with (assert ((x+u) - (y+v) == (k1+k2) * p))

let cong_mul_l (p:pos) (b x y:int) : Lemma (requires cong p x y) (ensures cong p (b*x) (b*y)) =
  eliminate exists k. x - y == k * p with (assert (b*x - b*y == (b*k) * p))

let cong_trans (p:pos) (x y z:int) : Lemma (requires cong p x y /\ cong p y z) (ensures cong p x z) =
  eliminate exists k1 k2. (x - y == k1 * p /\ y - z == k2 * p) with (assert (x - z == (k1+k2) * p))

let cong_sym (p:pos) (x y:int) : Lemma (requires cong p x y) (ensures cong p y x) =
  eliminate exists k. x - y == k * p with (assert (y - x == (-k) * p))

(* O2: sum of reduced scaled terms is congruent to b * original sum *)
let rec scale_cong (p:pos) (b:int) (cs ts:list int)
  : Lemma (ensures cong p (dot (scale p b cs) ts) (b * dot cs ts)) (decreases cs) =
  match cs, ts with
  | c::cs', t::ts' ->
    scale_cong p b cs' ts';
    symmod_cong (b*c) p;
    cong_mul_l p t (symmod (b*c) p) (b*c);
    cong_add p (t * symmod (b*c) p) (t * (b*c)) (dot (scale p b cs') ts') (b * dot cs' ts');
    assert (t * (b*c) + b * dot cs' ts' == b * (c*t + dot cs' ts'))
  | _ -> ()

let mod_imp_cong (p:pos) (x y:int) : Lemma (requires x % p == y % p) (ensures cong p x y) =
  FStar.Math.Lemmas.lemma_div_mod x p;
  FStar.Math.Lemmas.lemma_div_mod y p;
  assert (x - y == (x/p - y/p) * p)

let cong_imp_mod (p:pos) (x y:int) : Lemma (requires cong p x y) (ensures x % p == y % p) =
  eliminate exists k. x - y == k * p with (FStar.Math.Lemmas.lemma_mod_plus y k p)

(* O3: soundness of the rewrite. bc0 + a p = 1 comes from the Bezout call gcd(p,coeff,a,b)==1.
   For 0<=l<p:  (off + sum) mod p == l  <=>  (sum') mod p == (b*(l-off)) mod p *)
let rewrite_sound (p:pos) (a b c0 off l:int) (cs ts:list int)
  : Lemma (requires 0 <= l /\ l < p /\ a * p + b * c0 == 1)
          (ensures ((off + dot cs ts) % p == l) <==>
                   ((dot (scale p b cs) ts) % p == (b * (l - off)) % p)) =
  let s = dot cs ts in
  scale_cong p b cs ts;
  (* forward *)
  let fwd () : Lemma (requires (off + s) % p == l) (ensures (dot (scale p b cs) ts) % p == (b * (l - off)) % p) =
    FStar.Math.Lemmas.lemma_div_mod (off + s) p;
    assert (s - (l - off) == ((off+s)/p) * p);
    cong_mul_l p b s (l - off);
    cong_trans p (dot (scale p b cs) ts) (b * s) (b * (l - off));
    cong_imp_mod p (dot (scale p b cs) ts) (b * (l - off))
  in
  let bwd () : Lemma (requires (dot (scale p b cs) ts) % p == (b * (l - off)) % p) (ensures (off + s) % p == l) =
    FStar.Math.Lemmas.lemma_div_mod (dot (scale p b cs) ts) p;
    FStar.Math.Lemmas.lemma_div_mod (b * (l - off)) p;
    let u = dot (scale p b cs) ts in
    let w = b * (l - off) in
    mod_imp_cong p u w;
    cong_sym p u (b * s);
    cong_trans p (b * s) u w;
    cong_mul_l p c0 (b * s) w;
    let d = s - (l - off) in
    eliminate exists k. (c0 * (b*s) - c0 * w == k * p) with (
      FStar.Math.Lemmas.paren_mul_right c0 b s;
      FStar.Math.Lemmas.paren_mul_right c0 b (l - off);
      FStar.Math.Lemmas.distributivity_sub_right (c0 * b) s (l - off);
      assert (c0 * (b*s) - c0 * w == (c0 * b) * d);
      assert (c0 * b == 1 - a * p);
      assert ((1 - a * p) * d == d - (a * d) * p);
      let m = k + a * d in
      assert (d == m * p);
      assert ((off + s) - l == m * p);
      FStar.Math.Lemmas.lemma_mod_plus l m p;
      FStar.Math.Lemmas.small_mod l p)
  in
  Classical.move_requires fwd ();
  Classical.move_requires bwd ()

(* Issue #11360 instance: p = 100000007, b = 31337042 inverts 8691641 and symmod gives 1 *)
let issue_instance () : Lemma (symmod (31337042 * 8691641) 100000007 == 1 /\ (31337042 * 1) % 100000007 == 31337042) =
  assert_norm (symmod (31337042 * 8691641) 100000007 == 1)
