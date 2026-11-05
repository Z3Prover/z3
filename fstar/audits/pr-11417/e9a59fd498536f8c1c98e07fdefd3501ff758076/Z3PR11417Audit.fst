module Z3PR11417Audit
module L = FStar.Math.Lemmas

(* ---- Obligation 1/2: nested symbolic rotation folding (bv_rewriter.cpp) ---- *)
(* Rotation amount semantics: ext_rotate_left x y rotates by (y mod w).
   We model rotations by their effective amount mod w; composition is addition mod w. *)
let bvadd (n:pos) (a b:nat) : nat = (a + b) % n          (* n = 2^w *)
let bvsub (n:pos) (a b:nat) : nat = (a - b) % n

(* Intended: effective amount of fold must equal (y+z) mod w *)
let ok_add (w n y z:nat{w>0 /\ n>0}) = (bvadd n y z) % w = (y + z) % w

(* Obligation 1: counterexample at w=3, n=8, y=7, z=1 (guard: pre-PR code had no width guard;
   3 is not a power of two so the PR guard returns BR_FAILED) *)
let cex_rot_add : squash (not (ok_add 3 8 7 1)) = ()
let cex_rot_sub : squash (not ((bvsub 8 1 7) % 3 = (1 - 7) % 3)) = ()

(* Obligation 2: soundness of the guarded fold when w = 2^k (w | 2^w)
   For w power of two, w divides n=2^w. *)
let rec k_lt_pow2 (k:nat) : Lemma (k < pow2 k) = if k > 0 then k_lt_pow2 (k-1)

let fold_add_sound (k:nat) (y z:nat)
  : Lemma (let w = pow2 k in let n = pow2 w in bvadd n y z % w = (y + z) % w)
  = k_lt_pow2 k;
    L.pow2_modulo_modulo_lemma_1 (y+z) k (pow2 k)

let fold_sub_sound (k:nat) (y z:nat)
  : Lemma (let w = pow2 k in let n = pow2 w in bvsub n z y % w = (z - y) % w)
  = k_lt_pow2 k;
    L.pow2_modulo_modulo_lemma_1 (z-y) k (pow2 k)

(* ---- Obligation 3: bvsmod int-blast translation (bv2int_translator.cpp) ---- *)
(* N = 2^w (even, >= 2); x,y in [0,N). sign := v >= N/2 ; abs := sign ? N-v : v *)
let sgn (n:pos) (v:int) = v >= n/2
let absv (n:pos) (v:int) = if sgn n v then n - v else v
let sv (n:pos) (v:int) = if sgn n v then v - n else v

(* translator output (before final mod N), u = absx mod absy, with SMT mod; absy > 0 here *)
let tr (n:pos) (x y:int{y <> 0 /\ absv n y > 0}) : int =
  let u = (absv n x) % (absv n y) in
  let sx = sgn n x in let sy = sgn n y in
  if y = 0 then x
  else if u = 0 then 0
  else if (not sx) && sy then u + y
  else if sx && not sy then y - u
  else if (not sx) && (not sy) then u
  else -u

(* Spec of bvsmod for sy<>0: result r (signed) = sx - sy*k, with r=0 or sign r = sign sy, |r|<|sy| *)
let spec (n:pos) (x y r:int) : prop =
  exists (k:int). sv n r = sv n x - sv n y * k /\
    (sv n r = 0 \/ (sv n r > 0 == (sv n y > 0))) /\ abs (sv n r) < abs (sv n y)

let mod_n_range (n:pos) (v:int) : Lemma (v % n >= 0 /\ v % n < n) = ()

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let bsmod_sound (n:pos{n >= 2 /\ n % 2 = 0}) (x y:int)
  : Lemma (requires 0 <= x /\ x < n /\ 0 < y /\ y < n)
          (ensures  spec n x y ((tr n x y) % n))
  = let ax = absv n x in let ay = absv n y in
    let u = ax % ay in
    let q = ax / ay in
    L.euclidean_division_definition ax ay;
    assert (ax = q * ay + u);
    assert (u >= 0 /\ u < ay);
    let r = (tr n x y) % n in
    let h = n / 2 in
    assert (n = 2 * h);
    if u = 0 then begin
      assert (r = 0);
      // sx = +-q*ay = sy * (+-q or -+q)
      if (not (sgn n x)) && not (sgn n y) then assert (sv n x - sv n y * q = 0)
      else if sgn n x && sgn n y then assert (sv n x - sv n y * q = 0)
      else if sgn n x then assert (sv n x - sv n y * (-q) = 0)
      else assert (sv n x - sv n y * (-q) = 0)
    end else begin
      let sx = sgn n x in let sy = sgn n y in
      if (not sx) && not sy then begin
        L.small_mod u n; assert (r = u);
        assert (sv n r = u); assert (sv n x - sv n y * q = u)
      end else if sx && sy then begin
        // sv r = -u, in range since u < ay <= h
        assert (u < ay /\ ay <= h);
        L.lemma_mod_sub_1 u n; L.small_mod u n;
        assert (r = n - u);
        assert (sgn n r);
        assert (sv n r = -u);
        assert (sv n x - sv n y * q = -u)
      end else if sx && not sy then begin
        // y - u in (0, y)
        L.small_mod (y - u) n; assert (r = y - u);
        assert (y - u > 0 /\ y - u < y /\ y < h);
        assert (not (sgn n r));
        assert (sv n x - sv n y * (-q-1) = y - u)
      end else begin
        // y' = y - n <0, result y + u in [y... ) ; y + u = sv y + n + u
        assert (sv n y = y - n);
        assert (u + y < n);
        L.small_mod (u + y) n; assert (r = u + y);
        assert (sgn n r);
        assert (sv n r = u + y - n);
        assert (sv n r = u + sv n y /\ sv n r < 0 /\ abs (sv n r) < abs (sv n y));
        assert (sv n x - sv n y * (-q-1) = u + sv n y)
      end
    end
#pop-options
