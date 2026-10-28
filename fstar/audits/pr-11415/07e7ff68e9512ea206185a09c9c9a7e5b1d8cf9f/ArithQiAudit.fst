module ArithQiAudit
module L = FStar.List.Tot

(* Rationals as num/den, den > 0; equality by cross multiplication *)
type rat = { n: int; d: (d:int{d > 0}) }
let rmul (a b: rat) : rat = { n = a.n * b.n; d = a.d * b.d }
let radd (a b: rat) : rat = { n = a.n * b.d + b.n * a.d; d = a.d * b.d }
let req (a b: rat) : bool = a.n * b.d = b.n * a.d
let nonzero (a: rat) : bool = a.n <> 0
(* -1/c as in a.mk_real(-rational(1)/coefficient); c nonzero *)
let neg_inv (c: rat{nonzero c}) : rat =
  if c.n > 0 then { n = - c.d; d = c.n } else { n = c.d; d = - c.n }

(* O1: arith_unify solved step. coefficient*x + rest = 0 with x := (-1/coefficient)*rest *)
let o1_solve (c: rat{nonzero c}) (rest: rat)
  : Lemma (req (radd (rmul c (rmul (neg_inv c) rest)) rest) { n = 0; d = 1 })
  = ()

(* O2: de Bruijn / reversed-binding layout. C++ pushes values for i = hi-1 downto lo. *)
let rec desc (lo hi: nat) (f: nat -> int) : Tot (list int) (decreases (if hi > lo then hi - lo else 0)) =
  if hi <= lo then [] else f (hi - 1) :: desc lo (hi - 1) f

let rec desc_len (lo hi: nat) (f: nat -> int)
  : Lemma (ensures L.length (desc lo hi f) = (if hi > lo then hi - lo else 0))
          (decreases (if hi > lo then hi - lo else 0))
  = if hi <= lo then () else desc_len lo (hi - 1) f

let rec desc_index (lo hi: nat) (f: nat -> int) (j: nat)
  : Lemma (requires lo <= hi /\ j < hi - lo)
          (ensures (desc_len lo hi f; L.index (desc lo hi f) j = f (hi - 1 - j)))
          (decreases (hi - lo))
  = desc_len lo hi f;
    if j = 0 then () else (desc_len lo (hi-1) f; desc_index lo (hi - 1) f (j - 1))

(* guarded replacement: guarded_terms.set(nt - i - 1, cand) targets variable i, lo <= i < nt *)
let o2_guard_slot (lo nt i: nat) (f: nat -> int)
  : Lemma (requires lo <= i /\ i < nt)
          (ensures nt - i - 1 < nt - lo /\ (desc_len lo nt f; L.index (desc lo nt f) (nt - i - 1) = f i))
  = desc_len lo nt f; desc_index lo nt f (nt - i - 1)

(* guard substitution: substitution entry for var (lo_g + k) is source_terms[size-k-1], k < size *)
let o2_guard_subst (lo ns k: nat) (f: nat -> int)
  : Lemma (requires lo <= ns /\ k < ns - lo)
          (ensures (desc_len lo ns f; ns - lo - k - 1 < L.length (desc lo ns f) /\
                    L.index (desc lo ns f) (ns - lo - k - 1) = f (lo + k)))
  = desc_len lo ns f; desc_index lo ns f (ns - lo - k - 1)

(* O3: any ground instance of a forall over nq vars is entailed; instance has the right arity. *)
let o3_instance_sound (nq inner: nat) (body: list int -> prop) (f: nat -> int)
  : Lemma (requires forall (bs: list int{L.length bs = nq}). body bs)
          (ensures (desc_len inner (inner + nq) f;
                    L.length (desc inner (inner + nq) f) = nq /\
                    body (desc inner (inner + nq) f)))
  = desc_len inner (inner + nq) f
