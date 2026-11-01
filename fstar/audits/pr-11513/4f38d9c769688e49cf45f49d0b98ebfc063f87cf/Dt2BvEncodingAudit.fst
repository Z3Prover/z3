module Dt2BvEncodingAudit
(* Model of dt2bv_proof_converter::insert_enum (src/tactic/bv/dt2bv_proof_converter.cpp,
   head 4f38d9c769688e49cf45f49d0b98ebfc063f87cf): encoding starts as numeral n-1 and
   for i = n-2 downto 0 wraps it as ite(subject = c_i, i, encoding).
   Constructors are modelled by their distinct indices; subject s ranges over [0,n). *)

(* loop state after wrapping indices i..n-2 (i = n-1 means no wrapping) *)
let rec enc (n:pos) (i:nat{i <= n-1}) (s:nat) : Tot nat (decreases (n-1-i)) =
  if i = n-1 then n-1
  else if s = i then i else enc n (i+1) s
(* ite order: outermost test is c_0, matching the downward loop that wraps last at i=0 *)

let rec pow2' (w:nat) : Tot pos = if w = 0 then 1 else 2 * pow2' (w-1)

(* Obligation 1: the encoding of constructor s is its index *)
let rec ob1 (n:pos) (i:nat{i <= n-1}) (s:nat{i <= s /\ s < n})
  : Lemma (ensures enc n i s = s) (decreases (n-1-i)) =
  if i = n-1 then () else if s = i then () else ob1 n (i+1) s

(* Obligation 2: injective on the domain *)
let ob2 (n:pos) (s t:nat{s < n /\ t < n})
  : Lemma (enc n 0 s = enc n 0 t ==> s = t) = ob1 n 0 s; ob1 n 0 t

(* Obligation 3: guard n <= 2^w makes every numeral < 2^w, so no wrapping *)
let ob3 (n:pos) (w:nat) (s:nat{s < n})
  : Lemma (requires n <= pow2' w) (ensures enc n 0 s < pow2' w) = ob1 n 0 s

(* Counter-check: the rejected case n > 2^w genuinely wraps (witness n=3,w=1, s=2) *)
let witness () : Lemma (3 > pow2' 1 /\ enc 3 0 2 = 2 /\ 2 >= pow2' 1) = ob1 3 0 2
