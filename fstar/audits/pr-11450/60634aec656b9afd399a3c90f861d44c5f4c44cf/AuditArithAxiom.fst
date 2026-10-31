module AuditArithAxiom

(* Abstract row: value = c*m + k, "<= 0" or "< 0" when strict. *)
let holds (strict:bool) (v:int) : bool = if strict then v < 0 else v <= 0

(* check_ineq on a variable-free row. *)
let check_ineq (strict:bool) (k:int) : bool = k > 0 || (strict && k = 0)

(* is_infeasible: single term (mod u n), 0 <= m <= abs(n)-1 = nm1; c<0 shifts the constant. *)
let is_infeasible (strict:bool) (c k nm1:int) : bool =
  check_ineq strict (if c < 0 then k + c * nm1 else k)

(* O1: soundness of is_infeasible for every m in the range of mod (nm1 >= 0). *)
let o1 (strict:bool) (c k nm1 m:int)
  : Lemma (requires nm1 >= 0 /\ 0 <= m /\ m <= nm1 /\ is_infeasible strict c k nm1)
          (ensures ~(holds strict (c * m + k)))
  = if c < 0 then assert (c * m >= c * nm1) else assert (c * m >= 0)

(* O2: expand_definitions on (mod u n): u = n*d + m gives c*m = c*u - (c*n)*d. *)
let o2 (c u n d m:int)
  : Lemma (requires u == n * d + m) (ensures c * m == c * u - (c * n) * d)
  = ()

(* O2b: real division by nonzero numeral: n*q = u gives c*q*n = c*u, i.e. c*q = (c/n)*u. *)
let o2b (c u n q:int)
  : Lemma (requires n * q == u) (ensures (c * q) * n == c * u)
  = ()

(* O3: implies_nonnegative. Row r = (negated literal) satisfies r <= 0 (or < 0);
   t = a*u; lambda > 0 with r + lambda*t = K >= 0 constant. Then t >= 0. *)
let o3 (strict:bool) (r t lam kk:int)
  : Lemma (requires lam > 0 /\ kk >= 0 /\ holds strict r /\ r + lam * t == kk)
          (ensures t >= 0)
  = if t < 0 then assert (lam * t < 0)

(* O3b: abs case. With s in {1,-1}, s*u >= 0 implies abs u = s*u. *)
let abs_int (u:int) : int = if u >= 0 then u else - u
let o3b (s u:int)
  : Lemma (requires (s == 1 \/ s == -1) /\ s * u >= 0) (ensures abs_int u == s * u)
  = ()
