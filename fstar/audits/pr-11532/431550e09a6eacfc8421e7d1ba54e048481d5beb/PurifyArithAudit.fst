module PurifyArithAudit


let abs (y:int) : int = if y >= 0 then y else -y

(* Constraints pushed by process_idiv when y <> 0 (the y = 0 disjuncts are false). *)
let idiv_cnstr (x y k1 k2:int) : prop =
  x == k1 * y + k2 /\ 0 <= k2 /\ (y <= 0 \/ k2 < y) /\ (y >= 0 \/ k2 < -1 * y)

(* O1: for y <> 0 the constraints force the Euclidean quotient and remainder. *)
let nz_lemma (d y:int) : Lemma (requires y <> 0 /\ d <> 0) (ensures abs (d * y) >= abs y) =
  if d > 0 then assert (d * y - y == (d - 1) * y) else ()

let o1_unique (x y k1 k2 j1 j2:int)
  : Lemma (requires y <> 0 /\ idiv_cnstr x y k1 k2 /\ idiv_cnstr x y j1 j2)
          (ensures k1 == j1 /\ k2 == j2)
  = assert (k2 < abs y /\ j2 < abs y);
    assert ((k1 - j1) * y == j2 - k2);
    if k1 = j1 then () else begin
      FStar.Math.Lemmas.lemma_abs_mul (k1 - j1) y;
      assert (abs ((k1 - j1) * y) >= abs y)
    end

(* O2: Euclidean witness exists (constraints are satisfiable, so purification does not make things unsat). *)
let o2_exists (x y:int)
  : Lemma (requires y <> 0)
          (ensures exists k1 k2. idiv_cnstr x y k1 k2)
  = if y > 0 then begin
      FStar.Math.Lemmas.euclidean_division_definition x y;
      FStar.Math.Lemmas.lemma_mod_lt x y;
      assert (idiv_cnstr x y (x / y) (x % y))
    end else begin
      let p : pos = -y in
      FStar.Math.Lemmas.euclidean_division_definition x p;
      FStar.Math.Lemmas.lemma_mod_lt x p;
      assert (idiv_cnstr x y (-(x / p)) (x % p))
    end

(* O3: base process_mod passed the mod decl to process_idiv, so the defining premise
   made k1 = (mod x y). For x=5, y=2 that premise (k1 = 1) together with the idiv
   constraints is unsatisfiable, so the th-lemma premise was not a valid local fact. *)
let base_mod_defect () : Lemma (forall (k2:int). ~(idiv_cnstr 5 2 (5 % 2) k2)) = ()

(* With the PR's quotient definition k1 = div x y = 2, k2 = 1 satisfies the constraints. *)
let pr_mod_ok () : Lemma (idiv_cnstr 5 2 (5 / 2) (5 % 2)) = ()
