module ZeroExtAudit
module L = FStar.List.Tot

(* Self-contained model of the PR's zero_extend rewrite and append_number lemma. *)
let rec bits_number (bs:list bool) : Tot int =
  match bs with
  | [] -> 0
  | b :: r -> (if b then 1 else 0) + 2 * bits_number r

(* Obligation 1: zero_extend_rewrite value preservation under the concat model law
   project(l+r)(concat) = project l left * 2^r + project r right, literal zero projects to 0 *)
let zext_value (w:pos) (k:pos) (x:int)
  : Lemma (0 * pow2 w + x == x /\ (k + w) == (w + k)) = ()

(* Obligation 2: sort/width guard: rewrite range (extra+input) equals the original range (input+extra) *)
let zext_width (w:pos) (k:nat{w + k <= 4096})
  : Lemma (k + w <= 4096 /\ k + w == w + k) = ()

(* Obligation 3: lemma_append_number (calc form from the PR) *)
let rec lemma_append_number (xs ys:list bool)
  : Lemma (ensures bits_number (xs @ ys) == bits_number xs + pow2 (L.length xs) * bits_number ys)
          (decreases xs)
  = match xs with
    | [] -> ()
    | b :: rest ->
      lemma_append_number rest ys;
      FStar.Math.Lemmas.pow2_plus 1 (L.length rest);
      assert_norm (pow2 1 == 2)
