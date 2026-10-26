module AmcGuard
(* Model of the domain-size loop in check_array_map_coherence
   (src/ast/rewriter/array_map_coherence.h lines 157-175, head 61c58a9e).
   n = indices.size(); sizes = finite domain sizes (each >= 1).
   Unbounded nat models uint64 without wraparound; the loop's own checks are
   what justify that (see no_overflow_step). Uninterpreted domains are skipped. *)
open FStar.List.Tot

let rec prod (l: list pos) : pos =
  match l with [] -> 1 | s :: t -> s * prod t

(* One loop step in C++: exceeds iff s > n || ds > n / s; else ds' = ds * s. *)
let step_exceeds (n: nat) (ds: pos) (s: pos) : bool = s > n || ds > n / s

let rec loop (n: nat) (ds: pos) (l: list pos) : Tot (option pos) (decreases l) =
  match l with
  | [] -> Some ds
  | s :: t -> if step_exceeds n ds s then None else loop n (ds * s) t

(* Obligation 1: the single-step test is exactly "ds * s > n". *)
let step_exact (n: nat) (ds: pos) (s: pos)
  : Lemma (step_exceeds n ds s <==> ds * s > n)
  = FStar.Math.Lemmas.lemma_div_mod n s;
    let q = n / s in
    if s > n then begin
      assert (q == 0);
      FStar.Math.Lemmas.lemma_mult_le_right s 1 ds
    end else begin
      if ds > q then FStar.Math.Lemmas.lemma_mult_le_right s (q + 1) ds
      else FStar.Math.Lemmas.lemma_mult_le_right s ds q
    end

(* Obligation 2: no overflow: whenever a step is accepted, the product is <= n,
   hence fits in uint64 if n does (n is a vector size). *)
let no_overflow_step (n: nat) (ds: pos) (s: pos)
  : Lemma (requires not (step_exceeds n ds s)) (ensures ds * s <= n)
  = step_exact n ds s

(* Obligation 3: loop returns Some p exactly when the full product is <= n
   (given ds <= n initially it is the product ds * prod l), and then p = ds * prod l. *)
let rec loop_correct (n: nat) (ds: pos) (l: list pos)
  : Lemma (ensures (match loop n ds l with
                    | Some p -> p == ds * prod l /\ (l <> [] ==> p <= n)
                    | None -> ds * prod l > n))
          (decreases l)
  = match l with
    | [] -> ()
    | s :: t ->
      step_exact n ds s;
      if step_exceeds n ds s then begin
        assert (ds * s > n);
        FStar.Math.Lemmas.paren_mul_right ds s (prod t);
        assert (ds * (s * prod t) >= ds * s)
      end else begin
        loop_correct n (ds * s) t;
        FStar.Math.Lemmas.paren_mul_right ds s (prod t)
      end
