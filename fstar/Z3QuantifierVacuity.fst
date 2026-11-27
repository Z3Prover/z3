module Z3QuantifierVacuity

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
module Q = Z3QuantifierNnf
module L = FStar.List.Tot

include Z3QuantifierVacuitySyntax
include Z3QuantifierVacuitySemantics

let all_assignments (i:interpretation value) (rho:env value)
                    (count:nat) (body:expr) (truth:bool) : prop =
  all_assignments_by (fun v -> v == VBool true) i rho count body truth

let lemma_all_assignments (n count:nat) (body result:expr) (truth:bool)
                          (i:interpretation value) (rho:env value)
  : Lemma (requires quant_extensional i /\ n < count /\ lower n body == Some result)
          (ensures all_assignments i rho count body truth <==>
                   all_assignments i rho (count - 1) result truth) =
  lemma_all_assignments_by (VBool false) (fun v -> v == VBool true)
    n count body result truth i rho

let lemma_quantified_truth (i:interpretation value) (rho:env value)
                           (k:quantifier_kind) (bs:list sort) (body:expr)
  : Lemma (requires Q.quantifier_model i /\ quant_extensional i /\ get_sort body == bool_sort /\
                    (k = Forall_k \/ k = Exists_k))
          (ensures lit_true i rho (quantified k bs body) <==>
            (if k = Forall_k then all_assignments i rho (L.length bs) body true
             else ~(all_assignments i rho (L.length bs) body false))) =
  if bs <> [] then Q.lemma_quantifier_truth i rho k bs body
  else (
    let aux (vs:list value{L.length vs = 0})
      : Lemma (lit_true i (shift vs rho) body <==> lit_true i rho body) =
      (match vs with [] -> () | _ :: _ -> ());
      let pointwise (n:nat) : Lemma (shift vs rho n == rho n) = () in
      FStar.Classical.forall_intro pointwise;
      lemma_same_environment body i (shift vs rho) rho
    in
    FStar.Classical.forall_intro aux;
    aux [];
    FStar.Classical.excluded_middle (lit_true i rho body))

let lemma_remove_sound (n:nat) (e result:expr)
                       (i:interpretation value) (rho:env value)
  : Lemma (requires Q.quantifier_model i /\ boolean_model i /\ quant_extensional i /\
                    remove n e == Some result)
          (ensures eval i e rho == eval i result rho) =
  match e with
  | Quantifier k bs s body ->
    let b = Some?.v (lower n body) in
    let bs' = L.rev (erase n (L.rev bs)) in
    FStar.List.Tot.Properties.rev_length bs;
    lemma_erase_length n (L.rev bs);
    FStar.List.Tot.Properties.rev_length (erase n (L.rev bs));
    lemma_lower_sort n body b;
    Q.lemma_quantifier_truth i rho k bs body;
    lemma_quantified_truth i rho k bs' b;
    lemma_all_assignments n (L.length bs) body b true i rho;
    lemma_all_assignments n (L.length bs) body b false i rho;
    (match bs' with [] -> () | _ :: _ -> ());
    (match eval i e rho, eval i result rho with VBool _, VBool _ -> () | _, _ -> ())
  | _ -> ()

let rec lemma_first_removal_sound (remaining n:nat) (e result:expr)
                                  (i:interpretation value) (rho:env value)
  : Lemma (requires Q.quantifier_model i /\ boolean_model i /\ quant_extensional i /\
                    first_removal remaining n e == Some result)
          (ensures eval i e rho == eval i result rho)
          (decreases remaining) =
  if remaining > 0 then
    match remove n e with
    | Some _ -> lemma_remove_sound n e result i rho
    | None -> lemma_first_removal_sound (remaining - 1) (n + 1) e result i rho

let lemma_step_sound (e result:expr) (i:interpretation value) (rho:env value)
  : Lemma (requires Q.quantifier_model i /\ boolean_model i /\ quant_extensional i /\
                    step e == Some result)
          (ensures eval i e rho == eval i result rho) =
  match e with
  | Quantifier _ bs _ _ -> lemma_first_removal_sound (L.length bs) 0 e result i rho
  | _ -> ()

let rec lemma_equivalent_sound (fuel:nat) (s t:expr)
                               (i:interpretation value) (rho:env value)
  : Lemma (requires Q.quantifier_model i /\ boolean_model i /\ quant_extensional i /\
                    equivalent fuel s t)
          (ensures eval i s rho == eval i t rho)
          (decreases %[fuel; 0]) =
  if s = t || fuel = 0 then ()
  else (
    match step s, step t with
    | Some a, _ ->
      lemma_step_sound s a i rho;
      lemma_equivalent_sound (fuel - 1) a t i rho
    | None, Some b ->
      lemma_step_sound t b i rho;
      lemma_equivalent_sound (fuel - 1) s b i rho
    | None, None ->
      (match s, t with
       | App _ xs, App _ ys -> lemma_equivalent_args_sound (fuel - 1) xs ys i rho
       | Quantifier _ bs _ body, Quantifier _ _ _ body' ->
         let aux (vs:list value{L.length vs = L.length bs})
           : Lemma (eval i body (shift vs rho) == eval i body' (shift vs rho)) =
           lemma_equivalent_sound (fuel - 1) body body' i (shift vs rho)
         in FStar.Classical.forall_intro aux
       | _, _ -> ()))

and lemma_equivalent_args_sound (fuel:nat) (xs ys:list expr)
                                (i:interpretation value) (rho:env value)
  : Lemma (requires Q.quantifier_model i /\ boolean_model i /\ quant_extensional i /\
                    equivalent_args fuel xs ys)
          (ensures eval_args i xs rho == eval_args i ys rho)
          (decreases %[fuel; L.length xs + 1]) =
  match xs, ys with
  | x :: rest, y :: tail ->
    lemma_equivalent_sound fuel x y i rho;
    lemma_equivalent_args_sound fuel rest tail i rho
  | _, _ -> ()
