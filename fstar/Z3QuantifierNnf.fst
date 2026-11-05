module Z3QuantifierNnf

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
module L = FStar.List.Tot

let dual (kind:quantifier_kind) : quantifier_kind =
  match kind with Forall_k -> Exists_k | Exists_k -> Forall_k | Lambda_k -> Lambda_k

(* Existential truth is the classical negation of universal falsity. *)
let quantifier_model (i:interpretation value) : prop =
  forall (kind:quantifier_kind) (sorts:list sort) (body:expr) (rho:env value).
    get_sort body == bool_sort /\ (kind = Forall_k \/ kind = Exists_k) ==>
    (lit_true i rho (Quantifier kind sorts bool_sort body) <==>
      (if kind = Forall_k then
         (forall (vs:list value{L.length vs = L.length sorts}).
           lit_true i (shift vs rho) body)
       else
         ~(forall (vs:list value{L.length vs = L.length sorts}).
           ~(lit_true i (shift vs rho) body))))

let lemma_quantifier_truth (i:interpretation value) (rho:env value)
                           (kind:quantifier_kind) (sorts:list sort) (body:expr)
  : Lemma (requires quantifier_model i /\ get_sort body == bool_sort /\
                    (kind = Forall_k \/ kind = Exists_k))
          (ensures lit_true i rho (Quantifier kind sorts bool_sort body) <==>
            (if kind = Forall_k then
               (forall (vs:list value{L.length vs = L.length sorts}).
                 lit_true i (shift vs rho) body)
             else
               ~(forall (vs:list value{L.length vs = L.length sorts}).
                 ~(lit_true i (shift vs rho) body))))
  = ()

let lemma_not_truth (i:interpretation value) (rho:env value) (body:expr)
  : Lemma (requires boolean_model i /\ not_sound i /\ get_sort body == bool_sort)
          (ensures lit_true i rho (mk_not_expr body) <==> ~(lit_true i rho body))
  = match eval i body rho with VBool _ -> () | _ -> ()

let lemma_duality (i:interpretation value) (rho:env value)
                  (kind:quantifier_kind) (sorts:list sort) (body:expr)
  : Lemma (requires quantifier_model i /\ boolean_model i /\ not_sound i /\
                    get_sort body == bool_sort /\ (kind = Forall_k \/ kind = Exists_k))
          (ensures eval i (mk_not_expr (Quantifier kind sorts bool_sort body)) rho ==
                   eval i (Quantifier (dual kind) sorts bool_sort (mk_not_expr body)) rho)
  = lemma_quantifier_truth i rho kind sorts body;
    lemma_quantifier_truth i rho (dual kind) sorts (mk_not_expr body);
    lemma_not_truth i rho (Quantifier kind sorts bool_sort body);
    let negated (vs:list value{L.length vs = L.length sorts})
      : Lemma (lit_true i (shift vs rho) (mk_not_expr body) <==>
               ~(lit_true i (shift vs rho) body))
      = lemma_not_truth i (shift vs rho) body in
    FStar.Classical.forall_intro negated;
    let positive (vs:list value{L.length vs = L.length sorts})
      : Lemma (~(lit_true i (shift vs rho) (mk_not_expr body)) <==>
               lit_true i (shift vs rho) body) = () in
    FStar.Classical.forall_intro positive;
    match eval i (mk_not_expr (Quantifier kind sorts bool_sort body)) rho,
          eval i (Quantifier (dual kind) sorts bool_sort (mk_not_expr body)) rho with
    | VBool _, VBool _ -> ()
    | _, _ -> ()
