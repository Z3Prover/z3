module Z3QuantifierVacuitySemantics

open Z3AstTheory
open Z3QuantifierVacuitySyntax
module L = FStar.List.Tot

let removed_environment (#value:Type) (cutoff:nat) (source target:env value) : prop =
  forall (n:nat). n <> cutoff ==> source n == target (if n < cutoff then n else n - 1)

let lemma_removed_shift (#value:Type) (cutoff:nat) (source target:env value) (vs:list value)
  : Lemma (requires removed_environment cutoff source target)
          (ensures removed_environment (cutoff + L.length vs) (shift vs source) (shift vs target)) =
  let aux (n:nat{n <> cutoff + L.length vs}) : Lemma
      (shift vs source n ==
       shift vs target (if n < cutoff + L.length vs then n else n - 1)) = ()
  in FStar.Classical.forall_intro aux

let lemma_erased_environment (#value:Type) (n:nat) (vs:list value) (rho:env value)
  : Lemma (requires n < L.length vs)
          (ensures removed_environment n (shift vs rho) (shift (erase n vs) rho)) =
  lemma_erase_length n vs;
  let aux (j:nat{j <> n}) : Lemma
      (shift vs rho j ==
       shift (erase n vs) rho (if j < n then j else j - 1)) =
    if j < L.length vs then lemma_erase_index n j vs
  in FStar.Classical.forall_intro aux

let rec lemma_lower_sound (#value:Type) (cutoff:nat) (e result:expr)
                          (i:interpretation value) (source target:env value)
  : Lemma (requires quant_extensional i /\ lower cutoff e == Some result /\
                    removed_environment cutoff source target)
          (ensures eval i e source == eval i result target)
          (decreases e) =
  match e with
  | Var _ _ -> ()
  | App _ args ->
    lemma_lower_args_sound cutoff args (Some?.v (lower_args cutoff args)) i source target
  | Quantifier k bs s body ->
    let b = Some?.v (lower (cutoff + L.length bs) body) in
    let aux (vs:list value{L.length vs = L.length bs})
      : Lemma (eval i body (shift vs source) == eval i b (shift vs target)) =
      lemma_removed_shift cutoff source target vs;
      lemma_lower_sound (cutoff + L.length bs) body b i (shift vs source) (shift vs target)
    in FStar.Classical.forall_intro aux

and lemma_lower_args_sound (#value:Type) (cutoff:nat) (args results:list expr)
                           (i:interpretation value) (source target:env value)
  : Lemma (requires quant_extensional i /\ lower_args cutoff args == Some results /\
                    removed_environment cutoff source target)
          (ensures eval_args i args source == eval_args i results target)
          (decreases args) =
  match args, results with
  | a :: rest, b :: xs ->
    lemma_lower_sound cutoff a b i source target;
    lemma_lower_args_sound cutoff rest xs i source target
  | _, _ -> ()

let all_assignments_by (#value:Type) (holds:value -> prop) (i:interpretation value)
                       (rho:env value) (count:nat) (body:expr) (truth:bool) : prop =
  forall (vs:list value{L.length vs = count}).
    (holds (eval i body (shift vs rho)) <==> truth)

let lemma_all_assignments_by (#value:Type) (witness:value) (holds:value -> prop)
                             (n count:nat) (body result:expr) (truth:bool)
                             (i:interpretation value) (rho:env value)
  : Lemma (requires quant_extensional i /\ n < count /\ lower n body == Some result)
          (ensures all_assignments_by holds i rho count body truth <==>
                   all_assignments_by holds i rho (count - 1) result truth) =
  FStar.Classical.impl_intro
    #(all_assignments_by holds i rho count body truth)
    #(all_assignments_by holds i rho (count - 1) result truth)
    (fun _ ->
      let aux (vs:list value{L.length vs = count - 1})
        : Lemma (holds (eval i result (shift vs rho)) <==> truth) =
        lemma_insert_erase n witness vs;
        let full = insert n witness vs in
        lemma_erased_environment n full rho;
        lemma_lower_sound n body result i (shift full rho) (shift vs rho)
      in FStar.Classical.forall_intro aux);
  FStar.Classical.impl_intro
    #(all_assignments_by holds i rho (count - 1) result truth)
    #(all_assignments_by holds i rho count body truth)
    (fun _ ->
      let aux (vs:list value{L.length vs = count})
        : Lemma (holds (eval i body (shift vs rho)) <==> truth) =
        lemma_erase_length n vs;
        lemma_erased_environment n vs rho;
        lemma_lower_sound n body result i (shift vs rho) (shift (erase n vs) rho)
      in FStar.Classical.forall_intro aux)

let rec lemma_same_environment (#value:Type) (e:expr) (i:interpretation value) (source target:env value)
  : Lemma (requires quant_extensional i /\ (forall (n:nat). source n == target n))
          (ensures eval i e source == eval i e target)
          (decreases e) =
  match e with
  | Var _ _ -> ()
  | App _ args -> lemma_same_environment_args args i source target
  | Quantifier _ bs _ body ->
    let aux (vs:list value{L.length vs = L.length bs})
      : Lemma (eval i body (shift vs source) == eval i body (shift vs target)) =
      let pointwise (n:nat) : Lemma (shift vs source n == shift vs target n) = () in
      FStar.Classical.forall_intro pointwise;
      lemma_same_environment body i (shift vs source) (shift vs target)
    in FStar.Classical.forall_intro aux

and lemma_same_environment_args (#value:Type) (args:list expr) (i:interpretation value)
                                (source target:env value)
  : Lemma (requires quant_extensional i /\ (forall (n:nat). source n == target n))
          (ensures eval_args i args source == eval_args i args target)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_same_environment a i source target;
    lemma_same_environment_args rest i source target

