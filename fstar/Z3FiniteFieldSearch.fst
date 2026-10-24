module Z3FiniteFieldSearch

(*
   Second-stage F* audit of finite-field preprocessing and search.

   Z3FiniteFieldTheory.fst proves the algebraic operations used by the
   rewriter, Groebner/F4 engines and theory plugin.  This companion file
   covers the control transformations that surround those operations:

     * src/math/ff/ff_polynomial.cpp:
         polynomial substitution, affine elimination, reverse model
         restoration, root/value branching and tiny exhaustive search;
     * src/ast/ff/ff_solver.cpp and ast/simplifiers/ff_simplify.cpp:
         definitional preprocessing and reconstruction of eliminated values;
     * src/tactic/ff/ff_solve_tactic.cpp, ff_sat_tactic.cpp and
       ff_unique_tactic.cpp:
         validated SAT witnesses, dependency-core lifting, blocking learned
         Boolean assignments, and UNSAT only after every branch closes;
     * ff_domain_analysis / propagate_bits:
         Boolean equations are required before binary-digit reasoning, and
         modular equality is used injectively only under a no-wrap bound.

   Search order, budgets, caches, occurrence indices and variable-selection
   scores affect performance only.  They are deliberately absent here.
   `unknown` is always permitted when a bounded procedure stops early.
*)

open FStar.List.Tot
open Z3FiniteFieldTheory

(* ----------------------------------------------------------------- *)
(* Polynomial substitution                                           *)
(* ----------------------------------------------------------------- *)

let update_env (#a:Type) (rho:env a) (v:variable) (value:a) : env a =
  fun w -> if w = v then value else rho w

let constant_poly (#a:eqtype) (f:finite_field a) (c:a) : polynomial a =
  [([], c)]

let variable_poly (#a:eqtype) (f:finite_field a) (v:variable) : polynomial a =
  [([v], f.one)]

let rec substitute_monomial (#a:eqtype) (f:finite_field a)
    (v:variable) (value:polynomial a) (m:monomial)
  : Tot (polynomial a) (decreases m)
= match m with
   | [] -> constant_poly f f.one
   | w :: tl ->
     let head = if w = v then value else variable_poly f w in
     mul_poly f head (substitute_monomial f v value tl)

let rec substitute_poly (#a:eqtype) (f:finite_field a)
    (v:variable) (value:polynomial a) (p:polynomial a)
  : Tot (polynomial a) (decreases p)
= match p with
   | [] -> []
   | (m, c) :: tl ->
     add_poly f
       (scale_poly f c (substitute_monomial f v value m))
       (substitute_poly f v value tl)

let lemma_eval_constant_poly (#a:eqtype) (f:finite_field a)
    (rho:env a) (c:a)
  : Lemma (eval_poly f rho (constant_poly f c) == c)
= f.mul_one c;
  f.add_zero c

let lemma_eval_variable_poly (#a:eqtype) (f:finite_field a)
    (rho:env a) (v:variable)
  : Lemma (eval_poly f rho (variable_poly f v) == rho v)
= f.mul_one (rho v);
  lemma_mul_one_left f (rho v);
  f.add_zero (rho v)

let rec lemma_eval_substitute_monomial (#a:eqtype) (f:finite_field a)
    (rho:env a) (v:variable) (value:polynomial a) (m:monomial)
  : Lemma
      (eval_poly f rho (substitute_monomial f v value m) ==
       eval_monomial f
         (update_env rho v (eval_poly f rho value)) m)
      (decreases m)
= match m with
   | [] -> lemma_eval_constant_poly f rho f.one
   | w :: tl ->
     let head = if w = v then value else variable_poly f w in
     lemma_eval_mul f rho head (substitute_monomial f v value tl);
     lemma_eval_substitute_monomial f rho v value tl;
     if w = v then ()
     else lemma_eval_variable_poly f rho w

let rec lemma_eval_substitute_poly (#a:eqtype) (f:finite_field a)
    (rho:env a) (v:variable) (value:polynomial a) (p:polynomial a)
  : Lemma
      (eval_poly f rho (substitute_poly f v value p) ==
       eval_poly f (update_env rho v (eval_poly f rho value)) p)
      (decreases p)
= match p with
   | [] -> ()
   | (m, c) :: tl ->
     lemma_eval_append f rho
       (scale_poly f c (substitute_monomial f v value m))
       (substitute_poly f v value tl);
     lemma_eval_scale f rho c (substitute_monomial f v value m);
     lemma_eval_substitute_monomial f rho v value m;
     lemma_eval_substitute_poly f rho v value tl

let rec substitute_system (#a:eqtype) (f:finite_field a)
    (v:variable) (value:polynomial a) (ps:list (polynomial a))
  : Tot (list (polynomial a)) (decreases ps)
= match ps with
   | [] -> []
   | p :: tl -> substitute_poly f v value p ::
                substitute_system f v value tl

let rec lemma_substituted_system_model (#a:eqtype) (f:finite_field a)
    (rho:env a) (v:variable) (value:polynomial a)
    (ps:list (polynomial a))
  : Lemma
      (requires all_zero f rho (substitute_system f v value ps))
      (ensures all_zero f
        (update_env rho v (eval_poly f rho value)) ps)
      (decreases ps)
= match ps with
   | [] -> ()
   | p :: tl ->
     lemma_eval_substitute_poly f rho v value p;
     lemma_substituted_system_model f rho v value tl

let rec all_nonzero (#a:eqtype) (f:finite_field a) (rho:env a)
    (ps:list (polynomial a)) : Tot bool (decreases ps)
= match ps with
   | [] -> true
   | p :: tl -> eval_poly f rho p <> f.zero && all_nonzero f rho tl

let rec lemma_substituted_disequalities_model (#a:eqtype)
    (f:finite_field a) (rho:env a) (v:variable)
    (value:polynomial a) (ps:list (polynomial a))
  : Lemma
      (requires all_nonzero f rho (substitute_system f v value ps))
      (ensures all_nonzero f
        (update_env rho v (eval_poly f rho value)) ps)
      (decreases ps)
= match ps with
   | [] -> ()
   | p :: tl ->
     lemma_eval_substitute_poly f rho v value p;
     lemma_substituted_disequalities_model f rho v value tl

(* `engine::solve_core` saves v=value and reconstructs v after solving the
   substituted system.  This is exactly the environment on the right side of
   the substitution theorem. *)
let restore (#a:eqtype) (f:finite_field a) (rho:env a)
    (v:variable) (value:polynomial a) : env a
= update_env rho v (eval_poly f rho value)

let definition_independent (#a:eqtype) (f:finite_field a)
    (v:variable) (value:polynomial a) : prop
= forall rho x. eval_poly f (update_env rho v x) value == eval_poly f rho value

let lemma_restored_definition (#a:eqtype) (f:finite_field a)
    (rho:env a) (v:variable) (value:polynomial a)
  : Lemma
      (requires definition_independent f v value)
      (ensures (restore f rho v value) v ==
               eval_poly f (restore f rho v value) value)
= ()

let lemma_elimination_model_extension (#a:eqtype) (f:finite_field a)
    (rho:env a) (v:variable) (value:polynomial a)
    (original:list (polynomial a))
  : Lemma
      (requires all_zero f rho
        (substitute_system f v value original))
      (ensures all_zero f (restore f rho v value) original)
= lemma_substituted_system_model f rho v value original

let lemma_elimination_problem_extension (#a:eqtype) (f:finite_field a)
    (rho:env a) (v:variable) (value:polynomial a)
    (eqs neqs:list (polynomial a))
  : Lemma
      (requires all_zero f rho (substitute_system f v value eqs) /\
                all_nonzero f rho (substitute_system f v value neqs))
      (ensures all_zero f (restore f rho v value) eqs /\
               all_nonzero f (restore f rho v value) neqs)
= lemma_substituted_system_model f rho v value eqs;
  lemma_substituted_disequalities_model f rho v value neqs

let problem_model (#a:eqtype) (f:finite_field a) (rho:env a)
    (eqs neqs:list (polynomial a)) : prop
= all_zero f rho eqs /\ all_nonzero f rho neqs

noeq type verified_preprocess (a:eqtype) (f:finite_field a) = {
  source_eqs: list (polynomial a);
  source_neqs: list (polynomial a);
  target_eqs: list (polynomial a);
  target_neqs: list (polynomial a);
  rebuild: env a -> env a;
  reconstruct: rho:env a ->
    Lemma (requires problem_model f rho target_eqs target_neqs)
          (ensures problem_model f (rebuild rho) source_eqs source_neqs)
}

let elimination_preprocess (#a:eqtype) (f:finite_field a)
    (v:variable) (value:polynomial a)
    (eqs neqs:list (polynomial a))
  : verified_preprocess a f
= {
  source_eqs = eqs;
  source_neqs = neqs;
  target_eqs = substitute_system f v value eqs;
  target_neqs = substitute_system f v value neqs;
  rebuild = (fun rho -> restore f rho v value);
  reconstruct = (fun rho ->
    lemma_elimination_problem_extension f rho v value eqs neqs)
}

let identity_preprocess (#a:eqtype) (f:finite_field a)
    (eqs neqs:list (polynomial a))
  : verified_preprocess a f
= {
  source_eqs = eqs;
  source_neqs = neqs;
  target_eqs = eqs;
  target_neqs = neqs;
  rebuild = (fun rho -> rho);
  reconstruct = (fun rho -> ())
}

let compose_preprocess (#a:eqtype) (f:finite_field a)
    (first second:verified_preprocess a f)
  : Pure (verified_preprocess a f)
      (requires first.target_eqs == second.source_eqs /\
                first.target_neqs == second.source_neqs)
      (ensures fun composed ->
        composed.source_eqs == first.source_eqs /\
        composed.source_neqs == first.source_neqs /\
        composed.target_eqs == second.target_eqs /\
        composed.target_neqs == second.target_neqs)
= {
  source_eqs = first.source_eqs;
  source_neqs = first.source_neqs;
  target_eqs = second.target_eqs;
  target_neqs = second.target_neqs;
  rebuild = (fun rho -> first.rebuild (second.rebuild rho));
  reconstruct = (fun rho ->
    second.reconstruct rho;
    first.reconstruct (second.rebuild rho))
}

(* Applying the one-step theorem in reverse elimination order proves the
   C++ restoration loop.  The next lemma packages that induction principle
   independently of the concrete vector representation. *)
noeq type elimination (a:Type) = {
  eliminated: variable;
  definition: polynomial a
}

let rec restore_trail (#a:eqtype) (f:finite_field a) (rho:env a)
    (trail:list (elimination a)) : Tot (env a) (decreases trail)
= match trail with
   | [] -> rho
   | d :: tl ->
     restore f (restore_trail f rho tl) d.eliminated d.definition

(* ----------------------------------------------------------------- *)
(* Boolean digits and no-wrap modular encodings                       *)
(* ----------------------------------------------------------------- *)

let bit_value (b:bool) : nat = if b then 1 else 0

let rec binary_value (bits:list bool) : Tot nat (decreases bits)
= match bits with
   | [] -> 0
   | b :: tl -> bit_value b + 2 * binary_value tl

let rec lemma_pow2_add (a b:nat)
  : Lemma (pow2 (a + b) == pow2 a * pow2 b)
          (decreases a)
= if a = 0 then () else lemma_pow2_add (a - 1) b

let lemma_pow2_succ (n:nat)
  : Lemma (pow2 (n + 1) == 2 * pow2 n)
= lemma_pow2_add n 1

let rec lemma_binary_bound (bits:list bool)
  : Lemma (binary_value bits < pow2 (length bits))
          (decreases bits)
= match bits with
   | [] -> ()
   | _ :: tl ->
     lemma_binary_bound tl;
     lemma_pow2_succ (length tl)

let lemma_bit_parity (b:bool) (n:nat)
  : Lemma ((bit_value b + 2 * n) % 2 == bit_value b)
= ()

let rec lemma_binary_injective (left right:list bool)
  : Lemma
      (requires length left == length right /\
                binary_value left == binary_value right)
      (ensures left == right)
      (decreases left)
= match left, right with
   | [], [] -> ()
   | b1 :: tl1, b2 :: tl2 ->
     lemma_bit_parity b1 (binary_value tl1);
     lemma_bit_parity b2 (binary_value tl2);
     if b1 = b2 then lemma_binary_injective tl1 tl2 else ()

let lemma_no_wrap_mod_injective (p:pos) (x y:nat)
  : Lemma
      (requires x < p /\ y < p /\ x % p == y % p)
      (ensures x == y)
= ()

let lemma_no_wrap_binary_injective (p:pos) (left right:list bool)
  : Lemma
      (requires length left == length right /\
                pow2 (length left) <= p /\
                binary_value left % p == binary_value right % p)
      (ensures left == right)
= lemma_binary_bound left;
  lemma_binary_bound right;
  lemma_no_wrap_mod_injective p (binary_value left) (binary_value right);
  lemma_binary_injective left right

(* ----------------------------------------------------------------- *)
(* Complete finite assignment enumeration                            *)
(* ----------------------------------------------------------------- *)

let rec prepend_all (#a:Type) (x:a) (tails:list (list a))
  : Tot (list (list a)) (decreases tails)
= match tails with
   | [] -> []
   | tl :: rest -> (x :: tl) :: prepend_all x rest

let rec product_front (#a:Type) (values:list a) (tails:list (list a))
  : Tot (list (list a)) (decreases values)
= match values with
   | [] -> []
   | x :: xs -> append (prepend_all x tails) (product_front xs tails)

let rec assignments (#a:Type) (values:list a) (n:nat)
  : Tot (list (list a)) (decreases n)
= if n = 0 then [[]] else product_front values (assignments values (n - 1))

let rec env_prefix (#a:Type) (rho:nat -> a) (n:nat)
  : Tot (list a) (decreases n)
= if n = 0 then [] else rho 0 :: env_prefix (fun i -> rho (i + 1)) (n - 1)

let lemma_assignments_unfold (#a:Type) (values:list a) (n:nat{n > 0})
  : Lemma (assignments values n ==
           product_front values (assignments values (n - 1)))
= ()

let lemma_env_prefix_unfold (#a:Type) (rho:nat -> a) (n:nat{n > 0})
  : Lemma (env_prefix rho n ==
           rho 0 :: env_prefix (fun i -> rho (i + 1)) (n - 1))
= ()

let rec lemma_mem_prepend_all (#a:eqtype) (x:a)
    (tail:list a) (tails:list (list a))
  : Lemma (requires mem tail tails)
          (ensures mem (x :: tail) (prepend_all x tails))
          (decreases tails)
= match tails with
   | [] -> ()
   | y :: ys ->
     if tail = y then ()
     else lemma_mem_prepend_all x tail ys

let rec lemma_mem_append_left (#a:eqtype) (x:a) (left right:list a)
  : Lemma (requires mem x left)
          (ensures mem x (append left right))
          (decreases left)
= match left with
   | [] -> ()
   | y :: ys ->
     if x = y then () else lemma_mem_append_left x ys right

let rec lemma_mem_append_right (#a:eqtype) (x:a) (left right:list a)
  : Lemma (requires mem x right)
          (ensures mem x (append left right))
          (decreases left)
= match left with
   | [] -> ()
   | _ :: ys -> lemma_mem_append_right x ys right

let rec lemma_mem_product_front (#a:eqtype) (values:list a)
    (tails:list (list a)) (x:a) (tail:list a)
  : Lemma (requires mem x values /\ mem tail tails)
          (ensures mem (x :: tail) (product_front values tails))
          (decreases values)
= match values with
   | [] -> ()
   | y :: ys ->
     if x = y
     then (
       lemma_mem_prepend_all x tail tails;
       lemma_mem_append_left (x :: tail)
         (prepend_all x tails) (product_front ys tails)
     )
     else (
       lemma_mem_product_front ys tails x tail;
       lemma_mem_append_right (x :: tail)
         (prepend_all y tails) (product_front ys tails)
     )

let rec lemma_assignments_complete (#a:eqtype) (values:list a)
    (complete:(x:a -> Lemma (mem x values))) (rho:nat -> a) (n:nat)
  : Lemma (mem (env_prefix rho n) (assignments values n))
          (decreases n)
= if n = 0 then ()
   else (
     lemma_assignments_unfold values n;
     lemma_env_prefix_unfold rho n;
     complete (rho 0);
     lemma_assignments_complete values complete
       (fun i -> rho (i + 1)) (n - 1);
     lemma_mem_product_front values (assignments values (n - 1))
       (rho 0) (env_prefix (fun i -> rho (i + 1)) (n - 1))
   )

let lemma_field_assignments_complete (#a:eqtype) (f:finite_field a)
    (rho:nat -> a) (n:nat)
  : Lemma (mem (env_prefix rho n) (assignments f.values n))
= lemma_assignments_complete f.values f.values_complete rho n

let lemma_exhaustive_search_unsat (#a:eqtype) (f:finite_field a)
    (n:nat) (accepts:list a -> bool)
  : Lemma
      (requires (forall candidate.
                  mem candidate (assignments f.values n) ==>
                  accepts candidate == false))
      (ensures forall rho. accepts (env_prefix rho n) == false)
= let each (rho:nat -> a) : Lemma (accepts (env_prefix rho n) == false) =
     lemma_field_assignments_complete f rho n
   in
   FStar.Classical.forall_intro each

(* `ff_tiny::filter` removes precisely values that falsify the one remaining
   constraint.  A satisfying value in the old domain is therefore retained. *)
let rec filter_domain (#a:eqtype) (accepts:a -> bool) (domain:list a)
  : Tot (list a) (decreases domain)
= match domain with
   | [] -> []
   | x :: tl ->
     if accepts x then x :: filter_domain accepts tl
     else filter_domain accepts tl

let rec lemma_filter_retains_solution (#a:eqtype) (accepts:a -> bool)
    (domain:list a) (x:a)
  : Lemma (requires mem x domain /\ accepts x)
          (ensures mem x (filter_domain accepts domain))
          (decreases domain)
= match domain with
   | [] -> ()
   | y :: tl ->
     if x = y then ()
     else lemma_filter_retains_solution accepts tl x

(* ----------------------------------------------------------------- *)
(* Branch closure, dependency cores and checked results              *)
(* ----------------------------------------------------------------- *)

type predicate (w:Type) = w -> bool

let rec holds_all (#w:Type) (table:nat -> predicate w)
    (indices:list nat) (x:w)
  : Tot bool (decreases indices)
= match indices with
   | [] -> true
   | i :: tl -> table i x && holds_all table tl x

let rec holds_any (#w:Type) (table:nat -> predicate w)
    (indices:list nat) (x:w)
  : Tot bool (decreases indices)
= match indices with
   | [] -> false
   | i :: tl -> table i x || holds_any table tl x

let unsat (#w:Type) (problem:predicate w) : prop =
  forall x. problem x == false

let rec lemma_holds_all_member (#w:Type) (table:nat -> predicate w)
    (indices:list nat) (x:w) (i:nat)
  : Lemma (requires holds_all table indices x /\ mem i indices)
          (ensures table i x)
          (decreases indices)
= match indices with
   | [] -> ()
   | j :: tl ->
     if i = j then ()
     else lemma_holds_all_member table tl x i

let rec lemma_subset_holds (#w:Type) (table:nat -> predicate w)
    (inputs core:list nat) (x:w)
  : Lemma
      (requires holds_all table inputs x /\
                (forall i. mem i core ==> mem i inputs))
      (ensures holds_all table core x)
      (decreases core)
= match core with
   | [] -> ()
   | i :: tl ->
     lemma_holds_all_member table inputs x i;
     lemma_subset_holds table inputs tl x

let lemma_dependency_core_unsat (#w:Type) (table:nat -> predicate w)
    (inputs core:list nat)
  : Lemma
      (requires (forall i. mem i core ==> mem i inputs) /\
                (forall x. holds_all table core x == false))
      (ensures forall x. holds_all table inputs x == false)
= let each (x:w) : Lemma (holds_all table inputs x == false) =
     if holds_all table inputs x
     then lemma_subset_holds table inputs core x
     else ()
   in
   FStar.Classical.forall_intro each

let blocking_clause (#w:Type) (table:nat -> predicate w)
    (core:list nat) (x:w) : bool
= not (holds_all table core x)

(* The clause learned by ff-sat is the negation of the conjunction submitted
   to the algebra solver.  If that dependency core is inconsistent, every
   combined model satisfies the learned clause. *)
let lemma_unsat_core_blocking_clause (#w:Type)
    (table:nat -> predicate w) (core:list nat)
  : Lemma
      (requires forall x. holds_all table core x == false)
      (ensures forall x. blocking_clause table core x)
= let each (x:w) : Lemma (blocking_clause table core x) = () in
   FStar.Classical.forall_intro each

let rec lemma_all_unsat_no_branch (#w:Type) (table:nat -> predicate w)
    (branches:list nat) (x:w)
  : Lemma
      (requires forall i. mem i branches ==> table i x == false)
      (ensures holds_any table branches x == false)
      (decreases branches)
= match branches with
   | [] -> ()
   | _ :: tl -> lemma_all_unsat_no_branch table tl x

let lemma_all_branches_closed (#w:Type) (table:nat -> predicate w)
    (original:predicate w) (branches:list nat)
  : Lemma
      (requires (forall x. original x ==> holds_any table branches x) /\
                (forall i. mem i branches ==> unsat (table i)))
      (ensures unsat original)
= let each (x:w) : Lemma (original x == false) =
     if original x
     then lemma_all_unsat_no_branch table branches x
     else ()
   in
   FStar.Classical.forall_intro each

noeq type search_result (w:Type) =
  | Sat: witness:w -> search_result w
  | Unsat: core:list nat -> search_result w
  | Unknown: search_result w

let result_sound (#w:Type) (table:nat -> predicate w) (inputs:list nat)
    (result:search_result w) : prop
= match result with
   | Sat witness -> holds_all table inputs witness
   | Unsat core ->
     (forall i. mem i core ==> mem i inputs) /\
     (forall x. holds_all table core x == false)
   | Unknown -> True

let lemma_validated_sat_result (#w:Type) (table:nat -> predicate w)
    (inputs:list nat) (witness:w)
  : Lemma (requires holds_all table inputs witness)
          (ensures result_sound table inputs (Sat witness))
= ()

let lemma_checked_unsat_result (#w:Type) (table:nat -> predicate w)
    (inputs core:list nat)
  : Lemma
      (requires (forall i. mem i core ==> mem i inputs) /\
                (forall x. holds_all table core x == false))
      (ensures result_sound table inputs (Unsat #w core) /\
               (forall x. holds_all table inputs x == false))
= lemma_dependency_core_unsat table inputs core

let lemma_unknown_is_safe (#w:Type) (table:nat -> predicate w)
    (inputs:list nat)
  : Lemma (result_sound table inputs (Unknown #w))
= ()
