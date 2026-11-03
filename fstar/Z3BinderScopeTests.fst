(* Red/green tests for the binder-certificate scope guard
   (`Z3UnifiedProof.binder_scoped`, theorems in `Z3BinderScope`), on actual
   production certificates and `QuantifierIntroduction` nodes, computed by
   normalization with the checker's own bounds.

   * Rejected (pending 1). Every certificate in the first group was checked
     with pending 0 before the guard (scratch probe
     `Z3BinderScopeBaselineProbe` against the published 922 sources):
     - an ill-scoped binder (`Var 0` annotated Bool under an Int binder)
       whose Boolean wrapper equates `(or p (not p))` with `true`, for
       `forall`, `exists` and the `nnf-neg` dual; their conclusions are
       false in the standard model, so pending 1 is required;
     - a well-scoped closed root with an ill-scoped inner entry, through the
       QR wrapper and through congruence's reflexive short cut;
     - the same certificate as an entry of an abstract document whose
       expression table is empty (`bound = false`), which skips the
       document's own scope check;
     - binder sorts in the wrong (non-reversed) order;
     - one body proof shared under an Int and a Bool binder;
     - a premise scope of 1025 binders (limit 1024) and a shared diamond
       needing 128 scopes for one entry (limit 64).
     Malformed indices (forward, self, negative, missing premises; root out
     of range) are rejected before the guard, by `check_binder_entries` or
     the root lookup, and stay pending 1.
   * Accepted (pending 0): open bodies proved by commutativity and
     congruence, then `forall`/`exists` introduction, with mixed Int/Bool
     binders, nesting, an empty binder list, a lambda, a closed input
     assertion used inside a binder, a closed subproof shared at `[]` and
     `[Int]`, a premise scope of exactly 1024 binders, and the shared diamond
     at exactly 64 scopes for one entry.
   * Bounds: for an accepted certificate the guard holds with exactly the
     assignments and work units it uses and fails with one less. *)
module Z3BinderScopeTests

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3UnifiedProof
module GS = Z3GhostStandardModel
module GT = Z3GhostStandardModelTests
module C = Z3CanonicalOps
module PD = Z3ProofDocument
module BS = Z3BinderScope
module I = Z3ProofIndex
module L = FStar.List.Tot

type leaf = func_decl -> list value -> int
let g (base:leaf) : interpretation value = GS.ghost_standard base

(* --- Terms and certificates -------------------------------------------------------- *)

let int_s : sort = GT.int_s
let num (n:int) : expr = GT.num n
let plus (a b:expr) : expr = GT.plus a b
let eq (a b:expr) : expr = GT.eq a b
let conj (a b:expr) : expr = GT.conj a b
let or2 (a b:expr) : expr = App (C.or_decl 2) [a; b]
let taut (a:expr) : expr = or2 a (mk_not_expr a)
let all (bs:list sort) (b:expr) : expr = Quantifier Forall_k bs bool_sort b
let some (bs:list sort) (b:expr) : expr = Quantifier Exists_k bs bool_sort b

let x0 : expr = Var 0 int_s
let x1 : expr = Var 1 int_s
let p0 : expr = Var 0 bool_sort

let entry (name:string) (formula:expr) (premises:list int) (sorts:option (list sort)) : binder_entry =
  { binder_name = name; binder_formula = formula; binder_premises = premises; binder_sorts = sorts }

let cert (entries:list binder_entry) (root:int) : binder_certificate =
  { binder_entries = entries; binder_root = root }

let fact (j:judgment) : checked_fact = { conclusion = j; hypotheses = [] }

let intro (c:binder_certificate) (j:judgment) : proof_node =
  { kind = QuantifierIntroduction c; conclusion = j; premises = [] }

let result (n:proof_node) : option (checked_fact & nat) = check_node_with_context [] false [] n

let refl_true : binder_entry = entry "refl" (mk_eq_expr true_expr true_expr) [] None
let refl_false : binder_entry = entry "refl" (mk_eq_expr false_expr false_expr) [] None

(* --- Rejected: ill-scoped binders with false conclusions ------------------------------ *)

(* forall x:Int. (or p (not p)) = forall x:Int. true, with p = Var 0 : Bool. *)
let fa_lhs : expr = all [int_s] (taut p0)
let fa_rhs : expr = all [int_s] true_expr
let fa_node : proof_node =
  intro (cert [refl_true; entry "quant-intro" (mk_eq_expr fa_lhs fa_rhs) [0] (Some [int_s])] 1)
        (Equal fa_lhs fa_rhs)

let ex_lhs : expr = some [int_s] (taut p0)
let ex_rhs : expr = some [int_s] true_expr
let ex_node : proof_node =
  intro (cert [refl_true; entry "quant-intro" (mk_eq_expr ex_lhs ex_rhs) [0] (Some [int_s])] 1)
        (Equal ex_lhs ex_rhs)

(* not (forall x:Int. (or p (not p))) = exists x:Int. false, by nnf-neg. *)
let nn_lhs : expr = mk_not_expr fa_lhs
let nn_rhs : expr = some [int_s] false_expr
let nn_node : proof_node =
  intro (cert [refl_false; entry "nnf-neg" (mk_eq_expr nn_lhs nn_rhs) [0] (Some [int_s])] 1)
        (Equal nn_lhs nn_rhs)

let false_binders_pending ()
  : Lemma (result fa_node == Some (fact fa_node.conclusion, 1) /\
           result ex_node == Some (fact ex_node.conclusion, 1) /\
           result nn_node == Some (fact nn_node.conclusion, 1))
  = assert_norm (result fa_node == Some (fact fa_node.conclusion, 1));
    assert_norm (result ex_node == Some (fact ex_node.conclusion, 1));
    assert_norm (result nn_node == Some (fact nn_node.conclusion, 1))

(* The body is never true: `p` takes the integer value of the binder. *)
let body_false (base:leaf) (rho:env value) (x:int)
  : Lemma (~(eval (g base) (taut p0) (shift [VInt x] rho) == VBool true))
  = GS.lemma_connectives base;
    C.lemma_canonical_decls bool_sort 2;
    assert (eval (g base) p0 (shift [VInt x] rho) == VInt x)

let lhs_values (base:leaf) (rho:env value)
  : Lemma (eval (g base) fa_lhs rho == VBool false /\ eval (g base) ex_lhs rho == VBool false)
  = GT.lemma_forall_int base (taut p0) rho;
    GT.lemma_exists_int base (taut p0) rho;
    body_false base rho 0;
    FStar.Classical.forall_intro (body_false base rho)

let false_binders_false (base:leaf) (rho:env value)
  : Lemma (~(judgment_holds (g base) rho fa_node.conclusion) /\
           ~(judgment_holds (g base) rho ex_node.conclusion) /\
           ~(judgment_holds (g base) rho nn_node.conclusion))
  = lhs_values base rho;
    GS.lemma_connectives base;
    GT.lemma_forall_int base true_expr rho;
    GT.lemma_exists_int base true_expr rho;
    GT.lemma_exists_int base false_expr rho;
    assert (eval (g base) true_expr (shift [VInt 0] rho) == VBool true);
    assert (eval (g base) nn_lhs rho == VBool true)

(* --- Rejected: closed roots with ill-scoped inner entries ------------------------------ *)

(* Through the QR wrapper: the inner rewrite (or p (not p)) = true is used at [Int]. *)
let qr_lhs : expr = all [int_s] (taut (eq x0 x0))
let qr_node : proof_node =
  intro (cert [entry "rewrite" (mk_eq_expr (taut p0) true_expr) [] None;
               entry "quant-intro" (mk_eq_expr qr_lhs fa_rhs) [0] (Some [int_s])] 1)
        (Equal qr_lhs fa_rhs)

(* Through congruence's a = b short cut: an unread ill-scoped premise. *)
let unread_q : expr = all [int_s] (eq x0 x0)
let unread_node : proof_node =
  intro (cert [entry "refl" (mk_eq_expr p0 p0) [] None;
               entry "monotonicity" (mk_eq_expr (eq x0 x0) (eq x0 x0)) [0] None;
               entry "quant-intro" (mk_eq_expr unread_q unread_q) [1] (Some [int_s])] 2)
        (Equal unread_q unread_q)

(* Binder sorts in the wrong order: the body is scoped under [Int; Bool]
   (Var 0 is the Bool binder), not under [Bool; Int]. *)
let mixed_body : expr = conj p0 (eq x1 (num 3))
let mixed_body' : expr = conj (eq x1 (num 3)) p0
let mixed_comm : binder_entry = entry "commutativity" (mk_eq_expr mixed_body mixed_body') [] None
let swapped_lhs : expr = some [bool_sort; int_s] mixed_body
let swapped_rhs : expr = some [bool_sort; int_s] mixed_body'
let swapped_node : proof_node =
  intro (cert [mixed_comm; entry "quant-intro" (mk_eq_expr swapped_lhs swapped_rhs) [0] (Some [bool_sort; int_s])] 1)
        (Equal swapped_lhs swapped_rhs)

(* One body proof under an Int binder and, unread, under a Bool binder. *)
let shared_body : expr = eq (plus x0 (num 1)) (num 2)
let shared_body' : expr = eq (plus (num 1) x0) (num 2)
let shared_int : expr = all [int_s] shared_body
let shared_int' : expr = all [int_s] shared_body'
let shared_bool : expr = all [bool_sort] shared_body
let shared_bool' : expr = all [bool_sort] shared_body'
let conflict_node : proof_node =
  intro (cert [entry "commutativity" (mk_eq_expr (plus x0 (num 1)) (plus (num 1) x0)) [] None;
               entry "monotonicity" (mk_eq_expr shared_body shared_body') [0] None;
               entry "quant-intro" (mk_eq_expr shared_int shared_int') [1] (Some [int_s]);
               entry "quant-intro" (mk_eq_expr shared_bool shared_bool') [1] (Some [bool_sort]);
               entry "monotonicity" (mk_eq_expr (conj shared_int shared_int) (conj shared_int' shared_int'))
                 [2; 3] None] 4)
        (Equal (conj shared_int shared_int) (conj shared_int' shared_int'))

let inner_pending ()
  : Lemma (result qr_node == Some (fact qr_node.conclusion, 1) /\
           result unread_node == Some (fact unread_node.conclusion, 1) /\
           result swapped_node == Some (fact swapped_node.conclusion, 1) /\
           result conflict_node == Some (fact conflict_node.conclusion, 1))
  = assert_norm (result qr_node == Some (fact qr_node.conclusion, 1));
    assert_norm (result unread_node == Some (fact unread_node.conclusion, 1));
    assert_norm (result swapped_node == Some (fact swapped_node.conclusion, 1));
    assert_norm (result conflict_node == Some (fact conflict_node.conclusion, 1))

(* The abstract document route: an empty expression table (`bound = false`)
   skips the document's scope check; the guard still rejects the entry. *)
let fa_entry : PD.entry =
  { PD.rule = fa_node.kind; PD.formula = mk_eq_expr fa_lhs fa_rhs; PD.premise_ids = [] }

let document_pending ()
  : Lemma (PD.check_entry true false [] [] I.Empty fa_entry == Some (fact fa_node.conclusion, 1))
  = assert_norm (PD.check_entry true false [] [] I.Empty fa_entry == Some (fact fa_node.conclusion, 1))

(* --- Accepted: open bodies, binders, sharing --------------------------------------------- *)

(* forall x:Int, y:Int. x + y = 5  ==  forall x:Int, y:Int. y + x = 5 *)
let sum_body : expr = eq (plus x1 x0) (num 5)
let sum_body' : expr = eq (plus x0 x1) (num 5)
let sum_lhs : expr = all [int_s; int_s] sum_body
let sum_rhs : expr = all [int_s; int_s] sum_body'
let sum_cert : binder_certificate =
  cert [entry "commutativity" (mk_eq_expr (plus x1 x0) (plus x0 x1)) [] None;
        entry "monotonicity" (mk_eq_expr sum_body sum_body') [0] None;
        entry "quant-intro" (mk_eq_expr sum_lhs sum_rhs) [1] (Some [int_s; int_s])] 2
let sum_node : proof_node = intro sum_cert (Equal sum_lhs sum_rhs)

(* exists x:Int, p:Bool. p and x = 3  ==  exists x:Int, p:Bool. x = 3 and p *)
let mixed_lhs : expr = some [int_s; bool_sort] mixed_body
let mixed_rhs : expr = some [int_s; bool_sort] mixed_body'
let mixed_node : proof_node =
  intro (cert [mixed_comm; entry "quant-intro" (mk_eq_expr mixed_lhs mixed_rhs) [0] (Some [int_s; bool_sort])] 1)
        (Equal mixed_lhs mixed_rhs)

(* Nested: forall x:Int. exists p:Bool. p and x = 3, the body at [Bool; Int]. *)
let inner_lhs : expr = some [bool_sort] mixed_body
let inner_rhs : expr = some [bool_sort] mixed_body'
let nested_lhs : expr = all [int_s] inner_lhs
let nested_rhs : expr = all [int_s] inner_rhs
let nested_node : proof_node =
  intro (cert [mixed_comm;
               entry "quant-intro" (mk_eq_expr inner_lhs inner_rhs) [0] (Some [bool_sort]);
               entry "quant-intro" (mk_eq_expr nested_lhs nested_rhs) [1] (Some [int_s])] 2)
        (Equal nested_lhs nested_rhs)

(* An empty binder list. *)
let empty_lhs : expr = all [] (eq (plus (num 1) (num 2)) (num 3))
let empty_rhs : expr = all [] (eq (plus (num 2) (num 1)) (num 3))
let empty_node : proof_node =
  intro (cert [entry "commutativity" (mk_eq_expr (plus (num 1) (num 2)) (plus (num 2) (num 1))) [] None;
               entry "monotonicity" (mk_eq_expr (eq (plus (num 1) (num 2)) (num 3))
                                               (eq (plus (num 2) (num 1)) (num 3))) [0] None;
               entry "quant-intro" (mk_eq_expr empty_lhs empty_rhs) [1] (Some [])] 2)
        (Equal empty_lhs empty_rhs)

(* A lambda: (lambda x:Int. x + 0) = (lambda x:Int. 0 + x). The guard does
   not reject it; no lambda semantics is claimed. *)
let lam (b:expr) : expr = Quantifier Lambda_k [int_s] (ArraySort [int_s] int_s) b
let lambda_node : proof_node =
  intro (cert [entry "commutativity" (mk_eq_expr (plus x0 (num 0)) (plus (num 0) x0)) [] None;
               entry "quant-intro" (mk_eq_expr (lam (plus x0 (num 0))) (lam (plus (num 0) x0))) [0] (Some [int_s])] 1)
        (Equal (lam (plus x0 (num 0))) (lam (plus (num 0) x0)))

(* A closed input used inside a binder: (= a b) gives forall x:Int. p a = forall x:Int. p b. *)
let a_c : expr = App { decl_name = "a"; domain = []; range = int_s; interp = None; int_params = [] } []
let b_c : expr = App { decl_name = "b"; domain = []; range = int_s; interp = None; int_params = [] } []
let p_decl : func_decl = { decl_name = "p"; domain = [int_s]; range = bool_sort; interp = None; int_params = [] }
let input : judgment = Equal a_c b_c
let input_lhs : expr = all [int_s] (App p_decl [a_c])
let input_rhs : expr = all [int_s] (App p_decl [b_c])
let input_node : proof_node =
  intro (cert [entry "asserted" (mk_eq_expr a_c b_c) [] None;
               entry "monotonicity" (mk_eq_expr (App p_decl [a_c]) (App p_decl [b_c])) [0] None;
               entry "quant-intro" (mk_eq_expr input_lhs input_rhs) [1] (Some [int_s])] 2)
        (Equal input_lhs input_rhs)

(* A closed subproof (1 + 2 = 2 + 1) read at [Int], under the binder, and at
   [], next to it. *)
let one_two : expr = plus (num 1) (num 2)
let two_one : expr = plus (num 2) (num 1)
let closed_lhs : expr = all [int_s] (eq x0 one_two)
let closed_rhs : expr = all [int_s] (eq x0 two_one)
let shared_closed_node : proof_node =
  intro (cert [entry "commutativity" (mk_eq_expr one_two two_one) [] None;
               entry "monotonicity" (mk_eq_expr (eq x0 one_two) (eq x0 two_one)) [0] None;
               entry "quant-intro" (mk_eq_expr closed_lhs closed_rhs) [1] (Some [int_s]);
               entry "monotonicity" (mk_eq_expr (eq one_two (num 3)) (eq two_one (num 3))) [0] None;
               entry "monotonicity" (mk_eq_expr (conj closed_lhs (eq one_two (num 3)))
                                               (conj closed_rhs (eq two_one (num 3)))) [2; 3] None] 4)
        (Equal (conj closed_lhs (eq one_two (num 3))) (conj closed_rhs (eq two_one (num 3))))

let accepted ()
  : Lemma (result sum_node == Some (fact sum_node.conclusion, 0) /\
           result mixed_node == Some (fact mixed_node.conclusion, 0) /\
           result nested_node == Some (fact nested_node.conclusion, 0) /\
           result empty_node == Some (fact empty_node.conclusion, 0) /\
           result lambda_node == Some (fact lambda_node.conclusion, 0) /\
           check_node_with_context [] false [input] input_node == Some (fact input_node.conclusion, 0) /\
           result input_node == Some (fact input_node.conclusion, 1) /\
           result shared_closed_node == Some (fact shared_closed_node.conclusion, 0))
  = assert_norm (result sum_node == Some (fact sum_node.conclusion, 0));
    assert_norm (result mixed_node == Some (fact mixed_node.conclusion, 0));
    assert_norm (result nested_node == Some (fact nested_node.conclusion, 0));
    assert_norm (result empty_node == Some (fact empty_node.conclusion, 0));
    assert_norm (result lambda_node == Some (fact lambda_node.conclusion, 0));
    assert_norm (check_node_with_context [] false [input] input_node == Some (fact input_node.conclusion, 0));
    assert_norm (result input_node == Some (fact input_node.conclusion, 1));
    assert_norm (result shared_closed_node == Some (fact shared_closed_node.conclusion, 0))

(* --- Malformed indices: rejected before the guard ---------------------------------------- *)

let with_entries (c:binder_certificate) (es:list binder_entry) : binder_certificate =
  { c with binder_entries = es }

(* `sum_cert` with the premises of its middle entry replaced. *)
let reindex (ps:list int) : list binder_entry =
  match sum_cert.binder_entries with
  | [e0; e1; e2] -> [e0; { e1 with binder_premises = ps }; e2]
  | es -> es

let malformed ()
  : Lemma (result (intro (with_entries sum_cert (reindex [1])) sum_node.conclusion) ==
             Some (fact sum_node.conclusion, 1) /\                                  (* self *)
           result (intro (with_entries sum_cert (reindex [2])) sum_node.conclusion) ==
             Some (fact sum_node.conclusion, 1) /\                                  (* forward *)
           result (intro (with_entries sum_cert (reindex [(-1)])) sum_node.conclusion) ==
             Some (fact sum_node.conclusion, 1) /\                                  (* negative *)
           result (intro (with_entries sum_cert (reindex [7])) sum_node.conclusion) ==
             Some (fact sum_node.conclusion, 1) /\                                  (* missing *)
           result (intro ({ sum_cert with binder_root = 3 }) sum_node.conclusion) ==
             Some (fact sum_node.conclusion, 1) /\                                  (* root past the end *)
           result (intro ({ sum_cert with binder_root = (-1) }) sum_node.conclusion) ==
             Some (fact sum_node.conclusion, 1) /\                                  (* negative root *)
           result (intro ({ sum_cert with binder_root = 1 }) sum_node.conclusion) ==
             Some (fact sum_node.conclusion, 1))                                    (* wrong root *)
  = assert_norm (result (intro (with_entries sum_cert (reindex [1])) sum_node.conclusion) ==
                 Some (fact sum_node.conclusion, 1));
    assert_norm (result (intro (with_entries sum_cert (reindex [2])) sum_node.conclusion) ==
                 Some (fact sum_node.conclusion, 1));
    assert_norm (result (intro (with_entries sum_cert (reindex [(-1)])) sum_node.conclusion) ==
                 Some (fact sum_node.conclusion, 1));
    assert_norm (result (intro (with_entries sum_cert (reindex [7])) sum_node.conclusion) ==
                 Some (fact sum_node.conclusion, 1));
    assert_norm (result (intro ({ sum_cert with binder_root = 3 }) sum_node.conclusion) ==
                 Some (fact sum_node.conclusion, 1));
    assert_norm (result (intro ({ sum_cert with binder_root = (-1) }) sum_node.conclusion) ==
                 Some (fact sum_node.conclusion, 1));
    assert_norm (result (intro ({ sum_cert with binder_root = 1 }) sum_node.conclusion) ==
                 Some (fact sum_node.conclusion, 1))

(* --- Bounds -------------------------------------------------------------------------------- *)

(* forall over `n` Int binders of true; the premise scope has `n` sorts. *)
let rec ints (n:nat) : Tot (list sort) (decreases n) = if n = 0 then [] else int_s :: ints (n - 1)
let wide (n:nat) : expr = all (ints n) true_expr
let wide_node (n:nat) : proof_node =
  intro (cert [refl_true; entry "quant-intro" (mk_eq_expr (wide n) (wide n)) [0] (Some (ints n))] 1)
        (Equal (wide n) (wide n))

let scope_limit ()
  : Lemma (result (wide_node 1024) == Some (fact (wide_node 1024).conclusion, 0) /\
           result (wide_node 1025) == Some (fact (wide_node 1025).conclusion, 1))
  = assert_norm (result (wide_node 1024) == Some (fact (wide_node 1024).conclusion, 0));
    assert_norm (result (wide_node 1025) == Some (fact (wide_node 1025).conclusion, 1))

(* The shared diamond: level i introduces forall over Int and over Bool from
   the same closed premise and joins them by congruence, so the premise of
   level 1 is used at every Int/Bool sequence of length `levels`. *)
let q_entry (s:sort) (premise:int) : binder_entry =
  entry "quant-intro" (mk_eq_expr (all [s] true_expr) (all [s] true_expr)) [premise] (Some [s])
let join_entry (left right:int) : binder_entry =
  entry "monotonicity" (mk_eq_expr true_expr true_expr) [left; right] None

let rec diamond (levels:nat) : Tot (list binder_entry) (decreases levels) =
  if levels = 0 then [refl_true]
  else let a = 3 * (levels - 1) in
       L.append (diamond (levels - 1)) [q_entry int_s a; q_entry bool_sort a; join_entry (a + 1) (a + 2)]

let diamond_node (levels:nat) : proof_node =
  intro (cert (diamond levels) (3 * levels)) (Equal true_expr true_expr)

(* Level 1's premise is used at all 64 Int/Bool sequences of length 6 ... *)
let diamond_at_limit () : Lemma (result (diamond_node 6) == Some (fact (Equal true_expr true_expr), 0))
  = assert_norm (result (diamond_node 6) == Some (fact (Equal true_expr true_expr), 0))

(* ... and would need 128 scopes at length 7. *)
let diamond_over_limit () : Lemma (result (diamond_node 7) == Some (fact (Equal true_expr true_expr), 1))
  = assert_norm (result (diamond_node 7) == Some (fact (Equal true_expr true_expr), 1))

(* Exact budgets: the guard holds with exactly the assignments and work units
   a certificate uses, and fails with one less. *)
let cache_of (c:binder_certificate) : I.index_tree judgment =
  match check_binder_entries [] [] c.binder_entries I.Empty 0 with
  | Some cache -> cache
  | None -> I.Empty

let work_used (count:nat) (c:binder_certificate) : nat =
  let big = binder_work_limit (L.length c.binder_entries) in
  match binder_scopes count big c with
  | Some (t, w) ->
    (match scope_entries_checked t (cache_of c) 0 c.binder_entries w with
     | Some w' -> if w' <= big then big - w' else 0
     | None -> 0)
  | None -> 0

let less (n:nat) : nat = if n > 0 then n - 1 else 0

(* `sum_cert` needs 2 assignments. *)
let exact_budgets ()
  : Lemma (work_used 2 sum_cert > 0 /\
           binder_scoped_within 2 (work_used 2 sum_cert) sum_cert (cache_of sum_cert) == true /\
           binder_scoped_within 1 (work_used 2 sum_cert) sum_cert (cache_of sum_cert) == false /\
           binder_scoped_within 2 (less (work_used 2 sum_cert)) sum_cert (cache_of sum_cert) == false)
  = assert_norm (work_used 2 sum_cert > 0);
    assert_norm (binder_scoped_within 2 (work_used 2 sum_cert) sum_cert (cache_of sum_cert) == true);
    assert_norm (binder_scoped_within 1 (work_used 2 sum_cert) sum_cert (cache_of sum_cert) == false);
    assert_norm (binder_scoped_within 2 (less (work_used 2 sum_cert)) sum_cert (cache_of sum_cert) == false)

(* Sorts are compared node by node: a shared sort `deep k`, whose unfolded
   tree has 2^(k+1) - 1 nodes, annotates the bound variable. *)
let rec deep (k:nat) : Tot sort (decreases k) =
  if k = 0 then int_s else ArraySort [deep (k - 1)] (deep (k - 1))
let deep_body (k:nat) : expr = eq (Var 0 (deep k)) (Var 0 (deep k))
let deep_q (k:nat) : expr = all [deep k] (deep_body k)
let deep_cert (k:nat) : binder_certificate =
  cert [entry "refl" (mk_eq_expr (deep_body k) (deep_body k)) [] None;
        entry "quant-intro" (mk_eq_expr (deep_q k) (deep_q k)) [0] (Some [deep k])] 1
let deep_node (k:nat) : proof_node = intro (deep_cert k) (Equal (deep_q k) (deep_q k))

let deep_sorts ()
  : Lemma (result (deep_node 3) == Some (fact (deep_node 3).conclusion, 0) /\
           work_used 1 (deep_cert 2) < work_used 1 (deep_cert 3) /\
           binder_scoped_within 1 (work_used 1 (deep_cert 3)) (deep_cert 3) (cache_of (deep_cert 3)) == true /\
           binder_scoped_within 1 (less (work_used 1 (deep_cert 3))) (deep_cert 3) (cache_of (deep_cert 3)) == false)
  = assert_norm (result (deep_node 3) == Some (fact (deep_node 3).conclusion, 0));
    assert_norm (work_used 1 (deep_cert 2) < work_used 1 (deep_cert 3));
    assert_norm (binder_scoped_within 1 (work_used 1 (deep_cert 3)) (deep_cert 3) (cache_of (deep_cert 3)) == true);
    assert_norm (binder_scoped_within 1 (less (work_used 1 (deep_cert 3))) (deep_cert 3) (cache_of (deep_cert 3)) == false)

(* Base-sort names are charged by length before they are compared: the same
   certificate over a sort with a 40-character name uses more work than over
   a sort with a 1-character name, by at least both names' extra length. *)
let named_cert (name:string) : binder_certificate =
  let s = BaseSort name in
  let body = eq (Var 0 s) (Var 0 s) in
  let q = all [s] body in
  cert [entry "refl" (mk_eq_expr body body) [] None;
        entry "quant-intro" (mk_eq_expr q q) [0] (Some [s])] 1

let long_name : string = "Sort_with_a_name_of_forty_characters____"

let name_lengths ()
  : Lemma (FStar.String.strlen long_name == 40 /\
           work_used 1 (named_cert "S") > 0 /\
           work_used 1 (named_cert long_name) >= work_used 1 (named_cert "S") + 2 * 39 /\
           binder_scoped_within 1 (work_used 1 (named_cert long_name)) (named_cert long_name)
             (cache_of (named_cert long_name)) == true /\
           binder_scoped_within 1 (less (work_used 1 (named_cert long_name))) (named_cert long_name)
             (cache_of (named_cert long_name)) == false)
  = assert_norm (FStar.String.strlen long_name == 40);
    assert_norm (work_used 1 (named_cert "S") > 0);
    assert_norm (work_used 1 (named_cert long_name) >= work_used 1 (named_cert "S") + 2 * 39);
    assert_norm (binder_scoped_within 1 (work_used 1 (named_cert long_name)) (named_cert long_name)
                   (cache_of (named_cert long_name)) == true);
    assert_norm (binder_scoped_within 1 (less (work_used 1 (named_cert long_name))) (named_cert long_name)
                   (cache_of (named_cert long_name)) == false)

(* The guard's `name_length` is `FStar.String.strlen` (`Z3BinderScope.lemma_name_length`),
   computed by a tail-recursive count. On valid UTF-8 names the F* normalizer counts code
   points, including the scalar boundaries U+D7FE, U+D7FF, U+E000 and U+10FFFF, whose decoded
   characters are those of the corresponding character literals. *)
let name_length_values ()
  : Lemma (name_length "" == 0 /\
           name_length "Int" == 3 /\
           name_length "é" == 1 /\
           name_length "€" == 1 /\
           name_length "𝔸" == 1 /\
           name_length "é" == 2 /\
           name_length "😀" == 1 /\
           name_length "aé€😀" == 4 /\
           name_length "퟾퟿􏿿" == 4 /\
           FStar.String.list_of_string "퟾퟿􏿿" == ['퟾'; '퟿'; ''; '􏿿'])
  = assert_norm (name_length "" == 0);
    assert_norm (name_length "Int" == 3);
    assert_norm (name_length "é" == 1);
    assert_norm (name_length "€" == 1);
    assert_norm (name_length "𝔸" == 1);
    assert_norm (name_length "é" == 2);
    assert_norm (name_length "😀" == 1);
    assert_norm (name_length "aé€😀" == 4);
    assert_norm (name_length "퟾퟿􏿿" == 4);
    assert_norm (FStar.String.list_of_string "퟾퟿􏿿" == ['퟾'; '퟿'; ''; '􏿿'])

(* --- The structural theorems on accepted certificates ------------------------------------ *)

let sum_root_scoped () : Lemma (BS.binder_judgment_scoped [] sum_node.conclusion)
  = accepted ();
    assert_norm (check_binder_with_context [] [] sum_cert sum_node.conclusion);
    BS.lemma_checked_root_scoped [] [] sum_cert sum_node.conclusion

(* --- Controls: the opposite claims fail ---------------------------------------------------- *)

(* The guard turns the false forall node from pending 0 into pending 1. *)
[@@expect_failure [19]]
let false_forall_still_checked () : Lemma (result fa_node == Some (fact fa_node.conclusion, 0))
  = assert_norm (result fa_node == Some (fact fa_node.conclusion, 0))

[@@expect_failure [19]]
let sum_rejected () : Lemma (result sum_node == Some (fact sum_node.conclusion, 1))
  = assert_norm (result sum_node == Some (fact sum_node.conclusion, 1))
