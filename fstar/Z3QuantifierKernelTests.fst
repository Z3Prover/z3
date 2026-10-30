(* Tests for the typed quantifier-instantiation kernel theorem
   (`Z3QuantifierKernel`) on actual production terms and actual kernel
   nodes, checked against the classical standard model
   (`Z3GhostStandardModel.ghost_standard`), which is a joint model of
   `Z3TypedQuantifier.quantifier_model` (`lemma_quantifier_model`).

   * Accepted nodes: `check_node_with_context` is computed by normalization
     and returns pending 0; the node theorem then gives the conclusion in
     the standard model, and the instance itself follows from the true
     quantifier (Int numerals with distinct values, Bool, heterogeneous
     Int/Bool binders in reversed de Bruijn order, nested binders, a
     bounded bit-vector domain).
   * Rejected mutations: wrong instance, wrong binder order, wrong argument
     sorts, dropped/extra arguments, an unscoped argument, capture and
     shadowing mistakes, a dropped negation, an `Equal` conclusion,
     premises. They return `None` or pending 1. Several of them are false
     in the standard model, so a theorem that accepted `Some` alone would
     be false (`some_is_not_certification`).
   * The legacy untyped `forall_elimination_model` fails in the standard
     model, while the typed elimination holds. *)
module Z3QuantifierKernelTests

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3UnifiedProof
module GS = Z3GhostStandardModel
module GT = Z3GhostStandardModelTests
module TQ = Z3TypedQuantifier
module QK = Z3QuantifierKernel
module Q = Z3QuantifierInstantiation
module CO = Z3CoreModel
module C = Z3CanonicalOps
module L = FStar.List.Tot
module SM = Z3StandardModel
module BV = Z3BvLemma
module D = Z3Definitions

type leaf = func_decl -> list value -> int
let g (base:leaf) : interpretation value = GS.ghost_standard base

(* --- Nodes ------------------------------------------------------------------- *)

let int_s : sort = GT.int_s
let num (n:int) : expr = GT.num n
let plus (a b:expr) : expr = GT.plus a b
let eq (a b:expr) : expr = GT.eq a b
let or2 (a b:expr) : expr = App (C.or_decl 2) [a; b]

(* The instantiation clause (or (not q) inst). *)
let clause (q inst:expr) : expr = or2 (mk_not_expr q) inst

let fact (j:judgment) : checked_fact = { conclusion = j; hypotheses = [] }

let qi (args:list expr) (j:judgment) : proof_node =
  { kind = QuantifierInstantiation args; conclusion = j; premises = [] }

let result (n:proof_node) : option (checked_fact & nat) = check_node_with_context [] false [] n

(* --- The node theorem in the standard model ------------------------------------- *)

let lemma_node (base:leaf) (rho:env value) (n:proof_node)
  : Lemma (requires QuantifierInstantiation? n.kind /\ result n == Some (fact n.conclusion, 0))
          (ensures judgment_holds (g base) rho n.conclusion)
  = GS.lemma_quantifier_model base;
    QK.lemma_instantiation_node_sound [] (g base) GS.domains rho false [] n

let lemma_clause (base:leaf) (rho:env value) (q inst:expr)
  : Lemma (VBool? (eval (g base) q rho) ==>
           (lit_true (g base) rho (clause q inst) <==>
            (~(lit_true (g base) rho q) \/ lit_true (g base) rho inst)))
  = GS.lemma_connectives base;
    C.lemma_canonical_decls bool_sort 2

(* A checked clause and its true quantifier give the instance. *)
let lemma_instance (base:leaf) (rho:env value) (q inst:expr)
  : Lemma (requires lit_true (g base) rho (clause q inst) /\ lit_true (g base) rho q)
          (ensures lit_true (g base) rho inst)
  = lemma_clause base rho q inst

let lemma_num_eq (base:leaf) (rho:env value) (a b c:int)
  : Lemma (VBool? (eval (g base) (eq (plus (num a) (num b)) (num c)) rho) /\
           (lit_true (g base) rho (eq (plus (num a) (num b)) (num c)) <==> a + b == c))
  = GT.lemma_num base a rho;
    GT.lemma_num base b rho;
    GT.lemma_num base c rho;
    GT.lemma_plus base (num a) (num b) rho a b;
    GT.lemma_eq base (plus (num a) (num b)) (num c) rho

(* --- Int: forall x:Int. x + 0 = x, instantiated at 5 ----------------------------------- *)

let int_inst : expr = eq (plus (num 5) (num 0)) (num 5)
let int_node : proof_node = qi [num 5] (Holds (clause GT.valid int_inst))

let int_checked () : Lemma (result int_node == Some (fact int_node.conclusion, 0))
  = assert_norm (result int_node == Some (fact int_node.conclusion, 0))

let int_sound (base:leaf) (rho:env value)
  : Lemma (lit_true (g base) rho (clause GT.valid int_inst) /\ lit_true (g base) rho int_inst)
  = int_checked ();
    lemma_node base rho int_node;
    GT.valid_true base rho;
    lemma_instance base rho GT.valid int_inst

(* The instance at 5 with the wrong right-hand side 6: not checked, and false. *)
let int_wrong : expr = eq (plus (num 5) (num 0)) (num 6)
let int_wrong_node : proof_node = qi [num 5] (Holds (clause GT.valid int_wrong))

let int_wrong_pending () : Lemma (result int_wrong_node == Some (fact int_wrong_node.conclusion, 1))
  = assert_norm (result int_wrong_node == Some (fact int_wrong_node.conclusion, 1))

let int_wrong_false (base:leaf) (rho:env value)
  : Lemma (~(lit_true (g base) rho (clause GT.valid int_wrong)))
  = GT.valid_true base rho;
    lemma_num_eq base rho 5 0 6;
    lemma_clause base rho GT.valid int_wrong

(* `Some` is not certification: this node is returned with a false conclusion. *)
let some_is_not_certification (base:leaf) (rho:env value)
  : Lemma (Some? (result int_wrong_node) /\
           ~(scoped_holds (g base) rho (fst (Some?.v (result int_wrong_node)))))
  = int_wrong_pending ();
    int_wrong_false base rho

let membership_accept_all (_:judgment) : bool = true

let membership_entry_checked (base:leaf) (rho:env value)
  : Lemma (membership_accept_all int_node.conclusion /\
           check_node_with_membership [] false [] membership_accept_all int_node ==
             Some (fact int_node.conclusion, 0) /\
           scoped_holds (g base) rho (fact int_node.conclusion))
  = int_checked ();
    QK.lemma_instantiation_membership_irrelevant [] false [] membership_accept_all int_node;
    assert_norm (membership_accept_all int_node.conclusion);
    GS.lemma_quantifier_model base;
    QK.lemma_instantiation_membership_sound [] (g base) GS.domains rho false [] membership_accept_all int_node

let membership_entry_pending ()
  : Lemma (check_node_with_membership [] false [] membership_accept_all int_wrong_node ==
             Some (fact int_wrong_node.conclusion, 1))
  = int_wrong_pending ();
    QK.lemma_instantiation_membership_irrelevant [] false [] membership_accept_all int_wrong_node

(* The argument 6 with the instance at 5. *)
let int_wrong_argument : proof_node = qi [num 6] (Holds (clause GT.valid int_inst))

let int_wrong_argument_pending ()
  : Lemma (result int_wrong_argument == Some (fact int_wrong_argument.conclusion, 1))
  = assert_norm (result int_wrong_argument == Some (fact int_wrong_argument.conclusion, 1))

(* A Boolean argument for the Int binder; no argument; two arguments. *)
let int_bool_argument : proof_node = qi [true_expr] (Holds (clause GT.valid int_inst))
let int_no_argument : proof_node = qi [] (Holds (clause GT.valid int_inst))
let int_extra_argument : proof_node = qi [num 5; num 5] (Holds (clause GT.valid int_inst))

let int_arity_and_sort_pending ()
  : Lemma (result int_bool_argument == Some (fact int_bool_argument.conclusion, 1) /\
           result int_no_argument == Some (fact int_no_argument.conclusion, 1) /\
           result int_extra_argument == Some (fact int_extra_argument.conclusion, 1))
  = assert_norm (result int_bool_argument == Some (fact int_bool_argument.conclusion, 1));
    assert_norm (result int_no_argument == Some (fact int_no_argument.conclusion, 1));
    assert_norm (result int_extra_argument == Some (fact int_extra_argument.conclusion, 1))

(* The same clause as an `Equal` judgment (not q) = inst: accepted with
   pending 1, never checked (`lemma_equal_never_checked`), and false here. *)
let equal_node : proof_node = qi [num 5] (Equal (mk_not_expr GT.valid) int_inst)

let equal_pending () : Lemma (result equal_node == Some (fact equal_node.conclusion, 1))
  = assert_norm (result equal_node == Some (fact equal_node.conclusion, 1))

let equal_false (base:leaf) (rho:env value)
  : Lemma (~(judgment_holds (g base) rho equal_node.conclusion))
  = GT.valid_true base rho;
    lemma_num_eq base rho 5 0 5;
    GS.lemma_connectives base

(* An observational conclusion and a node with premises are rejected. *)
let observational_node : proof_node = qi [num 5] (Observational (mk_not_expr GT.valid) int_inst)
let premise_node : proof_node =
  { kind = QuantifierInstantiation [num 5]; conclusion = Holds (clause GT.valid int_inst);
    premises = [fact (Holds true_expr)] }

let rejected () : Lemma (result observational_node == None /\ result premise_node == None)
  = assert_norm (result observational_node == None);
    assert_norm (result premise_node == None)

(* --- Bool: forall p:Bool. p, instantiated at false --------------------------------------- *)

let all_p : expr = GT.all [bool_sort] GT.p0
let bool_node : proof_node = qi [false_expr] (Holds (clause all_p false_expr))

let bool_checked () : Lemma (result bool_node == Some (fact bool_node.conclusion, 0))
  = assert_norm (result bool_node == Some (fact bool_node.conclusion, 0))

(* The quantifier is false here, so the clause holds through its first
   disjunct; the instance itself is false. *)
let bool_sound (base:leaf) (rho:env value)
  : Lemma (lit_true (g base) rho (clause all_p false_expr) /\
           ~(lit_true (g base) rho all_p) /\ ~(lit_true (g base) rho false_expr))
  = bool_checked ();
    lemma_node base rho bool_node;
    GT.bool_quantifiers base rho;
    GS.lemma_connectives base;
    lemma_constants_canonical ()

(* Dropping the negation gives a false clause; it is not checked. *)
let dropped_not : expr = or2 all_p false_expr
let dropped_not_node : proof_node = qi [false_expr] (Holds dropped_not)

let dropped_not_pending () : Lemma (result dropped_not_node == Some (fact dropped_not_node.conclusion, 1))
  = assert_norm (result dropped_not_node == Some (fact dropped_not_node.conclusion, 1))

let dropped_not_false (base:leaf) (rho:env value) : Lemma (~(lit_true (g base) rho dropped_not))
  = GT.bool_quantifiers base rho;
    GS.lemma_connectives base;
    lemma_constants_canonical ();
    C.lemma_canonical_decls bool_sort 2

(* --- Heterogeneous binders: forall x:Int, p:Bool. p => x + 0 = x ----------------------------- *)

(* Arguments in binder order [3; true]; the substitution uses L.rev args, so
   Var 0 (p) becomes true and Var 1 (x) becomes 3. *)
let guarded_inst : expr = GT.implies true_expr (eq (plus (num 3) (num 0)) (num 3))
let guarded_node : proof_node = qi [num 3; true_expr] (Holds (clause GT.guarded guarded_inst))

let guarded_checked () : Lemma (result guarded_node == Some (fact guarded_node.conclusion, 0))
  = assert_norm (result guarded_node == Some (fact guarded_node.conclusion, 0))

let guarded_sound (base:leaf) (rho:env value)
  : Lemma (lit_true (g base) rho (clause GT.guarded guarded_inst) /\ lit_true (g base) rho guarded_inst)
  = guarded_checked ();
    lemma_node base rho guarded_node;
    GT.guarded_true base rho;
    lemma_instance base rho GT.guarded guarded_inst

(* Swapped arguments, a dropped argument, an extra argument, and the
   instance with the binder indices swapped (an ill-sorted term). *)
let guarded_swapped : proof_node = qi [true_expr; num 3] (Holds (clause GT.guarded guarded_inst))
let guarded_dropped : proof_node = qi [num 3] (Holds (clause GT.guarded guarded_inst))
let guarded_extra : proof_node = qi [num 3; true_expr; num 3] (Holds (clause GT.guarded guarded_inst))
let swapped_indices : expr = GT.implies (num 3) (eq (plus true_expr (num 0)) true_expr)
let guarded_swapped_indices : proof_node = qi [num 3; true_expr] (Holds (clause GT.guarded swapped_indices))

let guarded_mutations_pending ()
  : Lemma (result guarded_swapped == Some (fact guarded_swapped.conclusion, 1) /\
           result guarded_dropped == Some (fact guarded_dropped.conclusion, 1) /\
           result guarded_extra == Some (fact guarded_extra.conclusion, 1) /\
           result guarded_swapped_indices == Some (fact guarded_swapped_indices.conclusion, 1))
  = assert_norm (result guarded_swapped == Some (fact guarded_swapped.conclusion, 1));
    assert_norm (result guarded_dropped == Some (fact guarded_dropped.conclusion, 1));
    assert_norm (result guarded_extra == Some (fact guarded_extra.conclusion, 1));
    assert_norm (result guarded_swapped_indices == Some (fact guarded_swapped_indices.conclusion, 1))

(* Two Int binders, forall x:Int, y:Int. x + 0 = x, at [3; 4]: x is the
   first argument, 3. The instance at 4 (arguments not reversed) is not
   checked. *)
let x1 : expr = Var 1 int_s
let two : expr = GT.all [int_s; int_s] (eq (plus x1 (num 0)) x1)
let two_node : proof_node = qi [num 3; num 4] (Holds (clause two (eq (plus (num 3) (num 0)) (num 3))))
let two_unreversed : proof_node = qi [num 3; num 4] (Holds (clause two (eq (plus (num 4) (num 0)) (num 4))))

let two_binders ()
  : Lemma (result two_node == Some (fact two_node.conclusion, 0) /\
           result two_unreversed == Some (fact two_unreversed.conclusion, 1))
  = assert_norm (result two_node == Some (fact two_node.conclusion, 0));
    assert_norm (result two_unreversed == Some (fact two_unreversed.conclusion, 1))

(* --- Nested binders: forall x:Int. exists y:Int. y = x + 1, instantiated at 7 ----------------- *)

(* Under the inner binder, y is Var 0 and x is Var 1. The instance replaces
   only Var 1, by the closed argument 7 (lifted under the binder, which
   leaves a closed term unchanged), and keeps the inner Var 0. *)
let y0 : expr = Var 0 int_s
let inner : expr = eq y0 (plus x1 (num 1))
let nested : expr = GT.all [int_s] (GT.some [int_s] inner)
let nested_inst : expr = GT.some [int_s] (eq y0 (plus (num 7) (num 1)))
let nested_node : proof_node = qi [num 7] (Holds (clause nested nested_inst))

let nested_checked () : Lemma (result nested_node == Some (fact nested_node.conclusion, 0))
  = assert_norm (result nested_node == Some (fact nested_node.conclusion, 0))

let lemma_successor (base:leaf) (rho:env value) (x:int)
  : Lemma (lit_true (g base) (shift [VInt (x + 1)] (shift [VInt x] rho)) inner)
  = let r = shift [VInt (x + 1)] (shift [VInt x] rho) in
    assert (eval (g base) x1 r == VInt x);
    assert (eval (g base) y0 r == VInt (x + 1));
    GT.lemma_num base 1 r;
    GT.lemma_plus base x1 (num 1) r x 1;
    GT.lemma_eq base y0 (plus x1 (num 1)) r

let nested_true (base:leaf) (rho:env value) : Lemma (lit_true (g base) rho nested)
  = let pt (x:int) : Lemma (eval (g base) (GT.some [int_s] inner) (shift [VInt x] rho) == VBool true)
      = lemma_successor base rho x;
        GT.lemma_exists_int base inner (shift [VInt x] rho);
        FStar.Classical.exists_intro
          (fun (y:int) -> eval (g base) inner (shift [VInt y] (shift [VInt x] rho)) == VBool true) (x + 1) in
    FStar.Classical.forall_intro pt;
    GT.lemma_forall_int base (GT.some [int_s] inner) rho

let nested_sound (base:leaf) (rho:env value)
  : Lemma (lit_true (g base) rho (clause nested nested_inst) /\ lit_true (g base) rho nested_inst)
  = nested_checked ();
    lemma_node base rho nested_node;
    nested_true base rho;
    lemma_instance base rho nested nested_inst

(* Capture: x replaced by the inner y, `exists y. y = y + 1`. Shadowing
   mistake: the inner y replaced as well, `exists y. 7 = 7 + 1`. Both are
   false, so their clauses are false; neither is checked. *)
let captured : expr = GT.some [int_s] (eq y0 (plus y0 (num 1)))
let shadowed : expr = GT.some [int_s] (eq (num 7) (plus (num 7) (num 1)))

let captured_false (base:leaf) (rho:env value) : Lemma (eval (g base) captured rho == VBool false)
  = let pt (y:int) : Lemma (~(eval (g base) (eq y0 (plus y0 (num 1))) (shift [VInt y] rho) == VBool true))
      = let r = shift [VInt y] rho in
        GT.lemma_num base 1 r;
        GT.lemma_plus base y0 (num 1) r y 1;
        GT.lemma_eq base y0 (plus y0 (num 1)) r in
    FStar.Classical.forall_intro pt;
    GT.lemma_exists_int base (eq y0 (plus y0 (num 1))) rho

let shadowed_false (base:leaf) (rho:env value) : Lemma (eval (g base) shadowed rho == VBool false)
  = let pt (y:int) : Lemma (~(eval (g base) (eq (num 7) (plus (num 7) (num 1))) (shift [VInt y] rho) == VBool true))
      = let r = shift [VInt y] rho in
        GT.lemma_num base 7 r;
        GT.lemma_num base 1 r;
        GT.lemma_plus base (num 7) (num 1) r 7 1;
        GT.lemma_eq base (num 7) (plus (num 7) (num 1)) r in
    FStar.Classical.forall_intro pt;
    GT.lemma_exists_int base (eq (num 7) (plus (num 7) (num 1))) rho

let captured_node : proof_node = qi [num 7] (Holds (clause nested captured))
let shadowed_node : proof_node = qi [num 7] (Holds (clause nested shadowed))

(* Not instantiated: the inner body still refers to the removed binder
   (Var 1). An unscoped argument: Var 0 for x, whose capture-avoiding
   instance is that same open term, and whose naive (capturing) instance is
   `captured`. *)
let dangling_node : proof_node = qi [num 7] (Holds (clause nested (GT.some [int_s] inner)))
let unscoped_node : proof_node = qi [y0] (Holds (clause nested (GT.some [int_s] inner)))
let unscoped_captured_node : proof_node = qi [y0] (Holds (clause nested captured))

let nested_mutations_pending ()
  : Lemma (result captured_node == Some (fact captured_node.conclusion, 1) /\
           result shadowed_node == Some (fact shadowed_node.conclusion, 1) /\
           result dangling_node == Some (fact dangling_node.conclusion, 1) /\
           result unscoped_node == Some (fact unscoped_node.conclusion, 1) /\
           result unscoped_captured_node == Some (fact unscoped_captured_node.conclusion, 1))
  = assert_norm (result captured_node == Some (fact captured_node.conclusion, 1));
    assert_norm (result shadowed_node == Some (fact shadowed_node.conclusion, 1));
    assert_norm (result dangling_node == Some (fact dangling_node.conclusion, 1));
    assert_norm (result unscoped_node == Some (fact unscoped_node.conclusion, 1));
    assert_norm (result unscoped_captured_node == Some (fact unscoped_captured_node.conclusion, 1))

let open_int_instance : expr = eq (plus GT.x0 (num 0)) GT.x0
let open_int_node : proof_node = qi [GT.x0] (Holds (clause GT.valid open_int_instance))

let open_int_argument_pending ()
  : Lemma (result open_int_node == Some (fact open_int_node.conclusion, 1) /\
           C.canonical_or (C.or_decl 2) /\ C.canonical_not not_decl /\
           sorts_match [GT.x0] [int_s] /\ D.scoped [] GT.valid /\
           Q.substitute (L.rev [GT.x0]) open_int_instance == Some open_int_instance /\
           D.scoped_args [] [GT.x0] == false)
  = assert_norm (result open_int_node == Some (fact open_int_node.conclusion, 1));
    C.lemma_canonical_decls bool_sort 2;
    assert_norm (sorts_match [GT.x0] [int_s]);
    assert_norm (D.scoped [] GT.valid);
    assert_norm (Q.substitute (L.rev [GT.x0]) open_int_instance == Some open_int_instance);
    assert_norm (D.scoped_args [] [GT.x0] == false)

let open_int_argument_false (base:leaf) (rho:env value)
  : Lemma (Some? (result open_int_node) /\
           ~(scoped_holds (g base) (shift [VBool true] rho)
               (fst (Some?.v (result open_int_node)))))
  = open_int_argument_pending ();
    GT.valid_true base (shift [VBool true] rho);
    GT.untyped_body_false base rho;
    lemma_clause base (shift [VBool true] rho) GT.valid open_int_instance

(* The capture and shadowing clauses are false: certifying them would be unsound. *)
let nested_mutations_false (base:leaf) (rho:env value)
  : Lemma (~(lit_true (g base) rho (clause nested captured)) /\
           ~(lit_true (g base) rho (clause nested shadowed)))
  = nested_true base rho;
    captured_false base rho;
    shadowed_false base rho;
    lemma_clause base rho nested captured;
    lemma_clause base rho nested shadowed

(* --- Bounded bit-vectors: forall b:BV2. b = 0 or b = 1 or b = 2 or b = 3 ------------------- *)

let bv2 : sort = BV.bv_sort 2
let lit (k:int) : expr = BV.literal 2 k
let b0 : expr = Var 0 bv2
let or3 (a b c:expr) : expr = App (C.or_decl 3) [a; b; c]
let or4 (a b c d:expr) : expr = App (C.or_decl 4) [a; b; c; d]
let cover (t:expr) : expr = or4 (eq t (lit 0)) (eq t (lit 1)) (eq t (lit 2)) (eq t (lit 3))
let cover3 (t:expr) : expr = or3 (eq t (lit 0)) (eq t (lit 1)) (eq t (lit 2))
let all_bv : expr = GT.all [bv2] (cover b0)
let all_bv3 : expr = GT.all [bv2] (cover3 b0)

(* A literal of width 2 denotes the bit-vector value of its residue. *)
let lemma_lit (base:leaf) (rho:env value) (k:nat{k < 4})
  : Lemma (eval (g base) (lit k) rho == VSeq [2; k])
  = SM.lemma_width 2;
    SM.lemma_bool_width ();
    assert_norm (pow2 2 == 4);
    FStar.Math.Lemmas.small_mod k 4

let lemma_typed_bv2 (vs:list value)
  : Lemma (CO.args_typed GS.domains (L.rev [bv2]) vs <==> (exists (r:nat). r < 4 /\ vs == [VSeq [2; r]]))
  = assert_norm (L.rev [bv2] == [bv2]);
    assert_norm (pow2 2 == 4);
    GS.lemma_bv_domain 2 (match vs with [v] -> v | _ -> VInt 0)

let lemma_bool_app (base:leaf) (f:func_decl) (args:list expr) (rho:env value)
  : Lemma (requires Some? f.interp /\ f.range == bool_sort) (ensures VBool? (eval (g base) (App f args) rho))
  = GS.lemma_eval_app base f args rho;
    GS.lemma_gapp_fits base f (eval_args (g base) args rho)

let lemma_eq_lit (base:leaf) (r:env value) (t:expr) (k:nat{k < 4})
  : Lemma (VBool? (eval (g base) (eq t (lit k)) r) /\
           (lit_true (g base) r (eq t (lit k)) <==> eval (g base) t r == VSeq [2; k]))
  = lemma_lit base r k;
    GT.lemma_eq base t (lit k) r

let lemma_or (base:leaf) (r:env value) (n:nat) (args:list expr)
  : Lemma (VBool? (eval (g base) (App (C.or_decl n) args) r) /\
           (lit_true (g base) r (App (C.or_decl n) args) <==> clause_holds (g base) r args))
  = GS.lemma_connectives base;
    C.lemma_canonical_decls bool_sort n;
    lemma_bool_app base (C.or_decl n) args r

let lemma_clause4 (i:interpretation value) (r:env value) (a b c d:expr)
  : Lemma (clause_holds i r [a; b; c; d] <==>
           (lit_true i r a \/ lit_true i r b \/ lit_true i r c \/ lit_true i r d))
  = ()

let lemma_clause3 (i:interpretation value) (r:env value) (a b c:expr)
  : Lemma (clause_holds i r [a; b; c] <==> (lit_true i r a \/ lit_true i r b \/ lit_true i r c))
  = ()

(* The bodies at a term t: true exactly when t is one of the four (three)
   values of width 2. *)
let lemma_cover_at (base:leaf) (r:env value) (t:expr)
  : Lemma (VBool? (eval (g base) (cover t) r) /\
           (lit_true (g base) r (cover t) <==>
            (eval (g base) t r == VSeq [2; 0] \/ eval (g base) t r == VSeq [2; 1] \/
             eval (g base) t r == VSeq [2; 2] \/ eval (g base) t r == VSeq [2; 3])))
  = lemma_eq_lit base r t 0; lemma_eq_lit base r t 1; lemma_eq_lit base r t 2; lemma_eq_lit base r t 3;
    lemma_or base r 4 [eq t (lit 0); eq t (lit 1); eq t (lit 2); eq t (lit 3)];
    lemma_clause4 (g base) r (eq t (lit 0)) (eq t (lit 1)) (eq t (lit 2)) (eq t (lit 3))

let lemma_cover3_at (base:leaf) (r:env value) (t:expr)
  : Lemma (VBool? (eval (g base) (cover3 t) r) /\
           (lit_true (g base) r (cover3 t) <==>
            (eval (g base) t r == VSeq [2; 0] \/ eval (g base) t r == VSeq [2; 1] \/
             eval (g base) t r == VSeq [2; 2])))
  = lemma_eq_lit base r t 0; lemma_eq_lit base r t 1; lemma_eq_lit base r t 2;
    lemma_or base r 3 [eq t (lit 0); eq t (lit 1); eq t (lit 2)];
    lemma_clause3 (g base) r (eq t (lit 0)) (eq t (lit 1)) (eq t (lit 2))

(* The body at a value v: true exactly at the four values of width 2. *)
let lemma_cover (base:leaf) (rho:env value) (v:value)
  : Lemma (VBool? (eval (g base) (cover b0) (shift [v] rho)) /\
           (lit_true (g base) (shift [v] rho) (cover b0) <==>
            (v == VSeq [2; 0] \/ v == VSeq [2; 1] \/ v == VSeq [2; 2] \/ v == VSeq [2; 3])) /\
           VBool? (eval (g base) (cover3 b0) (shift [v] rho)) /\
           (lit_true (g base) (shift [v] rho) (cover3 b0) <==>
            (v == VSeq [2; 0] \/ v == VSeq [2; 1] \/ v == VSeq [2; 2])))
  = assert (eval (g base) b0 (shift [v] rho) == v);
    lemma_cover_at base (shift [v] rho) b0;
    lemma_cover3_at base (shift [v] rho) b0

let lemma_forall_typed (base:leaf) (bs:list sort) (body:expr) (rho:env value)
  : Lemma (VBool? (eval (g base) (GT.all bs body) rho) /\
           (lit_true (g base) rho (GT.all bs body) <==>
            (forall (vs:list value). CO.args_typed GS.domains (L.rev bs) vs ==> lit_true (g base) (shift vs rho) body)))
  = GS.lemma_forall base bs bool_sort body rho;
    GS.lemma_typed_quantifiers base

(* The quantifier over BV2 is true: its domain is exactly the four values. *)
let all_bv_true (base:leaf) (rho:env value) : Lemma (lit_true (g base) rho all_bv)
  = let pt (vs:list value)
      : Lemma (CO.args_typed GS.domains (L.rev [bv2]) vs ==> lit_true (g base) (shift vs rho) (cover b0))
      = lemma_typed_bv2 vs;
        match vs with [v] -> lemma_cover base rho v | _ -> () in
    FStar.Classical.forall_intro pt;
    lemma_forall_typed base [bv2] (cover b0) rho

(* Three values do not cover it: 3 is a counterexample. *)
let all_bv3_false (base:leaf) (rho:env value) : Lemma (~(lit_true (g base) rho all_bv3))
  = lemma_typed_bv2 [VSeq [2; 3]];
    lemma_cover base rho (VSeq [2; 3]);
    lemma_forall_typed base [bv2] (cover3 b0) rho

let bv_inst : expr = cover (lit 2)
let bv_node : proof_node = qi [lit 2] (Holds (clause all_bv bv_inst))

let bv_checked () : Lemma (result bv_node == Some (fact bv_node.conclusion, 0))
  = assert_norm (result bv_node == Some (fact bv_node.conclusion, 0))

(* The instance at 2 follows from the checked clause; 2 differs from 0. *)
let bv_sound (base:leaf) (rho:env value)
  : Lemma (lit_true (g base) rho (clause all_bv bv_inst) /\ lit_true (g base) rho bv_inst /\
           eval (g base) (eq (lit 2) (lit 0)) rho == VBool false)
  = bv_checked ();
    lemma_node base rho bv_node;
    all_bv_true base rho;
    lemma_instance base rho all_bv bv_inst;
    lemma_lit base rho 2;
    lemma_lit base rho 0;
    GT.lemma_eq base (lit 2) (lit 0) rho

(* The false three-value quantifier, instantiated at 3: checked, true through
   its first disjunct, while the instance itself is false. *)
let bv3_inst : expr = cover3 (lit 3)
let bv3_node : proof_node = qi [lit 3] (Holds (clause all_bv3 bv3_inst))

let bv3_sound (base:leaf) (rho:env value)
  : Lemma (result bv3_node == Some (fact bv3_node.conclusion, 0) /\
           lit_true (g base) rho (clause all_bv3 bv3_inst) /\ ~(lit_true (g base) rho bv3_inst))
  = assert_norm (result bv3_node == Some (fact bv3_node.conclusion, 0));
    lemma_node base rho bv3_node;
    all_bv3_false base rho;
    lemma_lit base rho 3;
    lemma_cover3_at base rho (lit 3)

(* A width-3 argument for the BV2 binder is not checked. *)
let bv_wide_node : proof_node = qi [BV.literal 3 2] (Holds (clause all_bv bv_inst))

let bv_wide_pending () : Lemma (result bv_wide_node == Some (fact bv_wide_node.conclusion, 1))
  = assert_norm (result bv_wide_node == Some (fact bv_wide_node.conclusion, 1))

(* Untyped values: an integer and an out-of-range residue 7 are not BV2
   values, and the true quantifier's body is false at both. *)
let bv_untyped_false (base:leaf) (rho:env value)
  : Lemma (~(CO.args_typed GS.domains (L.rev [bv2]) [VInt 0]) /\
           ~(CO.args_typed GS.domains (L.rev [bv2]) [VSeq [2; 7]]) /\
           ~(lit_true (g base) (shift [VInt 0] rho) (cover b0)) /\
           ~(lit_true (g base) (shift [VSeq [2; 7]] rho) (cover b0)))
  = lemma_typed_bv2 [VInt 0];
    lemma_typed_bv2 [VSeq [2; 7]];
    lemma_cover base rho (VInt 0);
    lemma_cover base rho (VSeq [2; 7])

(* --- Typed versus untyped elimination ------------------------------------------------------- *)

(* The legacy contract eliminates a true forall at every list of the right
   length; at [VBool true] for the Int binder of `valid` the body is false. *)
let untyped_elimination_fails (base:leaf)
  : Lemma (~(Q.forall_elimination_model (g base)) /\ TQ.typed_forall_elimination (g base) GS.domains)
  = let rho : env value = fun _ -> VInt 0 in
    let body = eq (plus GT.x0 (num 0)) GT.x0 in
    GT.valid_true base rho;
    GT.untyped_body_false base rho;
    let aux (_:squash (Q.forall_elimination_model (g base))) : Lemma False
      = assert (lit_true (g base) rho (Quantifier Forall_k [int_s] bool_sort body) ==>
                lit_true (g base) (shift [VBool true] rho) body) in
    FStar.Classical.impl_intro aux;
    GS.lemma_quantifier_model base;
    TQ.lemma_typed_forall_elimination (g base) GS.domains

(* The joint model of the kernel contract. *)
let quantifier_model_inhabited ()
  : Lemma (exists (i:interpretation value) (dom:CO.domains). TQ.quantifier_model i dom /\ GS.ghost_model i dom)
  = GS.lemma_quantifier_inhabited ()

(* --- Mutation controls: opposite claims are rejected ------------------------------------------- *)

[@@expect_failure [19]]
let int_instance_is_false (base:leaf) (rho:env value) : Lemma (~(lit_true (g base) rho int_inst))
  = int_sound base rho

[@@expect_failure [19]]
let int_wrong_is_checked () : Lemma (result int_wrong_node == Some (fact int_wrong_node.conclusion, 0))
  = assert_norm (result int_wrong_node == Some (fact int_wrong_node.conclusion, 0))

[@@expect_failure [19]]
let guarded_swapped_is_checked () : Lemma (result guarded_swapped == Some (fact guarded_swapped.conclusion, 0))
  = assert_norm (result guarded_swapped == Some (fact guarded_swapped.conclusion, 0))

[@@expect_failure [19]]
let dropped_not_is_true (base:leaf) (rho:env value) : Lemma (lit_true (g base) rho dropped_not)
  = dropped_not_false base rho

[@@expect_failure [19]]
let captured_is_checked () : Lemma (result captured_node == Some (fact captured_node.conclusion, 0))
  = assert_norm (result captured_node == Some (fact captured_node.conclusion, 0))

[@@expect_failure [19]]
let unscoped_is_checked () : Lemma (result unscoped_node == Some (fact unscoped_node.conclusion, 0))
  = assert_norm (result unscoped_node == Some (fact unscoped_node.conclusion, 0))

[@@expect_failure [19]]
let captured_is_true (base:leaf) (rho:env value) : Lemma (eval (g base) captured rho == VBool true)
  = captured_false base rho

[@@expect_failure [19]]
let bv3_instance_is_true (base:leaf) (rho:env value) : Lemma (lit_true (g base) rho bv3_inst)
  = bv3_sound base rho

[@@expect_failure [19]]
let bv_two_is_zero (base:leaf) (rho:env value) : Lemma (eval (g base) (eq (lit 2) (lit 0)) rho == VBool true)
  = bv_sound base rho

[@@expect_failure [19]]
let open_int_argument_is_checked ()
  : Lemma (result open_int_node == Some (fact open_int_node.conclusion, 0))
  = assert_norm (result open_int_node == Some (fact open_int_node.conclusion, 0))

[@@expect_failure [19]]
let membership_pending_is_checked ()
  : Lemma (check_node_with_membership [] false [] membership_accept_all int_wrong_node ==
             Some (fact int_wrong_node.conclusion, 0))
  = membership_entry_pending ();
    assert_norm (check_node_with_membership [] false [] membership_accept_all int_wrong_node ==
                   Some (fact int_wrong_node.conclusion, 0))
