module Z3SortedQuantifierRuleTests

(* Tests of the typed elim-unused rule on the Sorted route: the quant-intro
   certificate entry `elim-unused` (Z3NnfReplay.unused_eliminated, replayed
   at every scope the guard assigns it) and the premise-free closed
   ElimUnused node (Z3SortedProof.unused_elimination). The producer exports
   iff(q, e) (ast_manager::mk_elim_unused_vars): q the quantifier, e the
   same quantifier over the used binders, renumbered, or the bare body.

   U1 the executable check (normalized): the captured shapes
      (forall [Term^k] true) = true for k = 1 and 21; kept binders in order
      with renumbered indices; a lowered free index; heterogeneous binder
      lists (Real, Int, Term, an array sort, the Box datatype); exists. Its
      refusals: a dropped used binder, a free index not lowered, swapped
      kept binders, a wrong kept binder, a changed kind, the reversed
      orientation, lambda, an inner binder hiding a use, 65 binders.
   U2 the quant-intro path: a certificate whose leaf drops an unused Term
      binder under an Int binder is outside the old disjuncts and replays;
      wrong-index, premised, sorted and NNF-rooted variants stay pending;
      the refutation of the negated root equation is RootCertified and the
      equation holds in every root model.
   U3 the direct path: the captured node is outside the old disjuncts and
      checked; its refutation is RootCertified on the plain and epsilon
      routes; (exists [U] true) = true, whose truth needs an inhabited
      carrier, holds in every root model through the checked document;
      mutant, relabelled and premised nodes stay open.
   U4 a refused claim is false in a standard root model:
      (forall [Int] (<= x 0)) = true fails at x = 1.

   Every expected refusal is the checker's own verdict on a well-sorted
   input, computed by normalization. *)

open Z3AstTheory
open Z3ValueTheory
open FStar.List.Tot
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module D = Z3Definitions
module L = FStar.List.Tot
module TR = Z3TypedRoot
module SR = Z3SortedRoot
module SP = Z3SortedProof
module P = Z3ProofDocument
module U = Z3UnifiedProof
module R = Z3ResolutionProofTheory
module NR = Z3NnfReplay
module RD = Z3SortedRootDocument
module PT = Z3SortedProofTests
module QT = Z3QuantIntroReplayTests
module QCM = Z3QuantIntroCounterModelTests
module LA = Z3LinearArithmeticAst

(* ---------------------------------------------------------------------- *)
(* Shapes                                                                   *)
(* ---------------------------------------------------------------------- *)

let term : sort = QT.term
let integer : sort = TR.int_s
let real : sort = TR.real_s
let arr : sort = ArraySort [integer] term
let us : sort = BaseSort "U"

let forall_ (bs:list sort) (b:expr) : expr = Quantifier Forall_k bs bool_sort b
let exists_ (bs:list sort) (b:expr) : expr = Quantifier Exists_k bs bool_sort b

let pt (x:expr) : expr = App (QT.symbol "pt" [term] bool_sort) [x]
let pi (x:expr) : expr = App (QT.symbol "pi" [integer] bool_sort) [x]
let pb (x:expr) : expr = App (QT.symbol "pb" [PT.box] bool_sort) [x]
let pr2 (x y:expr) : expr = App (QT.symbol "pr2" [integer; term] bool_sort) [x; y]

let rec repeat (k:nat) (t:sort) : list sort = if k = 0 then [] else t :: repeat (k - 1) t

let eliminates (q e:expr) : bool = NR.unused_eliminated q e

(* ---------------------------------------------------------------------- *)
(* U1. The executable check                                                 *)
(* ---------------------------------------------------------------------- *)

let hetero : list sort = [real; integer; term; arr; PT.box]
let hetero_body : expr = QT.mk_and [pb (Var 0 PT.box); pi (Var 3 integer)]

let positives : list (expr & expr) = [
  (forall_ [term] R.true_expr, R.true_expr);
  (forall_ (repeat 21 term) R.true_expr, R.true_expr);
  (forall_ [integer; term] (pt (Var 0 term)), forall_ [term] (pt (Var 0 term)));
  (forall_ [integer; term] (pi (Var 1 integer)), forall_ [integer] (pi (Var 0 integer)));
  (exists_ [term] (pi (Var 1 integer)), pi (Var 0 integer));
  (forall_ hetero hetero_body,
   forall_ [integer; PT.box] (QT.mk_and [pb (Var 0 PT.box); pi (Var 1 integer)]));
  (exists_ [us] R.true_expr, R.true_expr)
]

let u1_positives () : Lemma (L.for_all (fun (qe:expr & expr) -> eliminates (fst qe) (snd qe)) positives) =
  assert_norm (L.for_all (fun (qe:expr & expr) -> eliminates (fst qe) (snd qe)) positives)

let mutants : list (expr & expr) = [
  (forall_ [integer] (pi (Var 0 integer)), R.true_expr);                     (* dropped used binder *)
  (forall_ [integer] (pi (Var 0 integer)), pi (Var 0 integer));              (* dropped used binder, kept body *)
  (exists_ [term] (pi (Var 1 integer)), pi (Var 1 integer));                 (* free index not lowered *)
  (forall_ hetero hetero_body,
   forall_ [PT.box; integer] (QT.mk_and [pb (Var 1 PT.box); pi (Var 0 integer)]));  (* swapped kept binders *)
  (forall_ [integer; term] (pt (Var 0 term)), forall_ [integer] (pt (Var 0 term)));  (* wrong kept binder *)
  (forall_ [integer; term] (pi (Var 1 integer)), exists_ [integer] (pi (Var 0 integer)));  (* kind changed *)
  (R.true_expr, forall_ [term] R.true_expr);                                 (* reversed orientation *)
  (Quantifier Lambda_k [term] (ArraySort [term] bool_sort) R.true_expr, R.true_expr);  (* lambda *)
  (forall_ [integer] (exists_ [term] (pi (Var 1 integer))), exists_ [term] (pi (Var 0 integer)));  (* inner use *)
  (forall_ (repeat 65 term) R.true_expr, R.true_expr)                        (* 65 binders *)
]

let u1_mutants () : Lemma (L.for_all (fun (qe:expr & expr) -> not (eliminates (fst qe) (snd qe))) mutants) =
  assert_norm (L.for_all (fun (qe:expr & expr) -> not (eliminates (fst qe) (snd qe))) mutants)

(* ---------------------------------------------------------------------- *)
(* U2. The quant-intro path                                                 *)
(* ---------------------------------------------------------------------- *)

(* forall x:Int. (or (pi x) (forall y:Term. (pi x)))
   = forall x:Int. (or (pi x) (pi x)): the leaf drops y at the scope [Int]. *)
let leaf_q : expr = forall_ [term] (pi (Var 1 integer))
let leaf_e : expr = pi (Var 0 integer)
let inner (e:expr) : expr = QT.mk_or [pi (Var 0 integer); e]
let root_of (e:expr) : expr = forall_ [integer] (inner e)

let elim_cert (name:string) (q e:expr) (ps:list int) : U.binder_certificate =
  QT.cert [{ U.binder_name = name; binder_formula = QT.eq q e; binder_premises = ps; binder_sorts = None };
           QT.be "monotonicity" (QT.eq (inner q) (inner e)) [0];
           QT.bq "quant-intro" [integer] (QT.eq (root_of q) (root_of e)) [1]] 2

let u2_replay ()
  : Lemma (not (QT.old_paths (QT.qi_node (elim_cert "elim-unused" leaf_q leaf_e []) (root_of leaf_q) (root_of leaf_e))) /\
           QT.replays (elim_cert "elim-unused" leaf_q leaf_e []) (root_of leaf_q) (root_of leaf_e) /\
           SP.check_node PT.core_schema [] (QT.qi_node (elim_cert "elim-unused" leaf_q leaf_e []) (root_of leaf_q) (root_of leaf_e)) ==
             QT.checked (root_of leaf_q) (root_of leaf_e)) =
  assert_norm (not (QT.old_paths (QT.qi_node (elim_cert "elim-unused" leaf_q leaf_e []) (root_of leaf_q) (root_of leaf_e))));
  assert_norm (QT.replays (elim_cert "elim-unused" leaf_q leaf_e []) (root_of leaf_q) (root_of leaf_e));
  assert_norm (SP.check_node PT.core_schema [] (QT.qi_node (elim_cert "elim-unused" leaf_q leaf_e []) (root_of leaf_q) (root_of leaf_e)) ==
               QT.checked (root_of leaf_q) (root_of leaf_e))

(* A leaf naming a wrong (closed) target, a leaf with a premise, a leaf with
   binder sorts, the same leaf under an NNF root, and the leaf under the
   `rewrite` label. *)
let wrong_e : expr = pi (QT.num 0)
let sorted_cert : U.binder_certificate =
  QT.cert [QT.bq "elim-unused" [term] (QT.eq leaf_q leaf_e) [];
           QT.be "monotonicity" (QT.eq (inner leaf_q) (inner leaf_e)) [0];
           QT.bq "quant-intro" [integer] (QT.eq (root_of leaf_q) (root_of leaf_e)) [1]] 2
let premised_cert : U.binder_certificate =
  QT.cert [QT.be "refl" (QT.eq R.true_expr R.true_expr) [];
           QT.be "elim-unused" (QT.eq leaf_q leaf_e) [0];
           QT.be "monotonicity" (QT.eq (inner leaf_q) (inner leaf_e)) [1];
           QT.bq "quant-intro" [integer] (QT.eq (root_of leaf_q) (root_of leaf_e)) [2]] 3
let nnf_cert : U.binder_certificate =
  QT.cert [QT.be "elim-unused" (QT.eq leaf_q leaf_e) [];
           QT.be "monotonicity" (QT.eq (inner leaf_q) (inner leaf_e)) [0];
           QT.bq "nnf-pos" [integer] (QT.eq (root_of leaf_q) (root_of leaf_e)) [1]] 2

let u2_mutants ()
  : Lemma (QT.pending (elim_cert "elim-unused" leaf_q wrong_e []) (root_of leaf_q) (root_of wrong_e) /\
           QT.pending sorted_cert (root_of leaf_q) (root_of leaf_e) /\
           QT.pending premised_cert (root_of leaf_q) (root_of leaf_e) /\
           QT.pending nnf_cert (root_of leaf_q) (root_of leaf_e) /\
           QT.pending (elim_cert "rewrite" leaf_q leaf_e []) (root_of leaf_q) (root_of leaf_e)) =
  assert_norm (QT.pending (elim_cert "elim-unused" leaf_q wrong_e []) (root_of leaf_q) (root_of wrong_e));
  assert_norm (QT.pending sorted_cert (root_of leaf_q) (root_of leaf_e));
  assert_norm (QT.pending premised_cert (root_of leaf_q) (root_of leaf_e));
  assert_norm (QT.pending nnf_cert (root_of leaf_q) (root_of leaf_e));
  assert_norm (QT.pending (elim_cert "rewrite" leaf_q leaf_e []) (root_of leaf_q) (root_of leaf_e))

let u2_documents ()
  : Lemma (RD.check_root_document PT.core_schema
             (QT.refutation (elim_cert "elim-unused" leaf_q leaf_e []) (root_of leaf_q) (root_of leaf_e)) == RD.RootCertified /\
           RD.check_root_document PT.core_schema
             (QT.refutation (elim_cert "elim-unused" leaf_q wrong_e []) (root_of leaf_q) (root_of wrong_e)) == RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema
                 (QT.refutation (elim_cert "elim-unused" leaf_q leaf_e []) (root_of leaf_q) (root_of leaf_e)) == RD.RootCertified);
  assert_norm (RD.check_root_document PT.core_schema
                 (QT.refutation (elim_cert "elim-unused" leaf_q wrong_e []) (root_of leaf_q) (root_of wrong_e)) == RD.RootPending 1)

let u2_valid (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
  : Lemma (requires TR.root_model u PT.core_schema i)
          (ensures RD.root_holds u PT.core_schema i (QT.eq (root_of leaf_q) (root_of leaf_e))) =
  u2_documents ();
  RD.lemma_root_certified u PT.core_schema
    (QT.refutation (elim_cert "elim-unused" leaf_q leaf_e []) (root_of leaf_q) (root_of leaf_e)) i;
  assert_norm (D.scoped [] (QT.neg (QT.eq (root_of leaf_q) (root_of leaf_e))));
  QT.lemma_not_holds u i (QT.eq (root_of leaf_q) (root_of leaf_e))

(* ---------------------------------------------------------------------- *)
(* U3. The direct premise-free closed ElimUnused path                       *)
(* ---------------------------------------------------------------------- *)

let elim_node (q e:expr) : U.proof_node = { U.kind = U.ElimUnused; conclusion = U.Equal q e; premises = [] }

let elim_pending (q e:expr) : option nat =
  match SP.check_node_cached PT.core_schema [] (elim_node q e) with
  | Some (_, n) -> Some n
  | None -> None

(* not (q = e), the ElimUnused step q = e, unit resolution. *)
let elim_document (q e:expr) : P.document =
  let f = QT.eq q e in
  QT.doc [QT.neg f] [QT.entry U.Asserted (QT.neg f) []; QT.entry U.ElimUnused f []; QT.entry U.UnitResolution R.false_expr [0; 1]] 2

let captured_q : expr = forall_ [term] R.true_expr
let inhabited_q : expr = exists_ [us] R.true_expr

let u3_nodes ()
  : Lemma (SP.unused_elimination (elim_node captured_q R.true_expr) /\
           not (QT.old_paths (elim_node captured_q R.true_expr)) /\
           elim_pending captured_q R.true_expr == Some 0 /\
           elim_pending inhabited_q R.true_expr == Some 0 /\
           elim_pending (forall_ (repeat 21 term) R.true_expr) R.true_expr == Some 0) =
  assert_norm (SP.unused_elimination (elim_node captured_q R.true_expr));
  assert_norm (not (QT.old_paths (elim_node captured_q R.true_expr)));
  assert_norm (elim_pending captured_q R.true_expr == Some 0);
  assert_norm (elim_pending inhabited_q R.true_expr == Some 0);
  assert_norm (elim_pending (forall_ (repeat 21 term) R.true_expr) R.true_expr == Some 0)

let u3_certified ()
  : Lemma (RD.check_root_document PT.core_schema (elim_document captured_q R.true_expr) == RD.RootCertified /\
           RD.check_root_document_epsilon PT.core_schema (elim_document captured_q R.true_expr) == RD.RootCertified /\
           RD.check_root_document PT.core_schema (elim_document inhabited_q R.true_expr) == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema (elim_document captured_q R.true_expr) == RD.RootCertified);
  assert_norm (RD.check_root_document_epsilon PT.core_schema (elim_document captured_q R.true_expr) == RD.RootCertified);
  assert_norm (RD.check_root_document PT.core_schema (elim_document inhabited_q R.true_expr) == RD.RootCertified)

(* exists x:U. true holds in every root model: U's carrier is inhabited
   (the law's inhabitant comes from the model itself). *)
let u3_inhabited (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
  : Lemma (requires TR.root_model u PT.core_schema i)
          (ensures RD.root_holds u PT.core_schema i (QT.eq inhabited_q R.true_expr)) =
  u3_certified ();
  RD.lemma_root_certified u PT.core_schema (elim_document inhabited_q R.true_expr) i;
  assert_norm (D.scoped [] (QT.neg (QT.eq inhabited_q R.true_expr)));
  QT.lemma_not_holds u i (QT.eq inhabited_q R.true_expr)

let cterm : expr = App (QT.symbol "c" [] term) []

let u3_mutants ()
  : Lemma (elim_pending (forall_ [integer] (pi (Var 0 integer))) R.true_expr == Some 1 /\
           elim_pending (forall_ [integer; term] (pt (Var 0 term))) (forall_ [term] (pt cterm)) == Some 1 /\
           not (SP.unused_elimination ({ elim_node captured_q R.true_expr with U.kind = U.RewriteRule })) /\
           not (SP.unused_elimination ({ elim_node captured_q R.true_expr with
                                         U.premises = [{ U.conclusion = U.Holds R.true_expr; hypotheses = [] }] })) /\
           not (SP.unused_elimination (elim_node R.true_expr captured_q)) /\
           RD.check_root_document PT.core_schema (elim_document (forall_ [integer] (pi (Var 0 integer))) R.true_expr) ==
             RD.RootPending 1) =
  assert_norm (elim_pending (forall_ [integer] (pi (Var 0 integer))) R.true_expr == Some 1);
  assert_norm (elim_pending (forall_ [integer; term] (pt (Var 0 term))) (forall_ [term] (pt cterm)) == Some 1);
  assert_norm (not (SP.unused_elimination ({ elim_node captured_q R.true_expr with U.kind = U.RewriteRule })));
  assert_norm (not (SP.unused_elimination ({ elim_node captured_q R.true_expr with
                                             U.premises = [{ U.conclusion = U.Holds R.true_expr; hypotheses = [] }] })));
  assert_norm (not (SP.unused_elimination (elim_node R.true_expr captured_q)));
  assert_norm (RD.check_root_document PT.core_schema (elim_document (forall_ [integer] (pi (Var 0 integer))) R.true_expr) ==
               RD.RootPending 1)

(* ---------------------------------------------------------------------- *)
(* U4. A refused claim is false in a standard root model                    *)
(* ---------------------------------------------------------------------- *)

let nonpositive : expr = QT.le (Var 0 integer) (QT.num 0)
let dropped_q : expr = forall_ [integer] nonpositive

let one_env (u:TR.uninterpreted) (x:int)
  : V.environment (TR.carrier u) (S.signature PT.core_schema) ([integer] @ []) =
  V.extend (S.signature PT.core_schema) [] [integer] [QCM.ival u x] (RD.empty_root u PT.core_schema)

(* (forall x:Int. x <= 0) is false in the standard root model of every u
   (x = 1), so the claim (forall x:Int. x <= 0) = true, refused in U1/U3, is
   false there. *)
let u4_false_claim (u:TR.uninterpreted)
  : Lemma (QCM.rtruth u QCM.none [] (RD.empty_root u PT.core_schema) dropped_q == false) =
  let i = QCM.model u QCM.none in
  let s1 = [integer] @ [] in
  let rho = one_env u 1 in
  QCM.lemma_model u QCM.none;
  QCM.int_classified ();
  assert_norm (L.rev [integer] == [integer] /\ s1 == [integer]);
  assert_norm (D.scoped [] dropped_q /\ D.scoped s1 nonpositive /\ D.scoped s1 (Var 0 integer));
  TR.lemma_eval_forall i [] (RD.empty_root u PT.core_schema) [integer] nonpositive;
  assert (QCM.rint u QCM.none s1 rho (Var 0 integer) == 1);
  QCM.lemma_numeral u QCM.none s1 rho 0;
  QCM.lemma_compare u QCM.none s1 rho (TR.le_decl TR.int_s) LA.Le (Var 0 integer) (QT.num 0);
  assert_norm (TR.icompare LA.Le 1 0 == false)

(* ---------------------------------------------------------------------- *)
(* D1. der: the executable check                                            *)
(* ---------------------------------------------------------------------- *)

(* The producer's der step keeps the binder list (der.cpp reduce1,
   update_quantifier): (forall bs. (or l1 .. ln)) = (forall bs. rest[x := t])
   with li = (not (= x t)) the first defining disequality, x a binder not
   occurring in t, the other literals kept in order. The captured
   Pulse.Checker.ForwardJumpLabel q3 node 477 leaves have this shape with
   x = #0 and t = #12, an index of the enclosing scope. *)
let neq (a b:expr) : expr = QT.neg (QT.eq a b)
let qt_ (x:expr) : expr = App (QT.symbol "qt" [term] bool_sort) [x]
let rt (x y:expr) : expr = App (QT.symbol "rt" [term; term] bool_sort) [x; y]
let fterm (x:expr) : expr = App (QT.symbol "ft" [term] term) [x]
let dterm : expr = App (QT.symbol "d" [] term) []
let x0 : expr = Var 0 term
let x1 : expr = Var 1 term
let x2 : expr = Var 2 term

let ders : list (expr & expr) = [
  (* captured shape at the scope [Term]: the free index #1 substituted *)
  (forall_ [term] (QT.mk_or [neq x1 x0; pt x0; qt_ x0]), forall_ [term] (QT.mk_or [pt x1; qt_ x1]));
  (* closed: one literal remains *)
  (forall_ [term] (QT.mk_or [neq x0 cterm; pt x0]), forall_ [term] (pt cterm));
  (* a later literal defines x, the remaining literal keeps its place *)
  (forall_ [term] (QT.mk_or [pt x0; neq cterm x0; qt_ x0]), forall_ [term] (QT.mk_or [pt cterm; qt_ cterm]));
  (* the definition lifted under a nested binder *)
  (forall_ [term] (QT.mk_or [neq x0 x1; exists_ [term] (rt x1 x0)]), forall_ [term] (exists_ [term] (rt x2 x0)));
  (* heterogeneous binders: x is the Term binder, the Int binder stays *)
  (forall_ [term; integer] (QT.mk_or [neq x1 cterm; pr2 (Var 0 integer) x1]),
   forall_ [term; integer] (pr2 (Var 0 integer) cterm))
]

let d1_ders () : Lemma (L.for_all (fun (qe:expr & expr) -> NR.der_step (fst qe) (snd qe)) ders) =
  assert_norm (L.for_all (fun (qe:expr & expr) -> NR.der_step (fst qe) (snd qe)) ders)

let der_mutants : list (expr & expr) = [
  (forall_ [term] (QT.mk_or [neq x0 cterm; pt x0]), forall_ [term] (pt dterm));            (* wrong substitution *)
  (forall_ [term] (QT.mk_or [neq x0 cterm; pt x0]), forall_ [term] (QT.mk_or [neq cterm cterm; pt cterm]));  (* literal kept *)
  (forall_ [term] (QT.mk_or [neq x0 cterm; pt x0]), pt cterm);                               (* binder dropped *)
  (forall_ [term] (QT.mk_or [neq x0 (fterm x0); pt x0]), forall_ [term] (pt (fterm x0)));   (* x occurs in t *)
  (forall_ [term] (QT.mk_or [QT.eq x0 cterm; pt x0]), forall_ [term] (pt cterm));           (* equality, not disequality *)
  (exists_ [term] (QT.mk_or [neq x0 cterm; pt x0]), exists_ [term] (pt cterm));             (* exists *)
  (forall_ [term] (QT.mk_or [neq x1 x0; pt x0; qt_ x0]), forall_ [term] (QT.mk_or [pt x0; qt_ x0]));  (* not substituted *)
  (forall_ [term] (QT.mk_or [neq x0 x1; exists_ [term] (rt x1 x0)]),
   forall_ [term] (exists_ [term] (rt x1 x0)));                                               (* not lifted *)
  (forall_ [term] (pt cterm), forall_ [term] (QT.mk_or [neq x0 cterm; pt x0]))               (* reversed orientation *)
]

let d1_mutants () : Lemma (L.for_all (fun (qe:expr & expr) -> not (NR.der_step (fst qe) (snd qe))) der_mutants) =
  assert_norm (L.for_all (fun (qe:expr & expr) -> not (NR.der_step (fst qe) (snd qe))) der_mutants)

(* ---------------------------------------------------------------------- *)
(* D2. der: the quant-intro path                                           *)
(* ---------------------------------------------------------------------- *)

(* forall y:Term. (or (pt y) <der q>) = forall y:Term. (or (pt y) <der e>):
   the captured shape at the scope [Term]. *)
let der_q : expr = forall_ [term] (QT.mk_or [neq x1 x0; pt x0; qt_ x0])
let der_e : expr = forall_ [term] (QT.mk_or [pt x1; qt_ x1])
let tinner (e:expr) : expr = QT.mk_or [pt x0; e]
let troot (e:expr) : expr = forall_ [term] (tinner e)

let der_cert (name:string) (q e:expr) : U.binder_certificate =
  QT.cert [QT.be name (QT.eq q e) [];
           QT.be "monotonicity" (QT.eq (tinner q) (tinner e)) [0];
           QT.bq "quant-intro" [term] (QT.eq (troot q) (troot e)) [1]] 2

let wrong_der_e : expr = forall_ [term] (QT.mk_or [pt cterm; qt_ cterm])

let d2_replay ()
  : Lemma (not (QT.old_paths (QT.qi_node (der_cert "der" der_q der_e) (troot der_q) (troot der_e))) /\
           QT.replays (der_cert "der" der_q der_e) (troot der_q) (troot der_e) /\
           QT.pending (der_cert "der" der_q wrong_der_e) (troot der_q) (troot wrong_der_e) /\
           QT.pending (der_cert "rewrite" der_q der_e) (troot der_q) (troot der_e) /\
           QT.pending (der_cert "elim-unused" der_q der_e) (troot der_q) (troot der_e) /\
           RD.check_root_document PT.core_schema
             (QT.refutation (der_cert "der" der_q der_e) (troot der_q) (troot der_e)) == RD.RootCertified) =
  assert_norm (not (QT.old_paths (QT.qi_node (der_cert "der" der_q der_e) (troot der_q) (troot der_e))));
  assert_norm (QT.replays (der_cert "der" der_q der_e) (troot der_q) (troot der_e));
  assert_norm (QT.pending (der_cert "der" der_q wrong_der_e) (troot der_q) (troot wrong_der_e));
  assert_norm (QT.pending (der_cert "rewrite" der_q der_e) (troot der_q) (troot der_e));
  assert_norm (QT.pending (der_cert "elim-unused" der_q der_e) (troot der_q) (troot der_e));
  assert_norm (RD.check_root_document PT.core_schema
                 (QT.refutation (der_cert "der" der_q der_e) (troot der_q) (troot der_e)) == RD.RootCertified)

let d2_valid (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
  : Lemma (requires TR.root_model u PT.core_schema i)
          (ensures RD.root_holds u PT.core_schema i (QT.eq (troot der_q) (troot der_e))) =
  d2_replay ();
  RD.lemma_root_certified u PT.core_schema (QT.refutation (der_cert "der" der_q der_e) (troot der_q) (troot der_e)) i;
  assert_norm (D.scoped [] (QT.neg (QT.eq (troot der_q) (troot der_e))));
  QT.lemma_not_holds u i (QT.eq (troot der_q) (troot der_e))

(* ---------------------------------------------------------------------- *)
(* D3. der: the direct premise-free closed DestructiveEquality path        *)
(* ---------------------------------------------------------------------- *)

let der_node (kind:U.rule) (q e:expr) : U.proof_node = { U.kind = kind; conclusion = U.Equal q e; premises = [] }

let der_pending (kind:U.rule) (q e:expr) : option nat =
  match SP.check_node_cached PT.core_schema [] (der_node kind q e) with
  | Some (_, n) -> Some n
  | None -> None

let der_closed_q : expr = forall_ [term] (QT.mk_or [neq x0 cterm; pt x0])
let der_closed_e : expr = forall_ [term] (pt cterm)

let der_document (kind:U.rule) (q e:expr) : P.document =
  let f = QT.eq q e in
  QT.doc [QT.neg f] [QT.entry U.Asserted (QT.neg f) []; QT.entry kind f []; QT.entry U.UnitResolution R.false_expr [0; 1]] 2

let d3_direct ()
  : Lemma (SP.der_rewrite (der_node U.DestructiveEquality der_closed_q der_closed_e) /\
           not (QT.old_paths (der_node U.DestructiveEquality der_closed_q der_closed_e)) /\
           der_pending U.DestructiveEquality der_closed_q der_closed_e == Some 0 /\
           der_pending U.DestructiveEquality der_closed_q (forall_ [term] (pt dterm)) == Some 1 /\
           der_pending U.RewriteRule der_closed_q der_closed_e == Some 1 /\
           RD.check_root_document PT.core_schema (der_document U.DestructiveEquality der_closed_q der_closed_e) ==
             RD.RootCertified /\
           RD.check_root_document PT.core_schema (der_document U.DestructiveEquality der_closed_q (forall_ [term] (pt dterm))) ==
             RD.RootPending 1) =
  assert_norm (SP.der_rewrite (der_node U.DestructiveEquality der_closed_q der_closed_e));
  assert_norm (not (QT.old_paths (der_node U.DestructiveEquality der_closed_q der_closed_e)));
  assert_norm (der_pending U.DestructiveEquality der_closed_q der_closed_e == Some 0);
  assert_norm (der_pending U.DestructiveEquality der_closed_q (forall_ [term] (pt dterm)) == Some 1);
  assert_norm (der_pending U.RewriteRule der_closed_q der_closed_e == Some 1);
  assert_norm (RD.check_root_document PT.core_schema (der_document U.DestructiveEquality der_closed_q der_closed_e) ==
               RD.RootCertified);
  assert_norm (RD.check_root_document PT.core_schema (der_document U.DestructiveEquality der_closed_q (forall_ [term] (pt dterm))) ==
               RD.RootPending 1)
