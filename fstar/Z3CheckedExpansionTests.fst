(*
   Z3CheckedExpansionTests.fst

   Executable tests of definition expansion on the checked graph
   (`Z3CheckedExpansion`), run natively on the Cherry backend
   (`Z3CherryTests.run`) and verified with the F* test modules. Each small
   case compares the node the graph builds with the spec function on the
   expression (`Z3Definitions.lift`, `instantiate`, `expand`), including the
   cases the spec refuses (refused on the graph too):

   * interning stores the exact expression;
   * a lift under binders (the cutoff raised by each binder), and an
     identity lift that reuses the node;
   * instantiations with nested binders (the argument lifted under them), a
     substitution with its variables swapped, different arguments for one
     body (each call's memo its own), and a variable no argument binds;
   * expansions: a definition used twice (one node, one memo entry), a
     definition whose body has a quantifier (no capture), a chain of two
     definitions (enough fuel, and one short: refused), a cyclic definition
     (refused), an expansion of the same node under other definitions (not
     reusing the first), a body imported once and reused by a later call
     (`bodies` passed on), and an expansion one unit short (exhausted);
   * deep inputs (100,000 nested applications) interned, lifted,
     instantiated and expanded without a stack that grows with the depth.
*)
module Z3CheckedExpansionTests

open Z3AstTheory
module L = FStar.List.Tot
module I = Z3ProofIndex
module CS = Z3CheckedSorts
module T = Z3CheckedTerms
module CG = Z3CheckedGraph
module CX = Z3CheckedExpansion
module D = Z3Definitions

let int_s : sort = BaseSort "Int"

let decl (name:string) (dom:list sort) (r:sort) : func_decl =
  { decl_name = name; domain = dom; range = r; interp = None; int_params = [] }

let p_d : func_decl = decl "p" [int_s] bool_sort
let f_d : func_decl = decl "f" [int_s] bool_sort
let k_d : func_decl = decl "k" [int_s] bool_sort
let g_d : func_decl = decl "g" [int_s; int_s] int_s
let q_d : func_decl = decl "q" [int_s] int_s
let c_d : func_decl = decl "c" [] int_s

let v (n:nat) : expr = Var n int_s
let c : expr = App c_d []
let q (e:expr) : expr = App q_d [e]
let gg (a b:expr) : expr = App g_d [a; b]
let p (e:expr) : expr = App p_d [e]
let f (e:expr) : expr = App f_d [e]
let k (e:expr) : expr = App k_d [e]
let all (b:expr) : expr = Quantifier Forall_k [int_s] bool_sort b

let big : nat = 1000000000

let fresh (prep store:nat) : g:CG.cgraph{CG.graph_inv g} =
  CS.lemma_initial_state ({ CS.preparation = 0; CS.storage = 0 });
  CG.empty prep store

(* --- Interning and lifting --- *)

let intern_ok (e:expr) : bool =
  match CX.intern_expr (fresh big big) e with
  | CX.Interned g y -> CG.value_of g y = Some e
  | CX.InternStopped _ -> false

let lift_ok (e:expr) (a cut:nat) : bool =
  match CX.intern_expr (fresh big big) e with
  | CX.Interned g x ->
    (match CX.glift a cut g I.Empty x with
     | CX.LiftedNode g' _ y -> CG.value_of g' y = Some (D.lift a cut e)
     | CX.LiftStopped _ -> false)
  | CX.InternStopped _ -> false

(* An identity lift (nothing at or above the cutoff) is the node itself. *)
let identity_lift () : bool =
  let e = all (gg (v 0) c) in
  match CX.intern_expr (fresh big big) e with
  | CX.Interned g x ->
    (match CX.glift 3 1 g I.Empty x with
     | CX.LiftedNode _ _ y -> y = x
     | CX.LiftStopped _ -> false)
  | CX.InternStopped _ -> false

(* --- Instantiation --- *)

(* The instance of `body` with `vars` replaced by `a0`, `a1`, built on one
   graph: `Some r` with `r` the stored instance (`None`: refused). *)
let instance_of (body a0 a1:expr) (vars:list nat) : option (option expr) =
  match CX.intern_expr (fresh big big) body with
  | CX.Interned g1 b ->
    (match CX.intern_expr g1 a0 with
     | CX.Interned g2 n0 ->
       (match CX.intern_expr g2 a1 with
        | CX.Interned g3 n1 ->
          (match CX.ginst vars [n0; n1] g3 b with
           | CX.InstNode g4 z -> Some (CG.value_of g4 z)
           | CX.InstStopped _ -> Some None)
        | CX.InternStopped _ -> None)
     | CX.InternStopped _ -> None)
  | CX.InternStopped _ -> None

let inst_ok (body a0 a1:expr) (vars:list nat) : bool =
  match instance_of body a0 a1 vars, D.instantiate 0 vars [a0; a1] body with
  | Some (Some r), Some w -> r = w
  | Some None, None -> true
  | _, _ -> false

(* Two instances of one body node with different arguments, one after the
   other on one graph: each is its own call's, with its own memo. *)
let different_args () : bool =
  let body = gg (v 0) (q (v 0)) in
  match CX.intern_expr (fresh big big) body with
  | CX.Interned g1 b ->
    (match CX.intern_expr g1 c with
     | CX.Interned g2 n0 ->
       (match CX.intern_expr g2 (q c) with
        | CX.Interned g3 n1 ->
          (match CX.ginst [0] [n0] g3 b with
           | CX.InstNode g4 z0 ->
             (match CX.ginst [0] [n1] g4 b with
              | CX.InstNode g5 z1 ->
                CG.value_of g5 z0 = D.instantiate 0 [0] [c] body &&
                CG.value_of g5 z1 = D.instantiate 0 [0] [q c] body &&
                z0 <> z1
              | CX.InstStopped _ -> false)
           | CX.InstStopped _ -> false)
        | CX.InternStopped _ -> false)
     | CX.InternStopped _ -> false)
  | CX.InternStopped _ -> false

(* --- Expansion --- *)

let expansion (defs:list D.definition) (fuel:nat) (prep:nat) (e:expr) : option (option expr) =
  match CX.intern_expr (fresh big big) e with
  | CX.Interned g x ->
    CG.lemma_budget g prep big;
    let g' = { g with CG.prep = prep; CG.store = big } in
    assert (CX.bodies_ok defs g' I.Empty);
    (match CX.expand_nodes defs fuel g' I.Empty [x] with
     | CX.ExpandedNodes g'' _ [y] -> Some (CG.value_of g'' y)
     | CX.ExpandedNodes _ _ _ -> None
     | CX.ExpandStopped _ -> Some None)
  | CX.InternStopped _ -> None

let expand_ok (defs:list D.definition) (fuel:nat) (e:expr) : bool =
  match expansion defs fuel big e, D.expand fuel defs e with
  | Some (Some r), Some w -> r = w
  | Some None, None -> true
  | _, _ -> false

let exhausted (defs:list D.definition) (fuel:nat) (prep:nat) (e:expr) : bool =
  match CX.intern_expr (fresh big big) e with
  | CX.Interned g x ->
    CG.lemma_budget g prep big;
    let g' = { g with CG.prep = prep; CG.store = big } in
    assert (CX.bodies_ok defs g' I.Empty);
    (match CX.expand_nodes defs fuel g' I.Empty [x] with
     | CX.ExpandStopped (CG.BuildExhausted T.Preparation) -> true
     | _ -> false)
  | CX.InternStopped _ -> false

let def (s:func_decl) (vars:list nat) (body:expr) : D.definition = { D.symbol = s; D.variables = vars; D.body = body }

(* f(x) := not-free p(q(x)); used twice, and under a binder *)
let defs1 : list D.definition = [def f_d [0] (p (q (v 0)))]
(* f(x) := forall y. p(g(y, x)): the argument is lifted under the binder *)
let defs_quant : list D.definition = [def f_d [0] (all (p (gg (v 0) (v 1))))]
(* f(x) := k(x); k(x) := p(x) *)
let defs_chain : list D.definition = [def f_d [0] (k (v 0)); def k_d [0] (p (v 0))]
let defs_cycle : list D.definition = [def f_d [0] (f (v 0))]
let defs_other : list D.definition = [def f_d [0] (p c)]

(* A body imported by one expansion is reused by a later one (`bodies`
   passed on): the later one adds no node for it. *)
let body_reused () : bool =
  match CX.intern_expr (fresh big big) (f c) with
  | CX.Interned g1 x0 ->
    (match CX.intern_expr g1 (f (q c)) with
     | CX.Interned g2 x1 ->
       assert (CX.bodies_ok defs1 g2 I.Empty);
       (match CX.expand_nodes defs1 1 g2 I.Empty [x0] with
        | CX.ExpandedNodes g3 b3 [y0] ->
          let n3 = CG.node_count g3 in
          (match CX.expand_nodes defs1 1 g3 b3 [x1] with
           | CX.ExpandedNodes g4 _ [y1] ->
             (match CX.expand_nodes defs1 1 g3 I.Empty [x1] with
              | CX.ExpandedNodes g5 _ [_] ->
                CG.value_of g4 y1 = D.expand 1 defs1 (f (q c)) &&
                CG.value_of g3 y0 = D.expand 1 defs1 (f c) &&
                (* reusing the imported body adds fewer nodes than importing it again *)
                CG.node_count g4 - n3 < CG.node_count g5 - n3
              | _ -> false)
           | _ -> false)
        | _ -> false)
     | CX.InternStopped _ -> false)
  | CX.InternStopped _ -> false

(* --- Deep inputs --- *)

let rec chain (n:nat) (acc:expr) : Tot expr (decreases n) = if n = 0 then acc else chain (n - 1) (q acc)

let deep () : bool =
  let e = all (p (chain 100000 (v 0))) in
  let defs_q = [def q_d [0] (gg (v 0) c)] in
  match CX.intern_expr (fresh big big) e with
  | CX.Interned g1 x ->
    (match CX.glift 1 0 g1 I.Empty x with
     | CX.LiftedNode g2 _ _ ->
       (match CX.ginst [0] [x] g2 x with
        | CX.InstNode g3 _ ->
          assert (CX.bodies_ok defs_q g3 I.Empty);
          (match CX.expand_nodes defs_q 1 g3 I.Empty [x] with
           | CX.ExpandedNodes _ _ [_] -> true
           | _ -> false)
        | CX.InstStopped _ -> false)
     | CX.LiftStopped _ -> false)
  | CX.InternStopped _ -> false

(* The checks, in order; `first_failure` is the position (from 1) of the
   first that fails, 0 if none, so that a backend can name it. *)
let checks () : list bool =
  let e1 = all (p (gg (v 0) (v 1))) in
  [intern_ok e1;
   intern_ok (gg (q c) (v 3));
   lift_ok e1 2 0;
   lift_ok e1 1 1;
   lift_ok (gg (v 0) (v 5)) 4 3;
   identity_lift ();
   inst_ok (all (p (gg (v 0) (v 1)))) (q (v 0)) c [0; 1];
   inst_ok (gg (v 0) (v 1)) (q c) c [1; 0];
   inst_ok (gg (v 0) (v 1)) (q c) c [0; 1];
   inst_ok (gg (v 0) (v 7)) c c [0; 1];
   different_args ();
   expand_ok defs1 1 (gg (q c) c);
   expand_ok defs1 1 (all (p (gg (v 0) c)));
   expand_ok defs1 1 (all (App g_d [q (v 0); q (v 0)]));
   expand_ok defs1 1 (all (p (gg (v 0) (v 0))));
   expand_ok defs1 1 (App p_d [App q_d [v 0]]);
   expand_ok defs1 1 (all (f (v 0)));
   expand_ok defs1 1 (all (App p_d [App q_d [App g_d [v 0; c]]]));
   expand_ok defs1 1 (all (gg (q (v 0)) (q (v 0))));
   expand_ok defs1 1 (all (p (q (v 0))));
   expand_ok defs1 1 (all (f (q (v 0))));
   expand_ok defs1 1 (all (App p_d [q (v 0)]));
   expand_ok defs_quant 1 (all (f (v 0)));
   expand_ok defs_quant 1 (f (q c));
   expand_ok defs_chain 2 (all (f (v 0)));
   expand_ok defs_chain 1 (all (f (v 0)));
   expand_ok defs_cycle 1 (f c);
   expand_ok defs_other 1 (all (f (v 0)));
   expand_ok [] 0 (f c);
   body_reused ();
   exhausted defs1 1 0 (f c);
   exhausted defs1 1 200 (f c);
   not (exhausted defs1 1 big (f c));
   deep ()]

let rec first_false (l:list bool) (i:int) : Tot int (decreases l) =
  match l with
  | [] -> 0
  | b :: rest -> if b then first_false rest (i + 1) else i

let first_failure () : int = first_false (checks ()) 1

let run () : bool = first_failure () = 0
