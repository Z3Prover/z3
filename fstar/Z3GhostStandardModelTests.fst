(* Tests for the classical ghost standard model (`Z3GhostStandardModel`):
   standard truth values of actual production quantifier/application
   terms, typed de Bruijn binder lists, integer numerals, extensional
   equality of production array values, the legacy untyped equality
   contract, the joint witness, and controls showing that the proved truth
   values discriminate (mutations fail) and that the untyped global
   contracts still have no model. *)
module Z3GhostStandardModelTests

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module GS = Z3GhostStandardModel
module CO = Z3CoreModel
module C = Z3CanonicalOps
module SM = Z3StandardModel
module A = Z3ArrayTheory
module OE = Z3ObservationalEquality
module U = Z3UnifiedProof
module L = FStar.List.Tot
module FE = FStar.FunctionalExtensionality

type leaf = func_decl -> list value -> int
let g (base:leaf) : interpretation value = GS.ghost_standard base

(* --- Production terms -------------------------------------------------------- *)

let int_s : sort = GS.int_sort
let arr_s : sort = GS.array_sort

let num_decl (n:int) : func_decl =
  { decl_name = "num"; domain = []; range = int_s; interp = Some op_num_rational; int_params = [n; 1] }
let num (n:int) : expr = App (num_decl n) []
let plus_decl : func_decl =
  { decl_name = "+"; domain = [int_s; int_s]; range = int_s; interp = Some op_plus; int_params = [] }
let plus (a b:expr) : expr = App plus_decl [a; b]
let eq (a b:expr) : expr = mk_eq_expr a b
let implies_decl : func_decl =
  { decl_name = "=>"; domain = [bool_sort; bool_sort]; range = bool_sort; interp = Some op_implies; int_params = [] }
let implies (a b:expr) : expr = App implies_decl [a; b]
let conj (a b:expr) : expr = App (C.and_decl 2) [a; b]
let select_decl : func_decl =
  { decl_name = "select"; domain = [arr_s; int_s]; range = int_s; interp = Some op_select; int_params = [] }
let store_decl : func_decl =
  { decl_name = "store"; domain = [arr_s; int_s; int_s]; range = arr_s; interp = Some op_store; int_params = [] }
let select (a i:expr) : expr = App select_decl [a; i]
let store (a i x:expr) : expr = App store_decl [a; i; x]

let x0 : expr = Var 0 int_s
let all (bs:list sort) (body:expr) : expr = Quantifier Forall_k bs bool_sort body
let some (bs:list sort) (body:expr) : expr = Quantifier Exists_k bs bool_sort body

(* --- Evaluation steps ------------------------------------------------------------ *)

let lemma_num (base:leaf) (n:int) (rho:env value) : Lemma (eval (g base) (num n) rho == VInt n)
  = GS.lemma_int_numerals base

let lemma_plus (base:leaf) (a b:expr) (rho:env value) (x y:int)
  : Lemma (requires eval (g base) a rho == VInt x /\ eval (g base) b rho == VInt y)
          (ensures eval (g base) (plus a b) rho == VInt (x + y))
  = GS.lemma_arithmetic_app base plus_decl a b rho

let lemma_eq (base:leaf) (a b:expr) (rho:env value)
  : Lemma (VBool? (eval (g base) (eq a b) rho) /\
           (eval (g base) (eq a b) rho == VBool true <==> eval (g base) a rho == eval (g base) b rho))
  = lemma_eq_decl_canonical (get_sort a);
    GS.lemma_equality_app base (eq_decl (get_sort a)) a b rho;
    GS.lemma_decide (eval (g base) a rho == eval (g base) b rho)

let lemma_typed_int (vs:list value)
  : Lemma (CO.args_typed GS.domains (L.rev [int_s]) vs <==> (exists (x:int). vs == [VInt x]))
  = assert_norm (L.rev [int_s] == [int_s]);
    GS.lemma_fits_int (match vs with [v] -> v | _ -> VInt 0)

(* forall/exists over Int: the whole of `int`. *)
let lemma_forall_int (base:leaf) (body:expr) (rho:env value)
  : Lemma (VBool? (eval (g base) (all [int_s] body) rho) /\
           (eval (g base) (all [int_s] body) rho == VBool true <==>
            (forall (x:int). eval (g base) body (shift [VInt x] rho) == VBool true)))
  = GS.lemma_forall base [int_s] bool_sort body rho;
    GS.lemma_typed_quantifiers base;
    FStar.Classical.forall_intro lemma_typed_int

let lemma_exists_int (base:leaf) (body:expr) (rho:env value)
  : Lemma (VBool? (eval (g base) (some [int_s] body) rho) /\
           (eval (g base) (some [int_s] body) rho == VBool true <==>
            (exists (x:int). eval (g base) body (shift [VInt x] rho) == VBool true)))
  = GS.lemma_exists base [int_s] bool_sort body rho;
    GS.lemma_typed_quantifiers base;
    FStar.Classical.forall_intro lemma_typed_int

let lemma_x_plus (base:leaf) (rho:env value) (x n:int)
  : Lemma (eval (g base) x0 (shift [VInt x] rho) == VInt x /\
           eval (g base) (plus x0 (num n)) (shift [VInt x] rho) == VInt (x + n))
  = lemma_num base n (shift [VInt x] rho);
    lemma_plus base x0 (num n) (shift [VInt x] rho) x n

(* --- Int quantifiers: valid, mutated, satisfiable, unsatisfiable ---------------- *)

(* forall x:Int. x + 0 = x *)
let valid : expr = all [int_s] (eq (plus x0 (num 0)) x0)

let valid_true (base:leaf) (rho:env value) : Lemma (eval (g base) valid rho == VBool true)
  = let body = eq (plus x0 (num 0)) x0 in
    let pt (x:int) : Lemma (eval (g base) body (shift [VInt x] rho) == VBool true)
      = lemma_x_plus base rho x 0;
        lemma_eq base (plus x0 (num 0)) x0 (shift [VInt x] rho) in
    FStar.Classical.forall_intro pt;
    lemma_forall_int base body rho

(* forall x:Int. x + 0 = x + 1 *)
let mutant : expr = all [int_s] (eq (plus x0 (num 0)) (plus x0 (num 1)))

let mutant_false (base:leaf) (rho:env value) : Lemma (eval (g base) mutant rho == VBool false)
  = let body = eq (plus x0 (num 0)) (plus x0 (num 1)) in
    lemma_x_plus base rho 0 0;
    lemma_x_plus base rho 0 1;
    lemma_eq base (plus x0 (num 0)) (plus x0 (num 1)) (shift [VInt 0] rho);
    lemma_forall_int base body rho

(* exists x:Int. x + 1 = 0, witness -1 *)
let satisfiable : expr = some [int_s] (eq (plus x0 (num 1)) (num 0))

let satisfiable_true (base:leaf) (rho:env value) : Lemma (eval (g base) satisfiable rho == VBool true)
  = let body = eq (plus x0 (num 1)) (num 0) in
    let rho' = shift [VInt (-1)] rho in
    lemma_x_plus base rho (-1) 1;
    lemma_num base 0 rho';
    lemma_eq base (plus x0 (num 1)) (num 0) rho';
    lemma_exists_int base body rho

(* exists x:Int. x + 1 = x *)
let unsatisfiable : expr = some [int_s] (eq (plus x0 (num 1)) x0)

let unsatisfiable_false (base:leaf) (rho:env value) : Lemma (eval (g base) unsatisfiable rho == VBool false)
  = let body = eq (plus x0 (num 1)) x0 in
    let pt (x:int) : Lemma (~(eval (g base) body (shift [VInt x] rho) == VBool true))
      = lemma_x_plus base rho x 1;
        lemma_eq base (plus x0 (num 1)) x0 (shift [VInt x] rho) in
    FStar.Classical.forall_intro pt;
    lemma_exists_int base body rho

(* Typing is load-bearing: at the untyped argument list [VBool true] the
   body of `valid` is false (`+` of a non-integer is `VInt 0`). *)
let untyped_body_false (base:leaf) (rho:env value)
  : Lemma (~(CO.args_typed GS.domains (L.rev [int_s]) [VBool true]) /\
           eval (g base) (eq (plus x0 (num 0)) x0) (shift [VBool true] rho) == VBool false)
  = lemma_typed_int [VBool true];
    lemma_num base 0 (shift [VBool true] rho);
    GS.lemma_arithmetic_app base plus_decl x0 (num 0) (shift [VBool true] rho);
    lemma_eq base (plus x0 (num 0)) x0 (shift [VBool true] rho)

(* --- Several binders: Int and Bool, reversed de Bruijn order ---------------------- *)

(* `forall x:Int, p:Bool. body` binds p to Var 0 and x to Var 1, so its
   argument lists are typed by L.rev [Int; Bool] = [Bool; Int]. *)
let lemma_typed_int_bool (vs:list value)
  : Lemma (CO.args_typed GS.domains (L.rev [int_s; bool_sort]) vs <==>
           (exists (p:bool) (x:int). vs == [VBool p; VInt x]))
  = assert_norm (L.rev [int_s; bool_sort] == [bool_sort; int_s]);
    match vs with
    | [a; b] -> GS.lemma_fits_bool a; GS.lemma_fits_int b
    | _ -> ()

let lemma_typed_bool_int (vs:list value)
  : Lemma (CO.args_typed GS.domains (L.rev [bool_sort; int_s]) vs <==>
           (exists (x:int) (p:bool). vs == [VInt x; VBool p]))
  = assert_norm (L.rev [bool_sort; int_s] == [int_s; bool_sort]);
    match vs with
    | [a; b] -> GS.lemma_fits_int a; GS.lemma_fits_bool b
    | _ -> ()

let p0 : expr = Var 0 bool_sort
let x1 : expr = Var 1 int_s

(* forall x:Int, p:Bool. p => x + 0 = x *)
let guarded_body : expr = implies p0 (eq (plus x1 (num 0)) x1)
let guarded : expr = all [int_s; bool_sort] guarded_body

let guarded_true (base:leaf) (rho:env value) : Lemma (eval (g base) guarded rho == VBool true)
  = GS.lemma_connectives base;
    let pt (vs:list value)
      : Lemma (CO.args_typed GS.domains (L.rev [int_s; bool_sort]) vs ==>
               eval (g base) guarded_body (shift vs rho) == VBool true)
      = lemma_typed_int_bool vs;
        match vs with
        | [VBool p; VInt x] ->
          let r = shift vs rho in
          assert (eval (g base) x1 r == VInt x);
          lemma_num base 0 r;
          lemma_plus base x1 (num 0) r x 0;
          lemma_eq base (plus x1 (num 0)) x1 r
        | _ -> () in
    FStar.Classical.forall_intro pt;
    GS.lemma_forall base [int_s; bool_sort] bool_sort guarded_body rho;
    GS.lemma_decide (forall (vs:list value). CO.args_typed GS.domains (L.rev [int_s; bool_sort]) vs ==>
                       eval (g base) guarded_body (shift vs rho) == VBool true)

(* The canonical binary conjunction. *)
let lemma_conj (base:leaf) (a b:expr) (rho:env value)
  : Lemma (eval (g base) (conj a b) rho == VBool true <==>
           (eval (g base) a rho == VBool true /\ eval (g base) b rho == VBool true))
  = GS.lemma_connectives base;
    C.lemma_canonical_decls bool_sort 2

(* exists x:Int, p:Bool. p and x = -1 *)
let witness_body : expr = conj p0 (eq x1 (num (-1)))
let witnessed : expr = some [int_s; bool_sort] witness_body

let witnessed_true (base:leaf) (rho:env value) : Lemma (eval (g base) witnessed rho == VBool true)
  = let vs = [VBool true; VInt (-1)] in
    let r = shift vs rho in
    lemma_typed_int_bool vs;
    assert (eval (g base) p0 r == VBool true /\ eval (g base) x1 r == VInt (-1));
    lemma_num base (-1) r;
    lemma_eq base x1 (num (-1)) r;
    lemma_conj base p0 (eq x1 (num (-1))) r;
    GS.lemma_exists base [int_s; bool_sort] bool_sort witness_body rho;
    FStar.Classical.exists_intro
      (fun (vs:list value) -> CO.args_typed GS.domains (L.rev [int_s; bool_sort]) vs /\
                             eval (g base) witness_body (shift vs rho) == VBool true) vs;
    GS.lemma_decide (exists (vs:list value). CO.args_typed GS.domains (L.rev [int_s; bool_sort]) vs /\
                       eval (g base) witness_body (shift vs rho) == VBool true)

(* The same body under the binder-swapped list [Bool; Int]: Var 0 is then
   an integer, so the conjunction never holds. *)
let swapped : expr = some [bool_sort; int_s] witness_body

let swapped_false (base:leaf) (rho:env value) : Lemma (eval (g base) swapped rho == VBool false)
  = GS.lemma_connectives base;
    C.lemma_canonical_decls bool_sort 2;
    let pt (vs:list value)
      : Lemma (~(CO.args_typed GS.domains (L.rev [bool_sort; int_s]) vs /\
                 eval (g base) witness_body (shift vs rho) == VBool true))
      = lemma_typed_bool_int vs;
        match vs with
        | [VInt x; VBool p] -> assert (eval (g base) p0 (shift vs rho) == VInt x)
        | _ -> () in
    FStar.Classical.forall_intro pt;
    GS.lemma_exists base [bool_sort; int_s] bool_sort witness_body rho;
    GS.lemma_decide (exists (vs:list value). CO.args_typed GS.domains (L.rev [bool_sort; int_s]) vs /\
                       eval (g base) witness_body (shift vs rho) == VBool true)

(* Bool quantifiers: forall p:Bool. p is false, exists p:Bool. p is true. *)
let lemma_typed_bool (vs:list value)
  : Lemma (CO.args_typed GS.domains (L.rev [bool_sort]) vs <==> (exists (p:bool). vs == [VBool p]))
  = assert_norm (L.rev [bool_sort] == [bool_sort]);
    GS.lemma_fits_bool (match vs with [v] -> v | _ -> VInt 0)

let bool_quantifiers (base:leaf) (rho:env value)
  : Lemma (eval (g base) (all [bool_sort] p0) rho == VBool false /\
           eval (g base) (some [bool_sort] p0) rho == VBool true)
  = FStar.Classical.forall_intro lemma_typed_bool;
    lemma_typed_bool [VBool false];
    lemma_typed_bool [VBool true];
    GS.lemma_forall base [bool_sort] bool_sort p0 rho;
    GS.lemma_exists base [bool_sort] bool_sort p0 rho;
    GS.lemma_typed_quantifiers base

(* --- Integer numerals --------------------------------------------------------------- *)

(* 1 = 0 is false; the old witness gives every numeral the opaque value 0. *)
let numeral_mutation (base:leaf) (rho:env value)
  : Lemma (eval (g base) (eq (num 1) (num 0)) rho == VBool false /\
           eval (CO.witness (fun _ _ -> 0)) (eq (num 1) (num 0)) rho == VBool true)
  = lemma_num base 1 rho;
    lemma_num base 0 rho;
    lemma_eq base (num 1) (num 0) rho;
    assert_norm (eval (CO.witness (fun _ _ -> 0)) (eq (num 1) (num 0)) rho == VBool true)

(* Other numeral forms are opaque: their value is the leaf's, not a
   truncation. A fraction 1/2 with range Int, a Real-range 1/1, and a
   wrong parameter list each take whatever value the leaf gives. *)
let fraction : expr =
  App { decl_name = "num"; domain = []; range = int_s; interp = Some op_num_rational; int_params = [1; 2] } []
let real_one : expr =
  App { decl_name = "num"; domain = []; range = BaseSort "Real"; interp = Some op_num_rational; int_params = [1; 1] } []
let short_numeral : expr =
  App { decl_name = "num"; domain = []; range = int_s; interp = Some op_num_rational; int_params = [1] } []

let opaque_numerals (rho:env value)
  : Lemma (eval (g (fun _ _ -> 5)) fraction rho == VInt 5 /\ eval (g (fun _ _ -> 7)) fraction rho == VInt 7 /\
           eval (g (fun _ _ -> 5)) real_one rho == VInt 5 /\ eval (g (fun _ _ -> 7)) real_one rho == VInt 7 /\
           eval (g (fun _ _ -> 5)) short_numeral rho == VInt 5)
  = GS.lemma_int_carried ();
    SM.lemma_bool_width ();
    assert_norm (SM.width_of_sort (BaseSort "Real") == None);
    assert_norm (~(C.canonical_connective (match fraction with App f _ -> f | _ -> num_decl 0)))

(* --- Extensional equality of production arrays ---------------------------------------- *)

let a0 : expr = Var 0 arr_s
let a1 : expr = Var 1 arr_s
let pair (x y:A.arr int int) (rho:env value) : env value = shift [VArr x; VArr y] rho

let identity : A.arr int int = FE.on int (fun k -> k)
let identity_plus_zero : A.arr int int = FE.on int (fun k -> k + 0)
let shifted : A.arr int int = FE.on int (fun k -> k + 1)

let lemma_array_eq (base:leaf) (x y:A.arr int int) (rho:env value)
  : Lemma (VBool? (eval (g base) (eq a0 a1) (pair x y rho)) /\
           (eval (g base) (eq a0 a1) (pair x y rho) == VBool true <==> (forall (k:int). A.select x k == A.select y k)))
  = lemma_eq base a0 a1 (pair x y rho);
    A.lemma_array_extensionality x y

let identity_equal (base:leaf) (rho:env value)
  : Lemma (eval (g base) (eq a0 a1) (pair identity identity_plus_zero rho) == VBool true)
  = lemma_array_eq base identity identity_plus_zero rho

let constant_equal (base:leaf) (rho:env value)
  : Lemma (eval (g base) (eq a0 a1) (pair (A.const_arr 0) (A.store (A.const_arr 0) 3 0) rho) == VBool true)
  = lemma_array_eq base (A.const_arr 0) (A.store (A.const_arr 0) 3 0) rho

let shifted_differs (base:leaf) (rho:env value)
  : Lemma (eval (g base) (eq a0 a1) (pair identity shifted rho) == VBool false)
  = lemma_array_eq base identity shifted rho;
    assert (A.select identity 0 =!= A.select shifted 0)

let store_differs (base:leaf) (rho:env value)
  : Lemma (eval (g base) (eq a0 a1) (pair (A.store identity 3 4) identity rho) == VBool false)
  = lemma_array_eq base (A.store identity 3 4) identity rho;
    assert (A.select (A.store identity 3 4) 3 =!= A.select identity 3)

(* forall a:(Array Int Int). store a 0 (select a 0) = a, over every
   production array; its mutation with +1 is false. *)
let lemma_typed_array (vs:list value)
  : Lemma (CO.args_typed GS.domains (L.rev [arr_s]) vs <==> (exists (x:A.arr int int). vs == [VArr x]))
  = assert_norm (L.rev [arr_s] == [arr_s]);
    GS.lemma_fits_array (match vs with [v] -> v | _ -> VInt 0)

let lemma_select_store (base:leaf) (rho:env value) (x:A.arr int int) (k v:int)
  : Lemma (eval (g base) (select a0 (num k)) (shift [VArr x] rho) == VInt (A.select x k) /\
           eval (g base) (store a0 (num k) (num v)) (shift [VArr x] rho) == VArr (A.store x k v))
  = lemma_num base k (shift [VArr x] rho);
    lemma_num base v (shift [VArr x] rho);
    GS.lemma_int_carried ();
    GS.lemma_array_carried ()

let store_select_body : expr = eq (store a0 (num 0) (select a0 (num 0))) a0

let store_select_true (base:leaf) (rho:env value)
  : Lemma (eval (g base) (all [arr_s] store_select_body) rho == VBool true)
  = let pt (vs:list value)
      : Lemma (CO.args_typed GS.domains (L.rev [arr_s]) vs ==>
               eval (g base) store_select_body (shift vs rho) == VBool true)
      = lemma_typed_array vs;
        match vs with
        | [VArr x] ->
          let r = shift vs rho in
          lemma_select_store base rho x 0 0;
          GS.lemma_int_carried ();
          GS.lemma_array_carried ();
          assert (eval (g base) (store a0 (num 0) (select a0 (num 0))) r == VArr (A.store x 0 (A.select x 0)));
          A.lemma_array_extensionality (A.store x 0 (A.select x 0)) x;
          lemma_eq base (store a0 (num 0) (select a0 (num 0))) a0 r
        | _ -> () in
    FStar.Classical.forall_intro pt;
    GS.lemma_forall base [arr_s] bool_sort store_select_body rho;
    GS.lemma_decide (forall (vs:list value). CO.args_typed GS.domains (L.rev [arr_s]) vs ==>
                       eval (g base) store_select_body (shift vs rho) == VBool true)

let store_shift_body : expr = eq (store a0 (num 0) (plus (select a0 (num 0)) (num 1))) a0

let store_shift_false (base:leaf) (rho:env value)
  : Lemma (eval (g base) (all [arr_s] store_shift_body) rho == VBool false)
  = let z : A.arr int int = A.const_arr 0 in
    let r = shift [VArr z] rho in
    lemma_select_store base rho z 0 0;
    lemma_num base 1 r;
    lemma_plus base (select a0 (num 0)) (num 1) r 0 1;
    GS.lemma_int_carried ();
    GS.lemma_array_carried ();
    assert (eval (g base) (store a0 (num 0) (plus (select a0 (num 0)) (num 1))) r == VArr (A.store z 0 1));
    assert (A.select (A.store z 0 1) 0 =!= A.select z 0);
    lemma_eq base (store a0 (num 0) (plus (select a0 (num 0)) (num 1))) a0 r;
    lemma_typed_array [VArr z];
    GS.lemma_forall base [arr_s] bool_sort store_shift_body rho;
    GS.lemma_decide (forall (vs:list value). CO.args_typed GS.domains (L.rev [arr_s]) vs ==>
                       eval (g base) store_shift_body (shift vs rho) == VBool true)

(* --- Legacy untyped equality, and the old witness ------------------------------------------ *)

(* The review counterexample: an Int variable mapped to an array value. The
   old core witness makes its `x = x` false; the ghost model makes it true,
   as the untyped `eq_sound` requires under every environment. *)
let rho_array_at_int : env value = fun _ -> VArr (A.const_arr 0)

let ill_typed_reflexive (base:leaf)
  : Lemma (eval (g base) (eq x0 x0) rho_array_at_int == VBool true /\
           eval (CO.witness (fun _ _ -> 0)) (eq x0 x0) rho_array_at_int == VBool false)
  = lemma_eq base x0 x0 rho_array_at_int;
    assert_norm (eval (CO.witness (fun _ _ -> 0)) (eq x0 x0) rho_array_at_int == VBool false)

(* One interpretation satisfies the typed core contracts and all seven
   canonical legacy connective contracts, equality included. The old
   witness satisfies the first six but not `eq_sound`
   (`Z3CoreModelTests.core_without_untyped_equality`), so `eq_sound` is not
   a consequence of `core_model`. *)
let ghost_with_untyped_equality (base:leaf)
  : Lemma (CO.core_model (g base) GS.domains /\
           not_sound (g base) /\ and_sound (g base) /\ or_sound (g base) /\ implies_sound (g base) /\
           true_sound (g base) /\ false_sound (g base) /\ eq_sound (g base))
  = GS.lemma_ghost_standard base

let joint_witness () : Lemma (exists (i:interpretation value) (dom:CO.domains). GS.ghost_model i dom)
  = GS.lemma_ghost_inhabited ()

(* --- Residual: the untyped global contracts still have no model --------------------------- *)

(* The untyped `boolean_model` asks a Bool variable to be a `VBool` under
   every environment; the ghost model, like every typed model, does not. *)
let ghost_boolean_model_fails (base:leaf)
  : Lemma (~(OE.boolean_model (g base)) /\ ~(U.model_sound (g base)))
  = assert (eval (g base) (Var 0 bool_sort) (fun _ -> VInt 0) == VInt 0)

(* --- Mutation controls: the opposite truth values are rejected ------------------------------ *)

[@@expect_failure [19]]
let valid_is_false (base:leaf) (rho:env value) : Lemma (eval (g base) valid rho == VBool false)
  = valid_true base rho

[@@expect_failure [19]]
let mutant_is_true (base:leaf) (rho:env value) : Lemma (eval (g base) mutant rho == VBool true)
  = mutant_false base rho

[@@expect_failure [19]]
let satisfiable_is_false (base:leaf) (rho:env value) : Lemma (eval (g base) satisfiable rho == VBool false)
  = satisfiable_true base rho

[@@expect_failure [19]]
let unsatisfiable_is_true (base:leaf) (rho:env value) : Lemma (eval (g base) unsatisfiable rho == VBool true)
  = unsatisfiable_false base rho

[@@expect_failure [19]]
let swapped_is_true (base:leaf) (rho:env value) : Lemma (eval (g base) swapped rho == VBool true)
  = swapped_false base rho

[@@expect_failure [19]]
let shifted_is_equal (base:leaf) (rho:env value)
  : Lemma (eval (g base) (eq a0 a1) (pair identity shifted rho) == VBool true)
  = shifted_differs base rho

[@@expect_failure [19]]
let one_is_zero (base:leaf) (rho:env value) : Lemma (eval (g base) (eq (num 1) (num 0)) rho == VBool true)
  = numeral_mutation base rho

[@@expect_failure [19]]
let store_shift_is_true (base:leaf) (rho:env value)
  : Lemma (eval (g base) (all [arr_s] store_shift_body) rho == VBool true)
  = store_shift_false base rho
