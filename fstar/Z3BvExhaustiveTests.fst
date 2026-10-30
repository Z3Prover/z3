module Z3BvExhaustiveTests

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module BV = Z3BvLemma
module E = Z3BvExhaustive
module C = Z3CanonicalOps
module SM = Z3StandardModel
module DT = Z3DatatypeLemma

(* Closed instances of the bounded bit-vector evaluation, decided by normalization. Normalizing an
   enumeration is slow, so the leaves here have 1 to 3 bits and the shapes of the egt-0160 and egt-7033
   obligations keep their 32-bit and 10-bit operators around a 2-bit leaf `x = (select packet #x000000f1)`.
   The 8-bit originals, the 12-bit boundary (4096 assignments) and the 13-bit cap are exercised on the
   extracted kernel by the `checked-bounded-bit-vector-evaluation` group of tools/test_native_bridge.ml. *)

let bv (w:pos) : sort = BV.bv_sort w
let num (w:pos) (n:int) : expr = BV.literal w n

let constant (s:sort) (name:string) : expr =
  App { decl_name = name; domain = []; range = s; interp = None; int_params = [] } []

let packet : expr = constant (ArraySort [bv 32] (bv 2)) "packet"

let select (a i:expr) : expr =
  App { decl_name = "select"; domain = [get_sort a; get_sort i]; range = bv 2;
        interp = Some op_select; int_params = [] } [a; i]

let x : expr = select packet (num 32 241)
let other : expr = select packet (num 32 242)
let u : expr = constant (bv 2) "u"
let p : expr = constant bool_sort "p"

let concat (m n:pos) (a b:expr) : expr =
  App { decl_name = "concat"; domain = [bv m; bv n]; range = bv (m + n);
        interp = Some BV.op_concat; int_params = [m; n] } [a; b]

let extract (w:pos) (h:nat) (l:nat{l <= h}) (a:expr) : expr =
  App { decl_name = "extract"; domain = [bv w]; range = bv (h - l + 1);
        interp = Some BV.op_extract; int_params = [w; h; l] } [a]

let zero_extend (w:pos) (k:nat) (a:expr) : expr =
  App { decl_name = "zero_extend"; domain = [bv w]; range = bv (w + k);
        interp = Some BV.op_zero_extend; int_params = [w; k] } [a]

let add (w:pos) (a b:expr) : expr = BV.binary w BV.op_add a b
let mul (w:pos) (a b:expr) : expr = BV.binary w BV.op_mul a b

let compare (name:string) (op:decl_kind) (w:pos) (a b:expr) : expr =
  App { decl_name = name; domain = [bv w; bv w]; range = bool_sort; interp = Some op; int_params = [w] } [a; b]

let ule (w:pos) (a b:expr) : expr = compare "bvule" BV.op_ule w a b
let ult (w:pos) (a b:expr) : expr = compare "bvult" BV.op_ult w a b

(* The connectives as the native bridge marshals them: Z3's name, the kind tag from
   `Z3NativeProof.operator_tag`, the argument sorts as domain, no parameters. *)
let disj (args:list expr) : expr = App (C.or_decl (FStar.List.Tot.length args)) args
let conj (args:list expr) : expr = App (C.and_decl (FStar.List.Tot.length args)) args

(* The same names without a kind tag: an uninterpreted function named `or`, never a connective. *)
let untagged (name:string) (args:list expr) : expr =
  App { decl_name = name; domain = FStar.List.Tot.map get_sort args; range = bool_sort;
        interp = None; int_params = [] } args
let eq (a b:expr) : expr = mk_eq_expr a b

(* t = concat(0_30, x); s = 242 + t, as in egt-0160 (where x has 8 bits and t = concat(0_24, x)). *)
let t : expr = concat 30 2 (num 30 0) x
let s : expr = add 32 (num 32 242) t

let split (c:int) : expr =
  conj [eq (extract 32 31 10 s) (num 22 0); ule 10 (extract 32 9 0 s) (extract 32 9 0 (num 32 c))]

let low_bound (c:int) : expr =
  disj [ule 10 (add 10 (num 10 242) (concat 8 2 (num 8 0) x)) (num 10 c); false_expr]

let reassociated (c:int) : expr = eq (add 32 (add 32 (num 32 2) t) (num 32 1)) (add 32 (num 32 c) t)

(* The bound split rewrite, the two range lemmas, and the constant re-association rewrite. *)
let split_rewrite () : Lemma (E.equivalent (ule 32 s (num 32 547)) (split 547)) =
  assert_norm (E.equivalent (ule 32 s (num 32 547)) (split 547))

let high_bits_lemma () : Lemma (E.valid (eq (extract 32 31 10 s) (num 22 0))) =
  assert_norm (E.valid (eq (extract 32 31 10 s) (num 22 0)))

let low_bound_lemma () : Lemma (E.valid (low_bound 547)) =
  assert_norm (E.valid (low_bound 547))

let reassociation () : Lemma (E.valid (reassociated 3)) =
  assert_norm (E.valid (reassociated 3))

(* False for some value of the leaf: mutated numerals, a constant too large for the split, a wrong extract
   range, a sum that crosses 2^10, and the conclusion `false`. *)
let mutated () : Lemma (not (E.valid (reassociated 4)) /\ not (E.valid (low_bound 244))) =
  assert_norm (not (E.valid (reassociated 4)));
  assert_norm (not (E.valid (low_bound 244)))

let wrong_split () : Lemma (not (E.equivalent (ule 32 s (num 32 0x423)) (split 0x423))) =
  assert_norm (not (E.equivalent (ule 32 s (num 32 0x423)) (split 0x423)))

let wrong_range ()
  : Lemma (not (E.valid (eq (extract 32 31 7 s) (num 25 0))) /\
           not (E.valid (eq (extract 32 31 10 (add 32 (num 32 0x3fe) t)) (num 22 0))) /\
           not (E.valid false_expr))
  = assert_norm (not (E.valid (eq (extract 32 31 7 s) (num 25 0))));
    assert_norm (not (E.valid (eq (extract 32 31 10 (add 32 (num 32 0x3fe) t)) (num 22 0))));
    assert_norm (not (E.valid false_expr))

(* Carry: x + 1 wraps at x = 3 in 2 bits, not after zero extension to 3 bits. *)
let carry ()
  : Lemma (not (E.valid (ule 2 x (add 2 x (num 2 1)))) /\
           E.valid (ule 3 (zero_extend 2 1 x) (add 3 (zero_extend 2 1 x) (num 3 1))))
  = assert_norm (not (E.valid (ule 2 x (add 2 x (num 2 1)))));
    assert_norm (E.valid (ule 3 (zero_extend 2 1 x) (add 3 (zero_extend 2 1 x) (num 3 1))))

(* Unsigned comparisons with the top bit set. *)
let unsigned ()
  : Lemma (not (E.valid (ule 2 (num 2 2) x)) /\
           E.valid (disj [ult 2 x (num 2 2); mk_not_expr (ult 2 x (num 2 2))]))
  = assert_norm (not (E.valid (ule 2 (num 2 2) x)));
    assert_norm (E.valid (disj [ult 2 x (num 2 2); mk_not_expr (ult 2 x (num 2 2))]))

(* A repeated leaf takes one value; distinct leaves, including two reads of the same array and a closed
   uninterpreted constant, are independent and never folded to a value. *)
let repeated_leaf () : Lemma (E.valid (eq (add 2 x x) (concat 1 1 (extract 2 0 0 x) (num 1 0)))) =
  assert_norm (E.valid (eq (add 2 x x) (concat 1 1 (extract 2 0 0 x) (num 1 0))))

let distinct_leaves ()
  : Lemma (not (E.valid (eq x other)) /\ not (E.valid (ule 2 x other)) /\ not (E.valid (eq u (num 2 1))))
  = assert_norm (not (E.valid (eq x other)));
    assert_norm (not (E.valid (ule 2 x other)));
    assert_norm (not (E.valid (eq u (num 2 1))))

(* The leaf-width bound is tested before any assignment is enumerated: 12 bits pass, 13 bits do not, and
   a valid claim over 5 + 8 leaf bits stays unchecked. *)
let y8 : expr = constant (bv 8) "y"
let w4 : expr = constant (bv 4) "w"
let w5 : expr = constant (bv 5) "w"

let bound ()
  : Lemma (E.within_bits [(y8, 8); (w4, 4)] 0 /\ not (E.within_bits [(y8, 8); (w5, 5)] 0) /\
           not (E.valid (eq (concat 5 8 w5 y8) (add 13 (concat 5 8 w5 (num 8 0)) (concat 5 8 (num 5 0) y8)))))
  = assert_norm (E.within_bits [(y8, 8); (w4, 4)] 0);
    assert_norm (not (E.within_bits [(y8, 8); (w5, 5)] 0));
    assert_norm (not (E.valid (eq (concat 5 8 w5 y8) (add 13 (concat 5 8 w5 (num 8 0)) (concat 5 8 (num 5 0) y8)))))

(* Malformed declarations of the evaluated kinds are neither evaluated nor opaque leaves: a wrong extract
   range, a wrong bvadd width parameter, a ternary bvadd, a concat whose parameters disagree with its
   argument sorts, and a numeral out of range. Each is placed in a well-formed context of its declared
   width, so `m = m` below would hold if `m` were treated as a leaf. *)
let bad_extract : expr =
  App { decl_name = "extract"; domain = [bv 2]; range = bv 2;
        interp = Some BV.op_extract; int_params = [2; 0; 0] } [x]

let bad_add : expr =
  App { decl_name = "bvadd"; domain = [bv 2; bv 2]; range = bv 2;
        interp = Some BV.op_add; int_params = [1] } [num 2 1; x]

let ternary_add : expr =
  App { decl_name = "bvadd"; domain = [bv 2; bv 2; bv 2]; range = bv 2;
        interp = Some BV.op_add; int_params = [2] } [num 2 1; num 2 1; x]

let bad_concat : expr =
  App { decl_name = "concat"; domain = [bv 1; bv 2]; range = bv 4;
        interp = Some BV.op_concat; int_params = [2; 2] } [num 1 0; x]

let reflexive (w:pos) (m:expr) : expr = eq (add w m (num w 0)) (add w m (num w 0))

let well_formed_context () : Lemma (E.valid (reflexive 2 x)) =
  assert_norm (E.valid (reflexive 2 x))

let malformed ()
  : Lemma (not (E.valid (reflexive 2 bad_extract)) /\
           not (E.valid (reflexive 2 bad_add)) /\
           not (E.valid (reflexive 2 ternary_add)) /\
           not (E.valid (reflexive 4 bad_concat)) /\
           not (E.valid (reflexive 2 (num 2 4))))
  = assert_norm (not (E.valid (reflexive 2 bad_extract)));
    assert_norm (not (E.valid (reflexive 2 bad_add)));
    assert_norm (not (E.valid (reflexive 2 ternary_add)));
    assert_norm (not (E.valid (reflexive 4 bad_concat)));
    assert_norm (not (E.valid (reflexive 2 (num 2 4))))

(* Outside the fragment: a bvmul term is an opaque leaf; an opaque signed comparison (the native bridge
   leaves `bvsle` uninterpreted, named by its unique declaration name), a Boolean constant, a free
   variable and a binder are not evaluated, although each claim below is valid. *)
let bvsle (a b:expr) : expr =
  App { decl_name = "decl!1042:bvsle"; domain = [bv 2; bv 2]; range = bool_sort; interp = None;
        int_params = [] } [a; b]

let unsupported ()
  : Lemma (not (E.valid (eq (mul 2 (num 2 2) x) (add 2 x x))) /\
           not (E.valid (disj [bvsle x x; false_expr])) /\
           not (E.valid (disj [p; mk_not_expr p])) /\
           not (E.valid (eq (Var 0 (bv 2)) (Var 0 (bv 2)))) /\
           not (E.valid (Quantifier Forall_k [bv 2] bool_sort (eq (Var 0 (bv 2)) (Var 0 (bv 2))))))
  = assert_norm (not (E.valid (eq (mul 2 (num 2 2) x) (add 2 x x))));
    assert_norm (not (E.valid (disj [bvsle x x; false_expr])));
    assert_norm (not (E.valid (disj [p; mk_not_expr p])));
    assert_norm (not (E.valid (eq (Var 0 (bv 2)) (Var 0 (bv 2)))));
    assert_norm (not (E.valid (Quantifier Forall_k [bv 2] bool_sort (eq (Var 0 (bv 2)) (Var 0 (bv 2))))))

(* --- Canonical dispatch ------------------------------------------------------------------------------ *)

(* The connectives are dispatched on the typed canonical declarations of `Z3CanonicalOps`, never on a name.
   Each declaration below has the name of a connective but not its kind tag or shape. None of them can come
   from the native bridge (Z3 rejects user symbols `=`/`true` with builtin argument sorts, uninterpreted
   symbols are marshaled under their unique `decl!N:` name, and bit-vector tags only come with Z3's own
   names); they check that the evaluation follows the tag, the meaning the ground contracts give them.

   Clash 1: a declaration named `=` whose kind tag is `bvult`. Its tag makes it the unsigned comparison
   0 < 0, false in every model of the ground contracts, so it is never accepted as the equation 0 = 0. *)
let clash_decl : func_decl =
  { decl_name = "="; domain = [bv 2; bv 2]; range = bool_sort; interp = Some BV.op_ult; int_params = [2] }

let clash_app : expr = App clash_decl [num 2 0; num 2 0]

let clash_equality ()
  : Lemma (not (C.canonical_eq clash_decl) /\ not (E.valid clash_app) /\ E.valid (mk_not_expr clash_app))
  = assert_norm (not (C.canonical_eq clash_decl));
    assert_norm (not (E.valid clash_app));
    assert_norm (E.valid (mk_not_expr clash_app))

(* Clash 2: two declarations named `true` whose kind tag is the bit-vector numeral, of values 0 and 1. They
   are the numerals their parameters say, distinct, and not the Boolean constant. *)
let true_numeral (n:int) : expr =
  App { decl_name = "true"; domain = []; range = bv 1; interp = Some BV.op_numeral; int_params = [1; n] } []

let clash_true ()
  : Lemma (not (E.valid (true_numeral 1)) /\
           not (E.valid (eq (true_numeral 0) (true_numeral 1))) /\
           E.valid (mk_not_expr (eq (true_numeral 0) (true_numeral 1))) /\
           E.valid (eq (true_numeral 1) (num 1 1)))
  = assert_norm (not (E.valid (true_numeral 1)));
    assert_norm (not (E.valid (eq (true_numeral 0) (true_numeral 1))));
    assert_norm (E.valid (mk_not_expr (eq (true_numeral 0) (true_numeral 1))));
    assert_norm (E.valid (eq (true_numeral 1) (num 1 1)))

(* Malformed Boolean kinds fail closed: `true` with a parameter, `true` without a kind tag, an untagged
   `or`, `not` whose kind tag is the bit-vector `bvnot`, and an `=` between different sorts. The canonical
   ones are evaluated. *)
let bad_true : expr =
  App { decl_name = "true"; domain = []; range = bool_sort; interp = Some op_true; int_params = [5] } []

let untagged_true : expr =
  App { decl_name = "true"; domain = []; range = bool_sort; interp = None; int_params = [] } []

let bvnot_named_not (a:expr) : expr =
  App { decl_name = "not"; domain = [bool_sort]; range = bool_sort; interp = Some BV.op_not; int_params = [] } [a]

let mixed_eq : expr =
  App { decl_name = "="; domain = [bv 2; bv 1]; range = bool_sort; interp = Some op_eq; int_params = [] }
      [num 2 1; num 1 1]

let malformed_boolean ()
  : Lemma (not (E.valid bad_true) /\ not (E.valid untagged_true) /\
           not (E.valid (untagged "or" [ult 2 x (num 2 2); mk_not_expr (ult 2 x (num 2 2))])) /\
           not (E.valid (bvnot_named_not false_expr)) /\ not (E.valid mixed_eq) /\
           E.valid true_expr /\ E.valid (mk_not_expr false_expr) /\ not (E.valid (mk_not_expr true_expr)))
  = assert_norm (not (E.valid bad_true));
    assert_norm (not (E.valid untagged_true));
    assert_norm (not (E.valid (untagged "or" [ult 2 x (num 2 2); mk_not_expr (ult 2 x (num 2 2))])));
    assert_norm (not (E.valid (bvnot_named_not false_expr)));
    assert_norm (not (E.valid mixed_eq));
    assert_norm (E.valid true_expr);
    assert_norm (E.valid (mk_not_expr false_expr));
    assert_norm (not (E.valid (mk_not_expr true_expr)))

(* Reachable through both native views: user datatype accessors and constructors named like connectives,
   e.g. `(declare-datatypes ((T 0)) (((mk (|and| Bool) (|or| Bool) (|not| Bool)))))`, carry the datatype
   kind tags 200/202 and Z3's user name. They are not connectives: an accessor `and` applied to a
   constructor whose fields are all true is true by the datatype semantics, which this evaluation does not
   have, so the claim stays unchecked rather than being read as a conjunction. *)
let t_sort : sort = BaseSort "T"
let datatype_t : expr = constant t_sort "t"

let mk_constructor : func_decl =
  { decl_name = "mk"; domain = [bool_sort; bool_sort; bool_sort]; range = t_sort;
    interp = Some DT.op_constructor; int_params = [0; 1; 3] }

let accessor (name:string) (index:nat) : func_decl =
  { decl_name = name; domain = [t_sort]; range = bool_sort; interp = Some DT.op_accessor;
    int_params = [0; 1; index] }

let or_constructor : func_decl =
  { decl_name = "or"; domain = [bool_sort; bool_sort]; range = t_sort;
    interp = Some DT.op_constructor; int_params = [0; 2; 2] }

let all_true : expr = App mk_constructor [true_expr; true_expr; true_expr]

let datatype_names ()
  : Lemma (not (C.canonical_and (accessor "and" 0)) /\ not (C.canonical_or (accessor "or" 1)) /\
           not (C.canonical_not (accessor "not" 2)) /\ not (C.canonical_or or_constructor) /\
           not (E.valid (App (accessor "and" 0) [all_true])) /\
           not (E.valid (App (accessor "not" 2) [datatype_t])) /\
           not (E.valid (disj [App (accessor "and" 0) [datatype_t]; mk_not_expr (App (accessor "and" 0) [datatype_t])])) /\
           not (E.valid (eq (App or_constructor [true_expr; false_expr]) (App or_constructor [true_expr; false_expr]))))
  = assert_norm (not (C.canonical_and (accessor "and" 0)));
    assert_norm (not (C.canonical_or (accessor "or" 1)));
    assert_norm (not (C.canonical_not (accessor "not" 2)));
    assert_norm (not (C.canonical_or or_constructor));
    assert_norm (not (E.valid (App (accessor "and" 0) [all_true])));
    assert_norm (not (E.valid (App (accessor "not" 2) [datatype_t])));
    assert_norm (not (E.valid (disj [App (accessor "and" 0) [datatype_t]; mk_not_expr (App (accessor "and" 0) [datatype_t])])));
    assert_norm (not (E.valid (eq (App or_constructor [true_expr; false_expr]) (App or_constructor [true_expr; false_expr]))))

(* --- The standard models ----------------------------------------------------------------------------- *)

let rho0 : env value = fun _ -> VInt 0
let leaf0 : func_decl -> list value -> int = fun _ _ -> 0

(* A leaf function that reads the index of a `select`: the two reads `x` and `other` of `packet` get the
   values 241 mod 4 = 1 and 242 mod 4 = 2, `u` gets 0. *)
let by_index : func_decl -> list value -> int =
  fun _ vs -> match vs with [_; VSeq [_; k]] -> k | _ -> 0

(* The clash term is false in the standard model, as its tag says; an equation would be true. *)
let standard_clash () : Lemma (eval (SM.standard leaf0) clash_app rho0 == VBool false) =
  assert_norm (eval (SM.standard leaf0) clash_app rho0 == VBool false)

(* Opaque leaves are independent: claims rejected above are false in some standard model, and distinct
   reads of the same array take distinct values while a repeated read takes one. *)
let countermodels ()
  : Lemma (eval (SM.standard by_index) (eq x other) rho0 == VBool false /\
           eval (SM.standard by_index) (eq x x) rho0 == VBool true /\
           eval (SM.standard by_index) (ule 2 x other) rho0 == VBool true /\
           eval (SM.standard leaf0) (eq u (num 2 1)) rho0 == VBool false /\
           eval (SM.standard by_index) (ule 2 (num 2 2) x) rho0 == VBool false /\
           eval (SM.standard leaf0) (reassociated 4) rho0 == VBool false)
  = assert_norm (eval (SM.standard by_index) (eq x other) rho0 == VBool false);
    assert_norm (eval (SM.standard by_index) (eq x x) rho0 == VBool true);
    assert_norm (eval (SM.standard by_index) (ule 2 x other) rho0 == VBool true);
    assert_norm (eval (SM.standard leaf0) (eq u (num 2 1)) rho0 == VBool false);
    assert_norm (eval (SM.standard by_index) (ule 2 (num 2 2) x) rho0 == VBool false);
    assert_norm (eval (SM.standard leaf0) (reassociated 4) rho0 == VBool false)

(* An accepted clause is true in every standard model, whatever its opaque leaves are. *)
let accepted_standard (leaf:func_decl -> list value -> int) (rho:env value)
  : Lemma (lit_true (SM.standard leaf) rho (reassociated 3) /\
           lit_true (SM.standard leaf) rho (mk_not_expr clash_app))
  = reassociation ();
    clash_equality ();
    E.lemma_valid_standard (reassociated 3) leaf rho;
    E.lemma_valid_standard (mk_not_expr clash_app) leaf rho

(* The width decoder of the standard model. `BV<w>` decodes to `w` for every 1 <= w <= 4096
   (`SM.lemma_width`, checked once for all 4096 widths); width 4097, width 0, a leading zero, a bare `BV`,
   `Bool` and the native bridge's unique names of user sorts do not decode. The projection contract is
   therefore claimed only up to width 4096, the bound of every bit-vector recognizer. *)
let decoder ()
  : Lemma (SM.width_of_sort (bv 1) == Some 1 /\ SM.width_of_sort (bv 4096) == Some 4096 /\
           SM.width_of_sort (BV.bv_sort 4097) == None /\ SM.width_of_sort (BV.bv_sort 0) == None /\
           SM.width_of_sort (BaseSort "BV08") == None /\ SM.width_of_sort (BaseSort "BV") == None /\
           SM.width_of_sort bool_sort == None /\ SM.width_of_sort (BaseSort "sort!7:BV8") == None)
  = SM.lemma_width 1;
    SM.lemma_width 4096;
    assert_norm (SM.width_of_sort (BV.bv_sort 4097) == None);
    assert_norm (SM.width_of_sort (BV.bv_sort 0) == None);
    assert_norm (SM.width_of_sort (BaseSort "BV08") == None);
    assert_norm (SM.width_of_sort (BaseSort "BV") == None);
    assert_norm (SM.width_of_sort bool_sort == None);
    assert_norm (SM.width_of_sort (BaseSort "sort!7:BV8") == None)

(* At the boundary: an opaque constant of sort BV4096 takes the bit-vector value its leaf function gives
   it; one of sort BV4097 is outside the fragment and gets an integer of the opaque sorts. *)
let wide (w:pos) : func_decl = { decl_name = "wide"; domain = []; range = bv w; interp = None; int_params = [] }

let boundary_values ()
  : Lemma (SM.std_project 4096 (eval (SM.standard (fun _ _ -> 5)) (App (wide 4096) []) rho0) == 5 /\
           eval (SM.standard (fun _ _ -> 5)) (App (wide 4097) []) rho0 == VInt 5)
  = SM.lemma_opaque_constant (wide 4096) 4096 5 rho0;
    assert_norm (eval (SM.standard (fun _ _ -> 5)) (App (wide 4097) []) rho0 == VInt 5)

(* The standard interpretation computes the bit-vector operators, not a dummy value: `BV<w>` values are
   `VSeq [w; r]` with r in [0, 2^w). Division and remainder by zero follow SMT-LIB. The bitwise operators
   and the shifts go through `FStar.UInt`'s bit-vector sequences, which do not normalize here; they are
   covered by the general proof `SM.lemma_standard_model`. *)
let op1 (name:string) (op:decl_kind) (w:pos) (a:expr) : expr =
  App { decl_name = name; domain = [bv w]; range = bv w; interp = Some op; int_params = [w] } [a]

let op2 (name:string) (op:decl_kind) (w:pos) (a b:expr) : expr =
  App { decl_name = name; domain = [bv w; bv w]; range = bv w; interp = Some op; int_params = [w] } [a; b]

let mkbv (args:list expr) : expr =
  App { decl_name = "mkbv"; domain = FStar.List.Tot.map (fun _ -> bool_sort) args;
        range = BV.bv_sort (FStar.List.Tot.length args);
        interp = Some BV.op_mkbv; int_params = [FStar.List.Tot.length args] } args

let concat3 (a b c:expr) : expr =
  App { decl_name = "concat"; domain = [bv 1; bv 1; bv 1]; range = bv 3; interp = Some BV.op_concat;
        int_params = [1; 1; 1] } [a; b; c]

let nary_add (a b c:expr) : expr =
  App { decl_name = "bvadd"; domain = [bv 3; bv 3; bv 3]; range = bv 3; interp = Some BV.op_add;
        int_params = [3] } [a; b; c]

let standard_value (e:expr) : GTot value = eval (SM.standard leaf0) e rho0

let standard_operations ()
  : Lemma (standard_value (op2 "bvmul" BV.op_mul 3 (num 3 3) (num 3 5)) == VSeq [3; 7] /\
           standard_value (op2 "bvudiv" BV.op_udiv 3 (num 3 5) (num 3 0)) == VSeq [3; 7] /\
           standard_value (op2 "bvurem" BV.op_urem 3 (num 3 5) (num 3 0)) == VSeq [3; 5] /\
           standard_value (op2 "bvsub" BV.op_sub 3 (num 3 1) (num 3 2)) == VSeq [3; 7] /\
           standard_value (op1 "bvneg" BV.op_neg 3 (num 3 1)) == VSeq [3; 7] /\
           standard_value (add 3 (num 3 7) (num 3 2)) == VSeq [3; 1] /\
           standard_value (nary_add (num 3 7) (num 3 7) (num 3 3)) == VSeq [3; 1] /\
           standard_value (concat 1 2 (num 1 1) (num 2 2)) == VSeq [3; 6] /\
           standard_value (concat3 (num 1 1) (num 1 0) (num 1 1)) == VSeq [3; 5] /\
           standard_value (extract 3 2 1 (num 3 6)) == VSeq [2; 3] /\
           standard_value (zero_extend 2 1 (num 2 3)) == VSeq [3; 3] /\
           standard_value (mkbv [true_expr; false_expr; true_expr]) == VSeq [3; 5])
  = assert_norm (standard_value (op2 "bvmul" BV.op_mul 3 (num 3 3) (num 3 5)) == VSeq [3; 7]);
    assert_norm (standard_value (op2 "bvudiv" BV.op_udiv 3 (num 3 5) (num 3 0)) == VSeq [3; 7]);
    assert_norm (standard_value (op2 "bvurem" BV.op_urem 3 (num 3 5) (num 3 0)) == VSeq [3; 5]);
    assert_norm (standard_value (op2 "bvsub" BV.op_sub 3 (num 3 1) (num 3 2)) == VSeq [3; 7]);
    assert_norm (standard_value (op1 "bvneg" BV.op_neg 3 (num 3 1)) == VSeq [3; 7]);
    assert_norm (standard_value (add 3 (num 3 7) (num 3 2)) == VSeq [3; 1]);
    assert_norm (standard_value (nary_add (num 3 7) (num 3 7) (num 3 3)) == VSeq [3; 1]);
    assert_norm (standard_value (concat 1 2 (num 1 1) (num 2 2)) == VSeq [3; 6]);
    assert_norm (standard_value (concat3 (num 1 1) (num 1 0) (num 1 1)) == VSeq [3; 5]);
    assert_norm (standard_value (extract 3 2 1 (num 3 6)) == VSeq [2; 3]);
    assert_norm (standard_value (zero_extend 2 1 (num 2 3)) == VSeq [3; 3]);
    assert_norm (standard_value (mkbv [true_expr; false_expr; true_expr]) == VSeq [3; 5])

(* An opaque function is a function of the values of its arguments, not of their syntax: `g(2)` and
   `g(1 + 1)` are equal in every standard model, and the leaf function decides the rest. *)
let g (a:expr) : expr = App { decl_name = "g"; domain = [bv 2]; range = bv 2; interp = None; int_params = [] } [a]

let successor : func_decl -> list value -> int = fun _ vs -> match vs with [VSeq [_; k]] -> k + 1 | _ -> 0

let opaque_function ()
  : Lemma (eval (SM.standard successor) (g (num 2 2)) rho0 == VSeq [2; 3] /\
           eval (SM.standard successor) (g (add 2 (num 2 1) (num 2 1))) rho0 == VSeq [2; 3] /\
           eval (SM.standard successor) (g (num 2 3)) rho0 == VSeq [2; 0])
  = assert_norm (eval (SM.standard successor) (g (num 2 2)) rho0 == VSeq [2; 3]);
    assert_norm (eval (SM.standard successor) (g (add 2 (num 2 1) (num 2 1))) rho0 == VSeq [2; 3]);
    assert_norm (eval (SM.standard successor) (g (num 2 3)) rho0 == VSeq [2; 0])

(* The ground contracts constrain every one of their models, standard or not: the Boolean constants are
   fixed, distinct numerals are distinct values, and the unsigned comparison orders them. *)
let ult12 : BV.unsigned_comparison = { BV.width = 2; BV.relation = BV.op_ult; BV.lhs = num 2 1; BV.rhs = num 2 2 }

let ground_constraints (i:interpretation value) (project:pos -> value -> int) (rho:env value)
  : Lemma (requires SM.ground_model i project)
          (ensures eval i true_expr rho == VBool true /\ eval i false_expr rho == VBool false /\
                   project 2 (eval i (num 2 1) rho) == 1 /\ project 2 (eval i (num 2 2) rho) == 2 /\
                   ~(eval i (num 2 1) rho == eval i (num 2 2) rho) /\
                   eval i (ult 2 (num 2 1) (num 2 2)) rho == VBool true)
  = assert_norm (true_expr == App C.true_decl []);
    assert_norm (false_expr == App C.false_decl []);
    C.lemma_canonical_decls bool_sort 0;
    assert_norm (BV.numeral (num 2 1) == Some (2, 1));
    assert_norm (BV.numeral (num 2 2) == Some (2, 2));
    assert_norm (SM.closed_ground (ult 2 (num 2 1) (num 2 2)));
    assert_norm (BV.unsigned_parts (ult 2 (num 2 1) (num 2 2)) == Some ult12);
    SM.lemma_ground_unsigned i rho project (ult 2 (num 2 1) (num 2 2)) ult12

(* The bit-vector numerals named `true` of clash 2 are bit-vectors in every model of the ground contracts,
   never the Boolean constant: their projections are 0 and 1, so they are distinct values. *)
let ground_true_numerals (i:interpretation value) (project:pos -> value -> int) (rho:env value)
  : Lemma (requires SM.ground_model i project)
          (ensures project 1 (eval i (true_numeral 0) rho) == 0 /\ project 1 (eval i (true_numeral 1) rho) == 1 /\
                   ~(eval i (true_numeral 0) rho == eval i (true_numeral 1) rho))
  = assert_norm (BV.numeral (true_numeral 0) == Some (1, 0));
    assert_norm (BV.numeral (true_numeral 1) == Some (1, 1))
