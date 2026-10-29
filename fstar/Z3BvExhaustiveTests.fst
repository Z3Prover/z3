module Z3BvExhaustiveTests

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module BV = Z3BvLemma
module E = Z3BvExhaustive

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

let connective (name:string) (args:list expr) : expr =
  App { decl_name = name; domain = FStar.List.Tot.map get_sort args; range = bool_sort;
        interp = None; int_params = [] } args

let disj (args:list expr) : expr = connective "or" args
let conj (args:list expr) : expr = connective "and" args
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
