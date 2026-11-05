module Z3BvAddNormalizeTests

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module L = FStar.List.Tot
module BV = Z3BvLemma
module E = Z3BvAddNormalize

(* Closed instances of the modular normalization of bit-vector sums, decided by normalization. Atoms are
   uninterpreted constants and array reads of any width and nothing is enumerated, so widths 1, 8, 32 and
   66 are tested directly. The marshaled forms (the QF_ABV bvadd family of the pulse reports at 32 bits,
   4096-bit numerals, premises and rule labels, the size bound on large sums) are exercised on the
   extracted kernel by the `checked-bit-vector-sum-normalization` group of tools/test_native_bridge.ml. *)

let bv (w:pos) : sort = BV.bv_sort w
let num (w:pos) (n:int) : expr = BV.literal w n

let constant (s:sort) (name:string) : expr =
  App { decl_name = name; domain = []; range = s; interp = None; int_params = [] } []

let add (w:pos) (a b:expr) : expr = BV.binary w BV.op_add a b
let mul (w:pos) (a b:expr) : expr = BV.binary w BV.op_mul a b

(* A bvadd of any arity. *)
let nadd (w:pos) (args:list expr) : expr =
  App { decl_name = "bvadd"; domain = L.map (fun _ -> bv w) args; range = bv w;
        interp = Some BV.op_add; int_params = [w] } args

let t32 : expr = constant (bv 32) "t"
let u32 : expr = constant (bv 32) "u"
let t8 : expr = constant (bv 8) "t"
let t1 : expr = constant (bv 1) "t"
let t66 : expr = constant (bv 66) "t"

(* The shape of the pulse report family, bvadd(bvadd(c1, t), c2) = bvadd(c3, t) with c3 = c1 + c2 modulo
   2^w, at several widths, with sums that wrap: 4294967292 is -4 in 32 bits, 255 + 1 is 0 in 8 bits and
   2^66 - 1 is the largest 66-bit numeral. *)
let reassociation (w:pos) (t:expr) (c1 c2 c3:int) : bool =
  E.equivalent (add w (add w (num w c1) t) (num w c2)) (add w (num w c3) t)

let widths ()
  : Lemma (reassociation 32 t32 2 1 3 /\ reassociation 8 t8 100 100 200 /\
           reassociation 1 t1 1 1 0 /\ reassociation 66 t66 5 7 12)
  = assert_norm (reassociation 32 t32 2 1 3);
    assert_norm (reassociation 8 t8 100 100 200);
    assert_norm (reassociation 1 t1 1 1 0);
    assert_norm (reassociation 66 t66 5 7 12)

let wrap ()
  : Lemma (reassociation 32 t32 4294967292 4294967292 4294967288 /\
           reassociation 8 t8 255 1 0 /\ reassociation 8 t8 255 255 254 /\
           reassociation 66 t66 73786976294838206463 73786976294838206463 73786976294838206462)
  = assert_norm (reassociation 32 t32 4294967292 4294967292 4294967288);
    assert_norm (reassociation 8 t8 255 1 0);
    assert_norm (reassociation 8 t8 255 255 254);
    assert_norm (reassociation 66 t66 73786976294838206463 73786976294838206463 73786976294838206462)

(* A numeral total that is 0 modulo 2^w cancels, so the other side may be the bare atom; a zero addend. *)
let cancellation ()
  : Lemma (E.equivalent (add 32 (add 32 (num 32 4294967292) t32) (num 32 4)) t32 /\
           E.equivalent t32 (add 32 (add 32 (num 32 4294967292) t32) (num 32 4)) /\
           E.equivalent (add 32 (add 32 (num 32 5) t32) (num 32 0)) (add 32 (num 32 5) t32) /\
           E.equivalent (add 8 (num 8 0) t8) t8)
  = assert_norm (E.equivalent (add 32 (add 32 (num 32 4294967292) t32) (num 32 4)) t32);
    assert_norm (E.equivalent t32 (add 32 (add 32 (num 32 4294967292) t32) (num 32 4)));
    assert_norm (E.equivalent (add 32 (add 32 (num 32 5) t32) (num 32 0)) (add 32 (num 32 5) t32));
    assert_norm (E.equivalent (add 8 (num 8 0) t8) t8)

(* Numerals only: both sides fold to the same residue. *)
let numerals ()
  : Lemma (E.equivalent (add 8 (num 8 200) (num 8 100)) (num 8 44) /\
           not (E.equivalent (add 8 (num 8 200) (num 8 100)) (num 8 45)))
  = assert_norm (E.equivalent (add 8 (num 8 200) (num 8 100)) (num 8 44));
    assert_norm (not (E.equivalent (add 8 (num 8 200) (num 8 100)) (num 8 45)))

(* The n-ary shapes of the pulse reports: a ternary inner sum, two inner sums into a ternary sum, and a
   numeral to the left of an outer sum with a nested ternary sum. The order of the atoms is kept. *)
let nary ()
  : Lemma (E.equivalent (add 32 (nadd 32 [num 32 7; t32; u32]) (num 32 9)) (nadd 32 [num 32 16; t32; u32]) /\
           E.equivalent (add 32 (add 32 (num 32 1) t32) (add 32 (num 32 2) u32)) (nadd 32 [num 32 3; t32; u32]) /\
           E.equivalent (add 32 (num 32 4) (nadd 32 [num 32 5; t32; u32])) (nadd 32 [num 32 9; t32; u32]) /\
           E.equivalent (nadd 32 [num 32 1; t32; num 32 2; u32; num 32 3]) (add 32 (num 32 6) (add 32 t32 u32)))
  = assert_norm (E.equivalent (add 32 (nadd 32 [num 32 7; t32; u32]) (num 32 9)) (nadd 32 [num 32 16; t32; u32]));
    assert_norm (E.equivalent (add 32 (add 32 (num 32 1) t32) (add 32 (num 32 2) u32)) (nadd 32 [num 32 3; t32; u32]));
    assert_norm (E.equivalent (add 32 (num 32 4) (nadd 32 [num 32 5; t32; u32])) (nadd 32 [num 32 9; t32; u32]));
    assert_norm (E.equivalent (nadd 32 [num 32 1; t32; num 32 2; u32; num 32 3]) (add 32 (num 32 6) (add 32 t32 u32)))

(* An atom is any closed term of sort BV<w>: an uninterpreted constant, a read of an array, a bvmul. A
   repeated atom is the same atom. *)
let packet : expr = constant (ArraySort [bv 32] (bv 8)) "packet"

let select (a i:expr) : expr =
  App { decl_name = "select"; domain = [get_sort a; get_sort i]; range = bv 8;
        interp = Some op_select; int_params = [] } [a; i]

let x : expr = select packet (num 32 241)
let other : expr = select packet (num 32 242)

let atoms ()
  : Lemma (E.equivalent (add 8 (add 8 (num 8 2) x) (num 8 1)) (add 8 (num 8 3) x) /\
           E.equivalent (add 32 (add 32 (num 32 4) (mul 32 (num 32 2) t32)) (num 32 1))
                        (add 32 (num 32 5) (mul 32 (num 32 2) t32)) /\
           E.equivalent (add 8 (add 8 (num 8 1) x) x) (nadd 8 [num 8 1; x; x]) /\
           E.equivalent (add 8 x x) (add 8 x x))
  = assert_norm (E.equivalent (add 8 (add 8 (num 8 2) x) (num 8 1)) (add 8 (num 8 3) x));
    assert_norm (E.equivalent (add 32 (add 32 (num 32 4) (mul 32 (num 32 2) t32)) (num 32 1))
                              (add 32 (num 32 5) (mul 32 (num 32 2) t32)));
    assert_norm (E.equivalent (add 8 (add 8 (num 8 1) x) x) (nadd 8 [num 8 1; x; x]));
    assert_norm (E.equivalent (add 8 x x) (add 8 x x))

(* A wrong numeral total, a dropped, extra, replaced or reordered atom, and the second occurrence of an atom
   merged into a product are not certified. The reordered and merged sums are valid, but stay pending. *)
let wrong_total ()
  : Lemma (not (reassociation 32 t32 2 1 4) /\ not (reassociation 8 t8 100 100 199) /\
           not (reassociation 66 t66 5 7 13) /\ not (reassociation 8 t8 255 1 1) /\
           not (E.equivalent (add 32 (num 32 3) (num 32 1)) (add 32 (num 32 3) t32)))
  = assert_norm (not (reassociation 32 t32 2 1 4));
    assert_norm (not (reassociation 8 t8 100 100 199));
    assert_norm (not (reassociation 66 t66 5 7 13));
    assert_norm (not (reassociation 8 t8 255 1 1));
    assert_norm (not (E.equivalent (add 32 (num 32 3) (num 32 1)) (add 32 (num 32 3) t32)))

let wrong_atoms ()
  : Lemma (not (E.equivalent (add 32 (add 32 (num 32 1) t32) (num 32 2)) (num 32 3)) /\
           not (E.equivalent (add 32 (add 32 (num 32 1) t32) u32) (add 32 (num 32 1) t32)) /\
           not (E.equivalent (add 32 (add 32 (num 32 1) t32) (num 32 2)) (add 32 (num 32 3) u32)) /\
           not (E.equivalent (add 32 (add 32 (num 32 1) t32) u32) (nadd 32 [num 32 1; u32; t32])) /\
           not (E.equivalent (add 8 (add 8 (num 8 2) x) (num 8 1)) (add 8 (num 8 3) other)) /\
           not (E.equivalent (add 32 (add 32 (num 32 2) t32) t32) (add 32 (num 32 2) (mul 32 (num 32 2) t32))))
  = assert_norm (not (E.equivalent (add 32 (add 32 (num 32 1) t32) (num 32 2)) (num 32 3)));
    assert_norm (not (E.equivalent (add 32 (add 32 (num 32 1) t32) u32) (add 32 (num 32 1) t32)));
    assert_norm (not (E.equivalent (add 32 (add 32 (num 32 1) t32) (num 32 2)) (add 32 (num 32 3) u32)));
    assert_norm (not (E.equivalent (add 32 (add 32 (num 32 1) t32) u32) (nadd 32 [num 32 1; u32; t32])));
    assert_norm (not (E.equivalent (add 8 (add 8 (num 8 2) x) (num 8 1)) (add 8 (num 8 3) other)));
    assert_norm (not (E.equivalent (add 32 (add 32 (num 32 2) t32) t32) (add 32 (num 32 2) (mul 32 (num 32 2) t32))))

(* Atoms are identified by their whole declaration, not by a printed name: constants whose names differ only
   by a quote or a space, or of another width, are other atoms, and two opaque sides are not related. *)
let same_name ()
  : Lemma (not (E.equivalent (add 32 (add 32 (num 32 1) t32) (num 32 2)) (add 32 (num 32 3) (constant (bv 32) "t'"))) /\
           not (E.equivalent (add 8 (num 8 1) t8) (add 8 (num 8 1) (constant (bv 8) "t "))) /\
           not (E.equivalent t32 u32) /\ not (E.equivalent (mul 32 t32 u32) (mul 32 u32 t32)))
  = assert_norm (not (E.equivalent (add 32 (add 32 (num 32 1) t32) (num 32 2)) (add 32 (num 32 3) (constant (bv 32) "t'"))));
    assert_norm (not (E.equivalent (add 8 (num 8 1) t8) (add 8 (num 8 1) (constant (bv 8) "t "))));
    assert_norm (not (E.equivalent t32 u32));
    assert_norm (not (E.equivalent (mul 32 t32 u32) (mul 32 u32 t32)))

(* Widths and sorts: sides of different widths, an atom of another width or of the sort Int in a sum, and an
   argument whose sort disagrees with the declaration of its sum are not certified. *)
let int_const : expr = constant (BaseSort "Int") "t"

let sorts ()
  : Lemma (not (E.equivalent (add 32 (num 32 1) t32) (add 8 (num 8 1) t8)) /\
           not (E.equivalent (add 32 (num 32 1) t32) (add 32 (num 32 1) (constant (bv 8) "t"))) /\
           not (E.equivalent (add 32 (num 32 1) t32) (add 32 (num 32 1) int_const)) /\
           not (E.equivalent (add 8 (num 8 1) (num 8 2)) (add 8 (num 8 1) (num 32 2))))
  = assert_norm (not (E.equivalent (add 32 (num 32 1) t32) (add 8 (num 8 1) t8)));
    assert_norm (not (E.equivalent (add 32 (num 32 1) t32) (add 32 (num 32 1) (constant (bv 8) "t"))));
    assert_norm (not (E.equivalent (add 32 (num 32 1) t32) (add 32 (num 32 1) int_const)));
    assert_norm (not (E.equivalent (add 8 (num 8 1) (num 8 2)) (add 8 (num 8 1) (num 32 2))))

(* Malformed declarations of the kinds read here are neither read nor atoms: a numeral outside [0, 2^w)
   (also a negative one) or whose range disagrees with its parameter, a bvadd with another width parameter,
   with one argument, with a domain that disagrees with its arguments, and one of width 4097. Each is placed
   as the same summand on both sides, so the claim `m + 0 = m + 0` would hold if `m` were an atom. *)
let numeral_decl (range:sort) (params:list int) : expr =
  App { decl_name = "bv"; domain = []; range = range; interp = Some BV.op_numeral; int_params = params } []

let reflexive (w:pos) (m:expr) : bool = E.equivalent (add w m (num w 0)) (add w m (num w 0))

let bad_add_width : expr =
  App { decl_name = "bvadd"; domain = [bv 8; bv 8]; range = bv 8; interp = Some BV.op_add;
        int_params = [4] } [num 8 1; t8]

let unary_add : expr =
  App { decl_name = "bvadd"; domain = [bv 8]; range = bv 8; interp = Some BV.op_add;
        int_params = [8] } [t8]

let bad_domain_add : expr =
  App { decl_name = "bvadd"; domain = [bv 8; bv 4]; range = bv 8; interp = Some BV.op_add;
        int_params = [8] } [num 8 1; t8]

let well_formed_context () : Lemma (reflexive 8 t8) = assert_norm (reflexive 8 t8)

let malformed ()
  : Lemma (not (reflexive 8 (numeral_decl (bv 8) [8; 256])) /\
           not (reflexive 8 (numeral_decl (bv 8) [8; -1])) /\
           not (reflexive 8 (numeral_decl (bv 4) [8; 1])) /\
           not (reflexive 8 bad_add_width) /\ not (reflexive 8 unary_add) /\ not (reflexive 8 bad_domain_add) /\
           not (E.equivalent (add 4097 (num 4097 1) (constant (bv 4097) "t")) (add 4097 (num 4097 1) (constant (bv 4097) "t"))))
  = assert_norm (not (reflexive 8 (numeral_decl (bv 8) [8; 256])));
    assert_norm (not (reflexive 8 (numeral_decl (bv 8) [8; -1])));
    assert_norm (not (reflexive 8 (numeral_decl (bv 4) [8; 1])));
    assert_norm (not (reflexive 8 bad_add_width));
    assert_norm (not (reflexive 8 unary_add));
    assert_norm (not (reflexive 8 bad_domain_add));
    assert_norm (not (E.equivalent (add 4097 (num 4097 1) (constant (bv 4097) "t")) (add 4097 (num 4097 1) (constant (bv 4097) "t"))))

(* Open terms: a free variable is not certified. *)
let open_terms ()
  : Lemma (not (E.equivalent (add 8 (add 8 (num 8 2) (Var 0 (bv 8))) (num 8 1)) (add 8 (num 8 3) (Var 0 (bv 8)))))
  = assert_norm (not (E.equivalent (add 8 (add 8 (num 8 2) (Var 0 (bv 8))) (num 8 1)) (add 8 (num 8 3) (Var 0 (bv 8)))))

(* The size bound is tested first: a sum whose tree has more than `max_nodes` occurrences is not certified
   although both sides are the same sum, and a smaller one is. *)
let rec chain (w:pos) (n:nat) (a:expr) : Tot expr (decreases n) =
  if n = 0 then a else add w (num w 1) (chain w (n - 1) a)

let budget ()
  : Lemma (E.equivalent (chain 8 3 t8) (add 8 (num 8 3) t8) /\
           not (E.equivalent (chain 8 300 t8) (chain 8 300 t8)))
  = assert_norm (E.equivalent (chain 8 3 t8) (add 8 (num 8 3) t8));
    assert_norm (not (E.equivalent (chain 8 300 t8) (chain 8 300 t8)))
