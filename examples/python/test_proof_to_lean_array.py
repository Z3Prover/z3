############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for the array slice of the Lean reconstruction: arrays over
# uninterpreted sorts, Int, and Real (elements also Bool), constant arrays
# over Int and Real indices, functions into arrays, and nested arrays,
# certified through the sat.smt clause log.
# An array is a function _m.U -> _m.U (array constants are the family
# _m.arrs), select is _select, store the classical update _store, and the
# array solver's extensionality witness (_ array-ext 0) is _array_diff, an
# index where two different arrays differ. The array solver's axiom
# instances (array hints) are proved by grind with the facts _store_apply
# and _array_ext instantiated per lemma. Validation without Lean, and
# end-to-end checks that need the z3 executable and the pinned Lean
# toolchain.
############################################
import copy
from pathlib import Path
import random
import re
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

import z3

_EXAMPLES = Path(__file__).resolve().parent
sys.path.insert(0, str(_EXAMPLES))
import proof_certificate
import proof_clause_log
import lean_test_support
import proof_to_lean
from test_proof_to_lean_lia import _STANDARD_AXIOMS, _hints, _z3_available

_DECLARATIONS = """(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a () (Array Index Element))
(declare-fun b () (Array Index Element))
(declare-fun i () Index)
(declare-fun j () Index)
(declare-fun e () Element)
(declare-fun f () Element)
"""

# Documented QF_AX inputs, each refuted by a different array axiom.
ARRAY_INPUTS = {
    # Read over write at the written index: the store axiom
    # (= (select (store a i e) i) e), which the array solver propagates.
    # (Z3's rewriter would simplify a read of the store term itself.)
    "read_own_write": "(set-logic QF_AX)\n" + _DECLARATIONS + """(assert (= b (store a i e)))
(assert (= (select b i) f))
(assert (not (= e f)))
(check-sat)
""",
    # Read over write at another index: i = j or the read sees a.
    "read_other_index": "(set-logic QF_AX)\n" + _DECLARATIONS + """(assert (not (= i j)))
(assert (= b (store a i e)))
(assert (not (= (select b j) (select a j))))
(check-sat)
""",
    # Writes at two different indices commute: extensionality (the array-ext
    # witness) and select over store at both indices.
    "store_commutes": "(set-logic QF_AX)\n" + _DECLARATIONS + """(assert (not (= i j)))
(assert (not (= (store (store a i e) j f) (store (store a j f) i e))))
(check-sat)
""",
    # Writing back what was read leaves the array unchanged: extensionality.
    "write_back_read": "(set-logic QF_AX)\n" + _DECLARATIONS + """(assert (= e (select a i)))
(assert (not (= (store a i e) a)))
(check-sat)
""",
    # Two arrays equal after the same write differ at most at that index.
    "store_injective_elsewhere": "(set-logic QF_AX)\n" + _DECLARATIONS + """(assert (= (store a i e) (store b i e)))
(assert (not (= i j)))
(assert (not (= (select a j) (select b j))))
(check-sat)
""",
    # An ite over arrays, and an uninterpreted function over the elements.
    "array_ite_and_function": "(set-logic QF_AUF)\n" + _DECLARATIONS + """(declare-fun g (Element) Element)
(declare-fun p () Bool)
(assert (= (select a i) e))
(assert (= (select b i) e))
(assert (not (= (g (select (ite p a b) i)) (g e))))
(check-sat)
""",
    # Two array sorts over the same index sort.
    "two_array_sorts": "(set-logic QF_AX)\n" + _DECLARATIONS + """(declare-sort Key 0)
(declare-fun c () (Array Index Key))
(declare-fun k () Key)
(assert (= (select (store c i k) j) (select c j)))
(assert (= (select (store a i e) j) f))
(assert (= i j))
(assert (not (= (select a i) f)))
(assert (not (= (select (store c j k) i) k)))
(check-sat)
""",
    # A predicate over arrays (injected into the carrier by _m.arrs_inj):
    # Z3 proves it by a th-lemma cnf step, not a rewrite, whose lemma needs
    # the store identity _store_select.
    "predicate_over_arrays": "(set-logic QF_AUF)\n" + _DECLARATIONS + """(declare-fun p ((Array Index Element)) Bool)
(assert (p a))
(assert (not (p (store a i (select a i)))))
(check-sat)
""",
    # Arrays next to integer arithmetic over an element function (qf_uflia).
    "arrays_with_integer_weights": "(set-logic QF_AUFLIA)\n" + _DECLARATIONS + """(declare-fun w (Element) Int)
(assert (= (select (store a i e) j) f))
(assert (= i j))
(assert (> (w f) (+ (w e) 2)))
(check-sat)
""",
    # The smtlib-sample QF_AX family storeinv (Armando, Bonacina, Ranise,
    # Schulz, PDPAR'05), z3test storeinv_t2_np_nf_ai_00001_001: swapping
    # one entry between two arrays twice gives arrays equal to each other
    # only if the originals were.
    "storeinv_t2_00001": """(set-logic QF_AX)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a1 () (Array Index Element))
(declare-fun a2 () (Array Index Element))
(declare-fun i1 () Index)
(assert (= (store a2 i1 (select a1 i1)) (store a1 i1 (select a2 i1))))
(assert (not (= a1 a2)))
(check-sat)
""",
    # z3test swap_t1_np_nf_ai_00006_006 (same family): a sequence of swaps
    # through two paths ends in the same array.
    "swap_t1_00006_006": """(set-logic QF_AX)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a1 () (Array Index Element))
(declare-fun i0 () Index)
(declare-fun i1 () Index)
(declare-fun i3 () Index)
(declare-fun i4 () Index)
(declare-fun i5 () Index)
(assert (let ((?v_0 (select a1 i1))) (let ((?v_1 (store (store a1 i1 ?v_0) i1 ?v_0))) (let ((?v_2 (store (store ?v_1 i3 (select ?v_1 i5)) i5 (select ?v_1 i3)))) (let ((?v_3 (store (store ?v_2 i5 (select ?v_2 i0)) i0 (select ?v_2 i5)))) (let ((?v_6 (select ?v_3 i1)) (?v_7 (select ?v_3 i5))) (let ((?v_4 (store (store ?v_3 i1 ?v_7) i5 ?v_6))) (let ((?v_5 (store (store ?v_4 i5 (select ?v_4 i1)) i1 (select ?v_4 i5))) (?v_8 (store (store ?v_3 i5 ?v_6) i1 ?v_7))) (let ((?v_9 (store (store ?v_8 i5 (select ?v_8 i1)) i1 (select ?v_8 i5)))) (not (= (store (store ?v_5 i4 (select ?v_5 i5)) i5 (select ?v_5 i4)) (store (store ?v_9 i5 (select ?v_9 i4)) i4 (select ?v_9 i5)))))))))))))
(check-sat)
""",
}
# Arrays over Int and Real (QF_ALIA, QF_AUFLIA): Int and Real index and
# element sorts are Int and Rat in Lean, so reads of Int arrays are atoms of
# the linear forms and indices are arithmetic terms.
_INT_ARRAYS = """(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
"""
ARITHMETIC_ARRAY_INPUTS = {
    # Read over write at another index, then a Farkas step over the reads.
    "int_read_other_index": "(set-logic QF_ALIA)\n" + _INT_ARRAYS + """(assert (= b (store a i 5)))
(assert (> (select b j) (+ (select a j) 2)))
(assert (not (= i j)))
(check-sat)
""",
    # Read over write at an index equal by arithmetic, not syntactically.
    "int_index_arithmetic": "(set-logic QF_ALIA)\n" + _INT_ARRAYS + """(assert (= j (+ i 1)))
(assert (< (select (store a (+ i 1) 7) j) 7))
(check-sat)
""",
    # Writes at two different Int indices commute: an extensionality witness
    # over Int, chosen with Lean's own inhabitant of Int.
    "int_store_commutes": "(set-logic QF_ALIA)\n" + _INT_ARRAYS + """(assert (< i j))
(assert (not (= (store (store a i 1) j 2) (store (store a j 2) i 1))))
(check-sat)
""",
    # Real indices and elements (qf_uflra).
    "real_read_own_write": """(set-logic QF_AUFLRA)
(declare-fun r () (Array Real Real))
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= y (* 2.0 x)))
(assert (> (select (store r (+ x x) 1.5) y) 2.0))
(check-sat)
""",
    # Int indices into an uninterpreted element sort, and an uninterpreted
    # index sort into Int elements, next to each other.
    "mixed_index_and_element_sorts": "(set-logic QF_AUFLIA)\n" + _DECLARATIONS + """(declare-fun c () (Array Int Element))
(declare-fun w () (Array Index Int))
(declare-fun k () Int)
(declare-fun m () Int)
(assert (= (select (store c k e) m) f))
(assert (<= m k))
(assert (>= m k))
(assert (= i j))
(assert (or (not (= e f)) (> (select w i) (select w j))))
(check-sat)
""",
    # Int indices into Real elements (qf_uflira).
    "int_indices_real_elements": """(set-logic QF_AUFLIRA)
(declare-fun r () (Array Int Real))
(declare-fun n () Int)
(assert (>= (select r n) 0.5))
(assert (<= (+ (select r n) (select (store r (+ n 1) 0.0) n)) 0.75))
(check-sat)
""",
    # A function over arrays: equal arrays have equal images.
    "function_over_arrays": "(set-logic QF_AUFLIA)\n" + _INT_ARRAYS + """(declare-fun sk ((Array Int Int) (Array Int Int)) Int)
(assert (= b (store a i (select a i))))
(assert (not (= (sk a b) (sk a a))))
(check-sat)
""",
    # A predicate over an uninterpreted and an Int array: each Lean array
    # type has its own injection, and the cnf lemma needs _store_select.
    "predicate_over_two_array_types": "(set-logic QF_AUFLIA)\n" + _DECLARATIONS + """(declare-fun c () (Array Int Int))
(declare-fun p ((Array Index Element) (Array Int Int)) Bool)
(declare-fun n () Int)
(assert (p a c))
(assert (not (p (store a i (select a i)) (store c n (select c n)))))
(check-sat)
""",
    # A predicate over an overwritten Int array: the cnf lemma needs
    # _store_store.
    "predicate_over_overwritten_array": "(set-logic QF_AUFLIA)\n" + _INT_ARRAYS + """(declare-fun p ((Array Int Int)) Bool)
(assert (p (store a i 3)))
(assert (not (p (store (store a i 2) i 3))))
(check-sat)
""",
    # z3test regressions/smt2/z3.20.smt2: a store that leaves its array
    # unchanged writes the value already there.
    "z3_20": """(set-option :auto-config true)
(set-option :produce-models true)

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const a1 (Array Int Int))
(declare-const a2 (Array Int Int))
(declare-const a3 (Array Int Int))
(assert (= (select a1 x) x))
(assert (= (store a1 x y) a1))
(assert (not (= x y)))
(check-sat)
""",
    # The smtlib-sample QF_AUFLIA family swap (Armando, Bonacina, Ranise,
    # Schulz, PDPAR'05), z3test swap_t1_pp_sf_ai_00003_002: sk is the
    # benchmark's extensionality Skolem function, an Int function over two
    # arrays.
    "swap_t1_pp_00003_002": """(set-logic QF_AUFLIA)
(declare-fun a_207 () (Array Int Int))
(declare-fun a_208 () (Array Int Int))
(declare-fun a_210 () (Array Int Int))
(declare-fun a_212 () (Array Int Int))
(declare-fun a_214 () (Array Int Int))
(declare-fun a_215 () (Array Int Int))
(declare-fun a_216 () (Array Int Int))
(declare-fun a_217 () (Array Int Int))
(declare-fun a_219 () (Array Int Int))
(declare-fun a_220 () (Array Int Int))
(declare-fun e_206 () Int)
(declare-fun e_209 () Int)
(declare-fun e_211 () Int)
(declare-fun e_213 () Int)
(declare-fun e_218 () Int)
(declare-fun e_222 () Int)
(declare-fun e_223 () Int)
(declare-fun i_221 () Int)
(declare-fun a1 () (Array Int Int))
(declare-fun i0 () Int)
(declare-fun i2 () Int)
(declare-fun sk ((Array Int Int) (Array Int Int)) Int)
(assert (= a_207 (store a1 i0 e_206)))
(assert (= a_208 (store a_207 i0 e_206)))
(assert (= a_210 (store a_208 i0 e_209)))
(assert (= a_212 (store a_210 i2 e_211)))
(assert (= a_214 (store a_212 i2 e_213)))
(assert (= a_215 (store a_214 i2 e_213)))
(assert (= a_216 (store a_208 i2 e_211)))
(assert (= a_217 (store a_216 i0 e_209)))
(assert (= a_219 (store a_217 i2 e_218)))
(assert (= a_220 (store a_219 i2 e_218)))
(assert (= e_206 (select a1 i0)))
(assert (= e_209 (select a_208 i2)))
(assert (= e_211 (select a_208 i0)))
(assert (= e_213 (select a_212 i2)))
(assert (= e_218 (select a_217 i2)))
(assert (= e_222 (select a_215 i_221)))
(assert (= e_223 (select a_220 i_221)))
(assert (= i_221 (sk a_215 a_220)))
(assert (not (= e_222 e_223)))
(check-sat)
""",
    # Z3's rewriter skips the stores at numerals other than the read's,
    # (select (store (store a 1 5) 2 7) 3) is (select a 3), with no read of
    # the level in between in the certificate, so the read gets the
    # _store_apply fact of every skipped level (missing before 2026-11-05).
    "read_through_numeral_stores": """(set-logic QF_ALIA)
(declare-fun a () (Array Int Int))
(assert (not (= (select (store (store a 1 5) 2 7) 3) (select a 3))))
(check-sat)
""",
    # The skip stops at a store at the read's own numeral, whose read the
    # rewriter evaluates in the same step: (select (store (store a 3 5) 2 7)
    # 3) is 5, so that level gets its fact too (missing before 2026-11-05).
    "read_through_numeral_stores_to_own_index": """(set-logic QF_ALIA)
(declare-fun a () (Array Int Int))
(assert (not (= (select (store (store a 3 5) 2 7) 3) 5)))
(check-sat)
""",
    # Negative numerals are (- n) in the certificate; the rewriter skips the
    # stores at -1 and -2 in a read at 3 all the same.
    "read_through_negative_numeral_stores": """(set-logic QF_ALIA)
(declare-fun a () (Array Int Int))
(assert (not (= (select (store (store a (- 1) 5) (- 2) 7) 3) (select a 3))))
(check-sat)
""",
}
# Constant arrays over Int indices, ((as const (Array Int E)) v): the
# constant function _const_array. The array solver relates them to other
# arrays through default values, (default (const v)) = v and (default (store
# a i v)) = (default a), which are the theorems _default_const and
# _default_store of _default over Int (an infinite index type).
CONSTANT_ARRAY_INPUTS = {
    # z3test regressions/smt2/2549.smt2: two different constant arrays stay
    # different after the same store (the default-value axioms).
    "z3test_2549": """(declare-const A0 (Array Int Int))
(declare-const A1 (Array Int Int))
(assert (= A0 ((as const (Array Int Int)) 0)))
(assert (= A1 ((as const (Array Int Int)) 1)))
(assert (= (store A0 2 3) (store A1 2 3)))
(check-sat)
""",
    # A read of a constant array (_select_const) under a Farkas step.
    "read_constant": "(set-logic QF_ALIA)\n" + _INT_ARRAYS + """(assert (= a ((as const (Array Int Int)) 5)))
(assert (> (select a i) 5))
(check-sat)
""",
    # Z3's rewriter decides the equality of a store over one constant array
    # with another constant array by their default values: the rewrite step
    # gets the default facts of the arrays it compares.
    "store_over_constants": """(set-logic QF_ALIA)
(assert (= (store ((as const (Array Int Int)) 0) 1 1) ((as const (Array Int Int)) 1)))
(check-sat)
""",
    # z3test regressions/smt2/array.smt2, third query: the rewriter compares
    # two store chains over one constant array at the stored indices (the
    # rewrite step gets the reads at those indices).
    "z3test_array_q2": """(define-fun a () (Array Int Int) ((as const (Array Int Int)) 0))
(assert (= (store (store (store (store a 0 1) 1 2) 2 3) 0 0) (store (store (store a 0 1) 1 2) 2 3)))
(check-sat)
""",
    # Real elements (qf_uflira).
    "real_constants": """(set-logic QF_AUFLIRA)
(declare-fun r () (Array Int Real))
(declare-fun s () (Array Int Real))
(declare-fun x () Real)
(assert (= r (store ((as const (Array Int Real)) 0.5) 3 x)))
(assert (= s (store ((as const (Array Int Real)) 1.5) 3 x)))
(assert (= r s))
(check-sat)
""",
    # Uninterpreted elements over Int indices: two stores cannot turn one
    # constant array into another.
    "element_constants": """(set-logic QF_AUFLIA)
(declare-sort Element 0)
(declare-fun e () Element)
(declare-fun f () Element)
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun c () (Array Int Element))
(assert (= c (store (store ((as const (Array Int Element)) e) i f) j f)))
(assert (= c ((as const (Array Int Element)) f)))
(assert (not (= e f)))
(check-sat)
""",
    # Z3's rewriter evaluates a read of a store over a constant array,
    # (select (store (const 0) y 1) x), to (ite (= x y) 1 0); no read of the
    # constant array at x is in the certificate, so the read gets the
    # _store_apply and _select_const facts of every level down to the
    # constant (they were missing before 2026-11-04).
    "read_of_store_over_constant": """(set-logic QF_ALIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (select (store ((as const (Array Int Int)) 0) y 1) x) 1))
(assert (not (= x y)))
(check-sat)
""",
    # The rewriter decides the asserted equality by the default values (c =
    # d) and the exporter ties the result to the assertion by a cnf
    # th-lemma, which gets the default facts of the arrays it compares like
    # a rewrite (Lean rejected it before 2026-11-06).
    "constant_comparison_under_cnf": """(set-logic QF_ALIA)
(declare-const c Int)
(declare-const d Int)
(assert (= (store ((as const (Array Int Int)) c) 0 5) (store ((as const (Array Int Int)) d) 0 5)))
(assert (not (= c d)))
(check-sat)
""",
    # The rewriter evaluates (select (const c) k1) to c and folds (store
    # (const c) k0 c) into (const c) (_select_const and _const_store_self in
    # the rewrite's simp set; Lean rejected it before 2026-11-06).
    "store_of_a_constant_read": """(set-logic QF_ALIA)
(declare-const x Int)
(declare-const c Int)
(declare-const k0 Int)
(declare-const k1 Int)
(assert (not (= ((as const (Array Int Int)) x)
                (store ((as const (Array Int Int)) c) k0 (select ((as const (Array Int Int)) c) k1)))))
(assert (= x c))
(check-sat)
""",
    # The rewriter pushes a read into an ite of arrays and evaluates the
    # read of the constant-array branch; the read gets the facts of a read
    # of each store or constant-array branch (Lean rejected it before
    # 2026-11-06).
    "read_of_an_ite_over_a_constant": """(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const q Bool)
(declare-const k Int)
(declare-const c Int)
(declare-const x Int)
(assert (distinct x (select (ite q ((as const (Array Int Int)) c) a) k) 5))
(assert (or (= x c) (= x (select a k))))
(assert (or (= c 5) (= (select a k) 5)))
(assert (= x 7))
(check-sat)
""",
    # The rewriter decides a constant array's equality with a store into it
    # by the stored value, either way round (_const_eq_store and
    # _store_eq_const; Lean rejected both before 2026-11-06).
    "constant_equal_to_a_store": """(set-logic QF_ALIA)
(declare-const x Int)
(declare-const k Int)
(declare-const p Bool)
(assert (or p (= ((as const (Array Int Int)) x) (store ((as const (Array Int Int)) x) k 5))))
(assert (not p))
(assert (not (= x 5)))
(check-sat)
""",
    "store_equal_to_a_constant": """(set-logic QF_ALIA)
(declare-const x Int)
(declare-const k Int)
(declare-const p Bool)
(assert (or p (not (= (store ((as const (Array Int Int)) x) k 5) ((as const (Array Int Int)) x)))))
(assert (not p))
(assert (= x 5))
(check-sat)
""",
    # Store chains over two constant arrays: the rewriter decides their
    # equality by the values at the stored indices and the constants' values
    # (array_rewriter::mk_eq_core); its converse needs extensionality (the
    # _x facts of _constant_chain_extensionality). One store against a
    # constant array of another value, two chains of different lengths, and
    # a store against an ite of one constant array (the rewriter drops the
    # ite first; random sweep seeds 131 and 139).
    "store_over_another_constant": """(set-logic QF_ALIA)
(declare-const x Int)
(declare-const y Int)
(declare-const k Int)
(declare-const p Bool)
(assert (or p (not (= (store ((as const (Array Int Int)) x) k y) ((as const (Array Int Int)) y)))))
(assert (not p))
(assert (= x y))
(check-sat)
""",
    "store_chains_over_two_constants": """(set-logic QF_ALIA)
(declare-const x Int)
(declare-const y Int)
(declare-const u Int)
(declare-const i Int)
(declare-const j Int)
(declare-const p Bool)
(assert (or p (not (= (store (store ((as const (Array Int Int)) x) i u) j y) (store ((as const (Array Int Int)) y) i u)))))
(assert (not p))
(assert (not (= i j)))
(assert (= x y))
(check-sat)
""",
    "store_against_an_ite_of_one_constant": """(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(declare-const k Int)
(declare-const p Bool)
(declare-const q Bool)
(assert (or p (not (= (store ((as const (Array Int Int)) x) k y)
                      (ite q ((as const (Array Int Int)) y) ((as const (Array Int Int)) y))))))
(assert (not p))
(assert (= x y))
(check-sat)
""",
    # A store of (ite p x x) into a constant array of x: the rewriter drops
    # the ite, then folds the store (ite_self in the simp set; random sweep
    # seed 246).
    "store_of_an_ite_of_the_constant": """(set-logic ALL)
(declare-const x Int)
(declare-const k Int)
(declare-const j Int)
(declare-const p Bool)
(declare-const a (Array Int Int))
(assert (= (store ((as const (Array Int Int)) x) k (ite p x x)) a))
(assert (not (= (select a j) x)))
(check-sat)
""",
    # An ite of different store chains over constant arrays compared with
    # a chain: the solver logs the asserted equality as x0 = x1, the
    # outcome of comparing each branch with the other side, and the replay
    # ties the two by a rewrite step; its converse needs extensionality per
    # pair of branches (_ite_chain_extensionality). On one side, on both
    # sides, and nested. Lean rejected all three before 2026-11-07 (random
    # sweep seed 102 over Real indices and Int elements).
    "ite_of_chains_against_a_chain": """(set-logic QF_ALIA)
(declare-const p Bool)
(declare-const k0 Int)
(declare-const x0 Int)
(declare-const x1 Int)
(declare-const y Int)
(assert (= (ite p (store ((as const (Array Int Int)) x0) k0 x1) ((as const (Array Int Int)) x0))
           (store ((as const (Array Int Int)) x1) 1 x0)))
(assert (= ((as const (Array Int Int)) x0) (store ((as const (Array Int Int)) x1) 2 y)))
(assert (not (= y x1)))
(check-sat)
""",
    "ites_of_chains_on_both_sides": """(set-logic QF_ALIA)
(declare-const p Bool)
(declare-const q Bool)
(declare-const k0 Int)
(declare-const x0 Int)
(declare-const x1 Int)
(declare-const y Int)
(assert (= (ite p (store ((as const (Array Int Int)) x0) k0 x1) ((as const (Array Int Int)) x0))
           (ite q ((as const (Array Int Int)) x1) (store ((as const (Array Int Int)) x1) 1 x0))))
(assert (= ((as const (Array Int Int)) x0) (store ((as const (Array Int Int)) x1) 2 y)))
(assert (not (= y x1)))
(check-sat)
""",
    "nested_ites_of_chains": """(set-logic QF_ALIA)
(declare-const p Bool)
(declare-const q Bool)
(declare-const k0 Int)
(declare-const x0 Int)
(declare-const x1 Int)
(declare-const y Int)
(assert (= (ite p (store ((as const (Array Int Int)) x0) k0 x1)
                  (ite q ((as const (Array Int Int)) x0) (store ((as const (Array Int Int)) x0) 3 x1)))
           (store ((as const (Array Int Int)) x1) 1 x0)))
(assert (= ((as const (Array Int Int)) x0) (store ((as const (Array Int Int)) x1) 2 y)))
(assert (not (= y x1)))
(check-sat)
""",
    # Long store chains over two constant arrays compared: more read facts
    # than _COMPARISON_READS at every index stored into the sort, so only
    # the reads of the compared chains are stated (_chain_comparison_reads),
    # down to the right chain's constant at index 0. Lean rejected it
    # before 2026-11-06 (no read facts above the cap).
    "long_store_chains_over_two_constants": """(set-logic QF_ALIA)
(declare-const x Int)
(declare-const y Int)
(declare-const u0 Int)
(declare-const u1 Int)
(declare-const u2 Int)
(declare-const u3 Int)
(declare-const u4 Int)
(declare-const u5 Int)
(declare-const p Bool)
(assert (or p (not (= (store (store (store (store (store (store ((as const (Array Int Int)) x) 0 u0) 1 u1) 2 u2) 3 u3) 4 u4) 5 u5)
                      (store (store (store (store (store ((as const (Array Int Int)) y) 5 u5) 4 u4) 3 u3) 2 u2) 1 u1)))))
(assert (not p))
(assert (= x y))
(assert (= u0 y))
(check-sat)
""",
    # The clause (not (= 3 (select a k))) split from the distinct is tied
    # to the assertions through (= a (const 1)), which implies it: a cnf
    # lemma reading a, with no read of the constant array
    # (_compared_side_reads).
    "read_of_an_array_equated_to_a_constant": """(set-logic ALL)
(declare-const a (Array Int Int))
(declare-const k Int)
(assert (= a ((as const (Array Int Int)) 1)))
(assert (distinct 3 (select a k) (select a 0)))
(check-sat)
""",
    # Z3's congruence closure takes (_ array-ext 0) as commutative: the
    # witnesses of (= K (ite p K b)) and (= (ite p K b) K) are merged by a
    # comm claim of an euf hint (_array_diff_comm).
    "commuted_extensionality_witnesses": """(set-logic ALL)
(declare-const p Bool)
(declare-const a0 (Array Int Int))
(declare-const k0 Int)
(declare-const k1 Int)
(declare-const x0 Int)
(assert (not (= ((as const (Array Int Int)) x0) (ite p ((as const (Array Int Int)) x0) (store a0 k0 x0)))))
(assert (= a0 (store ((as const (Array Int Int)) x0) k1 x0)))
(check-sat)
""",
}
# Constant arrays over Real indices: the same encoding over Rat, whose
# default values rest on _rat_unbounded (no finite list exhausts Rat).
REAL_INDEX_CONSTANT_ARRAY_INPUTS = {
    # z3test 2549 over Real indices: the default-value axioms.
    "real_index_2549": """(declare-const A0 (Array Real Int))
(declare-const A1 (Array Real Int))
(assert (= A0 ((as const (Array Real Int)) 0)))
(assert (= A1 ((as const (Array Real Int)) 1)))
(assert (= (store A0 2.5 3) (store A1 2.5 3)))
(check-sat)
""",
    # A read of a constant array at a Real variable under a Farkas step.
    "real_index_read": """(declare-fun a () (Array Real Real))
(declare-fun x () Real)
(assert (= a ((as const (Array Real Real)) 5.0)))
(assert (> (select a x) 5.0))
(check-sat)
""",
    # z3test array.smt2's third query over Real indices: the rewrite compares
    # two store chains at the stored indices.
    "real_index_comparison": """(define-fun a () (Array Real Int) ((as const (Array Real Int)) 0))
(assert (= (store (store (store (store a 0.0 1) 0.5 2) 1.5 3) 0.0 0) (store (store (store a 0.0 1) 0.5 2) 1.5 3)))
(check-sat)
""",
    # Stores at Real terms into constant arrays of different Real defaults.
    "real_index_terms": """(declare-fun r () (Array Real Real))
(declare-fun s () (Array Real Real))
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= r (store ((as const (Array Real Real)) 0.5) x y)))
(assert (= s (store ((as const (Array Real Real)) 1.5) (+ x 1.0) y)))
(assert (= r s))
(check-sat)
""",
    # Uninterpreted elements over Real indices.
    "real_index_elements": """(declare-sort Element 0)
(declare-fun e () Element)
(declare-fun f () Element)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun c () (Array Real Element))
(assert (= c (store (store ((as const (Array Real Element)) e) x f) y f)))
(assert (= c ((as const (Array Real Element)) f)))
(assert (not (= e f)))
(check-sat)
""",
    # A store over a constant array compared with a constant array of
    # another value, over Real indices (_constant_chain_extensionality).
    "real_index_store_over_another_constant": """(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(declare-const k Real)
(declare-const p Bool)
(assert (or p (not (= (store ((as const (Array Real Int)) x) k y) ((as const (Array Real Int)) y)))))
(assert (not p))
(assert (= x y))
(check-sat)
""",
    # read_of_an_array_equated_to_a_constant over Rat, with a fractional
    # value (random_constant_array_instance seed 87 over Real sorts).
    "real_read_of_an_array_equated_to_a_constant": """(set-logic ALL)
(declare-const a (Array Real Real))
(declare-const k Real)
(assert (= a ((as const (Array Real Real)) (/ 1 2))))
(assert (distinct (/ 3 2) (select a k) (select a 0.0)))
(check-sat)
""",
    # The rewriter turns the read into (ite (= k0 k2) x1 x0), an Int ite
    # over a Real condition: the farkas lemma over it is an Int step
    # (random_constant_array_instance seed 103 over Real indices and Int
    # elements).
    "int_read_of_a_store_at_real_indices": """(set-logic ALL)
(declare-const k0 Real)
(declare-const k2 Real)
(declare-const x0 Int)
(declare-const x1 Int)
(assert (= (+ x0 1) (select (store ((as const (Array Real Int)) x0) k0 x1) k2)))
(assert (< x1 (+ x0 1)))
(check-sat)
""",
}
# Store identities whose indices or values are numeral expressions of one
# value: Z3's rewriter evaluates (/ 2 2) to 1 before it folds (store a (/ 2
# 2) (select a 1.0)) into a, so the rewrite steps need the values stated
# before simp applies the identities (_numeral_facts). Each failed Lean
# before.
NUMERAL_EXPRESSION_INPUTS = {
    # _store_select at (/ 2 2) and 1.0 (iteration 86's sweep, seed 35).
    "read_stored_back_at_a_fraction_of_one": """(set-logic ALL)
(declare-const a0 (Array Real Int))
(declare-const a1 (Array Real Int))
(declare-const p Bool)
(assert (or p (= a1 (store a0 (/ 2 2) (select a0 1.0)))))
(assert (not p))
(assert (not (= a1 a0)))
(check-sat)
""",
    # _store_store at (* 1 2) and (- 3 1).
    "store_over_a_store_at_products": """(set-logic ALL)
(declare-const a (Array Int Int))
(declare-const b (Array Int Int))
(declare-const v Int)
(declare-const w Int)
(declare-const p Bool)
(assert (or p (= b (store (store a (* 1 2) v) (- 3 1) w))))
(assert (not p))
(assert (not (= b (store a 2 w))))
(check-sat)
""",
    # _const_store_self with the value (+ 1 0) stored into (const 1).
    "constant_stored_into_its_constant_array": """(set-logic ALL)
(declare-const b (Array Int Int))
(declare-const p Bool)
(assert (or p (= b (store ((as const (Array Int Int)) 1) (+ 0 1) (+ 1 0)))))
(assert (not p))
(assert (not (= b ((as const (Array Int Int)) 1))))
(check-sat)
""",
    # Real sums and products of fractions, the stored value too.
    "fraction_sums_as_indices": """(set-logic ALL)
(declare-const a (Array Real Real))
(declare-const b (Array Real Real))
(declare-const x Real)
(declare-const p Bool)
(assert (or p (= b (store (store a (+ (/ 1 4) (/ 1 4)) x) 0.5 (- (* 3.0 (/ 1 3)) 1.0)))))
(assert (not p))
(assert (not (= b (store a (/ 1 2) 0.0))))
(check-sat)
""",
    # (- 0 1) against the certificate's own -1, (- 1).
    "negative_index_as_a_difference": """(set-logic ALL)
(declare-const a (Array Int Int))
(declare-const b (Array Int Int))
(declare-const p Bool)
(assert (or p (= b (store a (- 0 1) (select a (- 1))))))
(assert (not p))
(assert (not (= b a)))
(check-sat)
""",
    # (+ 1 1) on its own and inside (- (+ 1 1) 0): simp must rewrite the
    # outer expression first (pre-order), or the inner one's fact changes it.
    "shared_numeral_expression": """(set-logic ALL)
(declare-const a (Array Int Int))
(declare-const b (Array Int Int))
(declare-const v Int)
(declare-const w Int)
(declare-const p Bool)
(assert (or p (= b (store (store a (+ 1 1) v) (- (+ 1 1) 0) w))))
(assert (not p))
(assert (not (= b (store a 2 w))))
(check-sat)
""",
}
# Functions into arrays: one family per Lean array type (_m.arrs_funs,
# _m.arrs_ii_funs, ...) taking the argument list like _m.funs. Their
# applications stay folded in the array lemmas like stores, each stated equal
# to its body, so grind compares them by congruence on their arguments.
ARRAY_FUNCTION_INPUTS = {
    # Equal arguments give equal arrays: (h i) = (h j), so the store at i
    # overwrites (h j) at i.
    "function_into_arrays": """(set-logic QF_AUF)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun h (Index) (Array Index Element))
(declare-fun i () Index)
(declare-fun j () Index)
(declare-fun e () Element)
(assert (= (h i) (store (h j) i e)))
(assert (= i j))
(assert (not (= (select (h j) i) e)))
(check-sat)
""",
    # An Int function into Int arrays, under a Farkas step over the read.
    "int_function_into_arrays": """(set-logic QF_AUFLIA)
(declare-fun f (Int) (Array Int Int))
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (f x) (store (f y) 0 x)))
(assert (<= x y))
(assert (<= y x))
(assert (< (select (f y) 0) x))
(check-sat)
""",
    # A Real function into Real arrays (qf_uflra).
    "real_function_into_arrays": """(set-logic QF_AUFLRA)
(declare-fun r (Real) (Array Real Real))
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= (r x) (store (r y) x 1.0)))
(assert (= x y))
(assert (< (select (r x) y) 0.5))
(check-sat)
""",
    # Extensionality over an application: arrays equal after the same store
    # and equal at the stored index are equal (the witness of (h i) and a).
    "function_result_extensionality": """(set-logic QF_AUF)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun h (Index) (Array Index Element))
(declare-fun a () (Array Index Element))
(declare-fun i () Index)
(declare-fun j () Index)
(declare-fun e () Element)
(assert (= (store (h i) j e) (store a j e)))
(assert (= (select (h i) j) (select a j)))
(assert (not (= (h i) a)))
(check-sat)
""",
    # A function from arrays into arrays: the rewriter's store identity
    # (store a i (select a i)) = a under the function.
    "array_to_array_function": """(set-logic QF_AUF)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun g ((Array Index Element)) (Array Index Element))
(declare-fun a () (Array Index Element))
(declare-fun i () Index)
(assert (not (= (g (store a i (select a i))) (g a))))
(check-sat)
""",
    # An application equal to a constant array over Int indices with Real
    # elements (qf_uflira): _select_const through the application.
    "function_into_constant_arrays": """(set-logic QF_AUFLIRA)
(declare-fun c (Int) (Array Int Real))
(declare-fun k () Int)
(assert (= (c k) ((as const (Array Int Real)) 2.0)))
(assert (< (select (c k) 5) 1.0))
(check-sat)
""",
    # An ite over two applications.
    "ite_over_applications": """(set-logic QF_AUF)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun h (Index) (Array Index Element))
(declare-fun i () Index)
(declare-fun j () Index)
(declare-fun k () Index)
(declare-fun e () Element)
(declare-fun p () Bool)
(assert (= (select (h i) k) e))
(assert (= (select (h j) k) e))
(assert (not (= (select (ite p (h i) (h j)) k) e)))
(check-sat)
""",
    # A predicate over an application (its injection and its family).
    "predicate_over_application": """(set-logic QF_AUFLIA)
(declare-fun p ((Array Int Int)) Bool)
(declare-fun f (Int) (Array Int Int))
(declare-fun x () Int)
(declare-fun y () Int)
(assert (p (f x)))
(assert (<= x y))
(assert (<= y x))
(assert (not (p (f y))))
(check-sat)
""",
    # An application at a read of an application.
    "nested_applications": """(set-logic QF_AUFLIA)
(declare-fun f (Int) (Array Int Int))
(declare-fun x () Int)
(assert (= (select (f x) 0) x))
(assert (= (f (select (f x) 0)) (store (f x) 1 2)))
(assert (not (= (select (f x) 1) 2)))
(check-sat)
""",
    # In the style of z3test's fuzzsmt QF_AUFLIA regressions (t168, t170,
    # both satisfiable): a function from Int arrays into Int arrays applied
    # twice.
    "array_function_twice": """(set-logic QF_AUFLIA)
(declare-fun f1 ((Array Int Int)) (Array Int Int))
(declare-fun v3 () (Array Int Int))
(declare-fun v0 () Int)
(declare-fun v1 () Int)
(assert (= (f1 v3) (store v3 v0 v1)))
(assert (= (f1 (f1 v3)) (store (f1 v3) v0 (+ v1 1))))
(assert (= (select (f1 (f1 v3)) v0) (select v3 v0)))
(assert (= (select (f1 v3) v0) (select v3 v0)))
(check-sat)
""",
    # Two functions of the same signature share one family at distinct
    # indices; the roles are asymmetric, so swapping them changes the input.
    "two_functions_into_arrays": """(set-logic QF_AUFLIA)
(declare-fun f (Int) (Array Int Int))
(declare-fun g (Int) (Array Int Int))
(declare-fun x () Int)
(assert (= (f x) (store (g x) 0 1)))
(assert (not (= (select (f x) 0) 1)))
(check-sat)
""",
}
# Arrays with Bool elements (sets), (Array I Bool) over an uninterpreted,
# Int, or Real index sort: the Lean element type is Prop, so an array is a
# predicate I -> Prop (the families _m.arrs_ub, _m.arrs_ib, _m.arrs_rb), a
# read is a formula, (_select a i) : Prop, a store's value a formula, and
# the array axioms' (= v (select (store a i v) i)) Bool equalities (Iff).
# The definitions are generic in the element type, Prop included, so the
# array lemmas are proved by grind from the same facts as over other sorts.
BOOL_ELEMENT_INPUTS = {
    # The store axiom over a Boolean value: (select (store a i p) i) is p.
    "bool_read_own_write": """(set-logic QF_AX)
(declare-sort Index 0)
(declare-fun a () (Array Index Bool))
(declare-fun b () (Array Index Bool))
(declare-fun i () Index)
(declare-fun p () Bool)
(assert (= b (store a i p)))
(assert (select b i))
(assert (not p))
(check-sat)
""",
    # A set of Int: inserting at i leaves membership at j > i unchanged
    # (the read-over-write axiom at another index, then a Farkas step).
    "set_insert_elsewhere": """(set-logic QF_ALIA)
(declare-fun a () (Array Int Bool))
(declare-fun b () (Array Int Bool))
(declare-fun i () Int)
(declare-fun j () Int)
(assert (< i j))
(assert (= b (store a i true)))
(assert (not (= (select b j) (select a j))))
(check-sat)
""",
    # Inserting an element that is already a member leaves the set
    # unchanged: extensionality over a predicate (the array-ext witness).
    "bool_insert_member": """(set-logic QF_AX)
(declare-sort Index 0)
(declare-fun a () (Array Index Bool))
(declare-fun i () Index)
(assert (select a i))
(assert (not (= (store a i true) a)))
(check-sat)
""",
    # Writes of two Boolean values at different indices commute.
    "bool_store_commutes": """(set-logic QF_ALIA)
(declare-fun a () (Array Int Bool))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (not (= i j)))
(assert (not (= (store (store a i p) j q) (store (store a j q) i p))))
(check-sat)
""",
    # Membership after two inserts elsewhere: reads through a store chain.
    "bool_store_chain": """(set-logic QF_ALIA)
(declare-fun a () (Array Int Bool))
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (not (select a z)))
(assert (select (store (store a x true) y true) z))
(assert (not (= x z)))
(assert (not (= y z)))
(check-sat)
""",
    # The empty set has no member (_select_const at False).
    "empty_set": """(set-logic QF_ALIA)
(declare-fun x () Int)
(assert (select ((as const (Array Int Bool)) false) x))
(check-sat)
""",
    # A singleton {y} has no member x other than y: the rewriter evaluates
    # the read of the store over the constant array.
    "singleton_set": """(set-logic QF_ALIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (select (store ((as const (Array Int Bool)) false) y true) x))
(assert (not (= x y)))
(check-sat)
""",
    # No insert turns the full set into the empty one: Bool default values
    # (formulas, _default over I -> Prop).
    "full_is_not_empty": """(set-logic QF_ALIA)
(declare-fun a () (Array Int Bool))
(declare-fun b () (Array Int Bool))
(declare-fun x () Int)
(assert (= a ((as const (Array Int Bool)) true)))
(assert (= b (store a x false)))
(assert (= b ((as const (Array Int Bool)) false)))
(check-sat)
""",
    # A set of Real numbers (qf_uflra).
    "real_set": """(set-logic QF_AUFLRA)
(declare-fun s () (Array Real Bool))
(declare-fun t () (Array Real Bool))
(declare-fun x () Real)
(assert (= t (store s x false)))
(assert (select t (+ x 0.0)))
(check-sat)
""",
    # An ite over sets.
    "ite_over_sets": """(set-logic QF_ALIA)
(declare-fun s () (Array Int Bool))
(declare-fun t () (Array Int Bool))
(declare-fun c () Bool)
(declare-fun x () Int)
(assert (select s x))
(assert (select t x))
(assert (not (select (ite c s t) x)))
(check-sat)
""",
    # A membership as the Boolean argument of a function, and a stored
    # value that is an equality over the uninterpreted sort.
    "membership_as_argument": """(set-logic QF_AUF)
(declare-sort Index 0)
(declare-fun f (Bool) Index)
(declare-fun a () (Array Index Bool))
(declare-fun i () Index)
(declare-fun j () Index)
(assert (= a (store a i (= (f (select a j)) i))))
(assert (not (= (f (select a j)) i)))
(assert (select a i))
(check-sat)
""",
    # Memberships as conditions of Int ites: counting two members.
    "membership_count": """(set-logic QF_ALIA)
(declare-fun s () (Array Int Bool))
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= y (+ (ite (select s x) 1 0) (ite (select s (+ x 1)) 1 0))))
(assert (> y 1))
(assert (not (and (select s x) (select s (+ x 1)))))
(check-sat)
""",
    # A function into sets (the family _m.arrs_ub_funs).
    "function_into_sets": """(set-logic QF_AUF)
(declare-sort Index 0)
(declare-fun h (Index) (Array Index Bool))
(declare-fun i () Index)
(declare-fun j () Index)
(assert (= i j))
(assert (select (h i) j))
(assert (not (select (h j) i)))
(check-sat)
""",
    # A function over sets (the injection _m.arrs_ib_inj).
    "function_over_sets": """(set-logic QF_AUFLIA)
(declare-fun g ((Array Int Bool)) Int)
(declare-fun s () (Array Int Bool))
(declare-fun x () Int)
(assert (select s x))
(assert (not (= (g s) (g (store s x true)))))
(check-sat)
""",
    # Membership through inserts at other numerals: the rewriter skips the
    # stores at 1, 2, and 4 in a read at 3 (read_through_numeral_stores).
    "set_read_through_numeral_stores": """(set-logic QF_ALIA)
(declare-fun a () (Array Int Bool))
(assert (select (store (store (store a 1 true) 2 true) 4 false) 3))
(assert (not (select a 3)))
(check-sat)
""",
    # Membership after an insert at 3 and removals at 2 and 1: the skip
    # stops at the insert (read_through_numeral_stores_to_own_index).
    "set_read_through_numeral_stores_to_own_index": """(set-logic QF_ALIA)
(declare-fun a () (Array Int Bool))
(assert (not (select (store (store (store a 3 true) 2 false) 1 false) 3)))
(check-sat)
""",
}
# Boolean combinators over sets: maps of not, and, or, => ((_ map f) a b)
# and Z3's set operators (union, intersection, setminus, complement). Lean's
# _map1/_map2 apply a function over Prop pointwise; a read of one is the
# connective over the reads by rfl (the array solver's select-map axiom),
# stated per read down through nested maps and into the stores and constant
# arrays below them, since the rewriter evaluates such reads. The identities
# the euf solver and the rewriter apply to maps (commutativity, idempotence,
# double complement, maps of stores and of constant arrays) are theorems,
# instantiated per map node (proof_to_lean._map_identities).
SET_COMBINATOR_INPUTS = {
    # z3test regressions/smt2/t8.smt2: De Morgan over sets (extensionality,
    # then the select-map axiom through three nested maps).
    "z3test_t8": """(declare-const s1 (Array Int Bool))
(declare-const s2 (Array Int Bool))
(set-info :status unsat)
(assert (not (= ((_ map and) s1 s2)
                ((_ map not) ((_ map or) ((_ map not) s1) ((_ map not) s2))))))
(check-sat)
""",
    # z3test regressions/smt2/issue-1665.smt2, its second and third queries
    # (the first, over an uninterpreted index sort, takes default values
    # there and stays rejected): refuted while preprocessing, by the read of
    # the map the rewriter evaluates; default values in the input.
    "z3test_issue_1665": """(declare-fun s1_1796 () (Array Int Bool))
(declare-fun s2_1797 () (Array Int Bool))
(declare-fun x_1795 () Int)
(assert (not (default s1_1796)))
(assert (not (default s2_1797)))
(assert (select ((_ map (and (Bool Bool) Bool))
          s1_1796
          ((_ map (not (Bool) Bool)) s2_1797))
        x_1795))
(assert (not (select s1_1796 x_1795)))
(check-sat)
""",
    # Set operators, read through by the rewriter.
    "union_member": """(declare-fun a () (Array Int Bool))
(declare-fun b () (Array Int Bool))
(declare-fun x () Int)
(assert (select (union a b) x))
(assert (not (select a x)))
(assert (not (select (intersection (complement a) b) x)))
(check-sat)
""",
    "setminus_disjoint": """(declare-sort E 0)
(declare-fun a () (Array E Bool))
(declare-fun b () (Array E Bool))
(declare-fun x () E)
(assert (select (setminus a b) x))
(assert (select b x))
(check-sat)
""",
    # A set difference kept as a term: the rewriter turns it into the map of
    # and over the complement, a different Lean function (the _md identity).
    "setminus_named": """(declare-fun a () (Array Int Bool))
(declare-fun b () (Array Int Bool))
(declare-fun c () (Array Int Bool))
(declare-fun x () Int)
(assert (= c (setminus a b)))
(assert (select c x))
(assert (select b x))
(check-sat)
""",
    "setminus_as_intersection": """(declare-sort E 0)
(declare-fun a () (Array E Bool))
(declare-fun b () (Array E Bool))
(assert (not (= (setminus a b) (intersection a (complement b)))))
(check-sat)
""",
    "setminus_under_function": """(declare-fun f ((Array Int Bool)) Int)
(declare-fun a () (Array Int Bool))
(declare-fun b () (Array Int Bool))
(assert (not (= (f (setminus a b)) (f (intersection a (complement b))))))
(check-sat)
""",
    "real_intersection": """(declare-fun a () (Array Real Bool))
(declare-fun b () (Array Real Bool))
(declare-fun x () Real)
(assert (select (intersection a b) (+ x 1.0)))
(assert (not (select b (+ 1.0 x))))
(check-sat)
""",
    # The select-map axiom as an array lemma, over an uninterpreted index.
    "map_equal_sets": """(declare-sort E 0)
(declare-fun a () (Array E Bool))
(declare-fun b () (Array E Bool))
(declare-fun c () (Array E Bool))
(declare-fun x () E)
(assert (= c ((_ map or) a b)))
(assert (select c x))
(assert (not (select a x)))
(assert (not (select b x)))
(check-sat)
""",
    "union_of_variable_sets": """(declare-sort E 0)
(declare-fun a () (Array E Bool))
(declare-fun b () (Array E Bool))
(declare-fun c () (Array E Bool))
(declare-fun x () E)
(declare-fun y () E)
(assert (= c (union a b)))
(assert (select c x))
(assert (= x y))
(assert (not (select a y)))
(assert (not (select b y)))
(check-sat)
""",
    "map_under_function": """(declare-sort E 0)
(declare-fun f ((Array E Bool)) Int)
(declare-fun a () (Array E Bool))
(declare-fun b () (Array E Bool))
(assert (= a b))
(assert (not (= (f ((_ map or) a b)) (f a))))
(check-sat)
""",
    "implication_map": """(declare-fun a () (Array Int Bool))
(declare-fun b () (Array Int Bool))
(declare-fun c () (Array Int Bool))
(declare-fun x () Int)
(assert (= c ((_ map =>) a b)))
(assert (select c x))
(assert (select a x))
(assert (not (select b x)))
(check-sat)
""",
    "map_of_store_read": """(declare-fun a () (Array Int Bool))
(declare-fun b () (Array Int Bool))
(declare-fun i () Int)
(declare-fun j () Int)
(assert (not (= i j)))
(assert (select ((_ map and) (store a i false) b) j))
(assert (not (select a j)))
(check-sat)
""",
    "complement_conflict": """(declare-fun a () (Array Int Bool))
(declare-fun x () Int)
(assert (select ((_ map and) a ((_ map not) a)) x))
(check-sat)
""",
    "flattened_and": """(declare-fun a () (Array Int Bool))
(declare-fun b () (Array Int Bool))
(declare-fun c () (Array Int Bool))
(declare-fun x () Int)
(assert (select ((_ map and) ((_ map and) a b) c) x))
(assert (not (select b x)))
(check-sat)
""",
    # Reads the rewriter evaluates into stores and constant arrays below a map.
    "read_of_map_over_stores": """(declare-fun a () (Array Int Bool))
(declare-fun b () (Array Int Bool))
(declare-fun i () Int)
(assert (not (select ((_ map and) (store a i true) (store b i true)) i)))
(check-sat)
""",
    "read_of_map_over_constants": """(declare-fun x () Int)
(assert (select ((_ map and) ((as const (Array Int Bool)) true) ((as const (Array Int Bool)) false)) x))
(check-sat)
""",
    # The identities (_map_identities): euf's commutativity of maps of or,
    # the rewriter's double complement, idempotence, maps of stores, maps of
    # stores next to a constant array, and maps of constant arrays.
    "union_commutes": """(declare-sort E 0)
(declare-fun a () (Array E Bool))
(declare-fun b () (Array E Bool))
(assert (not (= (union a b) (union b a))))
(check-sat)
""",
    "complement_twice": """(declare-fun a () (Array Int Bool))
(assert (not (= (complement (complement a)) a)))
(check-sat)
""",
    "default_of_double_complement": """(declare-fun a () (Array Int Bool))
(assert (default a))
(assert (not (default ((_ map not) ((_ map not) a)))))
(check-sat)
""",
    "intersection_idempotent": """(declare-fun a () (Array Int Bool))
(assert (not (= ((_ map and) a a) a)))
(check-sat)
""",
    "map_of_stores": """(declare-fun a () (Array Int Bool))
(declare-fun b () (Array Int Bool))
(declare-fun i () Int)
(declare-fun p () Bool)
(assert (not (= ((_ map and) (store a i p) (store b i true)) (store ((_ map and) a b) i p))))
(check-sat)
""",
    "complement_of_store": """(declare-fun a () (Array Int Bool))
(declare-fun i () Int)
(assert (not (= (complement (store a i true)) (store (complement a) i false))))
(check-sat)
""",
    "map_of_store_and_constant": """(declare-fun a () (Array Int Bool))
(declare-fun i () Int)
(declare-fun c () (Array Int Bool))
(assert (= c ((_ map or) (store a i false) ((as const (Array Int Bool)) false))))
(assert (not (= c (store ((_ map or) a ((as const (Array Int Bool)) false)) i false))))
(check-sat)
""",
    "map_of_constants": """(assert (not (= ((_ map or) ((as const (Array Int Bool)) false)
                               ((as const (Array Int Bool)) true))
                ((as const (Array Int Bool)) true))))
(check-sat)
""",
}
# Maps of other functions ((_ map f) a ...): uninterpreted functions and
# predicates of up to three arguments, the Boolean connective xor, = and
# distinct, Int and Real +, -, and comparisons, and ite, over elements of
# an uninterpreted sort, Int, Real, or Bool. Lean's _map1/_map2/_map3 apply
# a lambda pointwise (proof_to_lean._set_function); reads, maps of stores
# and constant arrays, and commutativity get the facts of the set
# combinators above.
MAP_FUNCTION_INPUTS = {
    # A read of a map of an uninterpreted function: f of the read (select-map).
    "map_function_read": """(declare-fun f (Int) Int)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(assert (= b ((_ map f) a)))
(assert (= (select a 3) 4))
(assert (not (= (select b 3) (f 4))))
(check-sat)
""",
    # A function the input maps but never applies: congruence of the maps.
    "mapped_function_congruence": """(declare-fun f (Int) Int)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(assert (= a b))
(assert (not (= ((_ map f) a) ((_ map f) b))))
(check-sat)
""",
    # Equal reads give equal reads of the maps of a function only mapped.
    "mapped_function_extensionality": """(declare-fun f (Int) Int)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(assert (= (select a i) (select b i)))
(assert (not (= (select ((_ map f) a) i) (select ((_ map f) b) i))))
(check-sat)
""",
    # A binary function over an uninterpreted element sort.
    "map_over_sort": """(declare-sort I 0)
(declare-sort E 0)
(declare-fun g (E E) E)
(declare-fun a () (Array I E))
(declare-fun b () (Array I E))
(declare-fun c () (Array I E))
(declare-fun i () I)
(assert (= c ((_ map g) a b)))
(assert (not (= (select c i) (g (select a i) (select b i)))))
(check-sat)
""",
    # A map of a predicate, a set (Array Int Bool), read as the predicate.
    "map_predicate": """(declare-fun p (Int) Bool)
(declare-fun a () (Array Int Int))
(assert (select ((_ map p) a) 0))
(assert (= (select a 0) 5))
(assert (not (p 5)))
(check-sat)
""",
    # A function of a Bool and an Int element, injected into the carrier.
    "map_over_bool_elements": """(declare-fun g (Bool Int) Int)
(declare-fun s () (Array Int Bool))
(declare-fun a () (Array Int Int))
(assert (select s 2))
(assert (= (select a 2) 7))
(assert (not (= (select ((_ map g) s a) 2) (g true 7))))
(check-sat)
""",
    # A function of an Int and a Real element (qf_uflira).
    "map_mixed_sorts": """(declare-fun h (Int Real) Real)
(declare-fun a () (Array Int Int))
(declare-fun r () (Array Int Real))
(assert (= (select a 0) 1))
(assert (= (select r 0) 2.5))
(assert (not (= (select ((_ map h) a r) 0) (h 1 2.5))))
(check-sat)
""",
    # Pointwise addition, Lean's + over Int.
    "map_addition": """(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun c () (Array Int Int))
(assert (= c ((_ map (+ (Int Int) Int)) a b)))
(assert (= (select a 3) 4))
(assert (= (select b 3) 5))
(assert (not (= (select c 3) 9)))
(check-sat)
""",
    # Pointwise subtraction over Real elements.
    "map_real_subtraction": """(declare-fun a () (Array Int Real))
(declare-fun b () (Array Int Real))
(declare-fun i () Int)
(assert (> (select ((_ map (- (Real Real) Real)) a b) i) 0.0))
(assert (<= (select a i) (select b i)))
(check-sat)
""",
    # Pointwise unary minus.
    "map_negation": """(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(assert (> (select a i) 0))
(assert (> (select ((_ map (- (Int) Int)) a) i) 0))
(check-sat)
""",
    # A map of <= into a set.
    "map_comparison": """(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun c () (Array Int Bool))
(assert (= c ((_ map (<= (Int Int) Bool)) a b)))
(assert (= (select a 3) 4))
(assert (= (select b 3) 5))
(assert (not (select c 3)))
(check-sat)
""",
    # Maps of < and > over Real indices and elements.
    "map_strict_comparisons": """(declare-fun a () (Array Real Real))
(declare-fun b () (Array Real Real))
(declare-fun x () Real)
(assert (select ((_ map (< (Real Real) Bool)) a b) x))
(assert (select ((_ map (> (Real Real) Bool)) a b) x))
(check-sat)
""",
    # A map of xor over sets with an uninterpreted index (the rewriter reads it as (not (= p q))).
    "map_xor": """(declare-sort I 0)
(declare-fun a () (Array I Bool))
(declare-fun b () (Array I Bool))
(declare-fun c () (Array I Bool))
(declare-fun i () I)
(assert (= c ((_ map xor) a b)))
(assert (select a i))
(assert (select b i))
(assert (select c i))
(check-sat)
""",
    # A map of = over Int elements.
    "map_equality": """(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(assert (select ((_ map (= (Int Int) Bool)) a b) i))
(assert (not (= (select a i) (select b i))))
(check-sat)
""",
    # A map of = over Bool elements, Lean's Iff.
    "map_bool_equality": """(declare-fun a () (Array Int Bool))
(declare-fun b () (Array Int Bool))
(declare-fun i () Int)
(assert (select ((_ map (= (Bool Bool) Bool)) a b) i))
(assert (select a i))
(assert (not (select b i)))
(check-sat)
""",
    # A map of distinct over an uninterpreted element sort, false for one array twice.
    "map_distinct": """(declare-sort I 0)
(declare-sort E 0)
(declare-fun a () (Array I E))
(declare-fun i () I)
(assert (select ((_ map (distinct (E E) Bool)) a a) i))
(check-sat)
""",
    # A map of ite, _map3 (refuted while preprocessing, by the rewriter's read).
    "map_ite": """(declare-fun p () (Array Int Bool))
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(assert (select p 0))
(assert (not (= (select ((_ map (ite (Bool Int Int) Int)) p a b) 0) (select a 0))))
(check-sat)
""",
    # A map of ite read through an array equality (the select-map axiom).
    "map_ite_symbolic": """(declare-fun p () (Array Int Bool))
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun c () (Array Int Int))
(declare-fun i () Int)
(assert (= c ((_ map (ite (Bool Int Int) Int)) p a b)))
(assert (not (select p i)))
(assert (not (= (select c i) (select b i))))
(check-sat)
""",
    # A map of ite over Bool branches, the formula (c and p) or (not c and q).
    "map_bool_ite": """(declare-fun p () (Array Int Bool))
(declare-fun q () (Array Int Bool))
(declare-fun r () (Array Int Bool))
(declare-fun i () Int)
(assert (select ((_ map (ite (Bool Bool Bool) Bool)) p q r) i))
(assert (not (select q i)))
(assert (not (select r i)))
(check-sat)
""",
    # Maps of a commutative function are commutative (euf's congruence closure, _mc).
    "addition_commutes": """(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(assert (not (= ((_ map (+ (Int Int) Int)) a b) ((_ map (+ (Int Int) Int)) b a))))
(check-sat)
""",
    # The same for a map of = over an uninterpreted sort.
    "equality_map_commutes": """(declare-sort I 0)
(declare-sort E 0)
(declare-fun a () (Array I E))
(declare-fun b () (Array I E))
(assert (not (= ((_ map (= (E E) Bool)) a b) ((_ map (= (E E) Bool)) b a))))
(check-sat)
""",
    # A map of stores at one index is the store of the map (the rewriter, _ms).
    "addition_map_of_stores": """(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(assert (not (= (select ((_ map (+ (Int Int) Int)) (store a i 2) (store b i 3)) i) 5)))
(check-sat)
""",
    # The same for a map of an uninterpreted function.
    "function_map_of_stores": """(declare-fun f (Int) Int)
(declare-fun a () (Array Int Int))
(declare-fun c () (Array Int Int))
(declare-fun i () Int)
(assert (= c ((_ map f) (store a i 2))))
(assert (not (= (select c i) (f 2))))
(check-sat)
""",
    # A map of constant arrays, read at a symbolic index.
    "addition_map_of_constants": """(declare-fun i () Int)
(assert (not (= (select ((_ map (+ (Int Int) Int)) ((as const (Array Int Int)) 1) ((as const (Array Int Int)) 2)) i) 3)))
(check-sat)
""",
    # A map of a store and a constant array (a store of its value there).
    "addition_map_of_store_and_constant": """(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(assert (not (= (select ((_ map (+ (Int Int) Int)) (store a i 2) ((as const (Array Int Int)) 1)) i) 3)))
(check-sat)
""",
    # Reads through nested maps of +, f, and unary minus, which the rewriter evaluates.
    "nested_function_maps": """(declare-fun f (Int) Int)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(assert (= (select a i) 1))
(assert (= (select b i) 2))
(assert (not (= (select ((_ map (+ (Int Int) Int)) ((_ map f) a) ((_ map (- (Int) Int)) b)) i) (- (f 1) 2))))
(check-sat)
""",
    # A read through a store at another numeral reaches a map: the rewriter
    # skips the store and evaluates the read of the map with no read term of
    # it in the certificate, so the map's read fact goes with the store's
    # (_skipped_to_map; random sweep seeds 110, 137, 172).
    "read_through_store_to_map": """(declare-fun a () (Array Int Int))
(assert (= (select (store ((_ map (- (Int) Int)) a) 1 2) 0) 2))
(assert (= (select a 0) 2))
(check-sat)
""",
    # The same over a set operator (failed before, with the connectives only).
    "set_read_through_store_to_map": """(declare-fun s () (Array Int Bool))
(assert (select (store ((_ map not) s) 1 false) 0))
(assert (select s 0))
(check-sat)
""",
    # A read of a map through a store below it, into the map below that.
    "map_read_through_store_to_map": """(declare-fun f (Int) Int)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(assert (= (select ((_ map (+ (Int Int) Int)) (store ((_ map f) a) 1 2) b) 0) 2))
(assert (= (select a 0) 3))
(assert (= (select b 0) 0))
(assert (= (f 3) 1))
(check-sat)
""",
    # Maps of two functions over the same arrays, as conjuncts: the replay
    # ties the split conjuncts to the input by key, and the two maps shared
    # one key (the mapped function was not in it), so the map of or was
    # derived from the map of and and Lean rejected the step (found by a
    # random sweep of such conjunctions).
    "conjuncts_map_and_or": """(declare-fun a () (Array Int Bool))
(declare-fun b () (Array Int Bool))
(declare-fun c () (Array Int Bool))
(declare-fun d () (Array Int Bool))
(declare-fun q () Bool)
(declare-fun r () Bool)
(assert (and q (= c ((_ map and) a b))))
(assert (and r (= c ((_ map or) a b)) (= c d)))
(assert (select a 0))
(assert (not (select b 0)))
(check-sat)
""",
    # The same collision with maps of two declared functions.
    "conjuncts_map_f_g": """(declare-fun a () (Array Int Int))
(declare-fun c () (Array Int Int))
(declare-fun d () (Array Int Int))
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun q () Bool)
(declare-fun r () Bool)
(assert (and q (= c ((_ map f) a))))
(assert (and r (= c ((_ map g) a)) (= c d)))
(assert (not (= (f (select a 0)) (g (select a 0)))))
(check-sat)
""",
    # The same collision with maps of addition and subtraction.
    "conjuncts_map_plus_minus": """(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun c () (Array Int Int))
(declare-fun d () (Array Int Int))
(declare-fun q () Bool)
(declare-fun r () Bool)
(assert (and q (= c ((_ map (+ (Int Int) Int)) a b))))
(assert (and r (= c ((_ map (- (Int Int) Int)) a b)) (= c d)))
(assert (not (= (select b 0) 0)))
(check-sat)
""",
}
# Arrays over Bool indices, (Array Bool E): Prop -> E in Lean, an index is a
# formula and two indices are equal as propositions (propext). A model's
# array over Bool is an instance through p |-> a(p), so select, store, and
# extensionality (whose witness is itself a formula) need nothing new.
# Constant arrays and default values stay rejected over Bool indices (a
# finite index sort).
BOOL_INDEX_INPUTS = {
    # z3test regressions/smt2/5798.smt2: a read at an index formula the
    # rewriter decides (|r6| = ||r6||) against the read at true.
    "z3test_5798": """(declare-fun r () (Array Bool Bool))
(declare-fun r6 () Int)
(assert (and (select r true) (not (select r (= (abs r6) (abs (abs r6)))))))
(check-sat)
""",
    "bool_index_store_self": """(declare-sort E 0)
(declare-fun a () (Array Bool E))
(declare-fun p () Bool)
(declare-fun e () E)
(assert (= (store a p e) a))
(assert (not (= (select a p) e)))
(check-sat)
""",
    # Read over write at another index: p = q or the read sees a.
    "bool_index_read_other": """(declare-fun a () (Array Bool Int))
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (not (= p q)))
(assert (not (= (select (store a p 1) q) (select a q))))
(check-sat)
""",
    # Arrays agreeing at true and false are equal: the extensionality
    # witness is a formula, and Lean decides it.
    "bool_index_extensionality": """(declare-fun a () (Array Bool Int))
(declare-fun b () (Array Bool Int))
(assert (= (select a true) (select b true)))
(assert (= (select a false) (select b false)))
(assert (not (= a b)))
(check-sat)
""",
    # Indices that are arithmetic atoms, equal after the rewriter's
    # normalization.
    "bool_index_arithmetic_atoms": """(declare-fun a () (Array Bool Bool))
(declare-fun x () Int)
(assert (select a (> x 0)))
(assert (not (select a (>= x 1))))
(check-sat)
""",
    # The rewriter skips a store at false in a read at true, as at distinct
    # numerals (read_through_numeral_stores).
    "bool_index_read_through_value_stores": """(declare-fun a () (Array Bool Int))
(assert (not (= (select (store (store a true 1) false 2) true) 1)))
(check-sat)
""",
    "function_into_bool_indexed_arrays": """(declare-sort U 0)
(declare-fun h (U) (Array Bool U))
(declare-fun x () U)
(declare-fun y () U)
(declare-fun p () Bool)
(assert (= x y))
(assert (not (= (select (h x) p) (select (h y) p))))
(check-sat)
""",
    # A function over Bool-indexed arrays: (h a) applies h to the array's
    # injection (_m.arrs_bi_inj).
    "function_over_bool_indexed_arrays": """(declare-fun h ((Array Bool Int)) Int)
(declare-fun a () (Array Bool Int))
(declare-fun b () (Array Bool Int))
(assert (= a b))
(assert (not (= (h a) (h b))))
(check-sat)
""",
    "bool_index_map":"""(declare-fun a () (Array Bool Bool))
(declare-fun b () (Array Bool Bool))
(declare-fun p () Bool)
(assert (select ((_ map and) a b) p))
(assert (not (select a p)))
(check-sat)
""",
    # An index that is a read of a set.
    "membership_as_index": """(declare-fun a () (Array Bool Bool))
(declare-fun s () (Array Int Bool))
(declare-fun i () Int)
(declare-fun j () Int)
(assert (= i j))
(assert (select a (select s i)))
(assert (not (select a (select s j))))
(check-sat)
""",
    # Stores at p and (not p): the array solver's index equality (= (not p)
    # p) has the gate clause (or (not (= (not p) p)) (not (not p)) p), which
    # the SAT solver resolves to p (the double negation is one literal there).
    "bool_index_negated_stores": """(declare-fun a () (Array Bool Int))
(declare-fun b () (Array Bool Int))
(declare-fun p () Bool)
(assert (= (store a p 0) (store b (not p) 0)))
(assert (not (= (select a (not p)) (select b p))))
(check-sat)
""",
    "bool_index_ite": """(declare-fun a () (Array Bool Int))
(declare-fun b () (Array Bool Int))
(declare-fun c () (Array Bool Int))
(declare-fun p () Bool)
(assert (= (select a true) (select c true)))
(assert (= (select a false) (select c false)))
(assert (= b (ite p a c)))
(assert (not (= b a)))
(check-sat)
""",
}
# Nested arrays: an index or element sort that is an array itself, a
# function type in Lean (I -> (J -> E), (J -> E) -> V). A read of a row is
# an array term; reads and extensionality witnesses are unfolded in the
# lemmas even when their values are arrays (proof_to_lean._folded_array).
NESTED_ARRAY_INPUTS = {
    # A matrix equal to another with one row replaced agrees elsewhere.
    "nested_equal_rows": """(declare-fun a () (Array Int (Array Int Int)))
(declare-fun b () (Array Int (Array Int Int)))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun k () Int)
(assert (= a (store b i (select b j))))
(assert (not (= (select (select a k) 0) (select (select b k) 0))))
(assert (not (= k i)))
(check-sat)
""",
    "nested_store_row": """(declare-fun a () (Array Int (Array Int Int)))
(declare-fun r () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(assert (= (select (store a i r) j) (select a j)))
(assert (= i j))
(assert (not (= r (select a i))))
(check-sat)
""",
    # Read over write in both dimensions.
    "nested_read_own_write": """(declare-fun a () (Array Int (Array Int Int)))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun i2 () Int)
(declare-fun j2 () Int)
(declare-fun v () Int)
(assert (= i i2))
(assert (= j j2))
(assert (not (= (select (select (store a i (store (select a i) j v)) i2) j2) v)))
(check-sat)
""",
    "nested_uninterpreted": """(declare-sort U 0)
(declare-fun a () (Array U (Array U U)))
(declare-fun b () (Array U (Array U U)))
(declare-fun i () U)
(declare-fun j () U)
(assert (= a b))
(assert (not (= (select (select a i) j) (select (select b i) j))))
(check-sat)
""",
    # A row stored at j and read back at i: the row read at i stays.
    "nested_rows_differ": """(declare-sort U 0)
(declare-fun a () (Array U (Array U U)))
(declare-fun i () U)
(declare-fun j () U)
(assert (not (= (select a i) (select (store a j (select a i)) i))))
(check-sat)
""",
    "outer_store_inner_store": """(declare-sort U 0)
(declare-fun m () (Array U (Array U U)))
(declare-fun i () U)
(declare-fun j () U)
(declare-fun k () U)
(declare-fun v () U)
(assert (not (= i k)))
(assert (not (= (select (select (store m i (store (select m i) j v)) k) j) (select (select m k) j))))
(check-sat)
""",
    "swap_rows": """(declare-fun a () (Array Int (Array Int Int)))
(declare-fun b () (Array Int (Array Int Int)))
(declare-fun i () Int)
(declare-fun j () Int)
(assert (= b (store (store a i (select a j)) j (select a i))))
(assert (not (= (select (select b j) 0) (select (select a i) 0))))
(check-sat)
""",
    "three_levels": """(declare-fun a () (Array Int (Array Int (Array Int Int))))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun k () Int)
(assert (= (select (select (select a i) j) k) 3))
(assert (= i 0))
(assert (not (= (select (select (select a 0) j) k) 3)))
(check-sat)
""",
    # Rows agreeing at true and false are equal: the extensionality witness
    # of the rows, which are reads.
    "row_extensionality": """(declare-fun a () (Array Int (Array Bool Int)))
(declare-fun i () Int)
(declare-fun j () Int)
(assert (= (select (select a i) true) (select (select a j) true)))
(assert (= (select (select a i) false) (select (select a j) false)))
(assert (not (= (select a i) (select a j))))
(check-sat)
""",
    "nested_ite": """(declare-fun a () (Array Int (Array Int Int)))
(declare-fun b () (Array Int (Array Int Int)))
(declare-fun p () Bool)
(declare-fun i () Int)
(assert (= (select a i) (select b i)))
(assert (not (= (select (ite p a b) i) (select a i))))
(check-sat)
""",
    "nested_distinct": """(declare-fun a () (Array Int (Array Int Int)))
(declare-fun r () (Array Int Int))
(declare-fun i () Int)
(assert (distinct (select (store a i r) i) r (select a 1)))
(check-sat)
""",
    "nested_constant": """(declare-fun a () (Array Int (Array Int Int)))
(declare-fun i () Int)
(declare-fun j () Int)
(assert (= a ((as const (Array Int (Array Int Int))) ((as const (Array Int Int)) 5))))
(assert (not (= (select (select a i) j) 5)))
(check-sat)
""",
    # The array solver relates constant arrays of rows through their default
    # rows, array-valued default terms of its own, unfolded in the lemmas.
    "const_rows_default": """(declare-fun r () (Array Int Int))
(declare-fun s () (Array Int Int))
(declare-fun a () (Array Int (Array Int Int)))
(assert (= a ((as const (Array Int (Array Int Int))) r)))
(assert (= (store a 3 s) ((as const (Array Int (Array Int Int))) s)))
(assert (not (= r s)))
(check-sat)
""",
    # Reads the rewriter evaluates through a stored row: the row read back,
    # then the read of the stored row (its _store_apply or _select_const
    # facts at the read's index, _n facts), two and three levels deep.
    "nested_sets": """(declare-fun s () (Array Int (Array Int Bool)))
(declare-fun i () Int)
(declare-fun j () Int)
(assert (not (select (select (store s i (store (select s i) j true)) i) j)))
(check-sat)
""",
    "nested_read_own_write_evaluated": """(declare-fun a () (Array Int (Array Int Int)))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun v () Int)
(assert (not (= (select (select (store a i (store (select a i) j v)) i) j) v)))
(check-sat)
""",
    "nested_constant_evaluated": """(declare-fun i () Int)
(declare-fun j () Int)
(assert (not (= (select (select ((as const (Array Int (Array Int Int)))
                                 (store ((as const (Array Int Int)) 5) 3 4)) i) j)
                (ite (= j 3) 4 5))))
(check-sat)
""",
    "three_levels_evaluated": """(declare-fun a () (Array Int (Array Int (Array Int Int))))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun k () Int)
(declare-fun v () Int)
(assert (not (= (select (select (select (store a i (store (select a i) j (store (select (select a i) j) k v))) i) j) k)
                v)))
(check-sat)
""",
    "array_of_sets_union": """(declare-fun s () (Array Int (Array Int Bool)))
(declare-fun i () Int)
(declare-fun x () Int)
(assert (select (union (select s i) (select s (+ i 1))) x))
(assert (not (select (select s i) x)))
(assert (not (select (select s (+ i 1)) x)))
(check-sat)
""",
    "real_nested": """(declare-fun a () (Array Real (Array Int Real)))
(declare-fun x () Real)
(declare-fun i () Int)
(assert (> (select (select a x) i) 1.0))
(assert (< (select (select (store a x (select a x)) x) i) 0.5))
(check-sat)
""",
    "function_into_nested": """(declare-fun h (Int) (Array Int (Array Int Int)))
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= x y))
(assert (not (= (select (select (h x) 1) 2) (select (select (h y) 1) 2))))
(check-sat)
""",
    "function_over_nested": """(declare-fun h ((Array Int (Array Int Int))) Int)
(declare-fun a () (Array Int (Array Int Int)))
(declare-fun r () (Array Int Int))
(assert (= (select a 0) r))
(assert (not (= (h a) (h (store a 0 r)))))
(check-sat)
""",
    # Arrays indexed by arrays.
    "array_index": """(declare-fun a () (Array (Array Int Int) Int))
(declare-fun b () (Array Int Int))
(declare-fun c () (Array Int Int))
(declare-fun i () Int)
(assert (= (select b i) (select c i)))
(assert (= b (store c i (select b i))))
(assert (not (= (select a b) (select a c))))
(check-sat)
""",
    "array_index_store": """(declare-fun a () (Array (Array Int Int) Int))
(declare-fun b () (Array Int Int))
(declare-fun c () (Array Int Int))
(assert (not (= b c)))
(assert (not (= (select (store a b 1) c) (select a c))))
(check-sat)
""",
    # The extensionality witness is an array, chosen with a constant function.
    "array_index_extensionality": """(declare-fun a () (Array (Array Int Int) Int))
(declare-fun b () (Array (Array Int Int) Int))
(declare-fun c () (Array Int Int))
(assert (not (= a b)))
(assert (= a (store b c (select a c))))
(assert (= (select a c) (select b c)))
(check-sat)
""",
    # The same over an uninterpreted element sort: the constant function
    # starts from _m.nonempty.
    "uninterpreted_array_index_extensionality": """(declare-sort U 0)
(declare-fun a () (Array (Array U U) Bool))
(declare-fun b () (Array (Array U U) Bool))
(declare-fun c () (Array U U))
(assert (not (= a b)))
(assert (= a (store b c (select a c))))
(assert (= (select a c) (select b c)))
(check-sat)
""",
    # z3test regressions/smt2/segfault2.smt2's sorts (that query is sat).
    "segfault2_sorts": """(define-sort bStack () (Array Int (Array Int Bool)))
(define-sort iStack () (Array Int (Array Int Int)))
(define-sort iArray () (Array Int Int))
(declare-fun bs () bStack)
(declare-fun bs2 () bStack)
(declare-fun is () iStack)
(declare-fun is2 () iStack)
(declare-fun p () iArray)
(declare-fun p2 () iArray)
(assert (= bs bs2))
(assert (= is is2))
(assert (= p p2))
(assert (not (and (= (select bs 1) (select bs2 1)) (= (select (select is 2) 3) (select (select is2 2) 3)))))
(check-sat)
""",
    # A read that is both an opaque Int atom of a lemma and the value of a
    # store, which stays folded: the fallback unfolds it from the atom
    # (random nested seed 12; stored_read_atom is the flat case).
    "stored_nested_read_atom": """(declare-fun a () (Array Int (Array Int Int)))
(declare-fun b () (Array Int (Array Int Int)))
(declare-fun r () (Array Int Int))
(declare-fun s () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun k () Int)
(assert (= (select (select b 0) i) (select (store (select b 1) j (select (select a 0) k)) j)))
(assert (not (= r s)))
(assert (not (= a a)))
(assert (= s (store s j (select (select a i) 1))))
(assert (not (= (ite (= 1 0) (ite (= 0 1) b a) a) b)))
(assert (not (= k (select (store (select a k) j k) 1))))
(check-sat)
""",
    "stored_read_atom": """(declare-fun r () (Array Int Int))
(declare-fun s () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun k () Int)
(assert (= (select s i) (select (store r j (select s k)) j)))
(assert (not (= (select s i) (select s k))))
(check-sat)
""",
}
ARRAY_INPUTS.update(ARITHMETIC_ARRAY_INPUTS)
ARRAY_INPUTS.update(CONSTANT_ARRAY_INPUTS)
ARRAY_INPUTS.update(REAL_INDEX_CONSTANT_ARRAY_INPUTS)
ARRAY_INPUTS.update(NUMERAL_EXPRESSION_INPUTS)
ARRAY_INPUTS.update(ARRAY_FUNCTION_INPUTS)
ARRAY_INPUTS.update(BOOL_ELEMENT_INPUTS)
ARRAY_INPUTS.update(SET_COMBINATOR_INPUTS)
ARRAY_INPUTS.update(MAP_FUNCTION_INPUTS)
ARRAY_INPUTS.update(BOOL_INDEX_INPUTS)
ARRAY_INPUTS.update(NESTED_ARRAY_INPUTS)
# The fragment of each documented input (the others are qf_uf).
_FRAGMENTS = {"arrays_with_integer_weights": "qf_uflia", "real_read_own_write": "qf_uflra",
              "int_indices_real_elements": "qf_uflira", "real_constants": "qf_uflira",
              "real_index_2549": "qf_uflira", "real_index_read": "qf_uflra",
              "real_index_comparison": "qf_uflira", "real_index_terms": "qf_uflra",
              "real_index_elements": "qf_uflra", "int_function_into_arrays": "qf_uflia",
              "real_function_into_arrays": "qf_uflra", "function_into_constant_arrays": "qf_uflira",
              "predicate_over_application": "qf_uflia", "nested_applications": "qf_uflia",
              "array_function_twice": "qf_uflia", "two_functions_into_arrays": "qf_uflia",
              "real_set": "qf_uflra", "real_index_store_over_another_constant": "qf_uflira",
              "real_read_of_an_array_equated_to_a_constant": "qf_uflra",
              "int_read_of_a_store_at_real_indices": "qf_uflira",
              "read_stored_back_at_a_fraction_of_one": "qf_uflira", "fraction_sums_as_indices": "qf_uflra"}
_FRAGMENTS.update((name, "qf_uflia") for name, source in BOOL_ELEMENT_INPUTS.items()
                  if "Array Int Bool" in source)
# Set combinators are over Int indices (qf_uflia) except these, named
# explicitly rather than guessed from the source text.
_SET_COMBINATOR_FRAGMENTS = {"setminus_disjoint": "qf_uf", "setminus_as_intersection": "qf_uf",
                             "map_equal_sets": "qf_uf", "union_of_variable_sets": "qf_uf",
                             "union_commutes": "qf_uf", "real_intersection": "qf_uflra"}
_FRAGMENTS.update((name, _SET_COMBINATOR_FRAGMENTS.get(name, "qf_uflia")) for name in SET_COMBINATOR_INPUTS)
# Maps of other functions are over Int indices and elements (qf_uflia) except these.
_MAP_FUNCTION_FRAGMENTS = {"map_over_sort": "qf_uf", "map_xor": "qf_uf", "map_distinct": "qf_uf",
                           "equality_map_commutes": "qf_uf", "map_mixed_sorts": "qf_uflira",
                           "map_real_subtraction": "qf_uflira", "map_strict_comparisons": "qf_uflra"}
_FRAGMENTS.update((name, _MAP_FUNCTION_FRAGMENTS.get(name, "qf_uflia")) for name in MAP_FUNCTION_INPUTS)
_FRAGMENTS.update((name, "qf_uflia") for name in list(ARITHMETIC_ARRAY_INPUTS) + list(CONSTANT_ARRAY_INPUTS)
                  + list(NUMERAL_EXPRESSION_INPUTS) if name not in _FRAGMENTS)
# Bool-indexed arrays over Int elements, or next to Int terms, are qf_uflia.
_FRAGMENTS.update((name, "qf_uf") for name in ("bool_index_store_self", "function_into_bool_indexed_arrays",
                                                "bool_index_map"))
_FRAGMENTS.update((name, "qf_uflia") for name in BOOL_INDEX_INPUTS if name not in _FRAGMENTS)
# Nested arrays over Int (and a Real index) are qf_uflia (qf_uflira) except these.
_FRAGMENTS.update((name, "qf_uf") for name in ("nested_uninterpreted", "nested_rows_differ",
                                                "outer_store_inner_store", "uninterpreted_array_index_extensionality"))
_FRAGMENTS["real_nested"] = "qf_uflira"
_FRAGMENTS.update((name, "qf_uflia") for name in NESTED_ARRAY_INPUTS if name not in _FRAGMENTS)


def _export(source):
    return proof_certificate.export_clause_log_certificate(source)


def _declarations(certificate, kind):
    return [d for d in certificate["declarations"] if d["kind"] == kind]


class TestArrayValidation(unittest.TestCase):
    """Validation without Lean: classification, rejections, the replay, and the encoding."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")
        cls.certificates = {name: _export(source) for name, source in ARRAY_INPUTS.items()}

    def test_fragments(self):
        for name, certificate in self.certificates.items():
            with self.subTest(name=name):
                self.assertEqual(certificate["fragment"], _FRAGMENTS.get(name, "qf_uf"))

    def test_unsupported_arrays_are_rejected(self):
        context = z3.Context()
        rejected = {
            # Bool elements and Bool indices are supported (BOOL_ELEMENT_INPUTS,
            # BOOL_INDEX_INPUTS), but not constant arrays or default values
            # over Bool indices (a finite index sort).
            "(assert (not (select ((as const (Array Bool Bool)) true) false)))":
                "constant arrays are supported over Int and Real indices only",
            "(declare-fun a () (Array Bool Int))(assert (> (default a) 0))":
                "default values are supported over Int and Real indices only",
            # Arrays of several indices, also inside a nested array.
            "(declare-sort I 0)(declare-fun a () (Array I I I))(declare-fun i () I)"
            "(assert (not (= (select a i i) (select a i i))))": "only arrays over uninterpreted sorts",
            "(declare-fun a () (Array Int (Array Int Int Int)))(assert (not (= a a)))":
                "only arrays over uninterpreted sorts",
            # Nested arrays are supported (NESTED_ARRAY_INPUTS), but not
            # constant arrays over array indices (no unboundedness proof)
            # nor default values that are arrays.
            "(assert (not (select ((as const (Array (Array Int Int) Bool)) true) ((as const (Array Int Int)) 0))))":
                "constant arrays are supported over Int and Real indices only",
            "(declare-fun a () (Array Int (Array Int Int)))(assert (= (select (default a) 0) 1))":
                "unsupported array operator: default",
            # Nor connectives over sets indexed by arrays (the embedding of
            # a model's outer arrays does not commute with them).
            "(declare-fun s () (Array (Array Int Int) Bool))(declare-fun x () (Array Int Int))"
            "(assert (select s x))(assert (select (complement s) x))":
                "maps and set operators over arrays indexed by arrays",
            "(declare-fun s () (Array (Array Bool Bool) Bool))(declare-fun t () (Array (Array Bool Bool) Bool))"
            "(declare-fun x () (Array Bool Bool))(assert (select (union s t) x))(assert (not (select s x)))"
            "(assert (not (select t x)))": "maps and set operators over arrays indexed by arrays",
            "(declare-fun g (Int) Int)(declare-fun a () (Array (Array Int Int) Int))(declare-fun x () (Array Int Int))"
            "(assert (= (select ((_ map g) a) x) 1))": "maps and set operators over arrays indexed by arrays",
            # Constant arrays over a possibly finite index sort.
            "(declare-sort I 0)(declare-fun e () I)(declare-fun i () I)"
            "(assert (not (= (select ((as const (Array I I)) e) i) e)))":
                "constant arrays are supported over Int and Real indices only",
            # Maps are supported over connectives, equality, distinct, linear
            # arithmetic, comparisons, ite, and uninterpreted functions of up
            # to three elements (SET_COMBINATOR_INPUTS, MAP_FUNCTION_INPUTS);
            # not of other functions, nor over arrays of arrays.
            "(declare-fun a () (Array Int Int))(declare-fun b () (Array Int Int))"
            "(assert (= (select ((_ map (* (Int Int) Int)) a b) 0) 1))": "maps are supported over connectives",
            "(declare-fun a () (Array Int Int))(assert (= (select ((_ map (to_real (Int) Real)) a) 0) 1.0))":
                "maps are supported over connectives",
            "(declare-fun g (Int Int Int Int) Int)(declare-fun a () (Array Int Int))"
            "(assert (= (select ((_ map g) a a a a) 0) 1))": "maps are supported over connectives",
            "(declare-fun g ((Array Int Int)) Int)(declare-fun a () (Array Int (Array Int Int)))"
            "(assert (= (select ((_ map g) a) 0) 1))": "maps over arrays of arrays are not supported",
            # Default values over a possibly finite index sort (issue-1665.smt2's first query).
            "(declare-sort I 0)(declare-fun a () (Array I Bool))(assert (default a))":
                "default values are supported over Int and Real indices only",
            "(declare-sort I 0)(declare-fun a () (Array I Int))(assert (> (default a) 0))":
                "default values are supported over Int and Real indices only",
            # Functions over and into arrays are supported, nested arrays
            # too, but not into or over arrays of an unsupported sort.
            "(declare-sort I 0)(declare-fun h (I) (Array Bool (Array Bool I I)))(declare-fun i () I)"
            "(assert (not (= (h i) (h i))))": "uninterpreted functions over",
            "(declare-fun h ((Array (Array Bool Int Int) Int)) Int)(declare-fun a () (Array (Array Bool Int Int) Int))"
            "(assert (> (h a) (h a)))": "uninterpreted functions over",
            # A quoted sort name that imitates the certificate's array sort names.
            "(declare-sort I 0)(declare-sort |(Array I I)| 0)(declare-fun x () |(Array I I)|)"
            "(assert (not (= x x)))": "unsupported uninterpreted sort name",
        }
        for source, message in rejected.items():
            with self.subTest(source=source):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, message):
                    proof_certificate.parse_assertions(source + "(check-sat)", context, integer=True)

    def test_the_legacy_core_rejects_arrays_explicitly(self):
        for name in ("read_own_write", "int_read_other_index", "function_over_arrays", "function_into_arrays"):
            with self.subTest(name=name):
                with self.assertRaisesRegex(proof_certificate.ProofExportError,
                                            "arrays are certified through the clause log"):
                    proof_certificate.export_certificate(ARRAY_INPUTS[name])

    def test_arithmetic_array_encoding(self):
        """Int and Real index and element sorts are Int and Rat; each Lean array type has its own family."""
        text = proof_to_lean.reconstruct(ARRAY_INPUTS["int_store_commutes"], self.certificates["int_store_commutes"])
        self.assertIn("  arrs_ii : Nat -> Int -> Int", text)
        self.assertIn('-- Array sorts "(Array Int Int)" are functions Int -> Int (_m.arrs_ii)', text)
        self.assertIn("-- No uninterpreted sort: the type _m.U carries only the arguments of the functions", text)
        # The witness over Int indices chooses with Int's own inhabitant: no
        # nonempty field.
        self.assertIn(":= (_array_diff (Nonempty.intro (0 : Int)) (term_", text)
        self.assertIn(":= _array_ext (Nonempty.intro (0 : Int)) ((term_", text)
        self.assertNotIn("nonempty", text)
        self.assertNotIn("arrs :", text)
        mixed = proof_to_lean.reconstruct(ARRAY_INPUTS["mixed_index_and_element_sorts"],
                                          self.certificates["mixed_index_and_element_sorts"])
        for field in ("  arrs_iu : Nat -> Int -> U", "  arrs_ui : Nat -> U -> Int"):
            self.assertIn(field, mixed)
        real = proof_to_lean.reconstruct(ARRAY_INPUTS["real_read_own_write"], self.certificates["real_read_own_write"])
        self.assertIn("  arrs_rr : Nat -> Rat -> Rat", real)
        lira = proof_to_lean.reconstruct(ARRAY_INPUTS["int_indices_real_elements"],
                                         self.certificates["int_indices_real_elements"])
        self.assertIn("  arrs_ir : Nat -> Int -> Rat", lira)
        # An array argument of a function is injected into the carrier.
        function = proof_to_lean.reconstruct(ARRAY_INPUTS["function_over_arrays"],
                                             self.certificates["function_over_arrays"])
        self.assertIn("  arrs_ii_inj : (Int -> Int) -> U", function)
        self.assertIn("_m.ifuns 0 [(_m.arrs_ii_inj (term_", function)
        # A predicate over arrays of two Lean types: one injection each, and
        # its th-lemma cnf step (not a rewrite) is offered the store
        # identities.
        predicate = proof_to_lean.reconstruct(ARRAY_INPUTS["predicate_over_two_array_types"],
                                              self.certificates["predicate_over_two_array_types"])
        for field in ("  arrs_inj : (U -> U) -> U", "  arrs_ii_inj : (Int -> Int) -> U"):
            self.assertIn(field, predicate)
        self.assertIn("_m.preds 0 [(_m.arrs_inj (term_", predicate)
        self.assertIn("private theorem th_lemma_", predicate)
        self.assertNotIn("private theorem rewrite_", predicate)
        self.assertIn("simp only [", predicate)
        for each in (text, mixed, real, lira, function, predicate):
            self.assertNotIn("sorry", each)
            self.assertNotIn("axiom ", each)

    def test_constant_array_encoding(self):
        """Constant arrays are _const_array over Int; default values are _default over Int's unboundedness."""
        text = proof_to_lean.reconstruct(ARRAY_INPUTS["z3test_2549"], self.certificates["z3test_2549"])
        self.assertIn(":= (@_const_array Int Int (term_", text)
        self.assertIn(":= (_default _int_unbounded (term_", text)
        self.assertIn(":= _default_store _int_unbounded ((term_", text)
        self.assertIn(":= _default_const (I := Int) _int_unbounded (((1 : Int)))", text)
        self.assertIn("private theorem _int_unbounded", text)
        self.assertNotIn("_rat_unbounded", text)  # only the index sorts present
        hints = [d["parameters"] for d in self.certificates["z3test_2549"]["declarations"] if d["name"] == "th-lemma"]
        self.assertIn(["array"], hints)
        read = proof_to_lean.reconstruct(ARRAY_INPUTS["read_constant"], self.certificates["read_constant"])
        self.assertIn(":= _select_const (I := Int) (((5 : Int)))", read)
        rewrite = proof_to_lean.reconstruct(ARRAY_INPUTS["store_over_constants"],
                                            self.certificates["store_over_constants"])
        self.assertIn(":= congrArg (_default _int_unbounded)", rewrite)
        chains = proof_to_lean.reconstruct(ARRAY_INPUTS["z3test_array_q2"], self.certificates["z3test_array_q2"])
        self.assertIn(":= congrArg (fun _x => _select _x (((2 : Int))))", chains)
        self.assertIn(":= _select_const (I := Int) (((0 : Int))) (((2 : Int)))", chains)
        elements = proof_to_lean.reconstruct(ARRAY_INPUTS["element_constants"], self.certificates["element_constants"])
        self.assertIn("(@_const_array Int _m.U (_m.elems ", elements)
        # Without a constant array there are no default definitions.
        plain = proof_to_lean.reconstruct(ARRAY_INPUTS["int_store_commutes"], self.certificates["int_store_commutes"])
        self.assertNotIn("_const_array", plain)
        self.assertNotIn("_default", plain)
        # Over Real indices: the same definitions over Rat and _rat_unbounded.
        real = proof_to_lean.reconstruct(ARRAY_INPUTS["real_index_2549"], self.certificates["real_index_2549"])
        self.assertIn(":= (@_const_array Rat Int (term_", real)
        self.assertIn(":= (_default _rat_unbounded (term_", real)
        self.assertIn(":= _default_store _rat_unbounded ((term_", real)
        self.assertIn(":= _default_const (I := Rat) _rat_unbounded (((1 : Int)))", real)
        self.assertIn("private theorem _rat_unbounded", real)
        self.assertNotIn("_int_unbounded", real)
        real_read = proof_to_lean.reconstruct(ARRAY_INPUTS["real_index_read"], self.certificates["real_index_read"])
        self.assertIn(":= _select_const (I := Rat) (((5 : Rat)))", real_read)
        real_chains = proof_to_lean.reconstruct(ARRAY_INPUTS["real_index_comparison"],
                                                self.certificates["real_index_comparison"])
        self.assertIn(":= congrArg (_default _rat_unbounded)", real_chains)
        self.assertIn(":= _select_const (I := Rat) (((0 : Int))) (((1 : Rat) / (2 : Rat)))", real_chains)
        for each in (text, read, rewrite, chains, elements, real, real_read, real_chains):
            self.assertNotIn("sorry", each)
            self.assertNotIn("axiom ", each)

    def test_constant_array_evaluations_of_the_rewriter(self):
        """The rewriter's evaluations over constant arrays get their facts and simp lemmas outside rewrites too."""
        # A cnf th-lemma comparing stores over constant arrays gets the
        # default facts, as a rewrite does.
        source = ARRAY_INPUTS["constant_comparison_under_cnf"]
        certificate = self.certificates["constant_comparison_under_cnf"]
        self.assertIn(["cnf"], [d["parameters"] for d in certificate["declarations"] if d["name"] == "th-lemma"])
        text = proof_to_lean.reconstruct(source, certificate)
        cnf = text.split("private theorem th_lemma_", 1)[1].split("\n\n", 1)[0]
        self.assertIn(":= congrArg (_default _int_unbounded)", cnf)
        self.assertIn(":= _default_const (I := Int) _int_unbounded", cnf)
        # A store of a constant array's value into it, and a constant
        # array compared with a store into it: the simp set of the array
        # rewrite alternative.
        for name in ("store_of_a_constant_read", "constant_equal_to_a_store", "store_equal_to_a_constant"):
            with self.subTest(name=name):
                text = proof_to_lean.reconstruct(ARRAY_INPUTS[name], self.certificates[name])
                self.assertIn("private theorem _const_eq_store", text)
                self.assertIn("simp only [", text)
                self.assertIn("_select_const, ite_self, ← _const_store_self, _const_eq_store, _store_eq_const, "
                              "_store_store, _store_select] at *)", text)
        # Store chains over two constant arrays compared: the converse of
        # the equality, one premise per stored index, proved by funext and
        # _store_off.
        for name, premises in (("store_over_another_constant", 1), ("store_chains_over_two_constants", 2),
                               ("store_against_an_ite_of_one_constant", 1),
                               ("real_index_store_over_another_constant", 1)):
            with self.subTest(name=name):
                text = proof_to_lean.reconstruct(ARRAY_INPUTS[name], self.certificates[name])
                self.assertIn("private theorem _store_off", text)
                facts = [line for line in text.split("\n") if re.match(r"\s*have _x\d+ : _select ", line)]
                self.assertTrue(facts, text)
                for fact in facts:
                    self.assertEqual(fact.count("_select "), 2 * premises, fact)
                    self.assertIn("funext _j; by_cases _c0 : _j = ", fact)
                    self.assertIn("(_store_off ", fact)
        text = proof_to_lean.reconstruct(ARRAY_INPUTS["store_against_an_ite_of_one_constant"],
                                         self.certificates["store_against_an_ite_of_one_constant"])
        self.assertIn("(congrFun (ite_self ", text)
        # Ites of different chains: one converse per pair of a leaf of one
        # side with a leaf of the other, stated over the leaves' terms; none
        # above _ITE_CHAIN_PAIRS pairs.
        # The premises are the reads at the indices stored into either leaf
        # of the pair (none for two constant arrays).
        for name, premises in (("ite_of_chains_against_a_chain", [1, 2]),
                               ("ites_of_chains_on_both_sides", [0, 1, 1, 2]), ("nested_ites_of_chains", [1, 2, 2])):
            with self.subTest(name=name):
                text = proof_to_lean.reconstruct(ARRAY_INPUTS[name], self.certificates[name])
                facts = dict(((fact[0], int(fact[1])), fact[2])
                             for fact in re.findall(r"\n\s*have (_x\d+)_(\d+) : (.*) := by intro ", text))
                self.assertEqual(len({equality for equality, _ in facts}), 1, text)
                pairs = len(premises)
                self.assertEqual({position for _, position in facts}, set(range(pairs)), text)
                self.assertEqual(sorted(statement.count("_select ") // 2 for statement in facts.values()), premises)
                with mock.patch.object(proof_to_lean, "_ITE_CHAIN_PAIRS", pairs - 1):
                    text = proof_to_lean.reconstruct(ARRAY_INPUTS[name], self.certificates[name])
                self.assertIsNone(re.search(r"have _x\d+_\d+ : ", text))
        # Above _COMPARISON_READS (13 arrays and the equality at 6 stored
        # indices: 84 reads) only the compared chains' reads are stated:
        # each chain read at the 6 indices down to the outermost store at
        # that index (21 levels on the left, 15 on the right) or, at index
        # 0 on the right, past all 5 stores to the constant.
        text = proof_to_lean.reconstruct(ARRAY_INPUTS["long_store_chains_over_two_constants"],
                                         self.certificates["long_store_chains_over_two_constants"])
        rewrite = text.split("private theorem rewrite_", 1)[1].split("\n    | ", 2)[1]
        with mock.patch.object(proof_to_lean, "_COMPARISON_READS", 10 ** 9):
            full = proof_to_lean.reconstruct(ARRAY_INPUTS["long_store_chains_over_two_constants"],
                                             self.certificates["long_store_chains_over_two_constants"])
        full = full.split("private theorem rewrite_", 1)[1].split("\n    | ", 2)[1]
        self.assertEqual(len(re.findall(r"have _(?:e|ds|dc)\d+_\d+ ", full)), 13 * 6 + 6, full)
        self.assertGreater(13 * 6 + 6, proof_to_lean._COMPARISON_READS)
        self.assertEqual(len(re.findall(r"have _e\d+_\d+ ", rewrite)), 6, rewrite)
        self.assertEqual(len(re.findall(r"have _ds\d+_\d+ := _store_apply ", rewrite)), 21 + 15 + 5, rewrite)
        self.assertEqual(len(re.findall(r"have _dc\d+_\d+ := _select_const ", rewrite)), 1, rewrite)
        self.assertEqual(len(re.findall(r"have _x\d+ : ", rewrite)), 1, rewrite)
        # A read of an ite over arrays: each constant-array branch's read.
        text = proof_to_lean.reconstruct(ARRAY_INPUTS["read_of_an_ite_over_a_constant"],
                                         self.certificates["read_of_an_ite_over_a_constant"])
        self.assertRegex(text, r"have _si\d+_0 := _select_const \(I := Int\) \(_vars \d+\) ")

    def test_ites_of_store_chains_are_walked_once(self):
        """The leaves of a shared ite DAG are found in linear time, and an equality with more than _ITE_CHAIN_PAIRS
        pairs of leaves has no chain-comparison reads (it gets no converse to use them)."""

        class Graph:
            def __init__(self):
                self.nodes = []

            def add(self, kind, *arguments):
                self.nodes.append((kind, arguments))
                return len(self.nodes) - 1

            def kind(self, node):
                return self.nodes[node][0]

            def arguments(self, node):
                return self.nodes[node][1]

        graph = Graph()
        condition = graph.add(z3.Z3_OP_UNINTERPRETED)
        value = graph.add(z3.Z3_OP_UNINTERPRETED)
        constant = graph.add(z3.Z3_OP_CONST_ARRAY, value)
        store = graph.add(z3.Z3_OP_STORE, constant, value, value)
        # a_{i+1} = ite(p, a_i, b_i), b_{i+1} = ite(p, b_i, a_i): 2^60 paths
        # to the two leaves when shared ites are walked as a tree.
        first, second = store, constant
        for _ in range(60):
            first, second = (graph.add(z3.Z3_OP_ITE, condition, first, second),
                             graph.add(z3.Z3_OP_ITE, condition, second, first))
        self.assertEqual(proof_to_lean._constant_chain_leaves(graph, first), [constant, store])
        equality = graph.add(z3.Z3_OP_EQ, first, store)
        compared, _ = proof_to_lean._chain_comparison_reads(graph, [equality])
        self.assertEqual(compared, {equality: {value}})
        # One side with n different chains against a chain: n pairs.
        for chains, expected in ((proof_to_lean._ITE_CHAIN_PAIRS, True), (proof_to_lean._ITE_CHAIN_PAIRS + 1, False)):
            with self.subTest(chains=chains):
                side = graph.add(z3.Z3_OP_STORE, constant, graph.add(z3.Z3_OP_UNINTERPRETED), value)
                for _ in range(chains - 1):
                    leaf = graph.add(z3.Z3_OP_STORE, constant, graph.add(z3.Z3_OP_UNINTERPRETED), value)
                    side = graph.add(z3.Z3_OP_ITE, condition, leaf, side)
                self.assertEqual(len(proof_to_lean._constant_chain_leaves(graph, side)), chains)
                equality = graph.add(z3.Z3_OP_EQ, side, store)
                compared, _ = proof_to_lean._chain_comparison_reads(graph, [equality])
                self.assertEqual(equality in compared, expected)

    def test_reads_of_arrays_compared_with_constant_arrays(self):
        """A cnf lemma reading an array equated to a constant array gets the constant array's reads.

        The cnf lemmas (not (= a K)) \\/ (not (= 3 (select a i))), for i = k
        and i = 0, read only a; each gets the read of the constant array K
        at its i (_compared_side_reads), none above _COMPARISON_READS.
        """
        for name, index_type in (("read_of_an_array_equated_to_a_constant", "Int"),
                                 ("real_read_of_an_array_equated_to_a_constant", "Rat")):
            with self.subTest(name=name):
                text = proof_to_lean.reconstruct(ARRAY_INPUTS[name], self.certificates[name])
                cnf = [lemma.split("\n\n")[0] for lemma in text.split("private theorem th_lemma_")[1:]
                       if re.search(r"have _e\d+ : ", lemma.split("\n\n")[0])]
                self.assertEqual(len(cnf), 2, text)
                for lemma in cnf:
                    reads = re.findall(r"have _dc\d+_\d+ := _select_const \(I := %s\) " % index_type, lemma)
                    self.assertEqual(len(reads), 1, lemma)
        with mock.patch.object(proof_to_lean, "_COMPARISON_READS", 0):
            text = proof_to_lean.reconstruct(ARRAY_INPUTS["read_of_an_array_equated_to_a_constant"],
                                             self.certificates["read_of_an_array_equated_to_a_constant"])
        self.assertNotRegex(text, r"have _dc\d+_\d+ ")

    def test_extensionality_witnesses_commute(self):
        text = proof_to_lean.reconstruct(ARRAY_INPUTS["commuted_extensionality_witnesses"],
                                         self.certificates["commuted_extensionality_witnesses"])
        self.assertIn("private theorem _array_diff_comm ", text)
        witnesses = re.findall(r"have _x(\d+) := _array_ext ", text)
        self.assertEqual(len(set(witnesses)), 2, text)
        for node in witnesses:
            self.assertIn("have _xc%s := _array_diff_comm " % node, text)

    def test_chain_comparison_reads_are_bounded(self):
        """Above _CHAIN_COMPARISON_READS the compared chains' reads are dropped too.

        Two 32-store chains over (const 0) and (const 1), equal under a
        guard, have 32 * 34 reads. With them Lean took 7.7 s and 3.5 GB, and
        at 64 stores more than the 12 GB watchdog; without them it checks
        in about 1 s, since the rewriter decides the comparison by the
        defaults alone.
        """
        def chain(default):
            array = "((as const (Array Int Int)) %d)" % default
            for k in range(32):
                array = "(store %s %d u%d)" % (array, k, k)
            return array

        source = "\n".join(["(set-logic QF_ALIA)", "(declare-const p Bool)"] +
                           ["(declare-const u%d Int)" % k for k in range(32)] +
                           ["(assert (or p (= %s %s)))" % (chain(0), chain(1)), "(assert (not p))",
                            "(check-sat)"]) + "\n"
        certificate = _export(source)
        read = re.compile(r"have _(?:e|ds|dc)\d+_\d+ ")
        with mock.patch.object(proof_to_lean, "_CHAIN_COMPARISON_READS", 10 ** 9):
            unbounded = proof_to_lean.reconstruct(source, certificate)
        rewrite = unbounded.split("private theorem rewrite_", 1)[1].split("\n    | ", 2)[1]
        self.assertEqual(len(read.findall(rewrite)), 32 * 34)
        self.assertGreater(32 * 34, proof_to_lean._CHAIN_COMPARISON_READS)
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertNotRegex(text, read)
        self.assertRegex(text, r"have _e\d+ : ")

    def test_tampered_constant_arrays_are_rejected(self):
        def declaration(certificate, kind):
            return next(d for d in certificate["declarations"] if d["kind"] == kind)

        def const_of_real(certificate):
            declaration(certificate, z3.Z3_OP_CONST_ARRAY)["domain"] = ["Real"]

        def renamed_const(certificate):
            declaration(certificate, z3.Z3_OP_CONST_ARRAY)["name"] = "store"

        def default_into_real(certificate):
            declaration(certificate, z3.Z3_OP_ARRAY_DEFAULT)["range"] = "Real"

        def uninterpreted_indices(index):
            # Default values need an infinite index type: over Element
            # indices (a sort that may be finite) the declarations are
            # rejected, not proved.
            def tamper(certificate):
                array = "(Array %s Element)" % index
                for d in certificate["declarations"]:
                    d["domain"] = ["(Array Element Element)" if s == array else s for s in d["domain"]]
                    if d["range"] == array:
                        d["range"] = "(Array Element Element)"
            return tamper

        def const_value_of_int(certificate):
            # The const's value (the element), not its index, relabelled to Int.
            declaration(certificate, z3.Z3_OP_CONST_ARRAY)["domain"] = ["Int"]

        def relabelled_sort(old, new):
            # One array sort renamed in every string of the certificate: the
            # certificate stays consistent, so only the comparison with the
            # input's own declarations catches it.
            def relabel(value):
                if isinstance(value, str):
                    return value.replace(old, new)
                if isinstance(value, list):
                    return [relabel(item) for item in value]
                if isinstance(value, dict):
                    return {key: relabel(item) for key, item in value.items()}
                return value

            def tamper(certificate):
                self.assertIn(old, repr(certificate))
                certificate.update(relabel(certificate))
            return tamper

        self._rejects("z3test_2549", const_of_real, "invalid constant array declaration")
        self._rejects("z3test_2549", renamed_const, "invalid constant array declaration")
        self._rejects("z3test_2549", default_into_real, "invalid default declaration")
        self._rejects("element_constants", uninterpreted_indices("Int"),
                      "invalid (constant array|default) declaration")
        self._rejects("real_index_elements", uninterpreted_indices("Real"),
                      "invalid (constant array|default) declaration")
        self._rejects("real_index_2549", default_into_real, "invalid default declaration")
        self._rejects("real_index_read", const_value_of_int, "invalid constant array declaration")
        # Real indices relabelled to Int (or the element sort changed) consistently.
        self._rejects("real_index_2549", relabelled_sort("(Array Real Int)", "(Array Int Int)"),
                      "certificate source does not match the original input")
        self._rejects("real_index_read", relabelled_sort("(Array Real Real)", "(Array Int Real)"),
                      "certificate source does not match the original input")

    def test_array_function_encoding(self):
        """A function into arrays is a family per Lean array type; its applications are tied to their bodies."""
        text = proof_to_lean.reconstruct(ARRAY_INPUTS["function_into_arrays"],
                                         self.certificates["function_into_arrays"])
        self.assertIn("  arrs_funs : Nat -> List U -> U -> U", text)
        self.assertIn('-- Array function 0: "h"', text)
        self.assertIn("-- Functions into array sorts are the families _m.arrs_funs, one per Lean array type.", text)
        self.assertIn(": (_m.U -> _m.U) := _m.arrs_funs 0 [(term_", text)
        self.assertRegex(text, r"have _t[0-9]+ : \(term_[0-9]+ _atoms _m\) = _m\.arrs_funs 0 \[\(_m\.elems [0-9]+\)\]")
        integer = proof_to_lean.reconstruct(ARRAY_INPUTS["int_function_into_arrays"],
                                            self.certificates["int_function_into_arrays"])
        self.assertIn("  arrs_ii_funs : Nat -> List U -> Int -> Int", integer)
        self.assertIn(":= _m.arrs_ii_funs 0 [(_m.int (term_", integer)
        # Over arrays and into arrays: the argument's injection and the
        # result's family, both of the same Lean array type.
        twice = proof_to_lean.reconstruct(ARRAY_INPUTS["array_function_twice"],
                                          self.certificates["array_function_twice"])
        self.assertIn("  arrs_ii_inj : (Int -> Int) -> U", twice)
        self.assertIn(":= _m.arrs_ii_funs 0 [(_m.arrs_ii_inj (term_", twice)
        mixed = proof_to_lean.reconstruct(ARRAY_INPUTS["function_into_constant_arrays"],
                                          self.certificates["function_into_constant_arrays"])
        self.assertIn("  arrs_ir_funs : Nat -> List U -> Int -> Rat", mixed)
        # Without a function into arrays there is no such family.
        plain = proof_to_lean.reconstruct(ARRAY_INPUTS["function_over_arrays"],
                                          self.certificates["function_over_arrays"])
        self.assertNotIn("_funs", plain)
        self.assertNotIn("Array function", plain)
        for each in (text, integer, twice, mixed):
            self.assertNotIn("sorry", each)
            self.assertNotIn("axiom ", each)

    def test_tampered_array_functions_are_rejected(self):
        def function(certificate, name):
            return next(d for d in certificate["declarations"] if d["name"] == name)

        def proof_argument(certificate):
            function(certificate, "h")["domain"] = ["Proof"]

        def array_constant(certificate):
            # The application turned into a constant of the array sort.
            function(certificate, "h")["domain"] = []

        def element_argument(certificate):
            function(certificate, "h")["domain"] = ["Element"]

        def into_real_arrays(certificate):
            function(certificate, "f")["range"] = "(Array Int Real)"

        def swapped_functions(certificate):
            # Two functions of the same signature exchanged: the certificate
            # stays well-formed, so only the binding to the input catches it.
            first, second = function(certificate, "f"), function(certificate, "g")
            first["name"], second["name"] = "g", "f"

        def renamed_function(certificate):
            function(certificate, "g")["name"] = "f2"

        self._rejects("function_into_arrays", proof_argument, "unsupported array declaration")
        self._rejects("function_into_arrays", array_constant, "wrong number of arguments")
        self._rejects("function_into_arrays", element_argument, "wrong argument sort")
        self._rejects("int_function_into_arrays", into_real_arrays, "wrong argument sort")
        self._rejects("two_functions_into_arrays", swapped_functions,
                      "certificate (source|assertions) do(es)? not match the original input")
        self._rejects("two_functions_into_arrays", renamed_function,
                      "certificate (source|assertions) do(es)? not match the original input")

    def test_bool_element_encoding(self):
        """An array with Bool elements is a predicate I -> Prop; reads, defaults, and stored values are formulas."""
        sets = proof_to_lean.reconstruct(ARRAY_INPUTS["set_insert_elsewhere"],
                                         self.certificates["set_insert_elsewhere"])
        self.assertIn("  arrs_ib : Nat -> Int -> Prop", sets)
        self.assertIn('-- Array sorts "(Array Int Bool)" are functions Int -> Prop (_m.arrs_ib)', sets)
        self.assertRegex(sets, r"def formula_[0-9]+ \(_atoms : Nat -> Prop\) \(_vars : Nat -> Int\) "
                               r"\(_m : Interpretation\) : Prop := \(_select \(term_")
        # The stored value true is the formula True.
        self.assertRegex(sets, r":= \(_store \(term_[0-9]+ [^)]*\) \(term_[0-9]+ [^)]*\) \(formula_")
        self.assertRegex(sets, r"have _s[0-9]+ := _store_apply \(\(term_[0-9]+ [^)]*\)\) \(_vars 0\) \(True\)")
        carrier = proof_to_lean.reconstruct(ARRAY_INPUTS["bool_read_own_write"],
                                            self.certificates["bool_read_own_write"])
        self.assertIn("  arrs_ub : Nat -> U -> Prop", carrier)
        defaults = proof_to_lean.reconstruct(ARRAY_INPUTS["full_is_not_empty"], self.certificates["full_is_not_empty"])
        self.assertRegex(defaults, r": Prop := \(_default _int_unbounded \(term_")
        self.assertIn("(@_const_array Int Prop (formula_", defaults)
        functions = proof_to_lean.reconstruct(ARRAY_INPUTS["function_into_sets"],
                                              self.certificates["function_into_sets"])
        self.assertIn("  arrs_ub_funs : Nat -> List U -> U -> Prop", functions)
        over = proof_to_lean.reconstruct(ARRAY_INPUTS["function_over_sets"], self.certificates["function_over_sets"])
        self.assertIn("  arrs_ib_inj : (Int -> Prop) -> U", over)
        real = proof_to_lean.reconstruct(ARRAY_INPUTS["real_set"], self.certificates["real_set"])
        self.assertIn("  arrs_rb : Nat -> Rat -> Prop", real)
        # The array solver's store axiom over a Boolean value is a Bool
        # equality, admitted in an array lemma only next to Bool elements.
        certificate = self.certificates["bool_read_own_write"]
        graph = proof_to_lean._validate_graph(ARRAY_INPUTS["bool_read_own_write"], certificate)
        lemmas = [node for node in range(len(graph.nodes)) if graph.kind(node) == z3.Z3_OP_PR_TH_LEMMA
                  and graph.decl(node).parameters[0] == "array"]
        self.assertTrue(any(graph.decl(graph.arguments(graph.conclusion(node))[0]).range == "Bool"
                            for node in lemmas))
        for each in (sets, carrier, defaults, functions, over, real):
            self.assertNotIn("sorry", each)
            self.assertNotIn("axiom ", each)

    def test_bool_index_encoding(self):
        """An array over Bool indices is a function Prop -> E; indices and the extensionality witness are formulas."""
        def text(name):
            return proof_to_lean.reconstruct(ARRAY_INPUTS[name], self.certificates[name])

        extensionality = text("bool_index_extensionality")
        self.assertIn("  arrs_bi : Nat -> Prop -> Int", extensionality)
        self.assertIn('-- Array sorts "(Array Bool Int)" are functions Prop -> Int (_m.arrs_bi)', extensionality)
        # The witness is a formula, chosen with Prop's inhabitant True.
        self.assertRegex(extensionality, r"def formula_[0-9]+ \(_atoms : Nat -> Prop\) \(_vars : Nat -> Int\) "
                                         r"\(_m : Interpretation\) : Prop := \(_array_diff \(Nonempty.intro True\) ")
        self.assertRegex(extensionality, r"have _x[0-9]+ := _array_ext \(Nonempty.intro True\) ")
        self.assertNotIn("nonempty :", extensionality)
        self.assertRegex(extensionality, r": Int := \(_select \(term_[0-9]+ [^)]*\) \(formula_")
        self.assertIn("  arrs_bu : Nat -> Prop -> U", text("bool_index_store_self"))
        self.assertIn("  arrs_bb : Nat -> Prop -> Prop", text("z3test_5798"))
        self.assertIn("  arrs_bu_funs : Nat -> List U -> Prop -> U", text("function_into_bool_indexed_arrays"))
        # A function over such arrays applies to the array's injection into U.
        over = text("function_over_bool_indexed_arrays")
        self.assertIn("  arrs_bi_inj : (Prop -> Int) -> U", over)
        self.assertRegex(over, r":= _m\.ifuns 0 \[\(_m\.arrs_bi_inj \(term_[0-9]+ ")
        # Both levels of a read at true through a store at false.
        through = text("bool_index_read_through_value_stores")
        self.assertRegex(through, r"have _s[0-9]+ := _store_apply \(\(term_[0-9]+ [^)]*\)\) \(False\) "
                                  r"\(\(\(2 : Int\)\)\) \(True\)\n")
        self.assertRegex(through, r"have _s[0-9]+_1 := _store_apply \(\(term_[0-9]+ [^)]*\)\) \(True\) "
                                  r"\(\(\(1 : Int\)\)\) \(True\)\n")
        # The gate clause's (not (not p)) is concluded as p by contradiction.
        negated = text("bool_index_negated_stores")
        self.assertRegex(negated, r"\(fun _literal => \(@Decidable\.byContradiction \(formula_([0-9]+) "
                                  r"[^)]*\) _df\1 _literal\)\) \(fun _tail => _tail\)")
        for each in (extensionality, through, negated):
            self.assertNotIn("sorry", each)
            self.assertNotIn("axiom ", each)

    def test_tampered_bool_index_arrays_are_rejected(self):
        def witness_into_int(certificate):
            next(d for d in certificate["declarations"] if d["kind"] == z3.Z3_OP_ARRAY_EXT)["range"] = "Int"

        def const_over_bool(certificate):
            # The read at true (a Bool-indexed array constant) relabelled a constant array.
            array = next(d for d in certificate["declarations"]
                         if d["kind"] == z3.Z3_OP_UNINTERPRETED and d["range"] == "(Array Bool Int)")
            array.update(kind=z3.Z3_OP_CONST_ARRAY, name="const", domain=["Int"])

        def double_negation_concluded_negated(certificate):
            # The unit resolution concluding p from the gate clause (or (not
            # (= (not p) p)) (not (not p)) p) concludes (not p) instead.
            graph = proof_to_lean._validate_graph(ARRAY_INPUTS["bool_index_negated_stores"], certificate)
            for node in range(len(graph.nodes)):
                if graph.kind(node) != z3.Z3_OP_PR_UNIT_RESOLUTION:
                    continue
                literals = graph.clause(graph.conclusion(graph.arguments(node)[0]))
                doubles = [literal for literal in literals if graph.kind(literal) == z3.Z3_OP_NOT
                           and graph.kind(graph.arguments(literal)[0]) == z3.Z3_OP_NOT]
                if doubles and graph.kind(graph.conclusion(node)) == z3.Z3_OP_UNINTERPRETED:
                    negation = graph.arguments(doubles[0])[0]
                    certificate["nodes"][node]["arguments"][-1] = negation
                    return
            self.fail("no unit resolution over a double negation")

        self._rejects("bool_index_extensionality", witness_into_int, "invalid array-ext declaration")
        self._rejects("bool_index_read_other", const_over_bool, "invalid constant array declaration")
        self._rejects("bool_index_negated_stores", double_negation_concluded_negated,
                      "incorrect unit-resolution conclusion")

    def test_nested_array_encoding(self):
        """A nested array is a function into or over functions; witnesses over array indices are constant functions."""
        def text(name):
            return proof_to_lean.reconstruct(ARRAY_INPUTS[name], self.certificates[name])

        over = text("function_over_nested")
        self.assertIn('-- Array sorts "(Array Int (Array Int Int))", "(Array Int Int)" are functions '
                      'Int -> (Int -> Int) (_m.arrs_iaii), Int -> Int (_m.arrs_ii);', over)
        self.assertIn("  arrs_iaii : Nat -> Int -> (Int -> Int)", over)
        self.assertIn("  arrs_iaii_inj : (Int -> (Int -> Int)) -> U", over)
        # A row is a read of an array-valued type.
        self.assertRegex(text("nested_store_row"), r"def term_[0-9]+ \(_atoms : Nat -> Prop\) \(_vars : Nat -> Int\) "
                                                   r"\(_m : Interpretation\) : \(Int -> Int\) := \(_select \(term_")
        self.assertIn("  arrs_iaiaii : Nat -> Int -> (Int -> (Int -> Int))", text("three_levels"))
        self.assertIn("  arrs_iaib : Nat -> Int -> (Int -> Prop)", text("nested_sets"))
        self.assertIn("  arrs_uauu : Nat -> U -> (U -> U)", text("nested_uninterpreted"))
        self.assertIn("  arrs_iaii_funs : Nat -> List U -> Int -> (Int -> Int)", text("function_into_nested"))
        self.assertIn("  arrs_rair : Nat -> Rat -> (Int -> Rat)", text("real_nested"))
        # Over array indices the witness is an array, chosen with a constant
        # function from the element type's inhabitant.
        index = text("array_index_extensionality")
        self.assertIn("  arrs_aiii : Nat -> (Int -> Int) -> Int", index)
        inhabitant = "(Nonempty.elim (Nonempty.intro (0 : Int)) (fun _e => Nonempty.intro (fun (_ : Int) => _e)))"
        self.assertIn(": (Int -> Int) := (_array_diff %s (term_" % inhabitant, index)
        self.assertIn(":= _array_ext %s " % inhabitant, index)
        self.assertNotIn("nonempty :", index)
        carrier = text("uninterpreted_array_index_extensionality")
        self.assertIn("  nonempty : Nonempty U", carrier)
        self.assertIn("  arrs_auub : Nat -> (U -> U) -> Prop", carrier)
        self.assertIn(":= _array_ext (Nonempty.elim _m.nonempty (fun _e => Nonempty.intro (fun (_ : _m.U) => _e))) ",
                      carrier)
        for each in (over, index, carrier):
            self.assertNotIn("sorry", each)
            self.assertNotIn("axiom ", each)

    def test_array_sort_names(self):
        """Certificate array sort names parse into their components, nested arrays too; malformed ones do not."""
        components = proof_to_lean._array_components
        self.assertEqual(components("(Array Int Bool)"), ("Int", "Bool"))
        self.assertEqual(components("(Array Int (Array U Bool))"), ("Int", "(Array U Bool)"))
        self.assertEqual(components("(Array (Array Int Int) (Array Bool (Array U Real)))"),
                         ("(Array Int Int)", "(Array Bool (Array U Real))"))
        for name in ("Int", "(Array Int)", "(Array Int Int Int)", "(Array Int (Array Int))", "(Array Int Int",
                     "(Array (Int) Int)", "(Array  Int Int)", "(Array Int (Array Int Int)))", "(Array |a b| Int)",
                     "(Array Int (Array Int Int) )", "(Array Int )(Array Int Int)"):
            with self.subTest(name=name):
                self.assertIsNone(components(name))
        self.assertEqual(proof_to_lean._array_family("(Array (Array Int Int) (Array Bool U))"), "arrs_aiiabu")
        # A tampered name nested past the cap is no sort name (not a RecursionError).
        deep = "Int"
        for _ in range(2000):
            deep = "(Array Int %s)" % deep
        self.assertIsNone(components(deep))
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "unsupported sort"):
            proof_to_lean._uninterpreted_sorts([{"range": deep}])

    def test_connectives_over_array_indexed_sets_are_rejected(self):
        """The reconstructor rejects maps and set operators over sets indexed by arrays, not over rows of sets."""
        def declaration(kind, name, sort, arity):
            return {"kind": kind, "name": name, "domain": [sort] * arity, "range": sort, "parameters": []}

        rows = "(Array Int Bool)"
        proof_to_lean._declaration(declaration(z3.Z3_OP_SET_UNION, "union", rows, 2), (rows,))
        for sort in ("(Array (Array Int Int) Bool)", "(Array (Array Bool Bool) Bool)"):
            for kind, name, arity in ((z3.Z3_OP_SET_UNION, "union", 2), (z3.Z3_OP_SET_COMPLEMENT, "complement", 1)):
                with self.subTest(sort=sort, name=name):
                    with self.assertRaisesRegex(proof_to_lean.ReconstructionError,
                                                "invalid map or set operator declaration"):
                        proof_to_lean._declaration(declaration(kind, name, sort, arity), (sort,))

    def test_tampered_nested_arrays_are_rejected(self):
        def row_read_into_element(certificate):
            # The read of a row relabelled as a read of one element.
            next(d for d in certificate["declarations"] if d["kind"] == z3.Z3_OP_SELECT
                 and d["range"] == "(Array Int Int)")["range"] = "Int"

        def malformed_inner_sort(certificate):
            for d in certificate["declarations"]:
                d["domain"] = ["(Array Int (Array Int))" if s == "(Array Int (Array Int Int))" else s
                               for s in d["domain"]]
                if d["range"] == "(Array Int (Array Int Int))":
                    d["range"] = "(Array Int (Array Int))"

        def witness_into_element(certificate):
            # The witness over array indices relabelled an Int.
            next(d for d in certificate["declarations"] if d["kind"] == z3.Z3_OP_ARRAY_EXT)["range"] = "Int"

        def proof_element(certificate):
            for d in certificate["declarations"]:
                if d["range"] == "(Array Int (Array Int Int))":
                    d["range"] = "(Array Int (Array Int Proof))"

        self._rejects("nested_store_row", row_read_into_element, "invalid select declaration|wrong argument sort")
        self._rejects("nested_store_row", malformed_inner_sort, "unsupported sort")
        self._rejects("array_index_extensionality", witness_into_element, "invalid array-ext declaration")
        self._rejects("nested_store_row", proof_element, "unsupported array sort")

    def test_store_level_facts(self):
        """Reads get facts for the store levels the rewriter skips, and only for those, over plain arrays."""
        def levels(name):
            text = proof_to_lean.reconstruct(ARRAY_INPUTS[name], self.certificates[name])
            return re.findall(r"have (_s\d+(?:_\d+)?) := (_store_apply|_select_const) ", text)

        # (select (store (store a 1 5) 2 7) 3): the levels at 2 and at 1.
        facts = levels("read_through_numeral_stores")
        self.assertTrue(any(name.count("_") == 2 and name.endswith("_1") for name, _ in facts), facts)
        self.assertFalse(any(name.count("_") == 2 and not name.endswith("_1") for name, _ in facts), facts)
        # Stores at 4, 2, 1 over a plain set read at 3: levels 0 to 2.
        facts = levels("set_read_through_numeral_stores")
        self.assertTrue(any(name.endswith("_2") for name, _ in facts), facts)
        self.assertFalse(any(name.endswith("_3") for name, _ in facts), facts)
        # Stores at 2 and 3 read at 3: the skipped level and the one at 3.
        facts = levels("read_through_numeral_stores_to_own_index")
        self.assertTrue(any(name.endswith("_1") for name, _ in facts), facts)
        self.assertFalse(any(name.endswith("_2") for name, _ in facts), facts)
        # Stores at 1, 2 over a set read at 3, the skip stopping at 3: levels 0 to 2.
        facts = levels("set_read_through_numeral_stores_to_own_index")
        self.assertTrue(any(name.endswith("_2") for name, _ in facts), facts)
        self.assertFalse(any(name.endswith("_3") for name, _ in facts), facts)
        # Stores at -2 and -1 read at 3: both levels, not the plain array.
        facts = levels("read_through_negative_numeral_stores")
        self.assertTrue(any(name.endswith("_1") for name, _ in facts), facts)
        self.assertFalse(any(name.endswith("_2") for name, _ in facts), facts)
        # Stores at symbolic indices over a plain array: one level per read.
        facts = levels("bool_store_chain")
        self.assertTrue(facts)
        self.assertEqual([name for name, _ in facts if name.count("_") == 2], [])
        # Stores over a constant array: every level and the constant.
        facts = levels("read_of_store_over_constant")
        self.assertIn("_select_const", [fact for _, fact in facts])

    def test_tampered_bool_element_arrays_are_rejected(self):
        def relabelled(source, target):
            def mutate(certificate):
                for d in certificate["declarations"]:
                    d["domain"] = [target if s == source else s for s in d["domain"]]
                    if d["range"] == source:
                        d["range"] = target
            return mutate

        def select_into_int(certificate):
            next(d for d in certificate["declarations"] if d["kind"] == z3.Z3_OP_SELECT)["range"] = "Int"

        def store_of_index(certificate):
            store = next(d for d in certificate["declarations"] if d["kind"] == z3.Z3_OP_STORE)
            store["domain"] = store["domain"][:2] + ["Int"]

        # Bool indices are supported, but the stores and reads stay at Int indices.
        self._rejects("set_insert_elsewhere", relabelled("(Array Int Bool)", "(Array Bool Bool)"),
                      "invalid select declaration|invalid store declaration|wrong argument sort")
        self._rejects("set_insert_elsewhere", relabelled("(Array Int Bool)", "(Array Int Int)"),
                      "invalid select declaration|invalid store declaration|wrong argument sort")
        self._rejects("set_insert_elsewhere", select_into_int, "invalid select declaration|wrong argument sort")
        self._rejects("set_insert_elsewhere", store_of_index, "invalid store declaration")
        # The input's sort is bound: Bool elements over another index sort.
        self._rejects("bool_read_own_write", relabelled("(Array Index Bool)", "(Array Index Index)"),
                      "invalid select declaration|invalid store declaration|wrong argument sort")

    def test_set_combinator_encoding(self):
        """Maps and set operators are _map1/_map2 of a function over Prop; reads of them get pointwise facts."""
        certificate = self.certificates["z3test_t8"]
        maps = _declarations(certificate, z3.Z3_OP_ARRAY_MAP)
        self.assertEqual(sorted(d["parameters"][0] for d in maps), ["and", "not", "or"])
        text = proof_to_lean.reconstruct(ARRAY_INPUTS["z3test_t8"], certificate)
        self.assertRegex(text, r":= \(_map2 And \(term_\d+ [^)]*\) \(term_\d+ [^)]*\)\)")
        self.assertRegex(text, r":= \(_map1 Not \(term_\d+ [^)]*\)\)")
        # The read of the outer complement, then the three maps below it.
        self.assertRegex(text, r"have _m\d+_3 : _select ")
        self.assertRegex(text, r"have _mc\d+ := _map2_or_comm ")
        sets = proof_to_lean.reconstruct(ARRAY_INPUTS["union_member"], self.certificates["union_member"])
        self.assertIn("(_map2 Or (term_", sets)
        self.assertIn("(_map1 Not (term_", sets)
        difference = proof_to_lean.reconstruct(ARRAY_INPUTS["setminus_disjoint"],
                                               self.certificates["setminus_disjoint"])
        self.assertIn("(_map2 (fun _p _q : Prop => And _p (Not _q)) (term_", difference)
        # Every set operator either shares its Lean function with the map
        # Z3's rewriter turns it into or, for setminus, states the identity.
        self.assertEqual({kind: proof_to_lean._SET_OPERATOR_FUNCTIONS[kind] for kind in
                          (z3.Z3_OP_SET_UNION, z3.Z3_OP_SET_INTERSECT, z3.Z3_OP_SET_COMPLEMENT)},
                         {z3.Z3_OP_SET_UNION: proof_to_lean._MAP_CONNECTIVES["or"][0],
                          z3.Z3_OP_SET_INTERSECT: proof_to_lean._MAP_CONNECTIVES["and"][0],
                          z3.Z3_OP_SET_COMPLEMENT: proof_to_lean._MAP_CONNECTIVES["not"][0]})
        self.assertEqual(set(proof_to_lean._SET_OPERATOR_FUNCTIONS), set(proof_certificate.SET_OPERATORS))
        named = proof_to_lean.reconstruct(ARRAY_INPUTS["setminus_named"], self.certificates["setminus_named"])
        self.assertRegex(named, r"have _md\d+ : .+ = _map2 And .+ \(_map1 Not .+\) := rfl")
        implication = proof_to_lean.reconstruct(ARRAY_INPUTS["implication_map"], self.certificates["implication_map"])
        self.assertIn("(_map2 (fun _p _q : Prop => _p -> _q) (term_", implication)
        constants = proof_to_lean.reconstruct(ARRAY_INPUTS["map_of_store_and_constant"],
                                              self.certificates["map_of_store_and_constant"])
        self.assertRegex(constants, r"have _mk\d+_1 := _const_store_self ")
        self.assertRegex(constants, r"have _ms\d+ := _map2_store Or ")
        for each in (text, sets, difference, implication, constants):
            self.assertNotIn("sorry", each)
            self.assertNotIn("axiom ", each)
        # The array solver's default values of maps over an uninterpreted
        # index sort occur in gate clauses the refutation does not use; the
        # certificate leaves them out (the reconstructor rejects such defaults).
        for name in ("map_equal_sets", "map_under_function"):
            self.assertEqual(_declarations(self.certificates[name], z3.Z3_OP_ARRAY_DEFAULT), [])

    def test_default_values_of_maps_are_rejected(self):
        """The default-map axiom holds only for arrays constant almost everywhere, which Lean cannot assume."""
        source = """(declare-fun a () (Array Int Bool))
(declare-fun b () (Array Int Bool))
(declare-fun x () Int)
(assert (= ((_ map =>) a b) ((as const (Array Int Bool)) true)))
(assert (select a x))
(assert (not (select b x)))
(check-sat)
"""
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "the default value of a map is not certified"):
            _export(source)

    def test_tampered_set_combinators_are_rejected(self):
        def parameter(value):
            def mutate(certificate):
                next(d for d in certificate["declarations"] if d["kind"] == z3.Z3_OP_ARRAY_MAP
                     and d["parameters"] == ["and"])["parameters"] = value
            return mutate

        def relabelled(source, target, name):
            def mutate(certificate):
                declaration = next(d for d in certificate["declarations"] if d["kind"] == source)
                declaration["kind"], declaration["name"] = target, name
            return mutate

        def map_into_int(certificate):
            declaration = next(d for d in certificate["declarations"] if d["kind"] == z3.Z3_OP_ARRAY_MAP
                               and d["parameters"] == ["not"])
            declaration["domain"] = ["(Array Int Int)"]
            declaration["range"] = "(Array Int Int)"

        def unary_and(certificate):
            declaration = next(d for d in certificate["declarations"] if d["kind"] == z3.Z3_OP_ARRAY_MAP
                               and d["parameters"] == ["and"])
            declaration["domain"] = declaration["domain"][:1]

        # A different connective proves another statement than the input's.
        self._rejects("z3test_t8", parameter(["or"]), "certificate assertions do not match the original input")
        self._rejects("z3test_t8", parameter(["xor"]), "certificate assertions do not match the original input")
        self._rejects("z3test_t8", parameter(["*"]), "a map takes one supported function")
        self._rejects("z3test_t8", parameter([]), "a map takes one supported function")
        self._rejects("z3test_t8", parameter(["and", "or"]), "a map takes one supported function")
        self._rejects("z3test_t8", parameter(["declared"]), "a map takes one supported function")
        self._rejects("z3test_t8", parameter(["+"]), "invalid map or set operator declaration")
        self._rejects("z3test_t8", unary_and, "invalid map or set operator declaration")
        self._rejects("z3test_t8", map_into_int, "invalid map or set operator declaration|unsupported array sort")
        self._rejects("union_member", relabelled(z3.Z3_OP_SET_INTERSECT, z3.Z3_OP_SET_UNION, "union"),
                      "certificate assertions do not match the original input")

    def test_map_function_encoding(self):
        """Maps of other functions are _map1/_map2/_map3 of a lambda; a mapped function is a symbol of the input."""
        certificate = self.certificates["mapped_function_congruence"]
        self.assertEqual([d["parameters"] for d in _declarations(certificate, z3.Z3_OP_ARRAY_MAP)],
                         [["declared", "f"]])
        # f is never applied: the map binds it, and Lean numbers it with the Int functions.
        self.assertNotIn("f", [d["name"] for d in _declarations(certificate, z3.Z3_OP_UNINTERPRETED)])
        text = proof_to_lean.reconstruct(ARRAY_INPUTS["mapped_function_congruence"], certificate)
        self.assertIn('-- Int function 0: "f"', text)
        self.assertIn("(_map1 (fun (_v0 : Int) => (_m.ifuns 0 [(_m.int _v0)])) (term_", text)
        addition = proof_to_lean.reconstruct(ARRAY_INPUTS["addition_commutes"], self.certificates["addition_commutes"])
        self.assertIn("(_map2 (fun (_v0 : Int) (_v1 : Int) => (_v0 + _v1)) (term_", addition)
        self.assertRegex(addition, r"have _mc\d+ := _map2_comm \(fun .*\) \(by intro _x _y; grind\) ")
        sort = proof_to_lean.reconstruct(ARRAY_INPUTS["map_over_sort"], self.certificates["map_over_sort"])
        self.assertIn("(_map2 (fun (_v0 : _m.U) (_v1 : _m.U) => (_m.funs 0 [_v0, _v1])) (term_", sort)
        predicate = proof_to_lean.reconstruct(ARRAY_INPUTS["map_predicate"], self.certificates["map_predicate"])
        self.assertIn("(_map1 (fun (_v0 : Int) => (_m.preds 0 [(_m.int _v0)])) (term_", predicate)
        choice = proof_to_lean.reconstruct(ARRAY_INPUTS["map_ite_symbolic"], self.certificates["map_ite_symbolic"])
        self.assertRegex(choice, r"noncomputable def term_\d+ .* := \(_map3 \(fun \(_v0 : Prop\) \(_v1 : Int\) "
                                 r"\(_v2 : Int\) => \(@ite Int _v0 \(Classical.propDecidable _\) _v1 _v2\)\)")
        nested = proof_to_lean.reconstruct(ARRAY_INPUTS["nested_function_maps"],
                                           self.certificates["nested_function_maps"])
        self.assertRegex(nested, r"have _m\d+_\d+ : _select .* = \(-\(_select ")
        for each in (text, addition, sort, predicate, choice, nested):
            self.assertNotIn("sorry", each)
            self.assertNotIn("axiom ", each)

    def test_tampered_map_functions_are_rejected(self):
        def parameter(name, old, new):
            def mutate(certificate):
                next(d for d in certificate["declarations"] if d["kind"] == z3.Z3_OP_ARRAY_MAP
                     and d["parameters"] == old)["parameters"] = new
            return mutate

        def elements(name, old, sort):
            def mutate(certificate):
                declaration = next(d for d in certificate["declarations"] if d["kind"] == z3.Z3_OP_ARRAY_MAP
                                   and d["parameters"] == old)
                declaration["range"] = sort
            return mutate

        # Another function, built in or declared, states another input.
        self._rejects("map_addition", parameter("map_addition", ["+"], ["-"]),
                      "certificate assertions do not match the original input")
        self._rejects("mapped_function_congruence", parameter("mapped_function_congruence", ["declared", "f"],
                                                              ["declared", "g"]),
                      "certificate assertions do not match the original input")
        # A declared name of another symbol, or of the same with another signature.
        self._rejects("map_function_read", parameter("map_function_read", ["declared", "f"], ["declared", "a"]),
                      "symbol used with two sorts|certificate assertions do not match")
        self._rejects("map_over_bool_elements", parameter("map_over_bool_elements", ["declared", "g"],
                                                          ["declared", "s"]),
                      "symbol used with two sorts|certificate assertions do not match")
        # Signatures a function does not have: + into Bool, a comparison into
        # Int, ite of three Int arrays, a declared function of no elements.
        self._rejects("map_addition", elements("map_addition", ["+"], "(Array Int Bool)"),
                      "invalid map or set operator declaration|wrong argument sort")
        self._rejects("map_comparison", parameter("map_comparison", ["<="], ["+"]),
                      "invalid map or set operator declaration")
        self._rejects("map_ite_symbolic", parameter("map_ite_symbolic", ["ite"], ["+"]),
                      "invalid map or set operator declaration")
        self._rejects("map_xor", parameter("map_xor", ["xor"], ["declared", ""]), "a map takes one supported function")
        self._rejects("map_xor", parameter("map_xor", ["xor"], ["<="]), "invalid map or set operator declaration")
        # The reconstructor alone rejects a map of an unbound function.
        graph = proof_to_lean._validate_graph(ARRAY_INPUTS["map_function_read"], self.certificates["map_function_read"])
        node = next(node for node in range(len(graph.nodes)) if graph.kind(node) == z3.Z3_OP_ARRAY_MAP)
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "map of an unbound function"):
            proof_to_lean._set_function(graph, node)

    def test_the_replay_reads_maps(self):
        """The replay rebuilds logged maps by function name: declared, built in, or rejected."""
        context = z3.Context()
        assertions, _ = proof_certificate.parse_assertions(ARRAY_INPUTS["mapped_function_congruence"], context,
                                                           integer=True)
        terms = proof_clause_log._Terms(context, assertions)
        self.assertIn("f", terms.functions)  # mapped, never applied
        mapped = terms.build([["_", "map", "f"], "a"])
        self.assertEqual(proof_certificate.map_parameters(mapped), ("declared", "f"))
        self.assertEqual(proof_certificate.map_parameters(terms.build([["_", "map", "+"], "a", "b"])), ("+",))
        self.assertEqual(proof_certificate.map_parameters(terms.build([["_", "map", "-"], "a"])), ("-",))
        # Z3 logs a built-in with its signature, which the trimmer needs to
        # parse the log back; the signature must be the application's.
        for head, arguments, parameters in (
                (["+", ["Int", "Int"], "Int"], ["a", "b"], ("+",)),
                (["-", ["Int"], "Int"], ["a"], ("-",)),
                (["<=", ["Int", "Int"], "Bool"], ["a", "b"], ("<=",)),
                (["f", ["Int"], "Int"], ["a"], ("declared", "f"))):
            with self.subTest(head=head):
                self.assertEqual(proof_certificate.map_parameters(terms.build([["_", "map", head]] + arguments)),
                                 parameters)
        for head, arguments, message in (
                (["+", ["Real", "Real"], "Real"], ["a", "b"], "another signature"),
                (["+", ["Int", "Int"], "Bool"], ["a", "b"], "another signature"),
                (["-", ["Int", "Int"], "Int"], ["a"], "another signature"),
                (["f", ["Int", "Int"], "Int"], ["a"], "another signature"),
                (["+", [], "Int"], ["a", "b"], "unsupported map function"),
                (["+", ["Int", "Int"]], ["a", "b"], "unsupported map function"),
                ([["+"], ["Int", "Int"], "Int"], ["a", "b"], "unsupported map function"),
                (["+", ["Int", ["Seq", "Int"]], "Int"], ["a", "b"], "unsupported sort")):
            with self.subTest(head=head):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, message):
                    terms.build([["_", "map", head]] + arguments)
        for head, arguments, message in (("*", ["a", "b"], "maps are supported over"),
                                         ("abs", ["a"], "unsupported map function|maps are supported over"),
                                         ("frobnicate", ["a"], "unsupported operator"),
                                         ("+", ["a", "3"], "map over unsupported sorts")):
            with self.subTest(head=head):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, message):
                    terms.build([["_", "map", head]] + arguments)
        # A built-in that z3py does not define on the elements is rejected, not a TypeError.
        assertions, _ = proof_certificate.parse_assertions("""(declare-sort E 0)
(declare-fun s () (Array Int Bool))
(declare-fun e () (Array Int E))
(assert (select s 0))
(assert (= (select e 0) (select e 1)))
(check-sat)
""", context, integer=True)
        terms = proof_clause_log._Terms(context, assertions)
        for head, arguments in (("-", ["s"]), ("<=", ["e", "e"]), ("not", ["e"])):
            with self.subTest(head=head, arguments=arguments):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, "ill-sorted map in the clause log"):
                    terms.build([["_", "map", head]] + arguments)

    def test_replay_keys_tell_maps_and_constant_arrays_apart(self):
        # The structural key of a map names its function, and that of a
        # constant array its sort; maps of and and or over the same arrays
        # shared one key, so the replay tied one to the other
        # (conjuncts_map_and_or, which Lean then rejected).
        context = z3.Context()
        assertions, _ = proof_certificate.parse_assertions("""(declare-fun a () (Array Int Bool))
(declare-fun b () (Array Int Bool))
(declare-fun c () (Array Int Bool))
(declare-fun x () (Array Int Int))
(declare-fun y () (Array Int Int))
(declare-fun z () (Array Int Int))
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun p () Bool)
(assert (= c ((_ map and) a b)))
(assert (= c ((_ map or) a b)))
(assert (= c ((_ map =>) a b)))
(assert (= z ((_ map f) x)))
(assert (= z ((_ map g) x)))
(assert (= z ((_ map (+ (Int Int) Int)) x y)))
(assert (= z ((_ map (- (Int Int) Int)) x y)))
(assert (= z ((_ map (- (Int) Int)) x)))
(assert (select ((as const (Array Int Bool)) p) 0))
(assert (select ((as const (Array Real Bool)) p) 0.0))
(check-sat)
""", context, integer=True)
        normalizer = proof_clause_log._Normalizer()
        keys = [normalizer.key(assertion) for assertion in assertions]
        self.assertEqual(len(set(keys)), len(assertions))
        # The clause log's maps, built in with their signature, key as the input's.
        terms = proof_clause_log._Terms(context, assertions)
        for head, arguments, assertion in ((["and", ["Bool", "Bool"], "Bool"], ["a", "b"], 0),
                                           ("or", ["a", "b"], 1), ("f", ["x"], 3),
                                           (["+", ["Int", "Int"], "Int"], ["x", "y"], 5),
                                           (["-", ["Int"], "Int"], ["x"], 7)):
            with self.subTest(head=head):
                mapped = terms.build([["_", "map", head]] + arguments)
                self.assertEqual(normalizer.key(assertions[assertion].arg(0) == mapped), keys[assertion])

    def test_numeral_expressions_get_their_values(self):
        # The outermost numeral expressions under a store get their values;
        # the certificate's own numerals, (- 1) and (/ 1 2), and the
        # summands of a sum that gets one do not.
        fact = re.compile(r"^\s*have _nv\d+ : \((.*)\) = (.*) := by grind$")
        expected = {"negative_index_as_a_difference": [("((((0 : Int))) - (((1 : Int))))", "((-1 : Int))")],
                    "fraction_sums_as_indices": [
                        ("((((((1 : Rat))) / (((4 : Rat))))) + (((((1 : Rat))) / (((4 : Rat))))))",
                         "((1 : Rat) / (2 : Rat))"),
                        ("((((((3 : Rat))) * (((((1 : Rat))) / (((3 : Rat))))))) - (((1 : Rat))))", "((0 : Rat))")]}
        for name, facts in expected.items():
            with self.subTest(name=name):
                text = proof_to_lean.reconstruct(ARRAY_INPUTS[name], self.certificates[name])
                found = {match.groups() for match in map(fact.match, text.split("\n")) if match}
                self.assertEqual(found, set(facts), text)

    def test_the_replay_reads_constant_arrays(self):
        context = z3.Context()
        assertions, _ = proof_certificate.parse_assertions(ARRAY_INPUTS["read_constant"], context, integer=True)
        terms = proof_clause_log._Terms(context, assertions)
        terms.define("$1", ["Array", "Int", "Int"], [["as", "const", ["Array", "Int", "Int"]], "5"])
        constant = terms.build("$1")
        self.assertTrue(z3.is_const_array(constant))
        self.assertTrue(z3.is_default(terms.build(["default", "a"])))
        # The axioms the array solver propagates list their equality.
        default = terms.build(["default", "$1"])
        self.assertTrue(proof_clause_log._store_axiom(default == 5))
        self.assertTrue(proof_clause_log._store_axiom(5 == terms.build(["select", "$1", "i"])))
        self.assertFalse(proof_clause_log._store_axiom(default == 6))
        for sort in (["Array", "Int", "Real"], ["Array", "Real", "Int"]):
            with self.subTest(sort=sort):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, "constant array of an unsupported"):
                    terms.build([["as", "const", sort], "5"])
        # Over Real indices, of an array sort of the input.
        assertions, _ = proof_certificate.parse_assertions(ARRAY_INPUTS["real_index_read"], context)
        terms = proof_clause_log._Terms(context, assertions)
        terms.define("$1", ["Array", "Real", "Real"], [["as", "const", ["Array", "Real", "Real"]], "5.0"])
        constant = terms.build("$1")
        self.assertTrue(z3.is_const_array(constant))
        self.assertTrue(constant.sort().domain().eq(z3.RealSort(context)))
        five = z3.RealVal(5, context)
        self.assertTrue(proof_clause_log._store_axiom(terms.build(["default", "$1"]) == five))
        self.assertTrue(proof_clause_log._store_axiom(five == terms.build(["select", "$1", "x"])))

    def test_reads_of_int_arrays_are_linear_atoms(self):
        """A Farkas lemma over reads of an Int array is checked over the reads as atoms."""
        certificate = self.certificates["int_read_other_index"]
        graph = proof_to_lean._validate_graph(ARRAY_INPUTS["int_read_other_index"], certificate)
        farkas = [node for node in range(len(graph.nodes)) if graph.kind(node) == z3.Z3_OP_PR_TH_LEMMA
                  and graph.decl(node).parameters[0] == "farkas"]
        self.assertTrue(farkas)
        reads = {node for node in range(len(graph.nodes)) if graph.kind(node) == z3.Z3_OP_SELECT}
        for node in farkas:
            terms = {}
            for literal in graph.clause(graph.conclusion(node)):
                atom = graph.arguments(literal)[0] if graph.kind(literal) == z3.Z3_OP_NOT else literal
                proof_to_lean._linear_term(graph, graph.arguments(atom)[0], 1, terms)
            self.assertTrue(set(terms) & reads)

    def test_tampered_arithmetic_arrays_are_rejected(self):
        def declaration(certificate, kind):
            return next(d for d in certificate["declarations"] if d["kind"] == kind)

        def select_into_real(certificate):
            declaration(certificate, z3.Z3_OP_SELECT)["range"] = "Real"

        def relabelled_arrays(target):
            def mutate(certificate):
                for d in certificate["declarations"]:
                    d["domain"] = [target if s == "(Array Int Int)" else s for s in d["domain"]]
                    if d["range"] == "(Array Int Int)":
                        d["range"] = target
            return mutate

        def farkas_as_array_lemma(certificate):
            # A Farkas lemma over reads of Int arrays: its inequalities are
            # not the (dis)equalities of an array axiom instance.
            for d in certificate["declarations"]:
                if d["name"] == "th-lemma" and d["parameters"][:1] == ["farkas"]:
                    d["parameters"] = ["array"]

        self._rejects("int_read_other_index", select_into_real, "invalid select declaration|wrong argument sort")
        # Bool elements are supported, but the reads stay Int-valued.
        self._rejects("int_read_other_index", relabelled_arrays("(Array Int Bool)"),
                      "invalid (select|store) declaration|wrong argument sort")
        self._rejects("int_read_other_index", relabelled_arrays("(Array Bool Int)"),
                      "invalid (select|store) declaration|wrong argument sort")
        self._rejects("int_read_other_index", relabelled_arrays("(Array Proof Int)"), "unsupported array sort")
        self._rejects("int_read_other_index", farkas_as_array_lemma, "array th-lemma literals must be equalities")

    def test_array_lemmas_are_equality_clauses(self):
        lemmas = {}
        for name, certificate in self.certificates.items():
            declarations, nodes = certificate["declarations"], certificate["nodes"]
            for node in nodes:
                declaration = declarations[node["declaration"]]
                if declaration["name"] == "th-lemma" and declaration["parameters"] == ["array"]:
                    lemmas.setdefault(name, []).append(node["arguments"][-1])
        self.assertLessEqual({"read_own_write", "read_other_index", "store_commutes", "write_back_read"},
                             set(lemmas))
        # The store axiom is a unit clause, the propagated equality itself
        # (its hint lists that equality, not its complement).
        certificate = self.certificates["read_own_write"]
        declarations, nodes = certificate["declarations"], certificate["nodes"]
        kinds = [declarations[nodes[clause]["declaration"]]["kind"] for clause in lemmas["read_own_write"]]
        self.assertIn(z3.Z3_OP_EQ, kinds)

    def test_extensionality_witnesses_reach_the_certificate(self):
        for name in ("store_commutes", "write_back_read", "storeinv_t2_00001"):
            with self.subTest(name=name):
                witnesses = _declarations(self.certificates[name], z3.Z3_OP_ARRAY_EXT)
                self.assertEqual(len(witnesses), 1)
                self.assertEqual(witnesses[0]["name"], "array-ext")
                self.assertEqual(witnesses[0]["parameters"], [])

    def test_encoding(self):
        text = proof_to_lean.reconstruct(ARRAY_INPUTS["store_commutes"], self.certificates["store_commutes"])
        self.assertIn("  arrs : Nat -> U -> U", text)
        self.assertIn("  nonempty : Nonempty U", text)
        self.assertIn("-- Array 0: \"a\"", text)
        self.assertIn(":= (_store (term_", text)
        self.assertIn(":= (_array_diff _m.nonempty (term_", text)
        self.assertIn(":= _array_ext _m.nonempty ((term_", text)
        self.assertIn(":= _store_apply ((term_", text)
        # Array terms stay folded in the lemmas, each store related to its
        # body by one definitional step.
        self.assertRegex(text, r"have _t[0-9]+ : \(term_[0-9]+ _atoms _m\) = \(_store \(\(term_")
        self.assertNotIn("sorry", text)
        self.assertNotIn("axiom ", text)
        # Without an extensionality witness there is no nonempty field.
        text = proof_to_lean.reconstruct(ARRAY_INPUTS["read_own_write"], self.certificates["read_own_write"])
        self.assertNotIn("nonempty", text)
        two = proof_to_lean.reconstruct(ARRAY_INPUTS["two_array_sorts"], self.certificates["two_array_sorts"])
        self.assertIn('-- Array sorts "(Array Index Element)", "(Array Index Key)" are functions', two)

    def test_array_facts_are_stated_over_folded_definitions(self):
        """Array facts and ite gates name the definitions they mention and are reverted around the unfold.

        Written out, the facts of array_chain_instance(8) repeated the stored
        chain of eight modular steps in full: 57 MB of Lean (55 MB with the
        chain as the index), now under 1 MB. The stored chain occurs in the
        goal only inside the folded store, so the unfold names it because the
        facts mention it (without that, grind fails on the lemmas).
        """
        for use in ("value", "index"):
            with self.subTest(use=use):
                source = array_chain_instance(8, use)
                text = proof_to_lean.reconstruct(source, _export(source))
                self.assertLess(len(text), 1500000)
                stores = 0
                for lemma in text.split("\nset_option maxHeartbeats ")[1:]:
                    lines = [line.strip() for line in lemma.split("\n")]
                    facts = [line for line in lines if re.match(r"have _[tsg]\d+", line)]
                    for fact in facts:
                        self.assertLess(len(fact), 400, fact)
                    store = next((re.match(r"have (_t\d+) : \(term_\d+ [^)]*\) = \(_store \(\(term_\d+ [^)]*\)\) "
                                           r"(.*)\) := rfl$", line)
                                  for line in facts if line.startswith("have _t")), None)
                    if store is None:
                        continue
                    name, stored = store.groups()
                    # The chain is the index or the value; the other is a
                    # variable or a numeral, written out.
                    chain = re.findall(r"term_\d+", stored)
                    self.assertEqual(len(chain), 1, stored)
                    stores += 1
                    revert = next(line for line in lines if line.startswith("revert "))
                    unfold = lines[lines.index(revert) + 1]
                    self.assertIn(name, revert.split())
                    self.assertTrue(unfold.startswith("unfold "), unfold)
                    self.assertIn(chain[0], unfold.split())
                    self.assertEqual(lines[lines.index(revert) + 2].split()[1:], revert.split()[1:])
                self.assertGreater(stores, 0)
                self.assertNotIn("sorry", text)
                self.assertNotIn("axiom ", text)

    def test_sort_header_comments(self):
        """The header names the carriers once and claims no missing sort, with or without arrays."""
        text = proof_to_lean.reconstruct(ARRAY_INPUTS["read_own_write"], self.certificates["read_own_write"])
        self.assertIn('-- Uninterpreted sorts "Element", "Index" are the one type _m.U;', text)
        self.assertIn('-- Array sorts "(Array Index Element)" are functions', text)
        self.assertNotIn("No uninterpreted sort", text)
        source = """(declare-sort S 0)
(declare-fun a () S)
(declare-fun b () S)
(declare-fun f (S) S)
(assert (= a b))
(assert (not (= (f a) (f b))))
(check-sat)
"""
        for export in (_export, proof_certificate.export_certificate):
            with self.subTest(export=export.__name__):
                text = proof_to_lean.reconstruct(source, export(source))
                self.assertIn('-- Uninterpreted sort "S" is the type _m.U;', text)
                self.assertNotIn("No uninterpreted sort", text)
                self.assertNotIn("Array sorts", text)

    def _rejects(self, name, mutate, message):
        certificate = copy.deepcopy(self.certificates[name])
        mutate(certificate)
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, message):
            proof_to_lean.reconstruct(ARRAY_INPUTS[name], certificate)

    def test_tampered_array_declarations_are_rejected(self):
        def declaration(certificate, kind):
            return next(d for d in certificate["declarations"] if d["kind"] == kind)

        def swap_store_domain(certificate):
            store = declaration(certificate, z3.Z3_OP_STORE)
            store["domain"] = [store["domain"][0], store["domain"][2], store["domain"][1]]

        def select_into_index(certificate):
            declaration(certificate, z3.Z3_OP_SELECT)["range"] = "Index"

        def rename_array_sort(certificate):
            for d in certificate["declarations"]:
                d["domain"] = ["(Array Element Index)" if s == "(Array Index Element)" else s for s in d["domain"]]
                if d["range"] == "(Array Index Element)":
                    d["range"] = "(Array Element Index)"

        def parenthesized_sort(certificate):
            for d in certificate["declarations"]:
                if d["range"] == "(Array Index Element)":
                    d["range"] = "(Array Index Element"

        self._rejects("read_other_index", swap_store_domain, "invalid store declaration")
        self._rejects("read_other_index", select_into_index, "invalid select declaration|wrong argument sort")
        self._rejects("read_other_index", rename_array_sort, "invalid store declaration")
        self._rejects("read_other_index", parenthesized_sort, "unsupported sort")

    def test_array_lemmas_over_other_atoms_are_rejected(self):
        certificate = self.certificates["arrays_with_integer_weights"]
        graph = proof_to_lean._validate_graph(ARRAY_INPUTS["arrays_with_integer_weights"], certificate)
        farkas = [node for node in range(len(graph.nodes)) if graph.kind(node) == z3.Z3_OP_PR_TH_LEMMA
                  and graph.decl(node).parameters[0] == "farkas"]
        self.assertTrue(farkas)
        relabeled = copy.deepcopy(certificate)
        declaration = relabeled["nodes"][farkas[0]]["declaration"]
        relabeled["declarations"][declaration]["parameters"] = ["array"]
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "array th-lemma literals must be equalities"):
            proof_to_lean.reconstruct(ARRAY_INPUTS["arrays_with_integer_weights"], relabeled)

    def test_the_replay_reads_array_terms(self):
        context = z3.Context()
        assertions, _ = proof_certificate.parse_assertions(ARRAY_INPUTS["store_injective_elsewhere"], context)
        terms = proof_clause_log._Terms(context, assertions)
        self.assertEqual(terms.sorts, {"Index", "Element"})
        terms.define("$1", ["Array", "Index", "Element"], ["store", "a", "i", "e"])
        terms.define("$2", "Index", [["_", "array-ext", "0"], "$1", "b"])
        witness = terms.build("$2")
        self.assertTrue(z3.is_app_of(witness, z3.Z3_OP_ARRAY_EXT))
        read = terms.build(["select", "$1", "$2"])
        self.assertEqual(str(read.sort()), "Element")
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "has sort"):
            terms.define("$3", ["Array", "Element", "Index"], ["store", "a", "i", "e"])
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "array-ext over"):
            terms.build([["_", "array-ext", "0"], "i", "j"])


def random_constant_array_instance(seed, variables=2, constraints=10, depth=2, constant=0.3, default=0.2,
                                   index="Int", element="Int", unnormalized=0.0):
    """A random input over (Array index element) with constant arrays, or None if sat.

    index and element are Int or Real. Array constants a0, a1, ..., constant
    arrays of element terms (with probability constant), stores, and ite
    over arrays; element terms are constants, numerals, reads at index
    constants and numerals, increments, ite, and default values of arrays
    built from constant arrays by store and ite (the default values the
    exporter admits next to array constants, with probability default also
    compared as atoms). Atoms are equalities, comparisons, distinct, and
    array equalities. Real numerals are integers or halves in lowest terms,
    1.0 or (/ 3 2). With probability unnormalized a numeral is written as an
    expression of its value instead, (+ 2 0), (* 1 2), (- (+ 2 1) 1), or
    over Real (/ 4 2), which Z3's rewriter evaluates. Over Int sorts and
    with unnormalized 0 the inputs are those of the generator before it
    took sorts, seed for seed.
    """
    rng = random.Random(seed)
    sort = "(Array %s %s)" % (index, element)
    lines = ["(set-logic ALL)", "(declare-const p Bool)", "(declare-const q Bool)"]
    lines += ["(declare-const a%d %s)" % (i, sort) for i in range(variables)]
    lines += ["(declare-const k%d %s)" % (i, index) for i in range(variables + 1)]
    lines += ["(declare-const x%d %s)" % (i, element) for i in range(variables)]

    def numeral(numeral_sort):
        number = rng.randrange(3)
        text = str(number) if numeral_sort == "Int" else rng.choice(["%d.0" % number, "(/ %d 2)" % (2 * number + 1)])
        if unnormalized and rng.random() < unnormalized:
            # The same value as an expression Z3's rewriter evaluates.
            one, zero = ("1", "0") if numeral_sort == "Int" else ("1.0", "0.0")
            forms = ["(+ %s %s)" % (text, zero), "(* %s %s)" % (one, text), "(- (+ %s %s) %s)" % (text, one, one)]
            if numeral_sort == "Real":
                forms.append("(/ (* 2.0 %s) 2.0)" % text if text.startswith("(") else "(/ %d 2)" % (2 * number))
            return rng.choice(forms)
        return text

    def position():
        if rng.random() < 0.3:
            return numeral(index)
        return "k%d" % rng.randrange(variables + 1)

    def array(d=depth):
        if rng.random() < constant:
            return "((as const %s) %s)" % (sort, value(max(d - 1, 0)))
        roll = rng.random()
        if d == 0 or roll < 0.4:
            return "a%d" % rng.randrange(variables)
        if roll < 0.8:
            return "(store %s %s %s)" % (array(d - 1), position(), value(d - 1))
        return "(ite %s %s %s)" % (rng.choice(["p", "q"]), array(d - 1), array(d - 1))

    def constant_built(d=depth):
        roll = rng.random()
        if d == 0 or roll < 0.4:
            return "((as const %s) %s)" % (sort, value(max(d - 1, 0)))
        if roll < 0.8:
            return "(store %s %s %s)" % (constant_built(d - 1), position(), value(d - 1))
        return "(ite %s %s %s)" % (rng.choice(["p", "q"]), constant_built(d - 1), constant_built(d - 1))

    def value(d=depth):
        roll = rng.random()
        if d == 0 or roll < 0.25:
            return "x%d" % rng.randrange(variables)
        if roll < 0.4:
            return numeral(element)
        if roll < 0.8:
            return "(select %s %s)" % (array(d - 1), position())
        if roll < 0.85:
            return "(default %s)" % constant_built(d - 1)
        if roll < 0.92:
            return "(+ %s %s)" % (value(d - 1), "1" if element == "Int" else "1.0")
        return "(ite %s %s %s)" % (rng.choice(["p", "q"]), value(d - 1), value(d - 1))

    def atom():
        if rng.random() < default:
            return "(= (default %s) %s)" % (constant_built(), value())
        roll = rng.random()
        if roll < 0.4:
            return "(= %s %s)" % (value(), value())
        if roll < 0.55:
            return "(<= %s %s)" % (value(), value())
        if roll < 0.65:
            return "(distinct %s %s %s)" % (value(), value(), value())
        if roll < 0.9:
            return "(= %s %s)" % (array(), array())
        return rng.choice(["p", "q"])

    def formula():
        roll = rng.random()
        if roll < 0.5:
            return atom()
        if roll < 0.8:
            return "(or %s %s)" % (atom(), atom())
        return "(not %s)" % atom()

    lines += ["(assert %s)" % formula() for _ in range(constraints)]
    lines.append("(check-sat)")
    source = "\n".join(lines) + "\n"
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set("timeout", 10000)
    solver.from_string(source)
    return source if solver.check() == z3.unsat else None


# Pinned unsatisfiable seeds of random_constant_array_instance. On
# iteration 84's macOS build each failed Lean before the rewriter's
# comparison of store chains over two constant arrays had its converse
# (131 and 139, _constant_chain_extensionality) or the fold of a store of
# (ite p c c) into a constant array of c had ite_self (246). (Seeds 1-200
# with the default options, 1-120 with variables=3, constraints=12,
# depth=3, 201-500 with constant=0.5, default=0.1, and 501-620 with
# constraints=12, depth=3, constant=0.4 then verify: 528 of 528.)
# Over (Array Real Real), 87 failed Lean on iteration 86's macOS build
# before a cnf lemma reading an array equated to a constant array got that
# constant array's reads (_compared_side_reads), and 48 before the
# extensionality witnesses of two arrays either way round were equal
# (_array_diff_comm). (Seeds 1-300 over Real/Real and 1-150 over Int/Real
# then verify.) Over (Array Real Int), 103 was rejected for an arithmetic
# step over both Int and Real atoms before the condition of an Int ite
# (a read of a store, rewritten) no longer counted among the step's atoms;
# seeds 1-300 then verify (192 of 192 on iteration 87's macOS build).
# With numerals written as expressions (unnormalized=0.8), 221 failed Lean
# on iteration 88's macOS build before the store identities' indices were
# evaluated first (_numeral_facts); 672 of the 673 unsat seeds of seeds
# 1-300 over Int/Int and Real/Real and 1-200 over Real/Int and Int/Real
# (constant=0.5) then verify. The remaining one, 102 over Real/Int, failed
# Lean before an ite of different store chains compared with a chain had
# a converse per branch (_ite_chain_extensionality).
_REAL_SORTS = {"index": "Real", "element": "Real"}
CONSTANT_ARRAY_SEEDS = (({}, 131), ({}, 139), ({"constant": 0.5, "default": 0.1}, 246), (_REAL_SORTS, 48),
                        (_REAL_SORTS, 87), ({"index": "Real", "element": "Int"}, 103), ({"unnormalized": 0.8}, 221),
                        ({"index": "Real", "element": "Int", "unnormalized": 0.8, "constant": 0.5}, 102))


def random_chain_comparison_instance(seed):
    """Random comparisons of store chains of 3 to 10 stores over constant arrays, or None if sat.

    Three chains over (Array Int Int) or (Array Real Int), at numeral and
    symbolic indices, compared pairwise under guards, with a few equalities,
    disequalities, and bounds over the values and indices. Most unsat seeds
    compare chains with more read facts than _COMPARISON_READS.
    """
    rng = random.Random(seed)
    sort = rng.choice(["Int", "Real"])
    lines = ["(set-logic ALL)", "(declare-const p Bool)", "(declare-const q Bool)"]
    lines += ["(declare-const k%d %s)" % (i, sort) for i in range(3)]
    lines += ["(declare-const x%d Int)" % i for i in range(3)]

    def index():
        if rng.random() < 0.6:
            return str(rng.randrange(6)) + (".0" if sort == "Real" else "")
        return "k%d" % rng.randrange(3)

    def value():
        return "x%d" % rng.randrange(3) if rng.random() < 0.7 else str(rng.randrange(3))

    def chain():
        array = "((as const (Array %s Int)) %s)" % (sort, value())
        for _ in range(rng.randrange(3, 11)):
            array = "(store %s %s %s)" % (array, index(), value())
        return array

    chains = [chain() for _ in range(3)]
    for _ in range(rng.randrange(2, 5)):
        left, right = rng.sample(chains, 2)
        atom = "(= %s %s)" % (left, right)
        lines.append("(assert (or %s %s))" % (rng.choice(["p", "q"]),
                                               atom if rng.random() < 0.5 else "(not %s)" % atom))
    lines.append("(assert (not p))")
    for _ in range(rng.randrange(1, 4)):
        if rng.random() < 0.5:
            lines.append("(assert (%s x%d x%d))" % (rng.choice(["=", "distinct", "<="]), rng.randrange(3),
                                                     rng.randrange(3)))
        else:
            lines.append("(assert (%s k%d %s))" % (rng.choice(["=", "distinct"]), rng.randrange(3), index()))
    lines.append("(check-sat)")
    source = "\n".join(lines) + "\n"
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set("timeout", 10000)
    solver.from_string(source)
    return source if solver.check() == z3.unsat else None


# Pinned unsatisfiable seeds of random_chain_comparison_instance (13 over
# Real indices, 14 over Int). On iteration 85's macOS build each failed Lean
# while _constant_array_comparisons dropped every read fact above
# _COMPARISON_READS; seeds 1-300 then verify, 145 of 145 unsat (91 above the
# cap), against 20 of the 45 unsat seeds 1-100 before.
CHAIN_COMPARISON_SEEDS = (13, 14)


def array_chain_instance(depth=6, use="value"):
    """The modular chains of test_proof_to_lean_lia.modular_chains_instance, compared through an array.

    a<depth> (x + 5 * depth modulo 17, an ite per step) is stored into A at
    i (use "value"; "real" over Real chains and elements) or is the index
    of a store of 1 (use "index"), and the read of M, said to be that store,
    at i or at b<depth / 2> (x + 10 * (depth / 2)) differs from it. Each
    step holds the previous one three times, so written out the stored term
    is about 3^depth times its definition: the shape of z3test's QF_AUFLIA
    dlx-regfile (register reads through shared nested ites), whose array
    facts were written out until they were stated folded (see
    proof_to_lean._array_helpers).

    The other uses reach the remaining kinds of array facts over a folded
    node: "const", a constant array of a<depth> (_select_const, the folded
    value); "bool", (< a<depth> 3) stored into an array of Bool (formula_N
    arguments); "ite", an ite over two stores at a<depth> whose condition
    is (< a<depth> 5), read at b<depth / 2> (the folded condition in the
    ite's _t fact).
    """
    real = use == "real"
    sort, suffix = ("Real", ".0") if real else ("Int", "")
    element = {"index": "Int", "ite": "Int", "bool": "Bool"}.get(use, sort)
    lines = ["(set-logic %s)" % ("QF_AUFLIRA" if real else "QF_ALIA"), "(declare-const x %s)" % sort,
             "(declare-const i Int)", "(declare-const A (Array Int %s))" % element,
             "(declare-const M (Array Int %s))" % element]
    if use == "ite":
        lines.append("(declare-const B (Array Int Int))")
    for name, step, count in (("a", 5, depth), ("b", 10, depth // 2)):
        previous = "x"
        for index in range(1, count + 1):
            lines.append("(define-fun %s%d () %s (let ((s (+ %s %d%s))) (ite (< s 17%s) s (- s 17%s))))" % (
                name, index, sort, previous, step, suffix, suffix, suffix))
            previous = "%s%d" % (name, index)
    lines.append("(assert (and (<= 0%s x) (< x 17%s)))" % (suffix, suffix))
    half = depth // 2
    if use == "index":
        lines += ["(assert (= M (store A a%d 1)))" % depth, "(assert (not (= (select M b%d) 1)))" % half]
    elif use == "const":
        lines += ["(assert (= M ((as const (Array Int Int)) a%d)))" % depth,
                  "(assert (not (= (select M i) b%d)))" % half]
    elif use == "bool":
        lines += ["(assert (= M (store A i (< a%d 3))))" % depth, "(assert (not (= (select M i) (< b%d 3))))" % half]
    elif use == "ite":
        lines += ["(assert (= M (ite (< a%d 5) (store A a%d 1) (store B a%d 1))))" % (depth, depth, depth),
                  "(assert (not (= (select M b%d) 1)))" % half]
    else:
        lines += ["(assert (= M (store A i a%d)))" % depth, "(assert (not (= (select M i) b%d)))" % half]
    return "\n".join(lines + ["(check-sat)"]) + "\n"


def _without_facts(text, matches):
    """The text without the have lines whose tactic matches selects, nor their names in revert and intro lines.

    Array facts that mention definitions are stated folded and reverted
    around the lemma's unfold (proof_to_lean._array_helpers), so a dropped
    fact leaves its name in those lines; a line the drop empties, or a dropped line that opens an
    alternative of first, becomes skip. The unfold also names the
    definitions the facts mention, so a dropped definitional equation lhs =
    rhs is kept as the tautology lhs = lhs /\\ rhs = rhs instead: its terms
    stay for the unfold to rewrite, its information goes.
    """
    names, kept = set(), []
    for line in text.split("\n"):
        tactic = line.lstrip(" |(")
        if tactic.startswith("have ") and matches(tactic):
            equation = re.match(r"have \S+ : (\(term_\d+ [^)]*\)) = (.*) := rfl$", tactic)
            if equation:
                line = line[:len(line) - len(tactic)] + "have %s : %s = %s /\\ %s = %s := ⟨rfl, rfl⟩" % (
                    tactic.split()[1], equation.group(1), equation.group(1), equation.group(2), equation.group(2))
                kept.append(line)
                continue
            names.add(tactic.split()[1])
            line = line[:len(line) - len(tactic)] + "skip"
        kept.append(line)
    for position, line in enumerate(kept):
        tactic = line.lstrip(" |(")
        words = tactic.split()
        if words[:1] in (["revert"], ["intro"]) and names.intersection(words[1:]):
            remaining = [word for word in words[1:] if word not in names]
            kept[position] = line[:len(line) - len(tactic)] + (" ".join(words[:1] + remaining) if remaining
                                                               else "skip")
    return "\n".join(kept)


def _check_in_lean(test, source, fragment):
    """Export through the clause log, reconstruct, and kernel-check; return the certificate."""
    certificate = _export(source)
    test.assertEqual(certificate["fragment"], fragment)
    _, report = lean_test_support.check(test, source, certificate)
    test.assertTrue(_STANDARD_AXIOMS in report or "does not depend on any axioms" in report, report)
    return certificate


class TestArrayLeanIntegration(unittest.TestCase):
    """End-to-end: clause log, certificate, Lean reconstruction, kernel check."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")

    def test_documented_inputs_verify(self):
        lean_test_support.prefetch((source, _export(source)) for source in ARRAY_INPUTS.values())
        hints = set()
        for name, source in ARRAY_INPUTS.items():
            with self.subTest(name=name):
                hints |= _hints(_check_in_lean(self, source, _FRAGMENTS.get(name, "qf_uf")))
        self.assertLessEqual({"array", "euf"}, hints)

    def test_pinned_random_constant_array_instances_verify(self):
        sources = []
        for arguments, seed in CONSTANT_ARRAY_SEEDS:
            source = random_constant_array_instance(seed, **arguments)
            self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
            sorts = {arguments.get("index", "Int"), arguments.get("element", "Int")}
            self.assertIn("(as const (Array %s %s))" % (arguments.get("index", "Int"), arguments.get("element", "Int")),
                          source)
            fragment = {frozenset({"Int"}): "qf_uflia", frozenset({"Real"}): "qf_uflra"}.get(frozenset(sorts),
                                                                                             "qf_uflira")
            sources.append((seed, source, fragment, _export(source)))
        lean_test_support.prefetch((source, certificate) for _, source, _, certificate in sources)
        for seed, source, fragment, certificate in sources:
            with self.subTest(seed=seed):
                self.assertEqual(certificate["fragment"], fragment)
                _, report = lean_test_support.check(self, source, certificate)
                self.assertTrue(_STANDARD_AXIOMS in report or "does not depend on any axioms" in report, report)

    def test_pinned_random_chain_comparisons_verify(self):
        sources = []
        for seed in CHAIN_COMPARISON_SEEDS:
            source = random_chain_comparison_instance(seed)
            self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
            sources.append((seed, source, _export(source)))
        lean_test_support.prefetch((source, certificate) for _, source, certificate in sources)
        for seed, source, certificate in sources:
            with self.subTest(seed=seed):
                _, report = lean_test_support.check(self, source, certificate)
                self.assertTrue(_STANDARD_AXIOMS in report or "does not depend on any axioms" in report, report)

    def test_nested_ite_chains_through_arrays_verify(self):
        """Chains of eight modular steps stored into an array, as its index, and over Real verify folded.

        Written out (see test_array_facts_are_stated_over_folded_definitions)
        the six-step chain stored as a value checked in 78 s at 3.9 GB, and
        eight steps (57 MB of Lean) were out of reach; folded, eight steps
        check in about 17 s (value), 6 s (index), and 4 s (Real) together
        at most 1.7 GB.
        """
        sources = [(use, array_chain_instance(8, use)) for use in ("value", "index", "real")]
        lean_test_support.prefetch((source, _export(source)) for _, source in sources)
        for use, source in sources:
            with self.subTest(use=use):
                _check_in_lean(self, source, "qf_uflira" if use == "real" else "qf_uflia")

    def test_folded_chains_in_other_array_facts_verify(self):
        """Six-step chains as a constant array's value, a Bool element, and an ite's condition and index verify.

        These reach the folded nodes of _select_const facts, formula_N
        arguments of a store, and the condition of an ite over arrays
        (array_chain_instance); written out they were 5 to 11 MB of Lean,
        folded they are under 0.7 MB.
        """
        sources = [(use, array_chain_instance(6, use)) for use in ("const", "bool", "ite")]
        lean_test_support.prefetch((source, _export(source)) for _, source in sources)
        for use, source in sources:
            with self.subTest(use=use):
                _check_in_lean(self, source, "qf_uflia")

    def test_numeral_facts_are_needed(self):
        """Without the values of numeral expressions, or rewritten after their subterms, simp misses the identities."""
        fact = re.compile(r"^\s*have _nv\d+ : .* = \(\(-?\d+ : (Int|Rat)\)( / \(\d+ : Rat\))?\) := by grind$")
        name = re.compile(r"↓ _nv\d+, ")
        for input_name, variant in (("read_stored_back_at_a_fraction_of_one", "dropped"),
                                    ("store_over_a_store_at_products", "dropped"),
                                    ("constant_stored_into_its_constant_array", "dropped"),
                                    ("shared_numeral_expression", "post-order")):
            with self.subTest(name=input_name, variant=variant):
                source = NUMERAL_EXPRESSION_INPUTS[input_name]
                lines = proof_to_lean.reconstruct(source, _export(source)).split("\n")
                self.assertTrue(any(map(fact.match, lines)), "\n".join(lines))
                if variant == "dropped":
                    stripped = "\n".join(name.sub("", line) for line in lines if not fact.match(line))
                else:
                    stripped = "\n".join(line.replace("↓ _nv", "_nv") for line in lines)
                with tempfile.TemporaryDirectory() as directory:
                    output = Path(directory) / "stripped.lean"
                    output.write_text(stripped)
                    result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(output)], text=True,
                                            capture_output=True)
                report = result.stdout + result.stderr
                self.assertNotEqual(result.returncode, 0, report)
                errors = [line for line in report.split("\n") if "error:" in line]
                self.assertTrue(errors, report)
                for error in errors:
                    self.assertIn("`grind` failed", error)

    def test_constant_chain_facts_are_needed(self):
        """Without the converse of store-chain comparisons, of their ites' branches, or without ite_self, grind
        cannot prove the rewrites."""
        chain_fact = re.compile(r"^\s*have _x\d+ : _select ")
        ite_fact = re.compile(r"^\s*have _x\d+_\d+ : ")
        cases = [(name, chain_fact) for name in ("store_over_another_constant", "store_chains_over_two_constants",
                                                 "store_against_an_ite_of_one_constant",
                                                 "real_index_store_over_another_constant",
                                                 "store_of_an_ite_of_the_constant")]
        cases += [(name, ite_fact) for name in ("ite_of_chains_against_a_chain", "ites_of_chains_on_both_sides",
                                                "nested_ites_of_chains")]
        for name, fact in cases:
            with self.subTest(name=name):
                source = ARRAY_INPUTS[name]
                text = proof_to_lean.reconstruct(source, _export(source))
                lines = text.split("\n")
                if name == "store_of_an_ite_of_the_constant":
                    self.assertIn("_select_const, ite_self, ", text)
                else:
                    self.assertTrue(any(map(fact.match, lines)), text)
                stripped = "\n".join(line.replace("ite_self, ", "") if fact is chain_fact and "simp only [" in line
                                     else line for line in lines if not fact.match(line))
                with tempfile.TemporaryDirectory() as directory:
                    output = Path(directory) / "stripped.lean"
                    output.write_text(stripped)
                    result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(output)], text=True,
                                            capture_output=True)
                report = result.stdout + result.stderr
                self.assertNotEqual(result.returncode, 0, report)
                errors = [line for line in report.split("\n") if "error:" in line]
                self.assertTrue(errors, report)
                for error in errors:
                    self.assertIn("`grind` failed", error)

    def test_array_facts_are_needed(self):
        """Without the _store_apply, _array_ext, and default-value facts grind cannot prove the array lemmas."""
        for name in ("store_commutes", "int_store_commutes", "z3test_2549", "store_over_constants",
                     "real_index_2549", "constant_comparison_under_cnf"):
            with self.subTest(name=name):
                source = ARRAY_INPUTS[name]
                text = proof_to_lean.reconstruct(source, _export(source))
                stripped = _without_facts(text, lambda tactic: any(
                    fact in tactic for fact in (":= _store_apply ", ":= _array_ext ", ":= _default_")))
                self.assertNotEqual(stripped, text)
                with tempfile.TemporaryDirectory() as directory:
                    output = Path(directory) / "stripped.lean"
                    output.write_text(stripped)
                    result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(output)], text=True,
                                            capture_output=True)
                report = result.stdout + result.stderr
                self.assertNotEqual(result.returncode, 0, report)
                # Every error is grind (after omega, over Int) failing on an
                # array lemma, not a dangling reference to a removed fact.
                errors = [line for line in report.split("\n") if "error:" in line]
                self.assertTrue(errors, report)
                for error in errors:
                    self.assertIn("`grind` failed", error)

    def test_application_facts_are_needed(self):
        """Without the _t facts of applications into arrays grind cannot compare them by their arguments."""
        source = ARRAY_INPUTS["function_into_arrays"]
        text = proof_to_lean.reconstruct(source, _export(source))
        application = re.compile(r"^\s*have _t\d+ : \(term_\d+ [^)]*\) = _m\.arrs_funs ")
        lines = text.split("\n")
        self.assertTrue(any(map(application.match, lines)), text)
        stripped = _without_facts(text, application.match)
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "stripped.lean"
            output.write_text(stripped)
            result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(output)], text=True, capture_output=True)
        report = result.stdout + result.stderr
        self.assertNotEqual(result.returncode, 0, report)
        errors = [line for line in report.split("\n") if "error:" in line]
        self.assertTrue(errors, report)
        for error in errors:
            self.assertIn("`grind` failed", error)

    def test_reads_down_to_constant_arrays_are_needed(self):
        """Without the lower-level facts of a read the rewriter evaluates grind cannot prove its rewrite.

        The read is of stores over a constant array, of stores at numerals
        other than the read's over a plain array, or of an ite over a
        constant array.
        """
        for name, fact in (("read_of_store_over_constant", "_select_const"), ("singleton_set", "_select_const"),
                           ("read_through_numeral_stores", "_store_apply"),
                           ("set_read_through_numeral_stores", "_store_apply"),
                           ("read_through_numeral_stores_to_own_index", "_store_apply"),
                           ("read_through_negative_numeral_stores", "_store_apply"),
                           ("bool_index_read_through_value_stores", "_store_apply"),
                           ("read_of_an_ite_over_a_constant", "_select_const")):
            with self.subTest(name=name):
                source = ARRAY_INPUTS[name]
                text = proof_to_lean.reconstruct(source, _export(source))
                # _s<n> is the read's store level, _s<n>_<k> the levels below,
                # _si<n>_<k> those of the branches of an ite read.
                level = re.compile(r"^\s*have _si?\d+_\d+ := %s " % fact)
                lines = text.split("\n")
                self.assertTrue(any(map(level.match, lines)), text)
                # The array rewrite alternative's simp set evaluates reads of
                # constant arrays too (_select_const), so it goes as well.
                stripped = "\n".join(line.replace("_select_const, ", "") if "simp only [" in line else line
                                     for line in _without_facts(text, level.match).split("\n"))
                with tempfile.TemporaryDirectory() as directory:
                    output = Path(directory) / "stripped.lean"
                    output.write_text(stripped)
                    result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(output)], text=True,
                                            capture_output=True)
                report = result.stdout + result.stderr
                self.assertNotEqual(result.returncode, 0, report)
                errors = [line for line in report.split("\n") if "error:" in line]
                self.assertTrue(errors, report)
                for error in errors:
                    self.assertIn("`grind` failed", error)

    def test_stored_row_facts_are_needed(self):
        """Without the _n facts of a read through a stored row grind cannot prove the rewriter's evaluation."""
        for name in ("nested_sets", "nested_constant_evaluated", "three_levels_evaluated"):
            with self.subTest(name=name):
                source = ARRAY_INPUTS[name]
                text = proof_to_lean.reconstruct(source, _export(source))
                fact = re.compile(r"^\s*have _n\d+_\d+ := _(store_apply|select_const) ")
                lines = text.split("\n")
                self.assertTrue(any(map(fact.match, lines)), text)
                stripped = _without_facts(text, fact.match)
                with tempfile.TemporaryDirectory() as directory:
                    output = Path(directory) / "stripped.lean"
                    output.write_text(stripped)
                    result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(output)], text=True,
                                            capture_output=True)
                report = result.stdout + result.stderr
                self.assertNotEqual(result.returncode, 0, report)
                errors = [line for line in report.split("\n") if "error:" in line]
                self.assertTrue(errors, report)
                for error in errors:
                    self.assertIn("`grind` failed", error)

    def test_comparison_reads_are_needed(self):
        """Without the read facts of _constant_array_comparisons grind cannot prove the rewrite of array.smt2's q2.

        Nor of long chains, whose reads above _COMPARISON_READS are those of
        the compared chains only (_chain_comparison_reads).
        """
        for name in ("z3test_array_q2", "real_index_comparison", "long_store_chains_over_two_constants"):
            with self.subTest(name=name):
                source = ARRAY_INPUTS[name]
                text = proof_to_lean.reconstruct(source, _export(source))
                # The reads at the stored indices: _e<n>_<i> (congruence of
                # an array equality), _ds<n>_<i> (_store_apply), _dc<n>_<i>
                # (_select_const).
                read = re.compile(r"^\s*have _(e|ds|dc)\d+_\d+ ")
                lines = text.split("\n")
                self.assertTrue({match.group(1) for match in map(read.match, lines) if match} >= {"e", "ds", "dc"},
                                text)
                stripped = "\n".join(line for line in lines if not read.match(line))
                with tempfile.TemporaryDirectory() as directory:
                    output = Path(directory) / "stripped.lean"
                    output.write_text(stripped)
                    result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(output)], text=True,
                                            capture_output=True)
                report = result.stdout + result.stderr
                self.assertNotEqual(result.returncode, 0, report)
                errors = [line for line in report.split("\n") if "error:" in line]
                self.assertTrue(errors, report)
                for error in errors:
                    self.assertIn("`grind` failed", error)

    def test_map_facts_are_needed(self):
        """Without the read facts below a map, or the map identities, grind cannot prove the steps over maps."""
        for name, fact in (("z3test_t8", r"have _m\d+_\d+ : "), ("read_of_map_over_constants", r"have _m\d+_\d+ := "),
                           ("union_commutes", r"have _mc\d+ := "), ("complement_twice", r"have _mn\d+ := "),
                           ("intersection_idempotent", r"have _mi\d+ := "), ("map_of_stores", r"have _ms\d+ := "),
                           ("setminus_named", r"have _md\d+ : "),
                           ("map_of_store_and_constant", r"have _mk\d+_\d+ := "),
                           ("map_of_constants", r"have _mk\d+ : "),
                           ("map_function_read", r"have _m\d+ : "), ("addition_commutes", r"have _mc\d+ := "),
                           ("equality_map_commutes", r"have _mc\d+ := "),
                           ("function_map_of_stores", r"have _ms\d+ := "),
                           ("nested_function_maps", r"have _m\d+_\d+ : "),
                           ("read_through_store_to_map", r"have _sm\d+ : "),
                           ("set_read_through_store_to_map", r"have _sm\d+ : ")):
            with self.subTest(name=name):
                source = ARRAY_INPUTS[name]
                text = proof_to_lean.reconstruct(source, _export(source))
                pattern = re.compile(r"^\s*" + fact)
                lines = text.split("\n")
                self.assertTrue(any(map(pattern.match, lines)), text)
                stripped = _without_facts(text, pattern.match)
                with tempfile.TemporaryDirectory() as directory:
                    output = Path(directory) / "stripped.lean"
                    output.write_text(stripped)
                    result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(output)], text=True,
                                            capture_output=True)
                report = result.stdout + result.stderr
                self.assertNotEqual(result.returncode, 0, report)
                errors = [line for line in report.split("\n") if "error:" in line]
                self.assertTrue(errors, report)
                for error in errors:
                    self.assertIn("`grind` failed", error)


if __name__ == "__main__":
    unittest.main()
