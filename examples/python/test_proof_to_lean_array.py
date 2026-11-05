############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for the array slice of the Lean reconstruction: arrays over
# uninterpreted sorts, Int, and Real (elements also Bool), constant arrays
# over Int and Real indices, and functions into arrays, certified through the
# sat.smt clause log.
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
import hashlib
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

import z3

_EXAMPLES = Path(__file__).resolve().parent
sys.path.insert(0, str(_EXAMPLES))
import proof_certificate
import proof_clause_log
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
ARRAY_INPUTS.update(ARITHMETIC_ARRAY_INPUTS)
ARRAY_INPUTS.update(CONSTANT_ARRAY_INPUTS)
ARRAY_INPUTS.update(REAL_INDEX_CONSTANT_ARRAY_INPUTS)
ARRAY_INPUTS.update(ARRAY_FUNCTION_INPUTS)
ARRAY_INPUTS.update(BOOL_ELEMENT_INPUTS)
# The fragment of each documented input (the others are qf_uf).
_FRAGMENTS = {"arrays_with_integer_weights": "qf_uflia", "real_read_own_write": "qf_uflra",
              "int_indices_real_elements": "qf_uflira", "real_constants": "qf_uflira",
              "real_index_2549": "qf_uflira", "real_index_read": "qf_uflra",
              "real_index_comparison": "qf_uflira", "real_index_terms": "qf_uflra",
              "real_index_elements": "qf_uflra", "int_function_into_arrays": "qf_uflia",
              "real_function_into_arrays": "qf_uflra", "function_into_constant_arrays": "qf_uflira",
              "predicate_over_application": "qf_uflia", "nested_applications": "qf_uflia",
              "array_function_twice": "qf_uflia", "two_functions_into_arrays": "qf_uflia",
              "real_set": "qf_uflra"}
_FRAGMENTS.update((name, "qf_uflia") for name, source in BOOL_ELEMENT_INPUTS.items()
                  if "Array Int Bool" in source)
_FRAGMENTS.update((name, "qf_uflia") for name in list(ARITHMETIC_ARRAY_INPUTS) + list(CONSTANT_ARRAY_INPUTS)
                  if name not in _FRAGMENTS)


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
            # Bool elements are supported (BOOL_ELEMENT_INPUTS), Bool indices not.
            "(declare-fun a () (Array Bool Int))(declare-fun b () (Array Bool Int))(assert (not (= a b)))":
                "only arrays over uninterpreted sorts, Int, and Real",
            "(declare-fun a () (Array Bool Bool))(assert (select a true))":
                "only arrays over uninterpreted sorts, Int, and Real",
            "(declare-fun a () (Array Int (Array Int Bool)))(assert (select (select a 0) 1))":
                "unsupported array operator: select",
            "(declare-sort I 0)(declare-fun a () (Array I I I))(declare-fun i () I)"
            "(assert (not (= (select a i i) (select a i i))))": "only arrays over uninterpreted sorts",
            "(declare-sort I 0)(declare-fun a () (Array I (Array I I)))(declare-fun i () I)"
            "(assert (not (= (select (select a i) i) i)))": "unsupported array operator: select",
            "(declare-sort I 0)(declare-fun a () (Array I (Array I I)))(declare-fun b () (Array I (Array I I)))"
            "(assert (not (= a b)))": "only arrays over uninterpreted sorts",
            # Constant arrays over a possibly finite index sort.
            "(declare-sort I 0)(declare-fun e () I)(declare-fun i () I)"
            "(assert (not (= (select ((as const (Array I I)) e) i) e)))":
                "constant arrays are supported over Int and Real indices only",
            # Array combinators of Z3's beyond SMT-LIB.
            "(declare-fun g (Int) Int)(declare-fun a () (Array Int Int))(assert (= (select ((_ map g) a) 1) 1))":
                "unsupported array operator",
            # Functions over and into arrays are supported, but not into or
            # over arrays of an unsupported sort.
            "(declare-sort I 0)(declare-fun h (I) (Array Bool I))(declare-fun i () I)"
            "(assert (not (= (h i) (h i))))": "uninterpreted functions over",
            "(declare-sort I 0)(declare-fun h (I) (Array I (Array I I)))(declare-fun i () I)"
            "(assert (not (= (h i) (h i))))": "uninterpreted functions over",
            "(declare-fun h ((Array Bool Int)) Int)(declare-fun a () (Array Bool Int))"
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

        # Bool indices are not supported (a finite index sort).
        self._rejects("set_insert_elsewhere", relabelled("(Array Int Bool)", "(Array Bool Bool)"),
                      "unsupported array sort")
        self._rejects("set_insert_elsewhere", relabelled("(Array Int Bool)", "(Array Int Int)"),
                      "invalid select declaration|invalid store declaration|wrong argument sort")
        self._rejects("set_insert_elsewhere", select_into_int, "invalid select declaration|wrong argument sort")
        self._rejects("set_insert_elsewhere", store_of_index, "invalid store declaration")
        # The input's sort is bound: Bool elements over another index sort.
        self._rejects("bool_read_own_write", relabelled("(Array Index Bool)", "(Array Index Index)"),
                      "invalid select declaration|invalid store declaration|wrong argument sort")

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
        self._rejects("int_read_other_index", relabelled_arrays("(Array Bool Int)"), "unsupported array sort")
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


def _check_in_lean(test, source, fragment):
    """Export through the clause log, reconstruct, and kernel-check; return the certificate."""
    certificate = _export(source)
    test.assertEqual(certificate["fragment"], fragment)
    with tempfile.TemporaryDirectory() as directory:
        output = Path(directory) / "checked.lean"
        proof_to_lean.check_and_write(source, certificate, output)
        text = output.read_text()
        namespace = "Z3Proofs.NativeCertificate.p" + hashlib.sha256(source.encode()).hexdigest()
        output.write_text(text + "\n#print axioms %s.unsat\n" % namespace)
        result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(output)], text=True, capture_output=True)
        test.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        report = " ".join(result.stdout.split())
        test.assertTrue(_STANDARD_AXIOMS in report or "does not depend on any axioms" in report, report)
    return certificate


class TestArrayLeanIntegration(unittest.TestCase):
    """End-to-end: clause log, certificate, Lean reconstruction, kernel check."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")

    def test_documented_inputs_verify(self):
        hints = set()
        for name, source in ARRAY_INPUTS.items():
            with self.subTest(name=name):
                hints |= _hints(_check_in_lean(self, source, _FRAGMENTS.get(name, "qf_uf")))
        self.assertLessEqual({"array", "euf"}, hints)

    def test_array_facts_are_needed(self):
        """Without the _store_apply, _array_ext, and default-value facts grind cannot prove the array lemmas."""
        for name in ("store_commutes", "int_store_commutes", "z3test_2549", "store_over_constants",
                     "real_index_2549"):
            with self.subTest(name=name):
                source = ARRAY_INPUTS[name]
                text = proof_to_lean.reconstruct(source, _export(source))
                stripped = "\n".join(line for line in text.split("\n")
                                     if ":= _store_apply " not in line and ":= _array_ext " not in line
                                     and ":= _default_" not in line)
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
        stripped = "\n".join(line for line in lines if not application.match(line))
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

        The read is of stores over a constant array, or of stores at
        numerals other than the read's over a plain array.
        """
        for name, fact in (("read_of_store_over_constant", "_select_const"), ("singleton_set", "_select_const"),
                           ("read_through_numeral_stores", "_store_apply"),
                           ("set_read_through_numeral_stores", "_store_apply"),
                           ("read_through_numeral_stores_to_own_index", "_store_apply"),
                           ("read_through_negative_numeral_stores", "_store_apply")):
            with self.subTest(name=name):
                source = ARRAY_INPUTS[name]
                text = proof_to_lean.reconstruct(source, _export(source))
                # _s<n> is the read's store level, _s<n>_<k> the levels below.
                level = re.compile(r"^\s*have _s\d+_\d+ := %s " % fact)
                lines = text.split("\n")
                self.assertTrue(any(map(level.match, lines)), text)
                stripped = "\n".join(line for line in lines if not level.match(line))
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
        """Without the read facts of _constant_array_comparisons grind cannot prove the rewrite of array.smt2's q2."""
        for name in ("z3test_array_q2", "real_index_comparison"):
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


if __name__ == "__main__":
    unittest.main()
